// The trusted shims of vbm-journal (docs/trust-ledger.md): POSIX file calls and SHA-256. Nothing here is verified;
// each function is the real counterpart of a Lean model (VbmJournal/Driver.lean, Sha256.lean), and is tested against it.
#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static lean_obj_res fail(const char *what, int e) {
  char buf[256];
  snprintf(buf, sizeof buf, "%s: %s", what, strerror(e));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}
static lean_obj_res ok(void) { return lean_io_result_mk_ok(lean_box(0)); }

static int write_all(int fd, const uint8_t *p, size_t n) {
  while (n > 0) {
    ssize_t r = write(fd, p, n);
    if (r < 0) { if (errno == EINTR) continue; return -1; }
    p += r; n -= (size_t)r;
  }
  return 0;
}

// fsync of the directory that holds `path` (the file's directory entry).
static int sync_dir(const char *path) {
  const char *slash = strrchr(path, '/');
  size_t n = slash ? (size_t)(slash - path) : 0;
  char *dir = strndup(slash ? (n ? path : "/") : ".", slash && n ? n : 1);
  if (!dir) return -1;
  int fd = open(dir, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  free(dir);
  if (fd < 0) return -1;
  int rc = fsync(fd), e = errno;
  close(fd);
  errno = e;
  return rc;
}

// write: append to `path` (created, owner-only), one loop of write(2), then close.
LEAN_EXPORT lean_obj_res vbm_write(b_lean_obj_arg path, b_lean_obj_arg bytes, lean_obj_arg w) {
  (void)w;
  int fd = open(lean_string_cstr(path), O_WRONLY | O_APPEND | O_CREAT | O_CLOEXEC, 0600);
  if (fd < 0) return fail("journal open", errno);
  if (write_all(fd, lean_sarray_cptr(bytes), lean_sarray_size(bytes)) != 0) { int e = errno; close(fd); return fail("journal write", e); }
  if (close(fd) != 0) return fail("journal close", errno);
  return ok();
}

// fsync: make the file's data durable.
LEAN_EXPORT lean_obj_res vbm_fsync(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  int fd = open(lean_string_cstr(path), O_RDONLY | O_CLOEXEC);
  if (fd < 0) return fail("journal open", errno);
  if (fsync(fd) != 0) { int e = errno; close(fd); return fail("journal fsync", e); }
  close(fd);
  return ok();
}

// fsyncDir: make the file's directory entry durable.
LEAN_EXPORT lean_obj_res vbm_fsync_dir(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  if (sync_dir(lean_string_cstr(path)) != 0) return fail("journal dir fsync", errno);
  return ok();
}

// truncate: cut the file back to `len` bytes, then make the cut durable.
LEAN_EXPORT lean_obj_res vbm_truncate(b_lean_obj_arg path, uint64_t len, lean_obj_arg w) {
  (void)w;
  int fd = open(lean_string_cstr(path), O_WRONLY | O_CLOEXEC);
  if (fd < 0) return fail("journal open", errno);
  if (ftruncate(fd, (off_t)len) != 0) { int e = errno; close(fd); return fail("journal truncate", e); }
  if (fsync(fd) != 0) { int e = errno; close(fd); return fail("journal fsync", e); }
  close(fd);
  return ok();
}

// readFile: all the bytes of the file; `none` when there is no such file.
LEAN_EXPORT lean_obj_res vbm_read_file(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  int fd = open(lean_string_cstr(path), O_RDONLY | O_CLOEXEC);
  if (fd < 0) return errno == ENOENT ? lean_io_result_mk_ok(lean_box(0)) : fail("journal open", errno);
  size_t cap = 4096, len = 0;
  uint8_t *buf = malloc(cap);
  for (;;) {
    if (!buf) { close(fd); return fail("journal read", ENOMEM); }
    if (len == cap) { cap *= 2; buf = realloc(buf, cap); continue; }
    ssize_t r = read(fd, buf + len, cap - len);
    if (r < 0 && errno == EINTR) continue;
    if (r < 0) { int e = errno; free(buf); close(fd); return fail("journal read", e); }
    if (r == 0) break;
    len += (size_t)r;
  }
  close(fd);
  lean_object *a = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(a), buf, len);
  free(buf);
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, a);
  return lean_io_result_mk_ok(some);
}

// replace: the file becomes exactly these bytes, all or nothing: write `path.tmp`, fsync it, rename over `path`, fsync the directory.
LEAN_EXPORT lean_obj_res vbm_replace(b_lean_obj_arg path, b_lean_obj_arg bytes, lean_obj_arg w) {
  (void)w;
  const char *p = lean_string_cstr(path);
  size_t n = strlen(p);
  char *tmp = malloc(n + 5);
  if (!tmp) return fail("signature", ENOMEM);
  memcpy(tmp, p, n); memcpy(tmp + n, ".tmp", 5);
  int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
  if (fd < 0) { int e = errno; free(tmp); return fail("signature open", e); }
  if (write_all(fd, lean_sarray_cptr(bytes), lean_sarray_size(bytes)) != 0 || fsync(fd) != 0) {
    int e = errno; close(fd); free(tmp); return fail("signature write", e);
  }
  if (close(fd) != 0 || rename(tmp, p) != 0) { int e = errno; free(tmp); return fail("signature rename", e); }
  free(tmp);
  if (sync_dir(p) != 0) return fail("signature dir fsync", errno);
  return ok();
}

// SHA-256 (FIPS 180-4), one shot.
static const uint32_t K[64] = {
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be,
  0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa,
  0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85,
  0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f,
  0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void block(uint32_t h[8], const uint8_t *p) {
  uint32_t w[64], v[8];
  for (int i = 0; i < 16; i++) w[i] = (uint32_t)p[4 * i] << 24 | (uint32_t)p[4 * i + 1] << 16 | (uint32_t)p[4 * i + 2] << 8 | p[4 * i + 3];
  for (int i = 16; i < 64; i++) {
    uint32_t a = w[i - 15], b = w[i - 2];
    w[i] = w[i - 16] + (ROR(a, 7) ^ ROR(a, 18) ^ (a >> 3)) + w[i - 7] + (ROR(b, 17) ^ ROR(b, 19) ^ (b >> 10));
  }
  memcpy(v, h, sizeof v);
  for (int i = 0; i < 64; i++) {
    uint32_t t1 = v[7] + (ROR(v[4], 6) ^ ROR(v[4], 11) ^ ROR(v[4], 25)) + ((v[4] & v[5]) ^ (~v[4] & v[6])) + K[i] + w[i];
    uint32_t t2 = (ROR(v[0], 2) ^ ROR(v[0], 13) ^ ROR(v[0], 22)) + ((v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]));
    memmove(v + 1, v, 7 * sizeof v[0]);
    v[4] += t1;
    v[0] = t1 + t2;
  }
  for (int i = 0; i < 8; i++) h[i] += v[i];
}

LEAN_EXPORT lean_obj_res vbm_sha256(b_lean_obj_arg msg) {
  uint32_t h[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
  const uint8_t *p = lean_sarray_cptr(msg);
  size_t n = lean_sarray_size(msg), i = 0;
  for (; i + 64 <= n; i += 64) block(h, p + i);
  uint8_t last[128] = {0};
  size_t r = n - i, total = r < 56 ? 64 : 128;
  memcpy(last, p + i, r);
  last[r] = 0x80;
  uint64_t bits = (uint64_t)n * 8;
  for (int k = 0; k < 8; k++) last[total - 1 - k] = (uint8_t)(bits >> (8 * k));
  block(h, last);
  if (total == 128) block(h, last + 64);
  lean_object *out = lean_alloc_sarray(1, 32, 32);
  for (int k = 0; k < 32; k++) lean_sarray_cptr(out)[k] = (uint8_t)(h[k / 4] >> (24 - 8 * (k % 4)));
  return out;
}
