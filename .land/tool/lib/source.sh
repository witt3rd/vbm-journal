#!/usr/bin/env bash
# Where the upstream copy of this tool lives, and how to look at it at one exact commit. Sourced, never run.
#   src_fetch SRC REF DEST   makes DEST a bare clone of SRC (OWNER/NAME on GitHub: an ANONYMOUS https clone first, so a public source needs no token, no `gh` login and no secret; only when that fails, `gh`, for a private source;
#   or anything git can clone: a URL or a path) and prints the 40-hex commit REF names. VBM_LAND_URL_BASE replaces https://github.com (the tests serve a local copy).
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/paths.sh"   # every consumer path, defined once (lib/paths.sh)

src_fetch() {
  local src=$1 ref=$2 dest=$3 c
  if [[ "$src" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] && [ ! -e "$src" ]; then
    GIT_TERMINAL_PROMPT=0 GIT_ASKPASS=true timeout 120 git -c credential.helper= clone -q --bare -- "${VBM_LAND_URL_BASE:-https://github.com}/$src.git" "$dest" >/dev/null 2>&1 || { rm -rf "$dest"
      "${GH:-gh}" repo clone "$src" "$dest" -- --quiet --bare >/dev/null 2>&1 || { echo "cannot clone $src (anonymously over https, nor with gh: a private source needs a read token in GH_TOKEN)" >&2; return 1; }; }
  else
    git clone -q --bare -- "$src" "$dest" >/dev/null 2>&1 || { echo "cannot clone $src" >&2; return 1; }
  fi
  c=$(git -C "$dest" rev-parse --verify -q "$ref^{commit}") || { echo "$src has no such tag or commit: $ref" >&2; return 1; }
  [[ "$c" =~ ^[0-9a-f]{40}$ ]] || return 1
  printf '%s\n' "$c"
}

# src_verify DEST REF SIGNERS   (DEST: the bare clone src_fetch made; REF: a tag or a commit; SIGNERS: an ssh allowed-signers file, or empty)
#   Is REF a release tag signed by an allowed signer, whose message records the hash of the manifest it points at?
#   Prints one line on stdout. Returns 0 verified | 10 not verified, and allowed because no signers file exists (an unsigned first install, or a pin by commit) | 1 REFUSED (a signers file exists and the
#   release does not satisfy it: not a tag, a lightweight tag, a signature that does not verify, an unknown signer, a manifest hash that differs from the tag's). A signers file makes signatures mandatory.
src_verify() {
  local dest=$1 ref=$2 signers=${3:-} kind want got
  if [ -z "$signers" ]; then echo "UNVERIFIED: no signers file ($LAND_SIGNERS_FILE): the release signature was not checked"; return 10; fi
  [ -r "$signers" ] || { echo "REFUSED: signers file $signers is not readable" >&2; return 1; }
  kind=$(git -C "$dest" cat-file -t "refs/tags/$ref" 2>/dev/null) || { echo "REFUSED: $ref is not a release tag, and this repository requires signed releases ($LAND_SIGNERS_FILE); pass the tag, not a commit" >&2; return 1; }
  [ "$kind" = tag ] || { echo "REFUSED: $ref is a lightweight tag: a signed, annotated release tag is required" >&2; return 1; }
  git -C "$dest" -c gpg.format=ssh -c "gpg.ssh.allowedSignersFile=$signers" verify-tag "$ref" >/dev/null 2>&1 || { echo "REFUSED: the signature of tag $ref does not verify against $signers (unsigned, or an unknown signer)" >&2; return 1; }
  want=$(git -C "$dest" tag -l --format='%(contents)' "$ref" | sed -n 's/^manifest_sha256=//p' | sed -n 1p)
  got=$(git -C "$dest" show "$ref^{commit}:MANIFEST.sha256" 2>/dev/null | sha256sum | cut -d' ' -f1)
  [ -n "$want" ] && [ "$want" = "$got" ] || { echo "REFUSED: tag $ref records manifest_sha256=${want:-none}, but the manifest at that commit hashes to $got" >&2; return 1; }
  echo "verified: tag $ref is signed by an allowed signer and records this manifest"; return 0
}
