# lib/verify.sh: the ONE verifier of this tool (docs/pin.md, docs/payload.md 6a): the tree hash and the check of a signed release tag. Sourced, never run.
# `install` embeds this file verbatim (it must run without a checkout); tests/test_verifier_one.sh fails when the copy differs.
# The tree hash of docs/pin.md section 1, defined ONCE.
# tree_hash DIR: print the SHA-256 of the sorted lines "<sha256 of the file> <path relative to DIR>" of every file under DIR except what is under a .lake or .git directory, at ANY depth (Lake builds a nested vendored library in place).
# Returns 1, with the reason on stderr, for a missing DIR, a symlink or other non-regular file, or a path with a newline or a backslash (sha256sum escapes those: never a silently different hash). Every other path is
# hashed as it is (a space, #, <, non-ASCII), sorted by bytes.
tree_hash() (
  set -euo pipefail; export LC_ALL=C
  [ -d "${1:-}" ] || { echo "treehash: ${1:-} is not a directory" >&2; exit 1; }
  cd "$1"; files=()
  while IFS= read -r -d '' p; do
    case $p in *$'\n'*|*\\*) echo "treehash: $1: unsafe path ${p@Q} (a newline or a backslash)" >&2; exit 1;; esac
    { [ -f "$p" ] && [ ! -L "$p" ]; } || { echo "treehash: $1/${p#./} is not a regular file" >&2; exit 1; }
    files+=("$p")
  done < <(find . \( -name .lake -o -name .git \) -prune -o ! -type d -print0)
  if [ ${#files[@]} = 0 ]; then printf '' | sha256sum | cut -d' ' -f1; exit 0; fi
  printf '%s\0' "${files[@]}" | xargs -0 sha256sum -- | sed -E 's/^([0-9a-f]{64})  \.\//\1 /' | sort | sha256sum | cut -d' ' -f1
)

# export_commit REPO REV DEST: the exported tree of REV in REPO (git archive) into the existing directory DEST. The tree hash of a commit is tree_hash of this export (docs/pin.md section 1).
export_commit() { git -C "$1" archive --format=tar "$2" | tar -x -C "$3"; }

# src_check_tag DEST REF SIGNERS [OUTDIR]: strict. DEST is a git repository (bare or not) holding the tag. Succeeds, printing the verified tree hash, only when REF is an annotated tag signed by an allowed
# signer of SIGNERS, its message records exactly one tree_sha256=, and the exported tree of the tagged commit (into OUTDIR when given, so the caller keeps it) hashes to it. Otherwise returns 1, the reason on stderr.
src_check_tag() {
  local dest=$1 ref=$2 signers=${3:-} out=${4:-} kind want got d
  { [ -n "$signers" ] && [ -r "$signers" ]; } || { echo "REFUSED: no readable signers file: a release signature cannot be checked" >&2; return 1; }
  signers=$(readlink -f "$signers")   # git below runs in the clone's directory: a relative path would be looked up there and a good signature would look unknown
  kind=$(git -C "$dest" cat-file -t "refs/tags/$ref" 2>/dev/null) || { echo "REFUSED: $ref is not a release tag, and signed releases are required; pass the tag, not a commit" >&2; return 1; }
  [ "$kind" = tag ] || { echo "REFUSED: $ref is a lightweight tag: a signed, annotated release tag is required" >&2; return 1; }
  git -C "$dest" -c gpg.format=ssh -c "gpg.ssh.allowedSignersFile=$signers" verify-tag "$ref" >/dev/null 2>&1 || { echo "REFUSED: the signature of tag $ref does not verify against $signers (unsigned, or an unknown signer)" >&2; return 1; }
  want=$(git -C "$dest" tag -l --format='%(contents)' "$ref" | sed -n -E 's/^tree_sha256=([0-9a-f]{64})$/\1/p')
  [ "$(printf '%s\n' "$want" | grep -c .)" = 1 ] || { echo "REFUSED: the message of $ref does not record exactly one tree_sha256=" >&2; return 1; }
  d=${out:-$(mktemp -d)}; export_commit "$dest" "$ref^{commit}" "$d"
  got=$(tree_hash "$d" 2>&1) || { [ -n "$out" ] || rm -rf "$d"; echo "REFUSED: the exported tree of $ref cannot be hashed: $got" >&2; return 1; }
  [ -n "$out" ] || rm -rf "$d"
  [ "$got" = "$want" ] || { echo "REFUSED: tag $ref records tree_sha256=$want, but its exported tree hashes to $got" >&2; return 1; }
  printf '%s\n' "$got"
}

# src_verify DEST REF SIGNERS: the rule of land-update and install. No signers file = an unsigned first install or a pin by commit: allowed, said so (returns 10). A signers file makes the signed tag mandatory (returns 1 when refused).
src_verify() {
  local dest=$1 ref=$2 signers=${3:-}
  if [ -z "$signers" ]; then echo "UNVERIFIED: no signers file ($LAND_SIGNERS_FILE): the release signature was not checked"; return 10; fi
  src_check_tag "$dest" "$ref" "$signers" >/dev/null || return 1
  echo "verified: tag $ref is signed by an allowed signer and records this tree"; return 0
}
