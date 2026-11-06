# Sourced by bin/no-build-guard: the heavy-host guard (docs/no-build-host.md). A host that carries a no-build MARKER must never run a test, a mutation run or any other long runner.
# The marker is the owner's (or the machine's configuration tool's), never an agent's: there is NO override. Nothing here reads the environment to decide that a marker does not count (the path below is a plain
# assignment, never `${X:-default}`); VBM_ALLOW_BUILD_HERE, XDG_CONFIG_HOME and HOME can only ADD places that are looked at, never remove one.
nbh_etc=/etc/vbm/no-build-host
nbh_markers() {   # every place a marker is looked for, one per line: the system file, the user's config dir as the environment names it, as HOME names it, and as the account database names it (a changed HOME does not hide it)
  local h; h=$(getent passwd "$(id -u)" 2>/dev/null | cut -d: -f6 || true)
  printf '%s\n' "$nbh_etc" "${XDG_CONFIG_HOME:-${HOME:-/nonexistent}/.config}/vbm/no-build-host" "${HOME:-/nonexistent}/.config/vbm/no-build-host"
  [ -z "$h" ] || printf '%s\n' "$h/.config/vbm/no-build-host"
}
nbh_found() {     # nbh_found: prints the first marker present (a dangling symlink counts) and succeeds; fails when there is none
  local m; while IFS= read -r m; do if [ -e "$m" ] || [ -L "$m" ]; then printf '%s\n' "$m"; return 0; fi; done < <(nbh_markers); return 1
}
nbh_guard() {     # nbh_guard NAME: returns 0 on a host without a marker; else says so on stderr and returns 2 (the caller exits 2 before it starts anything)
  local m; m=$(nbh_found) || return 0
  echo "$1: REFUSED: this host carries a no-build marker ($m): no test, mutation run or other long runner may run here. Run it on a build host. There is no override: an environment variable does not lift it, and an agent does not remove the marker." >&2
  return 2
}
