# Sourced library: stop the background jobs a script started, by the pids IT holds, never by pattern or a derived pid.
# A job started with job control on (`set -m; cmd & p=$!`) is its own process group with pgid = $p, so one signal to "-$p" reaches the job and everything it spawned.
# reap_pids PID...: SIGTERM the group of each pid that is still the leader of its own group (the pgid check keeps a recycled pid from being hit).
reap_pids() { local p; for p in "$@"; do [ -n "$p" ] || continue; [ "$(ps -o pgid= -p "$p" 2>/dev/null | tr -d ' ')" = "$p" ] || continue; kill -TERM -- "-$p" 2>/dev/null || true; done; }
