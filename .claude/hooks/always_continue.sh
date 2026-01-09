
#!/usr/bin/env bash
set -euo pipefail

# Optional escape hatch: if this file exists, allow Claude to stop normally.
if [[ -f ".claude/ALLOW_STOP" ]]; then
  exit 0
fi

# IMPORTANT: write to stderr so Claude Code captures it as the continuation message
cat >&2 <<'MSG'
Continue with the overall goal (xcelium parity / full SV+UVM support). Pick the next smallest task, implement it, add/adjust unit tests, run the relevant regression (e.g. in ~/repos/mbits-mirafra), and commit regularly. Do not stop; keep going.
MSG

# Exit 2 = "block stopping and continue"
exit 2


