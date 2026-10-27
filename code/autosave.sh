#!/usr/bin/env bash
# Auto-save for the 2026-10-27 run (main agent): every INTERVAL seconds until the deadline, stage everything, unstage
# files larger than 40 MB (GitHub rejects files over 100 MB), commit as the configured user and push.
# Usage: bash code/autosave.sh [INTERVAL_SECONDS] [DEADLINE_HHMM]
INTERVAL=${1:-2400}
DEADLINE=${2:-1645}
cd "$(dirname "$0")/.." || exit 1
while [ "$(date +%H%M)" -lt "$DEADLINE" ]; do
  sleep "$INTERVAL"
  git add -A >/dev/null 2>&1
  git diff --cached --name-only -z | while IFS= read -r -d '' f; do
    if [ -f "$f" ] && [ "$(wc -c < "$f")" -gt 41943040 ]; then git reset -q -- "$f"; echo "skipped large file $f"; fi
  done
  if ! git diff --cached --quiet; then
    git commit -q -m "Auto-save $(date +%H:%M): agents' logs, scripts and Lean files" && \
      GIT_TERMINAL_PROMPT=0 timeout 300 git push -q 2>&1 | grep -v "LF will be replaced"
    echo "$(date +%H:%M) saved $(git log --format=%h -1)"
  fi
done
