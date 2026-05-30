#!/usr/bin/env bash
# Remote build on uisai1 (local lake is disabled). Usage:
#   scripts/remote-build.sh [lake-target...]   # default: whole lib
# Syncs the repo to uisai1 and runs `lake build` under nohup, streaming the log.
set -euo pipefail
REMOTE=uisai1
RPATH='~/repos/AnalyticCombinatorics'
LOCAL="$(cd "$(dirname "$0")/.." && pwd)/"

rsync -az --delete \
  --exclude '.git' --exclude '.lake/build' --exclude 'HANDOFF/locks' \
  "$LOCAL" "$REMOTE:$RPATH/"

TARGETS="${*:-}"
ssh "$REMOTE" "cd $RPATH && export PATH=\$HOME/.elan/bin:\$PATH && \
  nohup lake build $TARGETS > /tmp/ac-build.log 2>&1 & echo PID \$!"
echo '--- streaming /tmp/ac-build.log (Ctrl-C to detach; build keeps running) ---'
ssh "$REMOTE" "tail -f /tmp/ac-build.log" 
