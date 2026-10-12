#!/usr/bin/env bash

set -euo pipefail

if test $# -ne 1; then
    echo "usage: $0 <uc3-user>" >&2
    exit 1
fi

root=$(git rev-parse --show-toplevel)
if ! test -f "$root/agda/borrowed-cf.agda-lib"; then
    echo "$0: please run from inside the git repository" >&2
    exit 1
fi

rsync -az \
      --exclude '_build/'        \
      --exclude 'util/'          \
      --include '*/'             \
      --include '*.agda'         \
      --include '*.lagda'        \
      --include '*.lagda.*'      \
      --include '*.agda-lib'     \
      --exclude '*'              \
      --info=progress,stats,name \
      "$root/agda"               \
      "$1@uc3.scc.kit.edu:borrowed-cf/"
