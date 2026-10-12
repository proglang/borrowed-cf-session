#!/usr/bin/env bash

set -euo pipefail

if test $# -ne 0; then
    echo "usage: $0" >&2
    exit 1
fi

root=$(git rev-parse --show-toplevel)
if ! test -f "$root/agda/borrowed-cf.agda-lib"; then
    echo "$0: please run from inside the git repository" >&2
    exit 1
fi

"$root/agda/util/agraph.sh" "$root/agda" | tred | gvpr -c 'N {
  if ($.indegree == 0) {
    $.style = "filled";
    $.fillcolor = "lightblue";
  }
}' | dot -Tsvg -og.svg
echo "$0: wrote module graph to g.svg" >&2
