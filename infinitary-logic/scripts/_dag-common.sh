#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEFAULT_TARGET="InfinitaryLogic"
DEFAULT_OUTPUT="dependency-graph.auto.html"

dag_abs_path() {
  local path="$1"
  case "$path" in
    /*)
      printf '%s\n' "$path"
      ;;
    *)
      printf '%s\n' "${ROOT_DIR}/${path}"
      ;;
  esac
}

dag_open() {
  local path="$1"

  local uri
  uri="$(python3 - "$path" <<'PY'
from pathlib import Path
import sys

print(Path(sys.argv[1]).resolve().as_uri())
PY
)"
  uri="${uri}?t=$(date +%s)"

  if command -v open >/dev/null 2>&1; then
    open "$uri"
  elif command -v xdg-open >/dev/null 2>&1; then
    xdg-open "$uri" >/dev/null 2>&1 &
  else
    echo "No browser opener found. Open the file manually: ${path}"
  fi
}
