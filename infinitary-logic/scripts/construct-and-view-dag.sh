#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/_dag-common.sh"

TARGET="$DEFAULT_TARGET"
OUTPUT="$DEFAULT_OUTPUT"
TARGET_SET=0

usage() {
  cat <<'EOF'
Usage: ./scripts/construct-and-view-dag.sh [MODULE] [--output FILE]

Builds a Lean target, regenerates an import DAG HTML, and opens it.

Examples:
  ./scripts/construct-and-view-dag.sh
  ./scripts/construct-and-view-dag.sh InfinitaryLogic.Syntax
  ./scripts/construct-and-view-dag.sh InfinitaryLogic.Syntax --output syntax-dag.html
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --output)
      if [[ $# -lt 2 ]]; then
        echo "Missing file path after --output" >&2
        exit 1
      fi
      OUTPUT="$2"
      shift 2
      ;;
    -*)
      echo "Unknown option: $1" >&2
      usage >&2
      exit 1
      ;;
    *)
      if [[ "$TARGET_SET" -eq 1 ]]; then
        echo "Unexpected extra module argument: $1" >&2
        usage >&2
        exit 1
      fi
      TARGET="$1"
      TARGET_SET=1
      shift
      ;;
  esac
done

"${SCRIPT_DIR}/construct-dag.sh" "$TARGET" --output "$OUTPUT"

ABS_OUTPUT="$(dag_abs_path "$OUTPUT")"
echo "Opening ${ABS_OUTPUT}"
dag_open "$ABS_OUTPUT"
