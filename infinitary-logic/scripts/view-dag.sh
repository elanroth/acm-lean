#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/_dag-common.sh"

OUTPUT="$DEFAULT_OUTPUT"

usage() {
  cat <<'EOF'
Usage: ./scripts/view-dag.sh [--output FILE]

Opens an existing DAG HTML file in your browser.

Examples:
  ./scripts/view-dag.sh
  ./scripts/view-dag.sh --output dependency-graph.auto.html
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
      echo "Unexpected argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

cd "$ROOT_DIR"

ABS_OUTPUT="$(dag_abs_path "$OUTPUT")"
if [[ ! -f "$ABS_OUTPUT" ]]; then
  cat >&2 <<EOF
DAG file not found: ${ABS_OUTPUT}

Construct it first with:
  ./scripts/construct-dag.sh
or:
  ./scripts/construct-and-view-dag.sh
EOF
  exit 1
fi

echo "Opening ${ABS_OUTPUT}"
dag_open "$ABS_OUTPUT"
