#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/_dag-common.sh"

TARGET="$DEFAULT_TARGET"
OUTPUT="$DEFAULT_OUTPUT"
TARGET_SET=0

usage() {
  cat <<'EOF'
Usage: ./scripts/construct-dag.sh [MODULE] [--output FILE]

Builds a Lean target and regenerates an import DAG HTML with `lake exe graph`.

Examples:
  ./scripts/construct-dag.sh
  ./scripts/construct-dag.sh InfinitaryLogic.Syntax
  ./scripts/construct-dag.sh InfinitaryLogic.Syntax --output syntax-dag.html
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

cd "$ROOT_DIR"

echo "Building ${TARGET}..."
if ! lake build "$TARGET"; then
  cat >&2 <<EOF
Failed to build ${TARGET}, so the DAG was not regenerated.

If the root target is currently broken, try a built module instead, for example:
  ./scripts/construct-dag.sh InfinitaryLogic.Syntax
EOF
  exit 1
fi

mkdir -p "$(dirname "$OUTPUT")"

echo "Generating ${OUTPUT}..."
TMP_GEXF="$(mktemp "${TMPDIR:-/tmp}/infinitary-dag-XXXXXX.gexf")"
trap 'rm -f "$TMP_GEXF"' EXIT
lake exe graph --to "$TARGET" --mark-sorry --include-direct --exclude-meta --show-transitive "$TMP_GEXF"
python3 scripts/render_dag.py --input "$TMP_GEXF" --output "$OUTPUT" --root "$ROOT_DIR" --title "$TARGET" --exclude "$TARGET"

ABS_OUTPUT="$(dag_abs_path "$OUTPUT")"
echo "DAG written to ${ABS_OUTPUT}"
