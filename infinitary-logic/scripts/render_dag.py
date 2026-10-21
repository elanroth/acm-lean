#!/usr/bin/env python3

from __future__ import annotations

import argparse
import colorsys
import hashlib
import json
import re
import xml.etree.ElementTree as ET
from collections import deque
from pathlib import Path


GEXF_NS = {"g": "http://www.gexf.net/1.2draft"}
DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+"
    r"(?P<name>[^\s:(\[{=]+)"
)
SORRY_RE = re.compile(r"\bsorry\b")
MAX_DECL_LIST = 140

PROJECT_GROUP_SPECS = [
  (
    "project:core",
    "Core",
    {
      "InfinitaryLogic",
      "InfinitaryLogic.Syntax",
      "InfinitaryLogic.Semantics",
      "InfinitaryLogic.Embedding",
      "InfinitaryLogic.NormalForm",
      "InfinitaryLogic.ModelExistence",
    },
    ("rgb(31, 78, 121)", "rgb(74, 158, 255)"),
  ),
  (
    "project:scott",
    "Scott",
    {"InfinitaryLogic.ScottFamily", "InfinitaryLogic.ScottSentence", "InfinitaryLogic.Rank"},
    ("rgb(58, 26, 26)", "rgb(255, 123, 114)"),
  ),
]

PROJECT_GROUP_FALLBACK = (
  "project:other",
  "Project",
  ("rgb(35, 48, 64)", "rgb(125, 184, 255)"),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Render a custom HTML import DAG from a GEXF graph."
    )
    parser.add_argument("--input", required=True, help="Input GEXF file")
    parser.add_argument("--output", required=True, help="Output HTML file")
    parser.add_argument("--root", required=True, help="Project root")
    parser.add_argument("--title", required=True, help="Graph title")
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="Module name to exclude from the rendered graph (repeatable)",
    )
    return parser.parse_args()


def cast_value(raw: str) -> object:
    lowered = raw.lower()
    if lowered == "true":
        return True
    if lowered == "false":
        return False
    try:
        return int(raw)
    except ValueError:
        pass
    try:
        return float(raw)
    except ValueError:
        return raw


def parse_gexf(path: Path) -> tuple[dict[str, dict[str, object]], list[tuple[str, str]]]:
    root = ET.parse(path).getroot()
    graph = root.find("g:graph", GEXF_NS)
    if graph is None:
        raise ValueError("Could not find <graph> in GEXF input.")

    attributes: dict[str, dict[str, str]] = {"node": {}, "edge": {}}
    for attrs in graph.findall("g:attributes", GEXF_NS):
        cls = attrs.attrib.get("class", "")
        for attr in attrs.findall("g:attribute", GEXF_NS):
            attributes.setdefault(cls, {})[attr.attrib["id"]] = attr.attrib.get(
                "title", attr.attrib["id"]
            )

    nodes_el = graph.find("g:nodes", GEXF_NS)
    edges_el = graph.find("g:edges", GEXF_NS)
    if nodes_el is None or edges_el is None:
        raise ValueError("Could not find <nodes> or <edges> in GEXF input.")

    nodes: dict[str, dict[str, object]] = {}
    for node_el in nodes_el.findall("g:node", GEXF_NS):
        node_id = node_el.attrib["id"]
        node_data: dict[str, object] = {
            "id": node_id,
            "label": node_el.attrib.get("label", node_id),
        }
        attvalues = node_el.find("g:attvalues", GEXF_NS)
        if attvalues is not None:
            for attvalue in attvalues.findall("g:attvalue", GEXF_NS):
                key = attributes["node"].get(
                    attvalue.attrib.get("for", ""), attvalue.attrib.get("for", "")
                )
                node_data[key] = cast_value(attvalue.attrib.get("value", ""))
        nodes[node_id] = node_data

    edges: list[tuple[str, str]] = []
    for edge_el in edges_el.findall("g:edge", GEXF_NS):
        edges.append((edge_el.attrib["source"], edge_el.attrib["target"]))

    return nodes, edges


def module_path(module_name: str) -> Path:
    return Path(*module_name.split(".")).with_suffix(".lean")


def resolve_local_file(module_name: str, project_root: Path) -> Path | None:
    relative = module_path(module_name)

    direct = project_root / relative
    if direct.exists():
        return direct.resolve()

    packages_root = project_root / ".lake" / "packages"
    if packages_root.exists():
        for candidate in packages_root.glob(f"*/{relative.as_posix()}"):
            if candidate.exists():
                return candidate.resolve()

    return None


def relative_file_ref(file_path: Path | None, project_root: Path) -> str | None:
    if file_path is None:
        return None
    try:
        return file_path.resolve().relative_to(project_root).as_posix()
    except ValueError:
        return file_path.name


def normalize_decl_kind(kind: str) -> str:
    if kind == "theorem":
        return "theorem"
    if kind == "lemma":
        return "lemma"
    return "definition"


def parse_declarations(file_path: Path | None) -> dict[str, object]:
    if file_path is None or not file_path.exists():
        return {
            "definitions": [],
            "lemmas": [],
            "theorems": [],
            "definitionCount": 0,
            "lemmaCount": 0,
            "theoremCount": 0,
            "lemmaSorryCount": 0,
            "theoremSorryCount": 0,
            "declarationListTruncated": False,
        }

    text = file_path.read_text(encoding="utf-8")
    lines = text.splitlines()

    starts: list[tuple[int, str, str]] = []
    for idx, line in enumerate(lines):
        match = DECL_RE.match(line)
        if match:
            starts.append((idx, match.group("kind"), match.group("name")))

    raw_decls: list[dict[str, object]] = []
    for i, (start, kind, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(lines)
        block = "\n".join(lines[start:end])
        normalized = normalize_decl_kind(kind)
        raw_decls.append(
            {
                "order": i,
                "kind": normalized,
                "badge": kind,
                "name": name,
                "sorry": bool(SORRY_RE.search(block)),
            }
        )

    definitions = [decl for decl in raw_decls if decl["kind"] == "definition"]
    lemmas = [decl for decl in raw_decls if decl["kind"] == "lemma"]
    theorems = [decl for decl in raw_decls if decl["kind"] == "theorem"]
    truncated = len(raw_decls) > MAX_DECL_LIST

    return {
        "definitions": definitions[:MAX_DECL_LIST],
        "lemmas": lemmas[:MAX_DECL_LIST],
        "theorems": theorems[:MAX_DECL_LIST],
        "definitionCount": len(definitions),
        "lemmaCount": len(lemmas),
        "theoremCount": len(theorems),
        "lemmaSorryCount": sum(1 for decl in lemmas if decl["sorry"]),
        "theoremSorryCount": sum(1 for decl in theorems if decl["sorry"]),
        "declarationListTruncated": truncated,
    }


def external_group_label(module_name: str) -> str:
    parts = module_name.split(".")
    if len(parts) >= 2:
        return ".".join(parts[:2])
    return parts[0]


def external_color_pair(group_label: str) -> tuple[str, str]:
    digest = hashlib.sha1(group_label.encode("utf-8")).digest()
    hue = digest[0] / 255.0
    bg = colorsys.hls_to_rgb(hue, 0.20, 0.35)
    border = colorsys.hls_to_rgb(hue, 0.54, 0.65)
    bg_rgb = tuple(round(channel * 255) for channel in bg)
    border_rgb = tuple(round(channel * 255) for channel in border)
    return (
        f"rgb({bg_rgb[0]}, {bg_rgb[1]}, {bg_rgb[2]})",
        f"rgb({border_rgb[0]}, {border_rgb[1]}, {border_rgb[2]})",
    )


def group_info(module_name: str, in_module: bool) -> tuple[str, str, str, str, int]:
    if in_module:
        for priority, (group_key, group_label, modules, colors) in enumerate(PROJECT_GROUP_SPECS):
            if module_name in modules:
                color, border = colors
                return group_key, group_label, color, border, priority
        color, border = PROJECT_GROUP_FALLBACK[2]
        return PROJECT_GROUP_FALLBACK[0], PROJECT_GROUP_FALLBACK[1], color, border, len(
            PROJECT_GROUP_SPECS
        )

    group_label = external_group_label(module_name)
    color, border = external_color_pair(group_label)
    return f"external:{group_label}", group_label, color, border, 100


def build_graph_data(
  nodes: dict[str, dict[str, object]],
  edges: list[tuple[str, str]],
  project_root: Path,
  exclude: set[str] | None = None,
) -> dict[str, object]:
  exclude = exclude or set()
  filtered_nodes = {node_id: node for node_id, node in nodes.items() if node_id not in exclude}
  filtered_edges = [
    (source, target)
    for source, target in edges
    if source in filtered_nodes and target in filtered_nodes
  ]

  imports: dict[str, list[str]] = {node_id: [] for node_id in filtered_nodes}
  imported_by: dict[str, list[str]] = {node_id: [] for node_id in filtered_nodes}
  indegree: dict[str, int] = {node_id: 0 for node_id in filtered_nodes}

  for source, target in filtered_edges:
    imports[target].append(source)
    imported_by[source].append(target)
    indegree[target] += 1

  level = {node_id: 0 for node_id in filtered_nodes}
  queue = deque(sorted(node_id for node_id, deg in indegree.items() if deg == 0))
  indegree_work = dict(indegree)
  while queue:
    node_id = queue.popleft()
    for dependent in sorted(imported_by[node_id]):
      level[dependent] = max(level[dependent], level[node_id] + 1)
      indegree_work[dependent] -= 1
      if indegree_work[dependent] == 0:
        queue.append(dependent)

  graph_nodes: list[dict[str, object]] = []
  legend: dict[str, dict[str, object]] = {}
  total_decls = 0
  total_defs = 0
  total_lemmas = 0
  total_theorems = 0
  total_sorries = 0

  for node_id in sorted(filtered_nodes):
    node = filtered_nodes[node_id]
    in_module = bool(node.get("in_module", False))
    decl_count = int(node.get("decl_count", 0))
    total_decls += decl_count

    group_key, group_label, color, border, group_priority = group_info(node_id, in_module)
    file_path = resolve_local_file(node_id, project_root)
    file_ref = relative_file_ref(file_path, project_root)
    decl_data = parse_declarations(file_path)
    total_defs += int(decl_data["definitionCount"])
    total_lemmas += int(decl_data["lemmaCount"])
    total_theorems += int(decl_data["theoremCount"])
    total_sorries += int(decl_data["lemmaSorryCount"]) + int(decl_data["theoremSorryCount"])

    legend.setdefault(
      group_key,
      {
        "group": group_label,
        "color": color,
        "border": border,
        "count": 0,
        "priority": group_priority,
      },
    )
    legend[group_key]["count"] += 1

    graph_nodes.append(
      {
        "id": node_id,
        "label": node.get("label", node_id),
        "modulePath": node_id,
        "declCount": decl_count,
        "imports": sorted(imports[node_id]),
        "importedBy": sorted(imported_by[node_id]),
        "level": level[node_id],
        "group": group_key,
        "groupLabel": group_label,
        "inModule": in_module,
        "filePath": file_ref,
        "fileHref": file_ref,
        "color": color,
        "border": border,
        **decl_data,
      }
    )

  graph_edges = [{"from": source, "to": target} for source, target in filtered_edges]

  legend_items = sorted(legend.values(), key=lambda item: (item["priority"], item["group"]))
  return {
    "nodes": graph_nodes,
    "edges": graph_edges,
    "legend": [
      {key: value for key, value in item.items() if key != "priority"}
      for item in legend_items
    ],
    "stats": {
      "modules": len(graph_nodes),
      "edges": len(graph_edges),
      "declarations": total_decls,
      "definitions": total_defs,
      "lemmas": total_lemmas,
      "theorems": total_theorems,
      "sorries": total_sorries,
    },
  }


HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>__PAGE_TITLE__</title>
<script src="https://unpkg.com/vis-network@9.1.9/standalone/umd/vis-network.min.js"></script>
<style>
  * { box-sizing: border-box; margin: 0; padding: 0; }

  :root {
    color-scheme: dark;
    --bg: #0a1016;
    --panel: #131a22;
    --panel-2: #1a2330;
    --text: #edf3fb;
    --muted: #9aabbd;
    --line: #283344;
    --accent: #7db8ff;
  }

  html, body {
    width: 100%;
    height: 100%;
    overflow: hidden;
    background: radial-gradient(circle at top, #172233 0%, var(--bg) 60%);
    color: var(--text);
    font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
  }

  body {
    display: flex;
    flex-direction: column;
  }

  header {
    padding: 18px 22px 14px;
    border-bottom: 1px solid var(--line);
    background: rgba(8, 12, 18, 0.9);
    backdrop-filter: blur(8px);
    display: grid;
    grid-template-columns: minmax(0, 1fr) auto;
    gap: 18px;
    flex-shrink: 0;
  }

  .header-copy h1 {
    font-size: 1.35rem;
    font-weight: 700;
    letter-spacing: 0.01em;
  }

  .header-copy p {
    margin-top: 4px;
    font-size: 0.86rem;
    color: var(--muted);
  }

  .toolbar {
    display: flex;
    align-items: center;
    justify-content: flex-end;
    gap: 10px;
    flex-wrap: wrap;
  }

  .tool-group {
    display: flex;
    align-items: center;
    gap: 6px;
    padding: 6px;
    border: 1px solid var(--line);
    border-radius: 12px;
    background: rgba(255, 255, 255, 0.03);
  }

  .tool-label {
    color: var(--muted);
    font-size: 0.72rem;
    text-transform: uppercase;
    letter-spacing: 0.08em;
    padding: 0 4px;
  }

  .tool-btn {
    border: 1px solid var(--line);
    background: var(--panel-2);
    color: var(--text);
    border-radius: 9px;
    padding: 7px 11px;
    font-size: 0.78rem;
    cursor: pointer;
  }

  .tool-btn:hover,
  .tool-btn.active {
    border-color: var(--accent);
    color: var(--accent);
  }

  .stats {
    display: flex;
    gap: 18px;
    flex-wrap: wrap;
  }

  .stat {
    text-align: right;
  }

  .stat-value {
    font-size: 1.05rem;
    font-weight: 700;
    font-variant-numeric: tabular-nums;
  }

  .stat-label {
    font-size: 0.68rem;
    color: var(--muted);
    text-transform: uppercase;
    letter-spacing: 0.08em;
  }

  .legend {
    display: flex;
    gap: 10px;
    flex-wrap: wrap;
    padding: 10px 22px;
    border-bottom: 1px solid var(--line);
    background: rgba(11, 17, 24, 0.82);
  }

  .legend-item {
    display: flex;
    align-items: center;
    gap: 8px;
    font-size: 0.76rem;
    color: var(--muted);
    padding: 5px 9px;
    border: 1px solid var(--line);
    border-radius: 999px;
    background: rgba(255, 255, 255, 0.02);
  }

  .legend-swatch {
    width: 11px;
    height: 11px;
    border-radius: 999px;
    border: 2px solid transparent;
    flex-shrink: 0;
  }

  .main {
    flex: 1;
    min-height: 0;
    display: flex;
    overflow: hidden;
  }

  #graph {
    flex: 1;
    min-width: 0;
    min-height: 0;
    position: relative;
    background:
      radial-gradient(circle at 20% 20%, rgba(125, 184, 255, 0.08), transparent 28%),
      radial-gradient(circle at 80% 30%, rgba(57, 208, 167, 0.06), transparent 24%);
  }

  .hint {
    position: absolute;
    left: 14px;
    bottom: 14px;
    padding: 8px 10px;
    border: 1px solid var(--line);
    border-radius: 10px;
    background: rgba(9, 14, 21, 0.78);
    color: var(--muted);
    font-size: 0.76rem;
    z-index: 1;
    pointer-events: none;
  }

  .sidebar {
    width: 420px;
    min-width: 360px;
    border-left: 1px solid var(--line);
    background: linear-gradient(180deg, rgba(19, 26, 34, 0.98), rgba(14, 19, 26, 0.98));
    display: flex;
    flex-direction: column;
    min-height: 0;
  }

  .sidebar-scroll {
    flex: 1;
    min-height: 0;
    overflow-y: auto;
    padding: 18px;
  }

  .sidebar-scroll::-webkit-scrollbar {
    width: 10px;
  }

  .sidebar-scroll::-webkit-scrollbar-thumb {
    background: #2c3a4c;
    border-radius: 999px;
  }

  .empty {
    height: 100%;
    display: flex;
    align-items: center;
    justify-content: center;
    text-align: center;
    color: var(--muted);
    font-size: 0.92rem;
    line-height: 1.6;
    padding: 24px;
  }

  .module-title {
    display: flex;
    align-items: center;
    gap: 10px;
    margin-bottom: 8px;
  }

  .swatch {
    width: 14px;
    height: 14px;
    border-radius: 999px;
    border: 2px solid transparent;
    flex-shrink: 0;
  }

  .module-title h2 {
    font-size: 1.02rem;
    font-weight: 700;
  }

  .module-path {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 0.78rem;
    color: var(--accent);
    word-break: break-all;
  }

  .module-meta {
    display: grid;
    grid-template-columns: repeat(3, minmax(0, 1fr));
    gap: 10px;
    margin: 16px 0;
  }

  .meta-box {
    border: 1px solid var(--line);
    border-radius: 12px;
    padding: 10px 12px;
    background: rgba(255, 255, 255, 0.02);
  }

  .meta-box .value {
    font-size: 1rem;
    font-weight: 700;
    font-variant-numeric: tabular-nums;
  }

  .meta-box .label {
    margin-top: 4px;
    font-size: 0.68rem;
    color: var(--muted);
    text-transform: uppercase;
    letter-spacing: 0.08em;
  }

  .open-link {
    display: inline-block;
    margin-bottom: 14px;
    padding: 8px 12px;
    border-radius: 10px;
    border: 1px solid var(--line);
    background: var(--panel-2);
    color: var(--text);
    text-decoration: none;
    font-size: 0.82rem;
  }

  .open-link:hover {
    border-color: var(--accent);
    color: var(--accent);
  }

  .open-link.disabled {
    color: var(--muted);
    pointer-events: none;
  }

  .section {
    margin-top: 18px;
  }

  .section h3 {
    margin-bottom: 8px;
    font-size: 0.74rem;
    color: var(--muted);
    text-transform: uppercase;
    letter-spacing: 0.1em;
  }

  .chip-row {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
  }

  .chip {
    padding: 6px 10px;
    border-radius: 999px;
    border: 1px solid var(--line);
    background: rgba(255, 255, 255, 0.03);
    font-size: 0.77rem;
    color: var(--text);
    cursor: pointer;
  }

  .chip:hover {
    border-color: var(--accent);
    color: var(--accent);
  }

  .empty-list,
  .truncated-note {
    color: var(--muted);
    font-size: 0.82rem;
  }

  .decl-list {
    display: flex;
    flex-direction: column;
    gap: 7px;
  }

  .decl-item {
    display: flex;
    align-items: flex-start;
    gap: 8px;
    padding: 8px 10px;
    border: 1px solid var(--line);
    border-radius: 10px;
    background: rgba(255, 255, 255, 0.02);
  }

  .decl-badge {
    padding: 2px 6px;
    border-radius: 6px;
    font-size: 0.68rem;
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    border: 1px solid transparent;
    flex-shrink: 0;
    text-transform: lowercase;
  }

  .badge-def { background: rgba(125, 184, 255, 0.12); border-color: rgba(125, 184, 255, 0.35); color: #9bc6ff; }
  .badge-lemma { background: rgba(100, 225, 180, 0.12); border-color: rgba(100, 225, 180, 0.35); color: #92efca; }
  .badge-theorem { background: rgba(255, 183, 90, 0.12); border-color: rgba(255, 183, 90, 0.35); color: #ffc97a; }

  .decl-name {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 0.79rem;
    line-height: 1.35;
    word-break: break-word;
  }

  .sorry-tag {
    display: inline-block;
    margin-left: 7px;
    padding: 1px 5px;
    border-radius: 999px;
    background: rgba(255, 100, 100, 0.14);
    border: 1px solid rgba(255, 100, 100, 0.3);
    color: #ff9f9f;
    font-size: 0.65rem;
    font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
  }

  .section-alert h3 {
    color: #ff9f9f;
  }

  .section-alert .decl-item {
    background: rgba(255, 100, 100, 0.04);
    border-color: rgba(255, 100, 100, 0.22);
  }
</style>
</head>
<body>
<header>
  <div class="header-copy">
    <h1>__PAGE_TITLE__</h1>
    <p>Custom DAG view from current Lean imports. Click a node for declarations and imports. Double-click to open the local `.lean` file.</p>
  </div>
  <div class="toolbar">
    <div class="tool-group">
      <span class="tool-label">View</span>
      <button class="tool-btn" id="fit-btn">Fit</button>
    </div>
    <div class="tool-group">
      <span class="tool-label">Labels</span>
      <button class="tool-btn active" id="label-mode-name" data-mode="name">Names</button>
      <button class="tool-btn" id="label-mode-counts" data-mode="counts">Names + Counts</button>
    </div>
    <div class="stats">
      <div class="stat">
        <div class="stat-value" id="stat-modules"></div>
        <div class="stat-label">Modules</div>
      </div>
      <div class="stat">
        <div class="stat-value" id="stat-definitions"></div>
        <div class="stat-label">Definitions</div>
      </div>
      <div class="stat">
        <div class="stat-value" id="stat-lemmas"></div>
        <div class="stat-label">Lemmas</div>
      </div>
      <div class="stat">
        <div class="stat-value" id="stat-theorems"></div>
        <div class="stat-label">Theorems</div>
      </div>
      <div class="stat">
        <div class="stat-value" id="stat-sorries"></div>
        <div class="stat-label">Sorry</div>
      </div>
    </div>
  </div>
</header>

<div class="legend" id="legend"></div>

<div class="main">
  <div id="graph">
    <div class="hint">Click for sidebar details. Double-click to open the file. Counts mode shows lemma/theorem sorry counts in parentheses.</div>
  </div>
  <aside class="sidebar">
    <div class="sidebar-scroll" id="sidebar">
      <div class="empty">
        Select a module node to inspect its declarations, imports, dependents, and sorry counts.
      </div>
    </div>
  </aside>
</div>

<script>
const GRAPH_DATA = __GRAPH_DATA__;
const MODULES = Object.fromEntries(GRAPH_DATA.nodes.map(node => [node.id, node]));
let labelMode = 'name';

document.getElementById('stat-modules').textContent = GRAPH_DATA.stats.modules;
document.getElementById('stat-definitions').textContent = GRAPH_DATA.stats.definitions;
document.getElementById('stat-lemmas').textContent = GRAPH_DATA.stats.lemmas;
document.getElementById('stat-theorems').textContent = GRAPH_DATA.stats.theorems;
document.getElementById('stat-sorries').textContent = GRAPH_DATA.stats.sorries;

function shortName(mod) {
  return mod.label.replace(/^.*\\./, '');
}

function labelFor(mod) {
  if (labelMode === 'name') {
    return shortName(mod);
  }
  return [
    shortName(mod),
    `Definitions: ${mod.definitionCount}`,
    `Lemmas: ${mod.lemmaCount} (${mod.lemmaSorryCount})`,
    `Theorems: ${mod.theoremCount} (${mod.theoremSorryCount})`,
  ].join('\\n');
}

const legendElem = document.getElementById('legend');
GRAPH_DATA.legend.forEach(item => {
  const elem = document.createElement('div');
  elem.className = 'legend-item';
  elem.innerHTML = `<span class="legend-swatch" style="background:${item.color}; border-color:${item.border};"></span>${item.group} <span style="color:#6f8094">(${item.count})</span>`;
  legendElem.appendChild(elem);
});

const nodes = new vis.DataSet(
  GRAPH_DATA.nodes.map(node => ({
    id: node.id,
    label: labelFor(node),
    title: node.modulePath,
    level: node.level,
    shape: 'box',
    margin: { top: 10, right: 14, bottom: 10, left: 14 },
    borderWidth: 2,
    borderWidthSelected: 3,
    font: {
      color: '#edf3fb',
      face: 'ui-monospace, SFMono-Regular, Menlo, monospace',
      size: labelMode === 'name' ? 14 : 12,
    },
    color: {
      background: node.color,
      border: node.border,
      highlight: { background: node.color, border: '#ffffff' },
      hover: { background: node.color, border: '#ffffff' },
    },
  }))
);

const edges = new vis.DataSet(
  GRAPH_DATA.edges.map(edge => ({
    from: edge.from,
    to: edge.to,
    arrows: { to: { enabled: true, scaleFactor: 0.72 } },
    color: {
      color: '#46576b',
      highlight: '#7db8ff',
      hover: '#7db8ff',
      opacity: 0.95,
    },
    width: 1.4,
    smooth: {
      enabled: true,
      type: 'cubicBezier',
      forceDirection: 'vertical',
      roundness: 0.28,
    },
  }))
);

const network = new vis.Network(
  document.getElementById('graph'),
  { nodes, edges },
  {
    autoResize: true,
    physics: false,
    interaction: {
      hover: true,
      keyboard: true,
      navigationButtons: false,
      tooltipDelay: 80,
    },
    layout: {
      hierarchical: {
        enabled: true,
        direction: 'UD',
        sortMethod: 'directed',
        blockShifting: true,
        edgeMinimization: true,
        parentCentralization: true,
        levelSeparation: 140,
        nodeSpacing: 180,
        treeSpacing: 220,
      }
    }
  }
);

function updateLabels() {
  nodes.update(
    GRAPH_DATA.nodes.map(node => ({
      id: node.id,
      label: labelFor(node),
      font: {
        color: '#edf3fb',
        face: 'ui-monospace, SFMono-Regular, Menlo, monospace',
        size: labelMode === 'name' ? 14 : 12,
      }
    }))
  );
}

function setLabelMode(mode) {
  labelMode = mode;
  document.querySelectorAll('[id^="label-mode-"]').forEach(elem => {
    elem.classList.toggle('active', elem.dataset.mode === mode);
  });
  updateLabels();
}

document.getElementById('fit-btn').addEventListener('click', () => {
  network.fit({ animation: true });
});
document.getElementById('label-mode-name').addEventListener('click', () => setLabelMode('name'));
document.getElementById('label-mode-counts').addEventListener('click', () => setLabelMode('counts'));

function chipMarkup(ids) {
  if (!ids.length) {
    return '';
  }
  return `<div class="chip-row">${ids.map(id => {
    const mod = MODULES[id];
    const label = mod ? shortName(mod) : id;
    return `<button class="chip" data-node="${id}">${label}</button>`;
  }).join('')}</div>`;
}

function chipSection(title, ids) {
  const content = chipMarkup(ids);
  if (!content) {
    return '';
  }
  return `
    <div class="section">
      <h3>${title}</h3>
      ${content}
    </div>
  `;
}

function defaultBadgeClass(decl) {
  if (decl.kind === 'lemma') {
    return 'badge-lemma';
  }
  if (decl.kind === 'theorem') {
    return 'badge-theorem';
  }
  return 'badge-def';
}

function declSection(title, decls, badgeClass, extraClass = '') {
  if (!decls.length) {
    return '';
  }
  return `
    <div class="section ${extraClass}">
      <h3>${title}</h3>
      <div class="decl-list">
        ${decls.map(decl => `
          <div class="decl-item">
            <span class="decl-badge ${badgeClass || defaultBadgeClass(decl)}">${decl.badge}</span>
            <div class="decl-name">
              ${decl.name}${decl.sorry ? '<span class="sorry-tag">sorry</span>' : ''}
            </div>
          </div>
        `).join('')}
      </div>
    </div>
    `;
}

function sorrySection(mod) {
  const decls = [...mod.lemmas, ...mod.theorems]
    .filter(decl => decl.sorry)
    .sort((a, b) => (a.order ?? 0) - (b.order ?? 0));
  return declSection('Sorries', decls, '', 'section-alert');
}

function fileHrefFor(mod) {
  if (!mod.fileHref) {
    return null;
  }
  return new URL(mod.fileHref, window.location.href).href;
}

function renderSidebar(id) {
  const mod = MODULES[id];
  if (!mod) return;

  const fileHref = fileHrefFor(mod);
  const openLink = fileHref
    ? `<a class="open-link" href="${fileHref}">Open ${mod.filePath}</a>`
    : `<span class="open-link disabled">Local file not found</span>`;

  const truncatedNote = mod.declarationListTruncated
    ? `<div class="section"><div class="truncated-note">Declaration list truncated to the first ${Math.max(mod.definitions.length, mod.lemmas.length, mod.theorems.length)} entries encountered in the source file.</div></div>`
    : '';

  document.getElementById('sidebar').innerHTML = `
    <div class="module-title">
      <span class="swatch" style="background:${mod.color}; border-color:${mod.border};"></span>
      <h2>${mod.label}</h2>
    </div>
    <div class="module-path">${mod.modulePath}</div>
    <div class="module-meta">
      <div class="meta-box">
        <div class="value">${mod.definitionCount}</div>
        <div class="label">Definitions</div>
      </div>
      <div class="meta-box">
        <div class="value">${mod.lemmaCount} / ${mod.lemmaSorryCount}</div>
        <div class="label">Lemmas / Sorry</div>
      </div>
      <div class="meta-box">
        <div class="value">${mod.theoremCount} / ${mod.theoremSorryCount}</div>
        <div class="label">Thms / Sorry</div>
      </div>
    </div>
    ${openLink}
    ${sorrySection(mod)}
    ${chipSection('Imports', mod.imports)}
    ${chipSection('Imported By', mod.importedBy)}
    ${declSection('Definitions', mod.definitions, 'badge-def')}
    ${declSection('Lemmas', mod.lemmas.filter(decl => !decl.sorry), 'badge-lemma')}
    ${declSection('Theorems', mod.theorems.filter(decl => !decl.sorry), 'badge-theorem')}
    ${truncatedNote}
  `;

  document.querySelectorAll('.chip').forEach(elem => {
    elem.addEventListener('click', () => selectNode(elem.dataset.node));
  });
}

function selectNode(id) {
  network.selectNodes([id]);
  network.focus(id, {
    scale: 1.0,
    animation: { duration: 350, easingFunction: 'easeInOutQuad' },
  });
  renderSidebar(id);
}

function openNode(id) {
  const mod = MODULES[id];
  const fileHref = mod ? fileHrefFor(mod) : null;
  if (fileHref) {
    window.location.href = fileHref;
  }
}

network.on('click', params => {
  if (params.nodes.length > 0) {
    renderSidebar(params.nodes[0]);
  }
});

network.on('doubleClick', params => {
  if (params.nodes.length > 0) {
    openNode(params.nodes[0]);
  }
});

network.once('afterDrawing', () => {
  network.fit({ animation: true });
});
</script>
</body>
</html>
"""


def main() -> None:
    args = parse_args()
    input_path = Path(args.input)
    output_path = Path(args.output)
    project_root = Path(args.root).resolve()

    nodes, edges = parse_gexf(input_path)
    graph_data = build_graph_data(nodes, edges, project_root, exclude=set(args.exclude))
    html = (
        HTML_TEMPLATE.replace("__PAGE_TITLE__", args.title)
        .replace("__GRAPH_DATA__", json.dumps(graph_data))
    )
    output_path.write_text(html, encoding="utf-8")


if __name__ == "__main__":
    main()
