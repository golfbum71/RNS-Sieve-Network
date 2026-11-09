"""Write docs/index.html: the network drawn as a wheel.

Called by graph.py; it reuses graph.py's loading and status helpers, so the
wheel always matches GRAPH.md and the node pages.

The layout:
  * Center: the RNS wheel itself, i.e. RNSNetwork/Vocabulary.lean (the
    primorial modulus, the CRT map, survivors, admissibility).
  * Rings: a node's ring is the length of its longest chain of arrows back
    to a node that rests on no other node. Ring 1 holds nodes that rest on
    no other node; each arrow points outward.
  * Wedges: one wedge per family, in the order of graph.GROUPS.
  * A faint spoke joins a ring-1 node to the center only when its
    Conclusions.lean actually uses a Vocabulary definition.

Nothing here decides what is proved: every status comes from graph.py.
"""
import json
import math
import os
import re

import graph as g

R_HUB = 125          # radius of the center disc
R_FIRST = 250        # radius of ring 1
R_STEP = 96          # distance between rings
MIN_ARC = 34         # smallest distance between neighbouring nodes on a ring
WEDGE_PAD = 0.05     # radians of empty space at each side of a wedge

DISPLAY = {"Wheel6": "Wheel6 (6n±1)"}

HERE = os.path.dirname(os.path.abspath(__file__))

# Runs in <head> so a saved light choice applies before the page draws.
THEME_JS = ('try { var t = localStorage.getItem("rns-theme"); '
            'if (t) document.documentElement.dataset.theme = t; } catch (e) {}')

# Wires up the button with id="theme"; dark is the default.
THEME_TOGGLE = """(function () {
  var b = document.getElementById("theme"), d = document.documentElement;
  function label() { b.textContent = d.dataset.theme === "light" ? "\u263E Dark" : "\u2600 Light"; }
  b.addEventListener("click", function () {
    if (d.dataset.theme === "light") delete d.dataset.theme; else d.dataset.theme = "light";
    try { localStorage.setItem("rns-theme", d.dataset.theme || "dark"); } catch (e) {}
    label();
  });
  label();
})();"""


def theme_css():
    return open(os.path.join(HERE, "theme.css"), encoding="utf-8").read()


def label_lines(text):
    """Split a long node name into two balanced lines at a word boundary."""
    if len(text) <= 13:
        return [text]
    words = text.split(" ") if " " in text else re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z]*|\d+|[a-z]+", text)
    if len(words) < 2:
        return [text]
    joiner = " " if " " in text else ""
    best = min(range(1, len(words)),
               key=lambda i: max(len(joiner.join(words[:i])), len(joiner.join(words[i:]))))
    return [joiner.join(words[:best]), joiner.join(words[best:])]


def vocabulary_defs():
    text = open(os.path.join(g.ROOT, "RNSNetwork", "Vocabulary.lean"), encoding="utf-8").read()
    return re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev)\s+(\w+)", text, re.M)


def uses_vocabulary(name, vocab):
    path = os.path.join(g.NODES, name, "Conclusions.lean")
    if not os.path.exists(path):
        return []
    text = open(path, encoding="utf-8").read()
    return [v for v in vocab if re.search(r"\b" + re.escape(v) + r"\b", text)]


def parents_of(nodes, edges):
    """Node -> set of nodes it rests on (built arrows and planned ones)."""
    par = {n: set() for n in nodes}
    for (src, dst) in edges:
        if src != dst:
            par[dst].add(src)
    for n in nodes.values():
        for src in n["planned"].get("rests_on") or []:
            if src != n["name"] and src in nodes:
                par[n["name"]].add(src)
    return par


def depths(nodes, par):
    memo = {}

    def d(n):
        if n not in memo:
            memo[n] = 1  # guards against a cycle in planned arrows
            memo[n] = 1 + max((d(p) for p in par[n]), default=0)
        return memo[n]

    return {n: d(n) for n in nodes}


def ring_radius(k):
    return R_FIRST + R_STEP * (k - 1)


def spread_clear(desired, lo, hi, gap, blocked):
    """Like `spread`, but also keeps clear of `blocked` angle intervals (the
    labels of the ring just inside). Falls back to `spread` if it cannot."""
    # Merge overlapping intervals first: jumping out of one interval into an
    # overlapping one could otherwise bounce between them for ever.
    merged = []
    for a, b in sorted(blocked):
        if merged and a <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else:
            merged.append((a, b))
    blocked = merged
    pos, prev = [], lo - gap
    for x in desired:
        p = max(x, lo, prev + gap)
        moved = True
        while moved:
            moved = False
            for a, b in blocked:
                if a < p < b:
                    # jump to whichever side is nearer, if the near side is allowed
                    back = a
                    p = back if back >= max(lo, prev + gap) and p - back < b - p else b
                    moved = True
                    break
        pos.append(p)
        prev = p
    if pos and pos[-1] > hi:
        return spread(desired, lo, hi, gap)
    return pos


def spread(desired, lo, hi, gap):
    """Positions as near `desired` (sorted) as possible, at least `gap` apart, inside [lo, hi]."""
    count = len(desired)
    if count == 0:
        return []
    if gap * (count - 1) >= hi - lo:
        step = (hi - lo) / count
        return [lo + step * (i + 0.5) for i in range(count)]
    pos = [min(max(x, lo), hi) for x in desired]
    for i in range(1, count):
        pos[i] = max(pos[i], pos[i - 1] + gap)
    if pos[-1] > hi:
        pos[-1] = hi
        for i in range(count - 2, -1, -1):
            pos[i] = min(pos[i], pos[i + 1] - gap)
    return pos


def layout(nodes, depth, par):
    """Angle (radians, 0 = up, clockwise) for every node."""
    fam_order = [key for key, _, _ in g.GROUPS] + ["other"]
    listed = {name: i for _, _, names in g.GROUPS for i, name in enumerate(names)}
    members = {f: [] for f in fam_order}
    for name in nodes:
        members[g.group_of(nodes[name])].append(name)
    fam_order = [f for f in fam_order if members[f]]

    # A wedge must be wide enough for its most crowded ring.
    need = {}
    for f in fam_order:
        counts = {}
        for name in members[f]:
            counts[depth[name]] = counts.get(depth[name], 0) + 1
        need[f] = max(c * MIN_ARC / ring_radius(k) for k, c in counts.items()) + 2 * WEDGE_PAD
    scale = 2 * math.pi / sum(need.values())
    wedges, start = {}, 0.0
    for f in fam_order:
        wedges[f] = (start, start + need[f] * scale)
        start += need[f] * scale

    angle = {}
    for k in range(1, max(depth.values()) + 1):
        gap = MIN_ARC / ring_radius(k)
        # the labels of the ring just inside run out across this ring
        half = 0.55 * MIN_ARC / ring_radius(k)
        blocked = [(angle[n] + turn - half, angle[n] + turn + half)
                   for n in angle if depth[n] == k - 1 for turn in (-2 * math.pi, 0, 2 * math.pi)]
        for f in fam_order:
            lo, hi = wedges[f][0] + WEDGE_PAD, wedges[f][1] - WEDGE_PAD
            ring = [n for n in members[f] if depth[n] == k]
            if not ring:
                continue
            if k == 1:
                ring.sort(key=lambda n: listed.get(n, 999))
                step = (hi - lo) / len(ring)
                for i, n in enumerate(ring):
                    angle[n] = lo + step * (i + 0.5)
                continue

            def want(n):
                ps = [angle[p] for p in par[n] if p in angle]
                if not ps:
                    return (lo + hi) / 2
                # circular mean, then brought into this wedge's range
                x = math.atan2(sum(math.sin(a) for a in ps), sum(math.cos(a) for a in ps))
                while x < lo - math.pi:
                    x += 2 * math.pi
                while x > hi + math.pi:
                    x -= 2 * math.pi
                return x

            ring.sort(key=lambda n: (want(n), listed.get(n, 999)))
            for n, a in zip(ring, spread_clear([want(n) for n in ring], lo, hi, gap, blocked)):
                angle[n] = a
    return angle, wedges, fam_order


def line_of(rel_path, name, keywords):
    """1-based line of the first `<keyword> name` in a repo file, or None."""
    path = os.path.join(g.ROOT, rel_path)
    if not name or not os.path.exists(path):
        return None
    pattern = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:"
                         + "|".join(keywords) + r")\s+(?:[\w.]*\.)?" + re.escape(name) + r"\b")
    for i, line in enumerate(open(path, encoding="utf-8"), 1):
        if pattern.match(line):
            return i
    return None


def claim_data(n, c):
    j = g.designated(c)
    proof = None
    if j and j.get("kind") != "literature" and j.get("solution"):
        decl = j.get("declaration") or ""
        proof = {"declaration": decl, "file": j.get("solution"),
                 "line": line_of(j.get("solution"), decl.split(".")[-1], ["theorem", "lemma", "def"]),
                 "assembled": bool(j.get("assembled"))}
    cite = None
    if j.get("kind") == "literature":
        cite = f"{j.get('source', '')}, {j.get('locator', '')}".strip(", ")
    return {
        "id": c["id"],
        "summary": " ".join(str(c.get("summary", "")).split()),
        "status": g.claim_word(c),
        "statement": n["statements"].get(c["id"], ""),
        "line": line_of(f"RNSNetwork/Nodes/{n['name']}/Conclusions.lean", c["id"], ["def"]),
        "rests_on": [list(g.node_of(r)) for r in c.get("imports") or []],
        "open": c.get("open_inputs") or [],
        "proof": proof,
        "cite": cite,
    }


def node_data(n, nodes, edges, par, depth, angle, vocab_used):
    name = n["name"]
    p = n["planned"]
    users = sorted({dst for (src, dst) in edges if src == name and dst != name}
                   | {m for m in nodes if name in (nodes[m]["planned"].get("rests_on") or [])},
                   key=lambda u: nodes[u]["order"])
    pub = [{"text": ", ".join(s.get("authors") or []), "title": s.get("title", ""),
            "url": s.get("url"), "how": " ".join(str(s.get("relationship", "")).split())}
           for s in g.published_sources(n)]
    ext = p.get("external") or None
    return {
        "name": name,
        "label": DISPLAY.get(name, name),
        "lines": label_lines(DISPLAY.get(name, name)),
        "title": n["title"],
        "family": g.group_of(n),
        "kind": g.node_kind(n),
        "status": g.status_word(n),
        "description": n["description"],
        "improves": n["improves"],
        "depth": depth[name],
        "angle": angle[name],
        "rests_on": sorted(par[name], key=lambda u: nodes[u]["order"]),
        "used_by": users,
        "open": g.opens_of(n),
        "claims": [claim_data(n, c) for c in n["conclusions"]] if n["built"] else [],
        "planned": {
            "claims": p.get("claims") or [],
            "plan": " ".join(str(p.get("plan", "") or "").split()),
            "progress": " ".join(str(p.get("progress", "") or "").split()),
            "citation": " ".join(str(p.get("citation", "") or "").split()),
            "external": ({"project": ext.get("project", ""), "url": ext.get("url", ""),
                          "declaration": ext.get("declaration", ""),
                          "note": " ".join(str(ext.get("note", "") or "").split())} if ext else None),
        } if not n["built"] else None,
        "sources": pub,
        "vocab": vocab_used,
        "built": n["built"],
        "order": n["order"],
        "related": [{"node": r.get("node", ""), "note": " ".join(str(r.get("note", "")).split())}
                    for r in n["related"]],
    }


def write_wheel(nodes, edges):
    par = parents_of(nodes, edges)
    depth = depths(nodes, par)
    angle, wedges, fam_order = layout(nodes, depth, par)
    vocab = vocabulary_defs()
    data = {
        "repo": g.REPO_URL,
        "rings": max(depth.values()),
        "arrows": sum(len(v) for v in edges.values()),
        "geometry": {"hub": R_HUB, "first": R_FIRST, "step": R_STEP},
        "families": [{"key": f, "title": g.GROUP_TITLE[f], "start": wedges[f][0], "end": wedges[f][1]}
                     for f in fam_order],
        "nodes": [node_data(nodes[nm], nodes, edges, par, depth, angle,
                            uses_vocabulary(nm, vocab) if depth[nm] == 1 else [])
                  for nm in g.by_order(nodes)],
        "edges": sorted({(s, d, "built") for (s, d) in edges if s != d}
                        | {(s, n["name"], "planned") for n in nodes.values()
                           for s in n["planned"].get("rests_on") or [] if s in nodes and s != n["name"]}),
        "vocab": vocab,
    }
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    template = open(os.path.join(HERE, "wheel_template.html"), encoding="utf-8").read()
    html = (template.replace("/*__THEME_JS__*/", THEME_JS).replace("/*__THEME__*/", theme_css())
            .replace("/*__THEME_TOGGLE__*/", THEME_TOGGLE).replace("/*__DATA__*/null", payload))
    open(os.path.join(g.ROOT, "docs", "index.html"), "w", encoding="utf-8").write(html)
    # GitHub Pages: serve the files as they are, without Jekyll turning the
    # .md node pages into .html files that would clash with the ones below.
    open(os.path.join(g.ROOT, "docs", ".nojekyll"), "w").close()
    import wheel_svg
    wheel_svg.write_svgs(data)
    import node_html
    for n in data["nodes"]:
        node_html.write_page(n, data, nodes)
