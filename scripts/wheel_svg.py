"""Write docs/wheel-dark.svg and docs/wheel-light.svg: still pictures of the wheel.

GitHub will not run the interactive page inside the README, so the README
shows one of these (matching the reader's GitHub theme) and links it to the
live page. Drawn from the same data and layout as docs/index.html; called by
wheel.py, so it is regenerated every time graph.py runs.
"""
import html
import math
import os

import graph as g

THEMES = {
    "dark": {
        "bg": "#0d1117", "ink": "#e6edf3", "ink2": "#9198a1", "line": "#30363d", "line2": "#21262d",
        "wedge_a": "#151b23", "wedge_b": "#11161d", "edge": "#6e7681", "hub": "#2a2720",
        "hub_stroke": "#8b8577", "verified_f": "#123d24", "verified_s": "#3fb950", "amber_s": "#d29922",
        "cited_f": "#0f2d4d", "cited_s": "#4493f8", "new_s": "#8b949e", "ext_f": "#2f1f4a",
        "ext_s": "#ab7df8", "hollow": "#0d1117",
    },
    "light": {
        "bg": "#ffffff", "ink": "#1f2328", "ink2": "#57606a", "line": "#d0d7de", "line2": "#eaeef2",
        "wedge_a": "#f2f4f7", "wedge_b": "#f8f9fb", "edge": "#8c959f", "hub": "#f3f0e8",
        "hub_stroke": "#a39e8f", "verified_f": "#dafbe1", "verified_s": "#1a7f37", "amber_s": "#9a6700",
        "cited_f": "#ddf4ff", "cited_s": "#0969da", "new_s": "#6e7781", "ext_f": "#fbefff",
        "ext_s": "#8250df", "hollow": "#ffffff",
    },
}

# fill, stroke, stroke width, dash — one per status, as on the interactive page
def mark(kind, c):
    return {
        "verified": (c["verified_f"], c["verified_s"], 2, None),
        "conditional_built": (c["verified_f"], c["amber_s"], 3, None),
        "cited_built": (c["cited_f"], c["cited_s"], 2, None),
        "draft": (c["hollow"], c["verified_s"], 2, "2 2"),
        "planned": (c["hollow"], c["verified_s"], 2, "3 2"),
        "conditional": (c["hollow"], c["amber_s"], 2, "3 2"),
        "cited": (c["hollow"], c["cited_s"], 2, "3 2"),
        "new": (c["hollow"], c["new_s"], 2, "3 2"),
        "external": (c["ext_f"], c["ext_s"], 2, None),
    }[kind]


LEGEND = [("verified", "Proved in Lean"), ("conditional_built", "Proved, assuming an open conjecture"),
          ("cited_built", "Cited from a paper"), ("new", "Planned"), ("external", "Outside source")]


def esc(text):
    return html.escape(str(text), quote=True)


def f(x):
    return f"{x:.1f}"


def pt(r, a):
    return r * math.sin(a), -r * math.cos(a)


def sector(r0, r1, a0, a1):
    large = 1 if a1 - a0 > math.pi else 0
    x0, y0 = pt(r1, a0)
    x1, y1 = pt(r1, a1)
    x2, y2 = pt(r0, a1)
    x3, y3 = pt(r0, a0)
    return (f"M{f(x0)},{f(y0)} A{r1},{r1} 0 {large} 1 {f(x1)},{f(y1)} "
            f"L{f(x2)},{f(y2)} A{r0},{r0} 0 {large} 0 {f(x3)},{f(y3)} Z")


def draw(data, theme):
    c = THEMES[theme]
    geo = data["geometry"]
    ring = lambda k: geo["first"] + geo["step"] * (k - 1)
    nodes = {n["name"]: n for n in data["nodes"]}
    fam_outer = {fm["key"]: ring(max(n["depth"] for n in data["nodes"] if n["family"] == fm["key"])) + 95
                 for fm in data["families"]}
    extent = max(fam_outer.values()) + 95
    legend_h = 40
    out, defs = [], []

    fams = data["families"]
    for i, fm in enumerate(fams):
        outer = fam_outer[fm["key"]]
        out.append(f'<path d="{sector(geo["hub"], outer, fm["start"], fm["end"])}" '
                   f'fill="{c["wedge_b"] if i % 2 else c["wedge_a"]}"/>')
        prev = fams[(i - 1) % len(fams)]
        x0, y0 = pt(geo["hub"], fm["start"])
        x1, y1 = pt(max(outer, fam_outer[prev["key"]]), fm["start"])
        out.append(f'<line x1="{f(x0)}" y1="{f(y0)}" x2="{f(x1)}" y2="{f(y1)}" stroke="{c["line"]}"/>')
        mid, r = (fm["start"] + fm["end"]) / 2, outer + 30
        bottom = math.cos(mid) < 0
        span = min(max(fm["end"] - fm["start"], 1.1), math.pi) / 2
        sx, sy = pt(r, mid + span if bottom else mid - span)
        ex, ey = pt(r, mid - span if bottom else mid + span)
        pid = f"fam-{theme}-{fm['key']}"
        defs.append(f'<path id="{pid}" d="M{f(sx)},{f(sy)} A{r},{r} 0 0 {0 if bottom else 1} {f(ex)},{f(ey)}"/>')
        out.append(f'<text font-size="22" font-weight="600" fill="{c["ink2"]}" dy="{18 if bottom else 0}">'
                   f'<textPath href="#{pid}" startOffset="50%" text-anchor="middle">{esc(fm["title"])}</textPath></text>')

    for k in range(1, data["rings"] + 1):
        out.append(f'<circle r="{ring(k)}" fill="none" stroke="{c["line2"]}" stroke-dasharray="2 4"/>')

    edges = {}
    for s, d, kind in data["edges"]:
        if (s, d) not in edges or kind == "built":
            edges[(s, d)] = kind
    for n in data["nodes"]:
        if n["depth"] == 1 and n["vocab"]:
            x0, y0 = pt(geo["hub"], n["angle"])
            x1, y1 = pt(ring(1) - 9, n["angle"])
            out.append(f'<line x1="{f(x0)}" y1="{f(y0)}" x2="{f(x1)}" y2="{f(y1)}" '
                       f'stroke="{c["hub_stroke"]}" opacity=".35"/>')
    for (s, d), kind in sorted(edges.items()):
        a, b = nodes[s], nodes[d]
        ra, rb = ring(a["depth"]), ring(b["depth"])
        rm = (ra + rb) / 2
        p = [pt(ra, a["angle"]), pt(rm, a["angle"]), pt(rm, b["angle"]), pt(rb, b["angle"])]
        dash = ' stroke-dasharray="4 4"' if kind == "planned" else ""
        out.append(f'<path d="M{f(p[0][0])},{f(p[0][1])} C{f(p[1][0])},{f(p[1][1])} {f(p[2][0])},{f(p[2][1])} '
                   f'{f(p[3][0])},{f(p[3][1])}" fill="none" stroke="{c["edge"]}" stroke-width="1.3" '
                   f'opacity="{.45 if kind == "planned" else .55}"{dash}/>')

    for n in data["nodes"]:
        x, y = pt(ring(n["depth"]), n["angle"])
        fill, stroke, width, dash = mark(n["kind"], c)
        big = n["name"] in ("Wheel6", "CRT")
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        left = math.sin(n["angle"]) < -1e-9
        rot = math.degrees(n["angle"]) - 90 + (180 if left else 0)
        tx = -15 if left else 15
        ink = c["ink2"] if n["kind"] in ("new", "planned", "conditional", "cited") else c["ink"]
        spans = "".join(
            f'<tspan x="{tx}" dy="{("-0.55em" if len(n["lines"]) > 1 else "0") if i == 0 else "1.1em"}">'
            f'{esc(line)}</tspan>' for i, line in enumerate(n["lines"]))
        out.append(f'<g transform="translate({f(x)},{f(y)})">'
                   f'<circle r="{10 if big else 8}" fill="{fill}" stroke="{stroke}" stroke-width="{width}"{dash_attr}/>'
                   f'<text transform="rotate({f(rot)})" font-size="13" fill="{ink}" dominant-baseline="central" '
                   f'text-anchor="{"end" if left else "start"}">{spans}</text></g>')

    out.append(f'<circle r="{geo["hub"]}" fill="{c["hub"]}" stroke="{c["hub_stroke"]}" stroke-width="1.5"/>')
    for text, size, weight, color, dy in [("The RNS wheel", 22, 650, c["ink"], -26),
                                          ("primorial modulus · CRT", 13, 400, c["ink2"], 4),
                                          ("survivors · admissibility", 13, 400, c["ink2"], 24),
                                          ("Vocabulary.lean", 13, 400, c["ink2"], 50)]:
        out.append(f'<text y="{dy}" font-size="{size}" font-weight="{weight}" fill="{color}" '
                   f'text-anchor="middle">{esc(text)}</text>')

    # legend along the bottom, then a pointer to the interactive page
    y = extent + 20
    x = -extent + 30
    for kind, word in LEGEND:
        fill, stroke, width, dash = mark(kind, c)
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        out.append(f'<circle cx="{x}" cy="{y}" r="8" fill="{fill}" stroke="{stroke}" stroke-width="{width}"{dash_attr}/>'
                   f'<text x="{x + 16}" y="{y}" font-size="17" fill="{c["ink2"]}" dominant-baseline="central">{esc(word)}</text>')
        x += 44 + len(word) * 9.6
    out.append(f'<text x="{extent - 30}" y="{y}" font-size="17" fill="{c["ink2"]}" text-anchor="end" '
               f'dominant-baseline="central">Click for the interactive wheel</text>')

    w = 2 * extent
    h = 2 * extent + legend_h + 10
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{-extent} {-extent} {w} {h}" width="{w}" height="{h}" '
            f'font-family="-apple-system, BlinkMacSystemFont, Segoe UI, Helvetica, Arial, sans-serif">\n'
            f'<!-- Generated by scripts/graph.py (scripts/wheel_svg.py). Do not edit. -->\n'
            f'<rect x="{-extent}" y="{-extent}" width="{w}" height="{h}" rx="16" fill="{c["bg"]}"/>\n'
            f'<defs>{"".join(defs)}</defs>\n' + "\n".join(out) + "\n</svg>\n")


def write_svgs(data):
    for theme in THEMES:
        path = os.path.join(g.ROOT, "docs", f"wheel-{theme}.svg")
        open(path, "w", encoding="utf-8").write(draw(data, theme))
