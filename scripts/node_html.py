"""Write docs/nodes/<Node>.html: one page per node for the GitHub Pages site.

Called by wheel.py with the same per-node data the wheel's summary panel
uses, so the page, the panel, GRAPH.md and docs/nodes/<Node>.md all say the
same thing. Dark by default, with the same light/dark switch as the wheel.
"""
import html
import os

import graph as g
import wheel

KIND = {
    "verified": "Proved in Lean",
    "conditional_built": "Proved in Lean, assuming an open conjecture",
    "cited_built": "Cited from a published paper",
    "draft": "Proof drafted, not yet built",
    "planned": "Planned: proved in a source file",
    "conditional": "Planned: will assume an open conjecture",
    "cited": "Planned: citation of a published result",
    "new": "Planned: new work, not yet proved",
    "external": "Outside source: proved in Lean elsewhere",
}

PAGE_CSS = """
* { box-sizing: border-box; }
html, body { margin: 0; background: var(--bg); color: var(--ink);
  font: 15px/1.55 -apple-system, BlinkMacSystemFont, "Segoe UI", system-ui, sans-serif; }
header { display: flex; align-items: center; gap: 16px; padding: 10px 20px;
  border-bottom: 1px solid var(--line); flex-wrap: wrap; position: sticky; top: 0; background: var(--bg); z-index: 2; }
header .brand { font-weight: 600; color: var(--ink); }
header .spacer { flex: 1; }
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }
main { max-width: 880px; margin: 0 auto; padding: 26px 22px 60px; }
h1 { font-size: 26px; margin: 0 0 2px; }
.title { color: var(--ink2); font-size: 17px; margin-bottom: 14px; }
h2 { font-size: 13px; text-transform: uppercase; letter-spacing: .06em; color: var(--ink2);
  margin: 30px 0 10px; border-bottom: 1px solid var(--line2); padding-bottom: 6px; }
.chip { display: inline-flex; align-items: center; gap: 6px; padding: 2px 10px; border-radius: 999px;
  border: 1px solid var(--line); font-size: 13px; margin: 0 6px 6px 0; color: var(--ink); }
.chip svg circle { stroke-width: 2; }
.k-verified circle { fill: var(--verified-f); stroke: var(--verified-s); }
.k-conditional_built circle { fill: var(--verified-f); stroke: var(--amber-s); stroke-width: 3; }
.k-cited_built circle { fill: var(--cited-f); stroke: var(--cited-s); }
.k-draft circle { fill: var(--hollow); stroke: var(--verified-s); stroke-dasharray: 2 2; }
.k-planned circle { fill: var(--hollow); stroke: var(--verified-s); stroke-dasharray: 3 2; }
.k-conditional circle { fill: var(--hollow); stroke: var(--amber-s); stroke-dasharray: 3 2; }
.k-cited circle { fill: var(--hollow); stroke: var(--cited-s); stroke-dasharray: 3 2; }
.k-new circle { fill: var(--hollow); stroke: var(--new-s); stroke-dasharray: 3 2; }
.k-external circle { fill: var(--ext-f); stroke: var(--ext-s); }
.nodelink { display: inline-block; padding: 1px 8px; margin: 0 5px 6px 0; border-radius: 6px;
  border: 1px solid var(--line); font: 13px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  color: var(--ink); background: var(--panel); }
.nodelink:hover { border-color: var(--accent); color: var(--accent); text-decoration: none; }
.claim { border: 1px solid var(--line); border-radius: 10px; padding: 14px 16px; margin: 0 0 14px;
  background: var(--panel); scroll-margin-top: 70px; }
.claim .cid { font: 600 14px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; word-break: break-all; }
.claim .cst { font-size: 13px; color: var(--ink2); margin: 2px 0 8px; }
.claim .row { margin-top: 8px; font-size: 14px; }
.claim .lbl { color: var(--ink2); }
pre { background: var(--code); border: 1px solid var(--line2); border-radius: 6px; padding: 10px 12px;
  overflow-x: auto; font: 13px/1.5 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; margin: 10px 0 0; }
code { font: 13px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
.openc { background: var(--open-f); border-radius: 4px; padding: 0 5px; }
.muted { color: var(--ink2); }
ul { padding-left: 20px; } li { margin: 5px 0; }
"""


def esc(text):
    return html.escape(str(text or ""), quote=True)


def node_link(name, data, claim=None):
    names = {n["name"] for n in data["nodes"]}
    text = f"{name}.{claim}" if claim else name
    if name not in names:
        return f'<span class="nodelink">{esc(text)}</span>'
    anchor = f"#{claim.lower()}" if claim else ""
    return f'<a class="nodelink" href="{esc(name)}.html{anchor}">{esc(text)}</a>'


def chip(kind):
    return (f'<span class="chip k-{kind}"><svg width="14" height="14"><circle cx="7" cy="7" r="5"/></svg>'
            f'{esc(KIND[kind])}</span>')


def gh(data, path, line=None):
    return f'{data["repo"]}/{path}' + (f"#L{line}" if line else "")


def write_page(n, data, nodes):
    name = n["name"]
    fam = {f["key"]: f["title"] for f in data["families"]}
    body = (f'<h1>{esc(n["label"])}</h1><div class="title">{esc(n["title"])}</div>'
            f'{chip(n["kind"])}<span class="chip">ring {n["depth"]}</span>'
            f'<span class="chip">{esc(fam.get(n["family"], n["family"]))}</span>'
            f'<p>{esc(n["description"])}</p>')
    if n["improves"]:
        body += f'<p><b>What it adds:</b> {esc(n["improves"])}</p>'
    if n["open"]:
        body += ('<p><b>Open conjectures it assumes</b> (never claimed): '
                 + " ".join(f'<code class="openc">{esc(o)}</code>' for o in n["open"]) + "</p>")

    body += "<h2>Rests on</h2>"
    if n["rests_on"]:
        body += "".join(node_link(r, data) for r in n["rests_on"])
    elif n["vocab"]:
        body += ('<p class="muted">No other node. Uses the shared vocabulary: '
                 + ", ".join(f"<code>{esc(v)}</code>" for v in n["vocab"]) + "</p>")
    else:
        body += '<p class="muted">No other node: Mathlib and the shared vocabulary only.</p>'
    body += "<h2>Used by</h2>" + ("".join(node_link(u, data) for u in n["used_by"])
                                   or '<p class="muted">No node yet.</p>')

    if n["sources"]:
        body += "<h2>Published sources</h2><ul>"
        for s in n["sources"]:
            title = f'<a href="{esc(s["url"])}">{esc(s["title"])}</a>' if s["url"] else esc(s["title"])
            body += (f'<li>{esc(s["text"]) + ", " if s["text"] else ""}{title}'
                     f'{" <span class=muted>— " + esc(s["how"]) + "</span>" if s["how"] else ""}</li>')
        body += "</ul>"

    if n["related"]:
        body += ('<h2>Related nodes</h2><p class="muted">Connected in content but not by an arrow; '
                 'each entry says how.</p><ul>')
        body += "".join(f'<li>{node_link(r["node"], data)} {esc(r["note"])}</li>' for r in n["related"])
        body += "</ul>"

    if n["claims"]:
        body += f'<h2>Claims ({len(n["claims"])})</h2>'
        for c in n["claims"]:
            body += (f'<div class="claim" id="{esc(c["id"].lower())}"><div class="cid">{esc(c["id"])}</div>'
                     f'<div class="cst">{esc(c["status"])}</div><div>{esc(c["summary"])}</div>')
            if c["statement"]:
                body += f'<pre><code>{esc(c["statement"])}</code></pre>'
            body += ('<div class="row"><span class="lbl">Rests on:</span> '
                     + ("".join(node_link(s, data, cl) for s, cl in c["rests_on"])
                        or "no other node (Mathlib and the Vocabulary only)") + "</div>")
            if c["open"]:
                body += ('<div class="row"><span class="lbl">Assumes, never claims:</span> '
                         + " ".join(f'<code class="openc">{esc(o)}</code>' for o in c["open"]) + "</div>")
            stmt_path = f"RNSNetwork/Nodes/{name}/Conclusions.lean"
            body += (f'<div class="row"><a href="{gh(data, stmt_path, c["line"])}">'
                     f'Statement in Conclusions.lean ↗</a></div>')
            if c["proof"]:
                p = c["proof"]
                body += (f'<div class="row"><span class="lbl">Proof:</span> '
                         f'<a href="{gh(data, p["file"], p["line"])}"><code>{esc(p["declaration"])}</code> ↗</a>')
                if p["assembled"]:
                    body += (f'; joined to its inputs in <a href="{gh(data, "RNSSolutions/Assemble.lean")}">'
                             f'<code>Assemble.lean</code> ↗</a>')
                body += "</div>"
            if c["cite"]:
                body += f'<div class="row muted">Cited: {esc(c["cite"])}. Not proved in Lean.</div>'
            body += "</div>"
    elif n["planned"]:
        p = n["planned"]
        if p["external"]:
            e = p["external"]
            decl = f"<code>{esc(e['declaration'])}</code> in " if e["declaration"] else ""
            body += f'<h2>Outside source</h2><p>{decl}<a href="{esc(e["url"])}">{esc(e["project"])} ↗</a></p>'
            if e["note"]:
                body += f'<p class="muted">{esc(e["note"])}</p>'
        if p["claims"]:
            body += "<h2>Planned claims</h2><p>" + ", ".join(f"<code>{esc(c)}</code>" for c in p["claims"]) + "</p>"
        for key, title in [("progress", "Progress"), ("plan", "Plan"), ("citation", "Citation")]:
            if p[key]:
                body += f"<h2>{title}</h2><p>{esc(p[key])}</p>"

    body += "<h2>Files</h2><ul>"
    if n["built"]:
        body += f'<li><a href="{gh(data, f"RNSNetwork/Nodes/{name}/Conclusions.lean")}">Conclusions.lean ↗</a></li>'
    body += (f'<li><a href="{gh(data, f"RNSNetwork/Nodes/{name}/formalization.yaml")}">formalization.yaml ↗</a></li>'
             f'<li><a href="{gh(data, f"docs/nodes/{name}.md")}">This page on GitHub ↗</a></li></ul>')

    page = f"""<!DOCTYPE html>
<!-- Generated by scripts/graph.py (scripts/node_html.py). Do not edit. -->
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(name)} — {esc(n["title"])} · RNS Sieve Network</title>
<script>{wheel.THEME_JS}</script>
<style>
{wheel.theme_css()}
{PAGE_CSS}
</style>
</head>
<body>
<header>
  <a class="brand" href="../index.html">RNS Sieve Network</a>
  <a href="../index.html#{esc(name)}">← Back to the wheel</a>
  <span class="spacer"></span>
  <button id="theme" type="button"></button>
  <a href="https://github.com/golfbum71/RNS-Sieve-Network">Repository</a>
</header>
<main>
{body}
</main>
<script>{wheel.THEME_TOGGLE}</script>
</body>
</html>
"""
    open(os.path.join(g.ROOT, "docs", "nodes", f"{name}.html"), "w", encoding="utf-8").write(page)
