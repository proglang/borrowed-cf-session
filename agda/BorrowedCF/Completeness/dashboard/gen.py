#!/usr/bin/env python3
"""Generate dashboard.html (auto-refreshing) and ../DASHBOARD.md from state.json."""
import json, html, os, datetime
here = os.path.dirname(os.path.abspath(__file__))
st = json.load(open(os.path.join(here, "state.json")))
def esc(s): return html.escape(str(s))
def badge(s):
    col = {"done":"#2e7d32","in-progress":"#f9a825","todo":"#9e9e9e","blocked":"#c62828","running":"#1565c0","finished":"#2e7d32","failed":"#c62828"}.get(s,"#607d8b")
    return f'<span style="background:{col};color:#fff;padding:2px 8px;border-radius:10px;font-size:12px">{esc(s)}</span>'
def table(rows, cols):
    h = "<table><tr>" + "".join(f"<th>{esc(c)}</th>" for c in cols) + "</tr>"
    for r in rows:
        h += "<tr>" + "".join(f"<td>{badge(r.get(c,'')) if c in ('status','state') else esc(r.get(c,''))}</td>" for c in cols) + "</tr>"
    return h + "</table>"

import glob
def status_sections():
    root = os.path.join(here, "..")
    out = ""
    for f in sorted(glob.glob(os.path.join(root, "**", "*STATUS*.md"), recursive=True)):
        rel = os.path.relpath(f, root)
        mtime = datetime.datetime.fromtimestamp(os.path.getmtime(f)).strftime("%H:%M:%S")
        out += f"<h3>{esc(rel)} <span class=meta>(modified {mtime})</span></h3><pre style='background:#fff;border:1px solid #ddd;padding:8px;white-space:pre-wrap;font-size:13px'>{esc(open(f).read())}</pre>"
    return out or "<p class=meta>no STATUS files yet</p>"

n_done = sum(1 for l in st["lemmas"] if l["status"]=="done"); n_all = len(st["lemmas"])
page = f"""<!doctype html><html><head><meta charset="utf-8"><meta http-equiv="refresh" content="20">
<title>Algorithmic completeness dashboard</title>
<style>body{{font-family:system-ui,sans-serif;margin:24px;background:#fafafa;color:#222}}
table{{border-collapse:collapse;width:100%;margin-bottom:24px;background:#fff}} th,td{{border:1px solid #ddd;padding:6px 10px;text-align:left;vertical-align:top;font-size:14px}}
th{{background:#eee}} h1{{margin-bottom:4px}} .meta{{color:#666;font-size:13px}} li{{margin-bottom:6px}}
.bar{{height:14px;background:#ddd;border-radius:7px;overflow:hidden;width:320px;display:inline-block;vertical-align:middle}}
.bar div{{height:100%;background:#2e7d32}}</style></head><body>
<h1>Algorithmic typing completeness</h1>
<div class="meta">state.json updated {esc(st['updated'])} · page generated {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')} · auto-refresh 20s</div>
<p>Lemmas done: {n_done}/{n_all} <span class="bar"><div style="width:{int(100*n_done/max(n_all,1))}%"></div></span></p>
<h2>Theorems</h2>{table(st['theorems'], ['name','module','status','note'])}
<h2>Lemmas</h2>{table(st['lemmas'], ['name','module','status','agent'])}
<h2>Agents</h2>{table(st['agents'], ['id','model','task','files','state'])}
<h2>Policy</h2><ul>{''.join(f'<li>{esc(i)}</li>' for i in st.get('policy',[]))}</ul>
<h2>Issues found (paper / development)</h2><ul>{''.join(f'<li>{esc(i)}</li>' for i in st['issues'])}</ul>
<h2>Memory watchdog log</h2><pre style="background:#fff;border:1px solid #ddd;padding:8px;font-size:13px">{esc(open(os.path.expanduser("~/.config/agda-mcp/watchdog.log")).read() if os.path.exists(os.path.expanduser("~/.config/agda-mcp/watchdog.log")) else "")}</pre>
<h2>Agent self-reports (STATUS.md files, unverified, refreshed automatically)</h2>{status_sections()}
</body></html>"""
open(os.path.join(here, "dashboard.html"), "w").write(page)
md = [f"# Algorithmic completeness dashboard\n\nGenerated from `dashboard/state.json` ({st['updated']}). Open `dashboard/dashboard.html` for the live view (`dashboard/serve.sh`).\n",
      "## Theorems\n", "| name | module | status | note |", "|---|---|---|---|"]
md += [f"| {t['name']} | {t['module']} | {t['status']} | {t['note']} |" for t in st['theorems']]
md += ["\n## Lemmas\n", "| name | module | status | agent |", "|---|---|---|---|"]
md += [f"| {l['name']} | {l['module']} | {l['status']} | {l.get('agent','-')} |" for l in st['lemmas']]
md += ["\n## Agents\n", "| id | model | task | files | state |", "|---|---|---|---|---|"]
md += [f"| {a['id']} | {a['model']} | {a['task']} | {a['files']} | {a['state']} |" for a in st['agents']]
md += ["\n## Issues found\n"] + [f"- {i}" for i in st['issues']]
open(os.path.join(here, "..", "DASHBOARD.md"), "w").write("\n".join(md) + "\n")
print("wrote dashboard.html and DASHBOARD.md")
