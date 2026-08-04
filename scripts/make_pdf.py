#!/usr/bin/env python3
"""Render the dossier (README.md) to the PDF artifact — the emailed PDF and the
repo's README are the same object by construction."""
import markdown
from weasyprint import HTML

MD = "README.md"
OUT = "heaviside-dossier.pdf"

with open(MD, encoding="utf-8") as f:
    text = f.read()
body = markdown.markdown(text, extensions=["tables", "fenced_code"])
html = f"""<!DOCTYPE html>
<html><head><meta charset="utf-8">
<style>
  @page {{ size: A4; margin: 1.2cm; }}
  body {{ font-family: "DejaVu Sans Mono", monospace; font-size: 10pt;
         line-height: 1.35; color: #111; }}
  h1 {{ font-size: 15pt; border-bottom: 2px solid #333; padding-bottom: 4px; }}
  h2 {{ font-size: 12pt; border-bottom: 1px solid #888; padding-bottom: 2px;
       margin-top: 18px; }}
  h3 {{ font-size: 10.5pt; }}
  code {{ font-family: "DejaVu Sans Mono", monospace; font-size: 9pt;
         background: #f2f2f2; padding: 0 2px; }}
  pre {{ background: #f6f6f6; padding: 6px; font-size: 9pt;
        border-left: 3px solid #888; white-space: pre-wrap; }}
  table {{ border-collapse: collapse; margin: 8px 0; }}
  th, td {{ border: 1px solid #999; padding: 3px 7px; font-size: 9pt; }}
  th {{ background: #eee; }}
  blockquote {{ margin: 6px 0; padding-left: 10px; border-left: 3px solid #aaa;
               color: #333; }}
  ol {{ padding-left: 20px; }}
</style></head><body>
{body}
</body></html>"""
HTML(string=html).write_pdf(OUT)
print(OUT)
