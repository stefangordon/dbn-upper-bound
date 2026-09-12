#!/usr/bin/env python3
"""Build the manuscript and its exact source-box table.

Requires Pandoc and LuaLaTeX. Mathematical text is kept in Markdown; the LaTeX
source emitted in build/paper is suitable for inspection and journal adaptation.
No author or affiliation is inferred from the machine's account settings.
"""

import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPER_INPUTS = [
    "manuscript/main.md",
    "manuscript/analytic-estimates.md",
    "manuscript/computational-estimates.md",
    "manuscript/source-boxes.md",
    "manuscript/references.md",
    "manuscript/preamble.tex",
    "scripts/build_paper.py",
]


def paper_inputs():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in PAPER_INPUTS}


def check_pdf():
    record = json.loads((ROOT / "output/pdf/build.json").read_text())
    if record.get("schema_version") != 1 or record.get("sources") != paper_inputs():
        raise ValueError("PDF source identity mismatch; rebuild the paper")
    if record.get("layout_warnings") != []:
        raise ValueError("recorded PDF build has unresolved layout warnings")
    pdf = ROOT / "output/pdf/dbn-upper-bound.pdf"
    if hashlib.sha256(pdf.read_bytes()).hexdigest() != record.get("pdf_sha256"):
        raise ValueError("PDF differs from the recorded build")


def source_table():
    data = json.loads((ROOT / "certificate/data/barriers.json").read_text())
    text = [
        "# Appendix B. Source boxes",
        "",
        "Each row specifies a closed time-height rectangle on which $V(x,h,t)>L$ for every $x\\ge X$. "
        "All entries are exact rationals. The printed table is generated from the same catalog consumed by the barrier checker and Lean.",
        "",
        "| Box | Time interval | Height interval | Floor $L$ |",
        "|:---|:----------------------|:--------------------------|-------------:|",
    ]
    for box in data["sources"]:
        label = "A" if box["id"] == 0 else f"{box['id']:02}"
        text.append(
            f"| {label} | $[{box['btl']},\\,{box['btr']}]$ | "
            f"$[{box['hlo']},\\,{box['hhi']}]$ | ${box['L']}$ |"
        )
    text += [
        "",
        "The source proof is Proposition C.3. The source evaluator checks these same 26 rectangles; "
        "an exact input-identity check connects its box file to this catalog.",
        "",
    ]
    return "\n".join(text)


def section_source(path, appendix=None):
    text = path.read_text()
    if appendix:
        title = "Analytic estimates" if appendix == "A" else "Computational estimates"
        text = re.sub(
            r"^# .*\n",
            f"# Appendix {appendix}. {title} {{#appendix-{appendix.lower()}}}\n",
            text,
            count=1,
        )
        text = re.sub(
            r"^(#{2,}) (\d+(?:\.\d+)*)\.?\s+(.+)$",
            lambda m: f"{m[1]} {appendix}.{m[2]}. {m[3]}",
            text,
            flags=re.M,
        )
    else:
        text = re.sub(r"^# .*\n", "", text, count=1)
        text = re.sub(r"^(#{2,}) ", lambda m: m[1][1:] + " ", text, flags=re.M)
    # In the combined PDF these links refer to included appendices, rather than
    # filesystem-relative Markdown files. Repository source links stay intact.
    text = re.sub(
        r"\[[^\]]*\]\((?:\.\./manuscript/)?analytic-estimates\.md\)",
        "[Appendix A](#appendix-a)",
        text,
    )
    text = re.sub(
        r"\[[^\]]*\]\((?:\.\./manuscript/)?computational-estimates\.md\)",
        "[Appendix C](#appendix-c)",
        text,
    )
    text = re.sub(
        r"\[[^\]]*\]\(\.\./support/source/boxes\.json\)", "[Appendix B](#appendix-b)", text
    )
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table-only", action="store_true")
    parser.add_argument(
        "--check-pdf",
        action="store_true",
        help="check PDF/source identities without typesetting or writing",
    )
    parser.add_argument(
        "--check-table", action="store_true", help="compare the source table without writing"
    )
    args = parser.parse_args()
    target = ROOT / "manuscript/source-boxes.md"
    expected = source_table()
    if args.check_pdf:
        try:
            check_pdf()
        except (ValueError, KeyError, OSError) as error:
            parser.exit(1, f"FAIL: {error}\n")
        print("PASS: PDF matches its recorded build and current manuscript sources.")
        return
    if args.check_table:
        if not target.is_file() or target.read_text() != expected:
            parser.exit(1, "FAIL: source-box table differs from the exact certificate\n")
        print("PASS: printed source-box table matches the exact certificate.")
        return
    target.write_text(expected)
    if args.table_only:
        return
    source_snapshot = paper_inputs()
    for executable in ["pandoc", "lualatex"]:
        if not shutil.which(executable):
            parser.exit(1, f"Missing {executable}; see README.md for typesetting dependencies.\n")
    build = ROOT / "build/paper"
    build.mkdir(parents=True, exist_ok=True)
    pieces = [
        section_source(ROOT / "manuscript/main.md"),
        "\\clearpage\n",
        section_source(ROOT / "manuscript/analytic-estimates.md", "A"),
        "\\clearpage\n",
        expected.replace(
            "# Appendix B. Source boxes", "# Appendix B. Source boxes {#appendix-b}", 1
        ),
        "\\clearpage\n",
        section_source(ROOT / "manuscript/computational-estimates.md", "C"),
        (ROOT / "manuscript/references.md").read_text(),
    ]
    combined = build / "paper.md"
    combined.write_text("\n\n".join(pieces))
    tex = build / "dbn-upper-bound.tex"
    command = [
        "pandoc",
        str(combined),
        "--standalone",
        "--from=markdown+tex_math_dollars+raw_tex",
        "--to=latex",
        "--no-highlight",
        "--top-level-division=section",
        "--metadata=title:A computer-assisted upper bound for the de Bruijn–Newman constant",
        "--metadata=author:Stefan Gordon",
        "--metadata=date:September 2026",
        "--variable=fontsize:11pt",
        "--variable=documentclass:article",
        "--variable=papersize:a4",
        "--variable=geometry:margin=26mm",
        "--variable=linestretch:1.04",
        "--variable=mainfont:Latin Modern Roman",
        "--variable=mathfont:Latin Modern Math",
        "--variable=monofont:DejaVu Sans Mono",
        "--variable=colorlinks:true",
        "--variable=linkcolor:blue",
        "--variable=urlcolor:blue",
        "--include-in-header",
        str(ROOT / "manuscript/preamble.tex"),
        "--output",
        str(tex),
    ]
    subprocess.run(command, check=True)
    env = os.environ.copy()
    env["SOURCE_DATE_EPOCH"] = "1789084800"
    env["FORCE_SOURCE_DATE"] = "1"
    for _ in range(2):
        result = subprocess.run(
            ["lualatex", "-interaction=nonstopmode", "-halt-on-error", tex.name],
            cwd=build,
            capture_output=True,
            text=True,
            env=env,
        )
        if result.returncode:
            parser.exit(1, result.stdout[-7000:] + "\n" + result.stderr[-1500:])
    pdf = ROOT / "output/pdf/dbn-upper-bound.pdf"
    if paper_inputs() != source_snapshot:
        parser.exit(1, "Manuscript sources changed during typesetting; build again.\n")
    pdf.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(build / "dbn-upper-bound.pdf", pdf)
    log = (build / "dbn-upper-bound.log").read_text()
    warnings = [
        line for line in log.splitlines() if "Overfull" in line or "Missing character" in line
    ]
    print(f"Built {pdf.relative_to(ROOT)}")
    if warnings:
        print("Layout warnings requiring inspection:\n" + "\n".join(warnings))
    else:
        print("No overfull boxes or missing characters reported by LuaLaTeX.")
    record = dict(
        schema_version=1,
        sources=source_snapshot,
        pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),
        pandoc=subprocess.check_output(["pandoc", "--version"], text=True).splitlines()[0],
        lualatex=subprocess.check_output(["lualatex", "--version"], text=True).splitlines()[0],
        layout_warnings=warnings,
    )
    (pdf.parent / "build.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
