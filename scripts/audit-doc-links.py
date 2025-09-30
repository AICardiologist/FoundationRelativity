#!/usr/bin/env python3
# scripts/audit-doc-links.py
import os, re, sys

ROOT = os.path.abspath(os.path.dirname(__file__) + "/..")
# Audit these areas plus the repo root README.md
SEARCH_ROOTS = [
    os.path.join(ROOT, "Papers", "P5_GeneralRelativity"),
]
TOP_LEVEL_README = os.path.join(ROOT, "README.md")

LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

def is_external(href: str) -> bool:
    href = href.strip()
    return (
        href.startswith("http://")
        or href.startswith("https://")
        or href.startswith("mailto:")
        or href.startswith("#")
    )

def normalize(target: str, base_dir: str) -> str:
    # strip anchor
    target = target.split("#", 1)[0].strip()
    if not target:
        return ""
    if target.startswith("/"):  # treat as repo-absolute
        return os.path.normpath(os.path.join(ROOT, target.lstrip("/")))
    # relative to the Markdown file
    return os.path.normpath(os.path.join(base_dir, target))

def collect_md_files() -> list[str]:
    out = []
    for root in SEARCH_ROOTS:
        for dirpath, _, files in os.walk(root):
            for f in files:
                if f.lower().endswith(".md"):
                    out.append(os.path.join(dirpath, f))
    if os.path.exists(TOP_LEVEL_README):
        out.append(TOP_LEVEL_README)
    return out

def main() -> int:
    missing: list[tuple[str, int, str, str]] = []
    for md in collect_md_files():
        base = os.path.dirname(md)
        try:
            with open(md, "r", encoding="utf-8") as fh:
                for lineno, line in enumerate(fh, start=1):
                    for m in LINK_RE.finditer(line):
                        href = m.group(1).strip()
                        if is_external(href):
                            continue
                        target = normalize(href, base)
                        if not target:
                            continue
                        if not os.path.exists(target):
                            missing.append((md, lineno, href, target))
        except Exception as e:
            print(f"⚠️  Skipping {md}: {e}", file=sys.stderr)
    if missing:
        print("❌ Broken relative Markdown links found:")
        for md, lineno, href, resolved in missing:
            print(f"  {md}:{lineno}: [{href}]  →  not found ({resolved})")
        return 1
    print("✅ Docs link audit passed (all relative links resolve).")
    return 0

if __name__ == "__main__":
    sys.exit(main())