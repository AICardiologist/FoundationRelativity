#!/usr/bin/env python3
# scripts/audit-doc-anchors.py
# Verifies that markdown links with fragments (file.md#fragment) resolve to headings in file.md
import os, re, sys
from collections import defaultdict

ROOT = os.path.abspath(os.path.dirname(__file__) + "/..")
SEARCH_ROOTS = [os.path.join(ROOT, "Papers", "P5_GeneralRelativity")]
TOP_LEVEL_README = os.path.join(ROOT, "README.md")

MD_EXTS = (".md", ".markdown", ".MD")
HDR_RE = re.compile(r"^(?P<indent>\s{0,3})(?P<h>#{1,6})\s+(?P<title>.+?)\s*$")
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

def collect_md_files():
    files = []
    for base in SEARCH_ROOTS:
        for d, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(MD_EXTS):
                    files.append(os.path.join(d, f))
    if os.path.exists(TOP_LEVEL_README):
        files.append(TOP_LEVEL_README)
    return files

def github_slug(title: str) -> str:
    # Emulate GitHub slug rules (approximate but robust for our use):
    # 1) lowercase; 2) strip leading/trailing spaces; 3) remove punctuation except hyphens/spaces;
    # 4) collapse spaces to hyphens; 5) collapse multiple hyphens.
    import unicodedata, string
    t = unicodedata.normalize("NFKD", title).encode("ascii", "ignore").decode("ascii")
    t = t.lower().strip()
    # keep alnum, spaces, and hyphen
    allowed = set(string.ascii_lowercase + string.digits + " -")
    t = "".join(ch for ch in t if ch in allowed)
    t = re.sub(r"\s+", "-", t)
    t = re.sub(r"-{2,}", "-", t)
    return t

def header_slugs(md_path: str) -> set[str]:
    slugs = set()
    counts = defaultdict(int)
    try:
        with open(md_path, "r", encoding="utf-8") as fh:
            for line in fh:
                m = HDR_RE.match(line)
                if not m:
                    continue
                base = github_slug(m.group("title"))
                if not base:
                    continue
                # GitHub duplicates: first occurrence is 'base', then 'base-1', 'base-2', ...
                cnt = counts[base]
                slug = base if cnt == 0 else f"{base}-{cnt}"
                counts[base] += 1
                slugs.add(slug)
    except Exception:
        pass
    return slugs

def is_external(href: str) -> bool:
    return href.startswith(("http://", "https://", "mailto:"))

def normalize(base_dir: str, href: str):
    # Split fragment
    if "#" in href:
        file_part, frag = href.split("#", 1)
    else:
        file_part, frag = href, ""
    file_part = file_part.strip()
    frag = frag.strip().lower()
    if not file_part:
        # in-page anchor (#foo). Resolve to current file
        path = None
    else:
        # repo-absolute (/...) or relative
        path = os.path.join(ROOT, file_part.lstrip("/")) if file_part.startswith("/") \
            else os.path.normpath(os.path.join(base_dir, file_part))
    return path, frag

def main() -> int:
    md_files = collect_md_files()
    # Preload slugs per file
    slug_map = {p: header_slugs(p) for p in md_files}
    missing = []
    for md in md_files:
        base = os.path.dirname(md)
        try:
            with open(md, "r", encoding="utf-8") as fh:
                for lineno, line in enumerate(fh, start=1):
                    for m in LINK_RE.finditer(line):
                        href = m.group(1).strip()
                        if is_external(href) or "#" not in href:
                            continue
                        target_file, frag = normalize(base, href)
                        if not frag:
                            continue
                        # If target_file is None, in-page anchor
                        target = md if target_file is None else target_file
                        if not os.path.exists(target):
                            # file nonexistence is handled by the other audit; skip here
                            continue
                        slugs = slug_map.get(target)
                        if not slugs:
                            slugs = header_slugs(target)
                            slug_map[target] = slugs
                        # normalize frag like GitHub (already lowered; normalize punctuation)
                        desired = github_slug(frag)
                        # Accept either exact slug or numbered duplicates (desired-<n>)
                        if desired not in slugs and not any(s == desired or s.startswith(desired + "-") for s in slugs):
                            missing.append((md, lineno, href, target))
        except Exception:
            pass
    if missing:
        print("❌ Broken anchor links found (no matching heading):")
        for md, ln, href, tgt in missing:
            print(f"  {md}:{ln}: ({href}) → {tgt}")
        return 1
    print("✅ Docs anchor audit passed (all fragments resolve).")
    return 0

if __name__ == "__main__":
    sys.exit(main())