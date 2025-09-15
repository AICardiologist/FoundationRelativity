# Zenodo Update Instructions for Paper 2 v0.3

## Important: This is an UPDATE to existing Zenodo record
Do NOT create a new DOI. Update the existing Paper 2 record.

## Files to Upload
1. `p2-crm-v0.3.tar.gz` (444KB) - Complete Lean 4 formalization
2. `p2-crm-v0.3.zip` (616KB) - Same content in ZIP format
3. `paper-v5.pdf` (if compiled) - LaTeX documentation with CRM methodology

## Metadata Updates

### Version
Update from v0.2 to v0.3

### Description (append to existing)
```
--- VERSION 0.3 UPDATE (2025-01-13) ---

Major improvements and bug fixes:
- Fixed critical field_simp tactic fragility in DirectDual.lean
- Aligned all terminology with standard Constructive Reverse Mathematics (CRM)
- Added comprehensive code-theorem correspondence documentation
- Three new appendices documenting the formalization
- Clear axiom hygiene separation between meta-classical and constructive parts

The LaTeX documentation (paper-v5.tex) now includes:
- Complete mathematical exposition with CRM methodology
- Detailed Lean-to-math crosswalk tables
- Explanation of witness extraction and constructive consumption pattern
```

### Keywords (add if not present)
- Constructive Reverse Mathematics
- CRM
- Witness extraction
- Ishihara kernel
- Axiom hygiene
- Lean 4 formalization

### Related Identifiers
Keep all existing identifiers and add:
- GitHub repository: https://github.com/AICardiologist/FoundationRelativity
- Related PR #184: DirectDual fixes
- Related PR #185: CRM documentation

### Notes for Upload
1. The tar.gz and zip files contain identical content
2. The LaTeX source is included in documentation/paper-v5.tex
3. All Lean files compile with lake build Papers.P2_BidualGap.P2_Full
4. The release preserves backward compatibility with v0.2

## File Locations
- Archives: `/Users/quantmann/FoundationRelativity/archival_folder/release_archives/paper2/`
- Source: `/Users/quantmann/FoundationRelativity/Papers/P2_BidualGap/`