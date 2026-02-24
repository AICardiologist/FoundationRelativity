#!/usr/bin/env bash
set -euo pipefail

# Check for axioms in GR subdirectory only (excluding framework axioms)
# Allowed: GR/Portals.lean (portal axioms)
# Also allowed: AxCalCore/* (framework axioms), EPSCore.lean (EPS axioms)
violations="$(grep -Rns --include='*.lean' -E '^\s*axiom\b' Papers/P5_GeneralRelativity/GR \
  | grep -v 'Papers/P5_GeneralRelativity/GR/Portals\.lean' \
  | grep -v 'Papers/P5_GeneralRelativity/GR/EPSCore\.lean' \
  | grep -v '_backup_' \
  | grep -v '_zenodo_pkg_' \
  | grep -v 'Zenodo_Deliverables' || true)"

if [[ -n "${violations}" ]]; then
  echo "❌ AxiomDeclAudit: found unexpected 'axiom' declarations in GR modules:"
  echo "${violations}"
  exit 1
fi

echo "✅ AxiomDeclAudit: no unexpected axiom declarations in GR modules (Portals.lean and EPSCore.lean exempted)"