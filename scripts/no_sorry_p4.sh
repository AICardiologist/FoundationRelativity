#!/usr/bin/env bash
set -euo pipefail

ROOT="Papers/P4_SpectralGeometry"
echo "[no_sorry] scanning $ROOT (excluding archive, .lake, lake-packages) ..."
if grep -R --line-number -E "\bsorry\b" \
  --include="*.lean" \
  --exclude-dir=archive \
  --exclude-dir=.lake \
  --exclude-dir=lake-packages \
  "$ROOT"; then
  echo "[no_sorry] found 'sorry' in Paper 4 modules."
  exit 1
else
  echo "[no_sorry] OK: no 'sorry' found in Paper 4 modules."
fi