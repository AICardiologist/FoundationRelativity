# Developer convenience targets for Riemann.lean quality gates

.PHONY: check baseline activation audit riemann-check

# Main check - runs both baseline and activation checks
check: riemann-check

riemann-check:
	@echo "▶ Running Riemann quality gates..."
	@./scripts/check.sh baseline

# Individual checks
baseline:
	@./scripts/check-baseline.sh

activation:
	@./scripts/check-activation.sh baseline

audit:
	@./scripts/audit-riemann.sh
	@./scripts/audit-doc-links.sh
	@./scripts/audit-doc-anchors.sh
	@./scripts/audit-riemann-signatures.sh

# Help
help:
	@echo "Available targets:"
	@echo "  make check      - Run all Riemann quality gates"
	@echo "  make baseline   - Check 51-error baseline only"
	@echo "  make activation - Check activation status only"
	@echo "  make audit      - Run full audit suite (Lean, docs, anchors, signatures)"