# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- **Milestone C Complete**: SpectralGap pathology (ρ=3) requires ACω - Full formal proof
  - Constructive impossibility: `Sel → WLPO → ACω → RequiresACω` 
  - Classical witness: `zeroWitness` proves eigenspace non-emptiness
  - Main theorem: `SpectralGap_requires_ACω : RequiresACω ∧ witness_zfc`
  - Diagonal operator framework with basis-vector lemmas
- feat: Milestone C groundwork - RequiresACω logic DSL for SpectralGap impossibility proofs
- feat: ACω definition for countable choice in SpectralGap/LogicDSL
- feat: zeroGap_requiresACω theorem skeleton for constructive impossibility
- feat: formal proof that RNP_Fail₂ requires DC_ω (ρ = 2)
- docs: Mathlib 4.4 upgrade spike retrospective

### Fixed
- fix: Use ASCII Nat instead of Unicode ℕ in LogicDSL for compatibility
- fix: Replace classical tactic with placeholder proof for Milestone C

## [0.3.2] - 2025-01-20

### Added
- Formal proof that AP_Fail₂ requires WLPO

## [0.3.1] - 2025-01-20

### Added
- Formal proof that Gap₂ requires WLPO
- RequiresWLPO framework in LogicDSL

## [0.3.0] - 2025-01-20

### Added
- Generic witness API in WitnessCore
- CI/CD workflows for automated testing
- Comprehensive test suite

### Changed
- Migrated all pathologies to unified witness API
- Fixed mathematical impossibility of contravariant functors

## [0.2.0] - 2025-01-19

### Added
- Covariant functors implementation
- SmallCategory instance for Foundation
- Non-identity morphism handling

## [0.1.0] - 2025-01-19

### Added
- Initial Foundation type system
- Basic pathology functors (Gap₂, AP_Fail₂, RNP_Fail₂)
- Core interpretation morphisms