# Foundation-Relativity

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Nightly](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml)

A Lean 4 formalization of foundation-relativity in constructive mathematics.

## Overview

This project formalizes the concept of foundation-relativity, showing how mathematical pathologies 
(like Gap₂, AP, and RNP) behave differently under different foundational assumptions (BISH vs ZFC).

## Key Components

- **Found**: Core definitions for foundations and interpretations
- **Gap2**: The Gap₂ pathology functor
- **APFunctor**: The AP (Approximate Pathology) functor  
- **RNPFunctor**: The RNP (Real Number Pathology) functor

## Building

```bash
lake build
```

## Testing

Run all tests:
```bash
lake exe testFunctors
lake exe testNonIdMorphisms
```

## Development

See [docs/DEV_GUIDE.md](docs/DEV_GUIDE.md) for development guidelines.

## CI/CD

- **CI**: Runs on all PRs and pushes to main
- **Nightly**: Tests against Lean nightly builds and updates dependencies

## License

[Add license information]