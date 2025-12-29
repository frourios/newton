# Newton: Physics Library for Lean

Website: https://newton.frourio.com/

![GitHub CI](https://github.com/frourios/newton/actions/workflows/lean_action_ci.yml/badge.svg?branch=main)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/frourios/newton)

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/frourios/newton)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/frourios/newton)

## Vision

Newton aims to create a world where anyone who discovers new theories in physics and mathematics can prove their consistency without peer review. We are building a foundation for:

- **Democratizing Scientific Discovery**: Enable researchers to verify theoretical consistency independently through formal proof
- **Preparing for Groundbreaking Proofs**: Build infrastructure ready for when unified field theories or Millennium Prize Problems are proven in Lean
- **Absolute Mathematical Rigor**: Only fully proven theorems without `axiom`, `sorry`, `admit`, or `trivial` are published on the main branch

## What is Newton?

Newton is a formalized physics library built on the Lean theorem prover. By leveraging Lean's powerful type system and proof verification capabilities, Newton provides:

- Mathematically rigorous foundations for physical theories
- Machine-verified proofs that eliminate human error
- A collaborative platform for advancing formal physics
- Integration with Mathlib for comprehensive mathematical support

## Current Focus

The library currently focuses on:

- **Analysis & Distribution Theory**: Schwartz space, distributions, and functional analysis
- **Convolution Theory**: Approximate identities, mollifiers, and convergence theorems
- **Lp Spaces**: Function space theory with rigorous density results
- **Mathematical Physics Foundations**: Building blocks for quantum mechanics and field theory

## Core Principles

### 1. No Axioms or Shortcuts

Every theorem in the main branch is **completely proven** without:
- `axiom` - No unproven assumptions
- `sorry` - No incomplete proofs
- `admit` - No bypassed proof obligations
- `trivial` - No unjustified claims

### 2. Peer Review Through Proof

Traditional peer review is replaced by **machine verification**. If it compiles in Lean, the mathematics is correct. This approach:
- Eliminates bias in the review process
- Provides instant verification of correctness
- Enables rapid iteration and collaboration
- Creates a permanent, verifiable record

### 3. Building for the Future

Newton is designed with ambitious goals in mind:
- Supporting the formalization of unified field theories
- Providing infrastructure for Millennium Prize Problem proofs
- Enabling new physics discoveries through formal methods
- Creating a foundation that will serve the scientific community for decades

## Getting Started

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (installed automatically via `elan`)
- [Git](https://git-scm.com/)

### Installation

`lakefile.toml`

```toml
[[require]]
name = "Newton"
git  = "https://github.com/frourios/newton.git"
rev  = "main"
```

### Quick Development

Use GitHub Codespaces or Gitpod for instant development environments:

- **Codespaces**: Click the badge above or press `.` on GitHub
- **Gitpod**: Click the "Open in Gitpod" badge above

### Exploring the Library

Browse the [API Documentation](https://newton.frourio.com/docs) to explore available theorems and proofs.

## Contributing

We welcome contributions from mathematicians, physicists, and formal methods enthusiasts!

### Contribution Guidelines

1. **All proofs must be complete** - No `sorry`, `axiom`, `admit`, or `trivial`
2. **Follow existing style** - Maintain consistency with the codebase
3. **Document your work** - Include clear docstrings and comments
4. **Build and test** - Ensure `lake build` succeeds before submitting
5. **CI must pass** - All GitHub Actions checks must pass

## Philosophy

### Why Formal Verification?

Formal verification in Lean provides:

- **Absolute Certainty**: Machine-checked proofs eliminate errors
- **Transparent Review**: Anyone can verify the proof themselves
- **Collaborative Science**: Build on verified foundations without doubt
- **Future-Proof Knowledge**: Proofs remain valid as the field evolves

### The Role of Intuition

While formal proofs are rigorous, they don't replace mathematical intuition. Newton bridges:

- **Intuitive Understanding**: Clear documentation and proof structure
- **Formal Rigor**: Complete machine verification
- **Educational Value**: Learn by exploring verified proofs

## License

CC0-1.0
