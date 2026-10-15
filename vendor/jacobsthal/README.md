# Jacobsthal dependency subset

This local Lake package contains the transitive Lean source imports of
`OAI.NumberTheory.Jacobsthal.Conclusions.QuadraticBound` from
[`openai/math` at `1581d4cbdd69a0faf34b2089614fe2a814316a6a`](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a).
It contains 844 Lean files; unrelated results and the stronger iterated-logarithm
conclusion are omitted. Mathlib remains a shared dependency of the main project.

The theorem `OAI.Erdos970.Erdos970Final.erdos_970_quadratic` states that some absolute
`C > 0` bounds the Jacobsthal window length by `C * k²` for every `k > 0`.
The window works for every positive modulus with at most `k` distinct prime factors
and every signed integer starting point. `ShiftedGcd/Iwaniec.lean` converts this to
the interval-covering bound used by the shifted-set results.

All vendored Lean source files are unchanged. Upstream uses Lean 4.34.1; this package
uses the main project's Lean/Mathlib 4.34.0. Only the package configuration is local.
`UPSTREAM.json` records the pinned source repositories, upstream compatibility
patches, and SHA-256 of every Lean file. The named patches come from the pinned
`openai/math` revision and were applied before extracting the dependency subset.

Sources and attribution:

- `OAI/`: `openai/math`, under the accompanying Apache 2.0 `LICENSE`.
- `PrimeNumberTheoremAnd/`: Alex Kontorovich and contributors' project, with the
  `openai/math` compatibility patch; see `licenses/PrimeNumberTheoremAnd/LICENSE`.
- `StrongPNT/`: Math Inc.'s strong prime number theorem formalization, through the
  namespaced files supplied by `openai/math`'s `StrongPNT-lean4341.patch`.
- `AbsorptionCutoff/`: Benny Avelin's project, with the `openai/math` compatibility
  patch; see `licenses/AbsorptionCutoff/LICENSE`. Source copyright notices are retained.

Build from the main repository with `lake build`. To build only the external theorem,
use `lake build OAI.NumberTheory.Jacobsthal.Conclusions.QuadraticBound`.
Run `python3 scripts/check_jacobsthal_sources.py` to check the source hashes and exact
dependency closure. Run `lake env lean scripts/CheckAxioms.lean` after building to check
the external theorem and the main results against the standard-axiom allowlist.
