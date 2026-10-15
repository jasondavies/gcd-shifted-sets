# GCD of Shifted Sets

A Lean 4 / Mathlib formalisation of

> R. Heyman, I. E. Shparlinski, *On the greatest common divisor of shifted sets*,
> J. Number Theory 154 (2015), 63–73, [doi:10.1016/j.jnt.2015.02.012](https://doi.org/10.1016/j.jnt.2015.02.012).

The same material appears as Section 3.1 of Heyman's PhD thesis. Its Section 3.2 adds a
result on uniform shifts, which is also formalised here:

> R. Heyman, *Topics in divisibility: pairwise coprimality, the GCD of shifted sets and
> polynomial irreducibility*, PhD thesis, UNSW Sydney, 2015,
> [doi:10.26190/unsworks/18489](https://doi.org/10.26190/unsworks/18489).

Keep the standalone `baker-harman-small-remainders` checkout beside this repository
at `../baker-harman-small-remainders` (a local Lake dependency until publication).
Build with `lake exe cache get && lake build`. There are no `sorry`s, and every main theorem
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| Paper | Lean | Status |
|---|---|---|
| Definitions (`𝔥`, `gcd`, `L`, `ℓ`, `R`, `κ`, `ϑ`) | `ShiftedGcd/Defs.lean` (`t(a)` is `tShift` in `UniformShift.lean`) | |
| Claims about `κ(n,ε)` (existence, uniqueness, `ϑ > 0`) | `kappa_existsUnique`, `theta_pos` | proved |
| Theorem 1 | `theorem1`, `theorem1_gcd` | proved unconditionally, with the original exponents |
| Lemma 6 (Iwaniec) | `iwaniecBound` | proved from the vendored quadratic Jacobsthal bound |
| Theorem 2 | `theorem2`, `theorem2_L` | proved unconditionally |
| Theorem 3 | `theorem3`, `theorem3_ell` | proved unconditionally |
| Theorem 4 | `theorem4` | proved unconditionally (with the divisor bound in `DivisorBound.lean`) |
| Thesis Theorem 3.2.1: `t(a) ≪ log² 𝔥(a)` (uniform shift) | `uniformShift_exists`, `tShift_le` | proved unconditionally |
| Abstract: gcd "much larger than `H`" | `abstract_claim_false`, `not_gcd_much_larger` | **disproved** (`AbstractClaim.lean`) |

Theorem 1 uses `BakerHarman.bakerHarman_equal_weights` from the standalone
[Baker–Harman small-remainders library](../baker-harman-small-remainders/README.md).
For `n ≥ 2`, `K ≥ 1`, sufficiently large `Q,R`, `Q ≤ R^γ(K)`, and a nonnegative
vector of Euclidean norm at most `R^K`, it supplies an integer modulus
`R ≤ r ≤ 2QR` with every coordinate's nearest-integer error at most `Q^(-1/n)`.
The conclusions and exponents `γ`, `κ`, and `ϑ` of Theorem 1 are unchanged.
The more general unequal-weight predicate `BakerHarman` is retained in `Defs.lean`
as a reference statement; it is neither proved nor assumed by any theorem here.

The standalone library adapts Baker–Harman's proof to retain the stronger exponent
quoted in the shifted-sets paper. Its README explains the discrepancy with the
original rounded exponent, the analytic estimates, and the lattice argument.
It owns the proofs, the sixteen vendored analytic sources, their provenance, and
`scripts/check_baker_harman_sources.py`. Run that source check from the library's
directory. This project's axiom audit also checks all imported `BakerHarman`,
`OAI.Problem337`, and `OAI.Erdos3` declarations.

The local dependency is configured in `lakefile.toml`; once the library is published,
replace its `path` with the Git URL and a pinned commit in `rev`, then run
`lake update baker_harman_small_remainders`.

Lemma 6 (`IwaniecBound`) is stated as the paper quotes it and proved in `Iwaniec.lean`.
The proof uses the stronger quadratic Jacobsthal bound from
[`openai/math`](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a),
whose 844-file dependency subset is included in [vendor/jacobsthal](vendor/jacobsthal/README.md).
The vendored sources are unchanged and share this project's Lean/Mathlib 4.34.0;
the first build compiles this substantial additional dependency.
Run `python3 scripts/check_jacobsthal_sources.py` to verify source hashes and dependency
closure, and `lake env lean scripts/CheckAxioms.lean` after building to audit the external
theorem and all `ShiftedGcd` declarations against the standard-axiom allowlist.

## Deviations from the paper

- **Theorem 1.** As printed (`gcd(a+h) ≫ 𝔥(h) H^ϑ` for some `𝔥(h) ≤ H`), the statement is
  trivially true with `h = 0`. `theorem1` formalises what the proof actually gives: a common
  divisor `r` of all `aᵢ + hᵢ` with `r ≫ 𝔥(h) H^ϑ` and also `r ≫ H^{1/(εκ)}`. `theorem1_gcd`
  is the gcd form for `𝔥(a)^ε ≤ H < 𝔥(a)`, where `a + h ≠ 0` is automatic. The second
  bound, `r ≫ H^{1/(εκ)}`, is weaker than the trivial `gcd ≥ 2H + 1`. Its only role is to
  stop `h = 0` from proving the statement for every `a`. It does not force a nonzero shift:
  when `gcd(a)` is already large, `h = 0` remains a valid witness, for example `a = (A, …, A)`
  with `h = 0` and `r = A`.
- **Theorem 2.** The bound needs `𝔥(a) ≥ 2`. The greedy construction must keep the shifted
  entries nonzero. The paper's remark that `𝔥(a)` can be replaced by the second-largest `|aᵢ|`
  is not formalised.
- **Theorem 3.** The primes need not exceed `H`.
- **Theorem 4.** `(h𝔥(a))^{o(1)}` is read as "for every `δ > 0`, `≪_{n,δ} (h𝔥(a))^δ`". The
  Möbius identity `R = Σ μ(d) U_d²` fails when `a·x = 0` has positive solutions (possible when
  `a` has entries of both signs). Those pairs are removed first.
- **Abstract.** The claim that some shift makes the gcd "much larger than `H`" is false. For
  `a = (A, A + 2H + 1, A, …, A)`, every shift has `gcd(a + h) ≤ 4H + 1`, because the gcd
  divides `2H + 1 + h₂ − h₁`. Choosing `A ≈ H^{1/ε}` puts this inside the hypotheses of
  Theorem 1, with all entries positive. On the other hand, `gcd ≥ 2H + 1` is always attainable
  when `H < 𝔥(a)` (`exists_shift_vgcd_ge`). So in the worst case the largest attainable gcd is
  `Θ(H)`. The sentence is probably a misstatement of Theorem 1, which says the gcd is much
  larger than `𝔥(h)`; the paper writes the height as a script `ℋ`. The sentence is not in
  the arXiv abstract. It is repeated word for word in the thesis's chapter overview, so it is
  unlikely to be a one-off slip.
- **Thesis Theorem 3.2.1.** The thesis bounds `ω(aᵣ − aₛ) log ω(aᵣ − aₛ)` by
  `ω(𝔥(a)) log ω(𝔥(a))`, which does not follow because `ω` is not monotone. We use
  `ω(m) log ω(m) ≪ log m` with `m = |aᵣ − aₛ| ≤ 2𝔥(a)` instead.
