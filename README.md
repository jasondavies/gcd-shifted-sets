# GCD of Shifted Sets

A Lean 4 / Mathlib formalisation of

> R. Heyman, I. E. Shparlinski, *On the greatest common divisor of shifted sets*,
> J. Number Theory 154 (2015), 63–73, [doi:10.1016/j.jnt.2015.02.012](https://doi.org/10.1016/j.jnt.2015.02.012).

The same material appears as Section 3.1 of Heyman's PhD thesis. Its Section 3.2 adds a
result on uniform shifts, which is also formalised here:

> R. Heyman, *Topics in divisibility: pairwise coprimality, the GCD of shifted sets and
> polynomial irreducibility*, PhD thesis, UNSW Sydney, 2015,
> [doi:10.26190/unsworks/18489](https://doi.org/10.26190/unsworks/18489).

Build with `lake exe cache get && lake build`. There are no `sorry`s, and every main theorem
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| Paper | Lean | Status |
|---|---|---|
| Definitions (`𝔥`, `gcd`, `L`, `ℓ`, `R`, `κ`, `ϑ`) | `ShiftedGcd/Defs.lean` (`t(a)` is `tShift` in `UniformShift.lean`) | |
| Claims about `κ(n,ε)` (existence, uniqueness, `ϑ > 0`) | `kappa_existsUnique`, `theta_pos` | proved |
| Theorem 1 | `theorem1`, `theorem1_gcd` | proved, assuming Lemma 5 (Baker–Harman) as hypothesis `BakerHarman` |
| Lemma 6 (Iwaniec) | `iwaniecBound` | proved from the vendored quadratic Jacobsthal bound |
| Theorem 2 | `theorem2`, `theorem2_L` | proved unconditionally |
| Theorem 3 | `theorem3`, `theorem3_ell` | proved unconditionally |
| Theorem 4 | `theorem4` | proved unconditionally (with the divisor bound in `DivisorBound.lean`) |
| Thesis Theorem 3.2.1: `t(a) ≪ log² 𝔥(a)` (uniform shift) | `uniformShift_exists`, `tShift_le` | proved unconditionally |
| Abstract: gcd "much larger than `H`" | `abstract_claim_false`, `not_gcd_much_larger` | **disproved** (`AbstractClaim.lean`) |

Lemma 5 (`BakerHarman`) remains an explicit hypothesis of Theorem 1, rather than an axiom.
It is stated in `Defs.lean` in a slightly weaker form: the vector must have positive
entries, the constants are existentially quantified, and "sufficiently large `R`" becomes
`R ≥ R₀`. Each change only weakens what is assumed relative to the shifted-sets paper's
Lemma 5.

There is an exponent discrepancy between that lemma and its cited theorem.
[Baker–Harman, *Small remainder of a vector to suitable modulus*, Math. Z. 221 (1996), 59–71](https://doi.org/10.1007/BF02622099),
p. 62, equation (2.1), gives `c(K) = 1 / (2^(k + 1) - 4)` with
`k = ⌈1 + max{K,1}⌉`, and explicitly uses this constant in its Theorem 1.
The shifted-sets paper's Lemma 5 (p. 67), and our `gammaBH`, instead use
`γ(K) = 1 / (2^(2 + max{1,K}) - 4)`. For noninteger `K > 1`, this allows a larger
range `Q ≤ R^γ(K)` than the original theorem supplies: at `K = 3/2`,
`c(K) = 1/12 ≈ 0.0833`, whereas `γ(K) ≈ 0.1367`.
Thus formalising the original theorem as stated would not discharge the current hypothesis.

The original **proof**, however, has enough numerical slack to accommodate `γ(K)`.
Before weakening its estimate to `R^(1-2c(K))`, the exponent pair in Lemma 1 gives
saving `s(K) = (k - max{1,K}) / (2^k - 2)`.
[`BakerHarmanExponent.lean`](ShiftedGcd/BakerHarmanExponent.lean) proves
`s(K) ≥ 4γ(K)/3`. Choosing the small-sum cutoff `R Q^(-5/4)` in Proposition 3
leaves a positive margin `s(K) - 5γ(K)/4 ≥ γ(K)/12`; the module also proves that
any fixed multiple of `R^(1-s(K))` is eventually at most half this cutoff,
uniformly for `0 < Q ≤ R^γ(K)`. This supplies the exponent bookkeeping needed to
adapt the original proof without changing `γ`, `κ` or `ϑ`.
The lattice induction and final approximation argument remain to be formalised.
**Theorem 1 is still conditional** on `BakerHarman`.

The analytic proof starts in
[`BakerHarman/ReciprocalSum.lean`](ShiftedGcd/BakerHarman/ReciprocalSum.lean).
It proves the base-order estimate `|Σ e(z/r)| ≤ 252(√R + R²/|z|)` for
`0 < |z| ≤ R²` on natural subintervals of `[R,2R)`, including real `R ≥ 1`.
[`BakerHarman/HigherDerivative.lean`](ShiftedGcd/BakerHarman/HigherDerivative.lean)
also proves explicit bounds at every higher derivative order, using an optimized
van der Corput induction. [`BakerHarman/PowerBands.lean`](ShiftedGcd/BakerHarman/PowerBands.lean)
converts them to power savings on explicit numerator bands and combines finite chains
of overlapping bands. [`BakerHarman/BandSelection.lean`](ShiftedGcd/BakerHarman/BandSelection.lean)
selects bands covering the full range, and
[`BakerHarman/ExponentialSum.lean`](ShiftedGcd/BakerHarman/ExponentialSum.lean)
proves `|Σ e(z/r)| ≤ C(R^(1-6γ(K)/5) + R²/|z|)` for
`0 < |z| ≤ R^(K+1)`, `K ≥ 1`, on closed integer subintervals of `[R,2R]`.
Allowing any fixed factor in the numerator range retains saving `23γ(K)/20`
for sufficiently large `R`. [`BakerHarman/LargeSums.lean`](ShiftedGcd/BakerHarman/LargeSums.lean)
then proves that a sum of size at least `T ≥ R Q^(-11/10)` has
`|z| ≤ C R²/T`, uniformly for `0 < Q ≤ R^γ(K)`. This completes the analytic
input to the lattice argument, using a different saving and cutoff from the
original exponent-pair bookkeeping above.
[`BakerHarman/DyadicSelection.lean`](ShiftedGcd/BakerHarman/DyadicSelection.lean)
proves the finite counting steps: discarding small sums, selecting a dyadic class,
bounding the number of classes logarithmically, and finding a small scalar product
or a small difference by the box argument, including singleton classes.
The derivative, differencing and basic lattice definitions use sixteen Apache-2.0 sources from the
same pinned `openai/math` revision, in `vendor/baker-harman-analytics`.
Only their import paths are relocated to avoid overlapping Lake module roots;
`python3 scripts/check_baker_harman_sources.py` verifies local and upstream hashes,
the import-only relocation, and the exact dependency closure. The axiom audit below
also checks every imported declaration in their `OAI.Problem337` and `OAI.Erdos3` namespaces.

[`BakerHarman/Lattice/DetectionBudget.lean`](ShiftedGcd/BakerHarman/Lattice/DetectionBudget.lean)
proves a Gaussian alternative to the original Fourier detection lemma. For any
dimension `d`, its threshold is uniform over ambient inner product spaces and
lattices with minimum nonzero length at least one and covolume at most `Q`.
A finite sequence avoiding the unit neighborhoods has Fourier-sum mass at least
one quarter of its length among nonzero dual vectors of length `O_d(log Q + 1)`;
there are at most `O_d(Q(log Q + 1)^d)` such vectors.
The local `Lattice` modules extract and adapt the required Poisson and integration
proofs from the same pinned `openai/math` revision, with source attribution and
the upstream Apache-2.0 license retained. They avoid its unrelated import branches.
[`BakerHarman/LogFactors.lean`](ShiftedGcd/BakerHarman/LogFactors.lean) absorbs fixed
logarithmic powers in the numerator range, retaining saving `23γ(K)/20`.
The small-sum removal lemma also accommodates logarithmic factors in the frequency
count. [`BakerHarman/SmallDualVector.lean`](ShiftedGcd/BakerHarman/SmallDualVector.lean)
combines these estimates: failure of reciprocal approximation produces a nonzero
dual vector of length `O(log Q + 1)` with scalar product `O(R(log Q + 1))`.
The constants are uniform over ambient spaces and lattices of a fixed dimension.
[`BakerHarman/DimensionOne.lean`](ShiftedGcd/BakerHarman/DimensionOne.lean)
proves the one-dimensional large-vector approximation case. The lattice modules
also prove primitive-normal reduction, the exact hyperplane covolume formula,
dual norm and covolume lower bounds, scaling, and lifting approximations from a
scaled hyperplane lattice.
[`BakerHarman/DimensionInduction.lean`](ShiftedGcd/BakerHarman/DimensionInduction.lean)
proves the large-vector approximation in every positive dimension, with constants
and a logarithmic degree depending only on the dimension and `K`. The induction
preserves `Q ≤ R^γ(K)` exactly; its output interval is bounded by
`B R Q (log Q + 1)^m / ρ`, where `ρ ≥ 1` is a lower bound for nonzero lattice lengths.
The final simultaneous approximation argument, including its small-vector case,
remains unfinished; Theorem 1 is still conditional and its exponents have not changed.

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
