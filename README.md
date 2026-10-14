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
| Definitions (`𝔥`, `gcd`, `L`, `ℓ`, `R`, `κ`, `ϑ`) | `ShiftedGcd/Defs.lean` | |
| Claims about `κ(n,ε)` (existence, uniqueness, `ϑ > 0`) | `kappa_existsUnique`, `theta_pos` | proved |
| Theorem 1 | `theorem1`, `theorem1_gcd` | proved, assuming Lemma 5 (Baker–Harman) as hypothesis `BakerHarman` |
| Theorem 2 | `theorem2`, `theorem2_L` | proved, assuming Lemma 6 (Iwaniec) as hypothesis `IwaniecBound` |
| Theorem 3 | `theorem3`, `theorem3_ell` | proved unconditionally |
| Theorem 4 | `theorem4` | proved unconditionally (with the divisor bound in `DivisorBound.lean`) |
| Thesis Theorem 3.2.1: `t(a) ≪ log² 𝔥(a)` (uniform shift) | `uniformShift_exists`, `tShift_le` | proved, assuming Lemma 6 (Iwaniec) as hypothesis `IwaniecBound` |
| Abstract: gcd "much larger than `H`" | `abstract_claim_false`, `not_gcd_much_larger` | **disproved** (`AbstractClaim.lean`) |

The two deep external results (Lemmas 5 and 6) are stated in `Defs.lean` as `Prop`s, exactly
as the paper quotes them, and are passed as explicit hypotheses rather than axioms.

## Deviations from the paper

- **Theorem 1.** As printed (`gcd(a+h) ≫ 𝔥(h) H^ϑ` for some `𝔥(h) ≤ H`), the statement is
  trivially true with `h = 0`. `theorem1` formalises what the proof actually gives: a common
  divisor `r` of all `aᵢ + hᵢ` with `r ≫ 𝔥(h) H^ϑ` and also `r ≫ H^{1/(εκ)}`. `theorem1_gcd`
  is the gcd form for `𝔥(a)^ε ≤ H < 𝔥(a)`, where `a + h ≠ 0` is automatic. The second
  bound, `r ≫ H^{1/(εκ)}`, is weaker than the trivial `gcd ≥ 2H + 1`. Its only role is to
  stop `h = 0` from proving the statement for every `a`. It does not force a nonzero shift:
  when `gcd(a)` is already large, `h = 0` remains a valid witness, for example `a = (A, …, A)`
  with `h = 0` and `r = A`.
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
- **Theorem 2.** The bound needs `𝔥(a) ≥ 2`. The greedy construction must keep the shifted
  entries nonzero. The paper's remark that `𝔥(a)` can be replaced by the second-largest `|aᵢ|`
  is not formalised.
- **Theorem 3.** The primes need not exceed `H`.
- **Theorem 4.** `(h𝔥(a))^{o(1)}` is read as "for every `δ > 0`, `≪_{n,δ} (h𝔥(a))^δ`". The
  Möbius identity `R = Σ μ(d) U_d²` fails when `a·x = 0` has positive solutions (possible when
  `a` has entries of both signs). Those pairs are removed first.
