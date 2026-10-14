# Shifted GCD

A Lean 4 / Mathlib formalisation of

> R. Heyman, I. E. Shparlinski, *On the greatest common divisor of shifted sets*,
> [arXiv:1402.1208](https://arxiv.org/abs/1402.1208), J. Number Theory 154 (2015), 63–73.

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

The two deep external results (Lemmas 5 and 6) are stated in `Defs.lean` as `Prop`s, exactly
as the paper quotes them, and are passed as explicit hypotheses rather than axioms.

## Deviations from the paper

- **Theorem 1.** As printed (`gcd(a+h) ≫ 𝔥(h) H^ϑ` for some `𝔥(h) ≤ H`), the statement is
  trivially true with `h = 0`. `theorem1` formalises what the proof actually gives: a common
  divisor `r` of all `aᵢ + hᵢ` with `r ≫ 𝔥(h) H^ϑ` and also `r ≫ H^{1/(εκ)}`. `theorem1_gcd`
  is the gcd form for `𝔥(a)^ε ≤ H < 𝔥(a)`, where `a + h ≠ 0` is automatic. The paper's
  "`εκ < 1`" should read `εκ > 1`.
- **Theorem 2.** The bound needs `𝔥(a) ≥ 2`. The greedy construction must keep the shifted
  entries nonzero.
- **Theorem 3.** The congruences should read `a_k ≡ −i_k`. The primes need not exceed `H`.
- **Theorem 4.** `(h𝔥(a))^{o(1)}` is read as "for every `δ > 0`, `≪_{n,δ} (h𝔥(a))^δ`". The
  Möbius identity `R = Σ μ(d) U_d²` fails when `a·x = 0` has positive solutions (possible when
  `a` has entries of both signs). Those pairs are removed first. In (14), `D^{2n-1}` should be
  `D^{n-1}`, and the tail of `Σ μ(d)/d²` is `O(n/h)`, not `O(1/D)`.
