# Audit: `PROOF.md` against the Lean code

Lean checks the code, not the prose. This file records, claim by claim, how each mathematical
statement in `PROOF.md` corresponds to a Lean declaration in `WolstenholmeHarmonic.lean`: the
same content, the same hypotheses and the same modulus.

**Context.** In the sections `Bridge`, `Math` and `BernoulliPart`, every lemma about `p` has the
section hypothesis `[Fact p.Prime]`. The lemmas that hold for any `p` are marked
`omit [Fact p.Prime]` (for example `binomial_product_expansion`, `inv_sq_double`, `pow_double`). The generic
layers use no hypothesis on `p` at all.

Legend: **=** means the Lean statement says exactly this. After the last revision every claim
in `PROOF.md` is **=**: there are no informal claims, and where Lean proves a more general
statement, `PROOF.md` now states that general form.

## Notation

| `PROOF.md` | Lean | Match |
|---|---|---|
| `k` is a unit mod `pⁿ` for `1 ≤ k ≤ p−1` | `coprime_succ_pow` | = |
| reduction `q mod pⁿ` is additive and multiplicative | `ratToZMod_add'`, `ratToZMod_mul` (denominators prime to the modulus) | = |
| reduction commutes with `ℤ/pⁿ → ℤ/pᵐ` | `castHom_ratToZMod` | = |
| `q ≡ 0 (mod pⁿ)` ⇔ `pⁿ ∣ num q` (when `p ∤ den q`) | `ratToZMod_eq_zero_iff` | = |
| `den H_n ∣ n!` | `harmonic_den_dvd_factorial` | = |
| `H_{p−1} mod pⁿ = S₁` | `ratToZMod_harmonic` | = |
| `den H_{n,2} ∣ (n!)²`, `H_{p−1,2} mod pⁿ = S₂` | `harmonic2`, `harmonic2_den_dvd`, `ratToZMod_harmonic2` | = |

## Part I

| `PROOF.md` | Lean | Match |
|---|---|---|
| Lemma 1: `S_j ≡ 0 (mod p)` if `p − 1 ∤ j` | `harmonic_sum_pow_mod` (in `ZMod p`) | =¹ |
| Lemma 2: `C = ∏ (1 + p·x_k)` in `ℤ/pⁿ` | `choose_cast_eq_prod` (any `n`) | = |
| Lemma 3: `C = 1 + pS₁ + p²e₂ + p³e₃` in `ℤ/p⁴` | `binomial_product_expansion`, from the generic `prod_one_add_mul_of_pow_four_eq_zero` | = |
| Lemma 4: `2e₂ = S₁² − S₂`, `6e₃ = S₁³ − 3S₁S₂ + 2S₃` | `two_mul_E_two`, `six_mul_E_three` (any modulus), from the generic `sum_sq_eq_sum_sq_add_two_mul_E2`, `sum_cube_add_two_sum_cube_eq` | = |
| `p²S₁² = 0`, `p³e₃ = 0` in `ℤ/p⁴` (`p ≥ 5`) | `p_sq_mul_S_one_sq`, `p_cube_mul_E_three` | = |
| Lemma 5: `p(2S₁ + pS₂) = 0` in `ℤ/p⁴` (`p ≥ 5`) | `harmonic_pairing` | = |
| Theorem A: `C − 1 ≡ 2pS₁ (mod p⁴)` (`p ≥ 5`) | `binomial_harmonic_congruence` | = |
| Corollary: `C ≡ 1 (mod p⁴)` ⇔ `p³ ∣ num H_{p−1}` | `wolstenholme_core` | = |
| Corollary: `p² ∣ num H_{p−1}` | `harmonic_num_dvd_sq` | = |
| Corollary: `C ≡ 1 (mod p³)` | `wolstenholme_theorem_mod_p_cube` | = |

## Part II

| `PROOF.md` | Lean | Match |
|---|---|---|
| Step 0: `2S₁ + pS₂ ≡ 0 (mod p³)`; `S₁ ≡ 0 (p³)` ⇔ `S₂ ≡ 0 (p²)` | inside `wolstenholme_bernoulli_core` (`hpair3`, `step1`) | = |
| Step 0, rational form: `p³ ∣ num H_{p−1}` ⇔ `p² ∣ num H_{p−1,2}` | `harmonic_iff_harmonic2` | = |
| Step A: `Σ_{k=1}^{p−1} k^{p−3} ≡ p·B_{p−3} (mod p²)` | `sum_pow_p_sub_three` | = |
| `den Bᵢ` prime to `p` for `i < p − 1` | `bernoulli_den_coprime` | = |
| Step B: `k ↦ 2k mod p` permutes `1, …, p−1` for odd `p` | `sum_range_double` (`p ≥ 3`) | = |
| `r ≡ 2k − pf`, `k, r` prime to `p` ⇒ `4/r² ≡ 1/k² + pf/k³ (mod p²)` | `inv_sq_double` | = |
| `r ≡ 2k − pf` ⇒ `rⁿ ≡ (2k)ⁿ − n(2k)ⁿ⁻¹pf (mod p²)` for every `n` | `pow_double` | = |
| `F = Σ ⌊2k/p⌋/k³`, `T = Σ k^{p−3}` in `ℤ/p²` | `Fz`, `Tz` | = |
| (B1) `3S₂ ≡ pF (mod p²)` | `three_S_two_eq_p_F` | = |
| (B2) `2T ≡ pF (mod p²)` | `two_T_eq_p_F` | = |
| Step B: `3S₂ ≡ 2T (mod p²)` | `three_S_two_eq` | = |
| Assembly: `C ≡ 1 (mod p⁴)` ⇔ `p ∣ num B_{p−3}` | `wolstenholme_bernoulli_core` (with `bernoulli`) | = |
| `bernoulli' n = bernoulli n` for `n ≠ 1` | Mathlib `bernoulli_eq_bernoulli'_of_ne_one` | = |
| Remark: Glaisher's `3H_{p−1,2} ≡ 2pB_{p−3} (mod p²)` | `glaisher` | = |
| Remark: `F ≡ 2B_{p−3} (mod p)`, `F` rational | `voronoiF`, `voronoiF_mod_p` | = |

## Final statements

| Formal Conjectures statement (copied verbatim) | Proved by | Hypotheses |
|---|---|---|
| `wolstenholme_theorem` | `wolstenholme_theorem_mod_p_cube` | `p > 3`, prime (so `p ≥ 5`, since 4 is not prime) |
| `wolstenholme_harmonic` | `wolstenholme_core` | `p > 7`, prime |
| `wolstenholme_bernoulli` | `wolstenholme_bernoulli_core` and `bernoulli_eq_bernoulli'_of_ne_one` | `p > 7`, prime |

The CI checks that all ten theorems listed in `scripts/Axioms.lean` depend only on `propext`,
`Classical.choice` and `Quot.sound` (`scripts/check_axioms.sh`).

## Note

1. `PROOF.md` proves Lemma 1 with a generator of `(ℤ/p)ˣ`. Lean uses Mathlib's
   `FiniteField.sum_pow_units` after the substitution `u ↦ u⁻¹`. The statements are the same; only
   the method differs.

Every claim in `PROOF.md` is now a Lean theorem with the same content, the same hypotheses and
the same modulus.
