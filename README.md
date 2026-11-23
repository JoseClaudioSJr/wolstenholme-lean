# Wolstenholme primes in Lean 4

[![CI](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions/workflows/ci.yml)

Lean 4 / Mathlib proofs of the three textbook statements about Wolstenholme primes in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/WolstenholmePrime.lean`):

| Theorem | Statement |
|---|---|
| `wolstenholme_theorem` | `p > 3 → p.Prime → C(2p−1, p−1) ≡ 1 [MOD p ^ 3]` (Wolstenholme, 1862) |
| `wolstenholme_harmonic` | `IsWolstenholmePrime p ↔ p > 7 ∧ p.Prime ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num` |
| `wolstenholme_bernoulli` | `IsWolstenholmePrime p ↔ p > 7 ∧ p.Prime ∧ ↑p ∣ (bernoulli' (p - 3)).num` |

In Formal Conjectures, the last two are `sorry`. The first links to an external short proof; here
it is a corollary of the stronger congruence `C(2p−1, p−1) − 1 ≡ 2p·H_{p−1} (mod p⁴)`, together
with `H_{p−1} ≡ 0 (mod p²)` (`harmonic_num_dvd_sq`).

Also proved along the way: Glaisher's congruence `3·H_{p−1,2} ≡ 2p·B_{p−3} (mod p²)` (`glaisher`),
the equivalence `p³ ∣ num H_{p−1} ⇔ p² ∣ num H_{p−1,2}` (`harmonic_iff_harmonic2`), and
`Σ_{k<p} ⌊2k/p⌋/k³ ≡ 2·B_{p−3} (mod p)` (`voronoiF_mod_p`).

Here `IsWolstenholmePrime p` means `p > 7`, `p` is prime, and `C(2p−1, p−1) ≡ 1 (mod p⁴)`.

Mathlib's `bernoulli'` uses the convention `B₁ = +1/2`, while `bernoulli` uses `B₁ = −1/2`. They agree at
every even index, in particular at `p − 3` for odd `p`, so the statement is the classical one.

## Verification status

Every push runs CI on a clean clone ([Actions](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions)).
The CI fetches the Mathlib cache for `0df444a3`, compiles everything with `import Mathlib`, and
runs `scripts/check_axioms.sh`. The script prints `#print axioms` for every exported theorem and
fails unless each depends only on `[propext, Classical.choice, Quot.sound]`. The first run
([45191292172](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions/runs/45191292172))
compiled with no errors or warnings.

All three results are classical (Wolstenholme 1862, Glaisher 1900). What this repository adds is a complete
formalization: no `sorry`, only Lean's standard axioms, and no use of Kummer's congruence,
which Mathlib does not have. (The repository now also proves the case of Kummer's congruence
that Jensen's theorem needs; see below. Part II does not use it.)

## Files

- `PROOF.md`: the complete proof in ordinary mathematical notation, with no Lean, step by step
  and with the Lean name of each step.
- `AUDIT.md`: a claim-by-claim check that `PROOF.md` says exactly what the Lean code proves.
- `WolstenholmeHarmonic.lean`: the proofs, about 1,100 lines. They are organised in reusable layers:
  generic symmetric-function identities, reduction of rationals into `ZMod m`, then the
  number theory.
- `FormalConjecturesCheck.lean`: the Formal Conjectures definition and all three statements, copied
  verbatim in their own namespace (Apache-2.0, see the file header), each proved in a few lines
  from the main file.
- `Kummer.lean`: Faulhaber mod `p²` for all exponents, Voronoi's congruence, the case of Kummer's
  congruence used by Jensen, and Jensen's argument (see the next section).
- `Jensen.lean`: the analytic input (`|B_{2k}| > 1` for large `k`, from Mathlib's formula for
  `ζ(2k)`) and Jensen's theorem.
- `RegularPrimesCheck.lean`: the Formal Conjectures definitions of regular and irregular primes,
  copied verbatim, and the reduction of `infinitude_of_irregularprimes` to Kummer's criterion.
- `Erdos291Check.lean`: the Formal Conjectures definitions for Erdős Problem 291, copied verbatim,
  and a proof of `erdos_291.variants.steinerberger_generalization` (see below).
- `scripts/check_axioms.sh`: fails unless every theorem listed in `scripts/Axioms.lean` depends only on
  `propext`, `Classical.choice` and `Quot.sound`. This also catches any `sorry`.

## Kummer's congruence and Jensen's theorem

**Jensen's theorem (1915)** (`jensen_bernoulli`): infinitely many primes `p` divide the numerator of
some Bernoulli number `B_k` with `k` even and `2 ≤ k ≤ p − 3`.

By Kummer's criterion these are exactly the irregular primes. Formal Conjectures states the
criterion (`isRegularPrime_iff_Bernoulli`) and the infinitude of irregular primes
(`infinitude_of_irregularprimes`), both with `sorry`; the definition of a regular prime there uses
the class group of the cyclotomic field. `RegularPrimesCheck.lean` proves that the infinitude
follows from the easy direction of the criterion (`p ∣ B_k` ⇒ `p` irregular). That direction needs
the class number formula for cyclotomic fields and is **not** proved here.

The steps, all in `Kummer.lean` except the last:

1. `sum_pow_eq_p_mul_bernoulli`: `Σ_{k=1}^{p−1} kⁿ ≡ p·B_n (mod p²)` for every even `n ≥ 2` with
   `(p − 1) ∤ n` (`p ≥ 5`). Unlike Step A above, `n` may exceed `p`, so some `Bᵢ` in Faulhaber's
   formula have `p` in the denominator; `p·Bᵢ` is always `p`-integral, and `p^(m−3)/m` is
   `p`-integral for `m ≥ 3`.
2. `voronoi_mod_p` (Voronoi's congruence): for `p ∤ a`,
   `(aⁿ − 1)·B_n ≡ n·a^{n−1}·Σ_{k=1}^{p−1} ⌊ak/p⌋·k^{n−1} (mod p)`. This is Step B above with `2`
   replaced by any `a` and `p − 3` by any `n`.
3. `kummer_dvd`: if `p ∤ n`, `(p − 1) ∤ n` and `p ∣ B_n`, then `p ∣ B_{n mod (p−1)}`. Take `a` a
   primitive root; the right side of Voronoi's congruence depends only on `n mod (p − 1)`.
4. `dvd_den_bernoulli`: if `(p − 1) ∣ 2k`, then `p` divides the denominator of `B_{2k}`.
5. `exists_irregular_gt` (Jensen's argument): given `P`, let `M = ∏_{q ≤ P prime} (q − 1)` and
   `n = 2·2^K·M`. A prime `p` dividing the numerator of `B_n` has `(p − 1) ∤ n` (by 4), hence
   `p > P`, and `p ∤ n`; by 3, `p ∣ B_{n mod (p−1)}`.
6. `one_lt_abs_bernoulli` (`Jensen.lean`): the numerator of `B_n` is not `±1`, because
   `|B_{2k}| = 2·(2k)!·ζ(2k)/(2π)^{2k} ≥ 2·(2k)!/(2π)^{2k} > 1` for large `k`.

## Erdős Problem 291: Steinerberger's criterion

Write `L_n = lcm(1, …, n)` and `1 + 1/2 + ⋯ + 1/n = a_n / L_n`. Formal Conjectures states
(`erdos_291.variants.steinerberger_generalization`, category *research solved*, with `sorry`):
for a prime `p ≤ n`, with `k` the leading digit of `n` in base `p`,
`p ∣ gcd(a_n, L_n) ⇔ p ∣ num(1 + 1/2 + ⋯ + 1/k)`. `Erdos291Check.lean` proves it.

With `e = ⌊log_p n⌋`: `L_n = pᵉ·L'` with `p ∤ L'` (if `p ∣ L'`, every `j ≤ n` would divide
`L_n/p`). In `a_n = Σ_{j ≤ n} L_n/j`, the terms with `pᵉ ∤ j` are divisible by `p`, and the terms
`j = pᵉ·m`, `1 ≤ m ≤ k`, equal `L'/m`. So `a_n ≡ L'·H_k (mod p)`; since `p ∣ L_n` and `p ∤ L'`, the
criterion follows. The same file reuses the reduction of rationals into `ZMod p`.

## Proof strategy

**Part I (`wolstenholme_harmonic`).** For every prime `p ≥ 5`,

    C(2p−1, p−1) − 1 ≡ 2p · H_{p−1}   (mod p⁴),

and 2 is invertible mod `p`, so `p⁴ ∣ C − 1 ⇔ p³ ∣ num(H_{p−1})`. In `ZMod p⁴`:

1. `C(2p−1, p−1) = ∏_{k=1}^{p−1} (1 + p/k)`.
2. Expand the product: `1 + p·S₁ + p²·e₂ + p³·e₃`, where `S_j = Σ k^{−j}` and the `e_j` are the
   elementary symmetric functions of the `1/k`. All `p⁴` terms vanish.
3. `S_j ≡ 0 (mod p)` when `p − 1 ∤ j`. This comes from Mathlib's `FiniteField.sum_pow_units`.
4. Newton identities give `2e₂ = S₁² − S₂` and `6e₃ = S₁³ − 3S₁S₂ + 2S₃`, so `p²S₁² = 0` and `p³e₃ = 0`.
5. Pairing `k ↔ p − k` gives `p·(2S₁ + p·S₂) = 0`.

**Part II (`wolstenholme_bernoulli`).**

- **Step A (Faulhaber and von Staudt–Clausen):** `Σ_{k=1}^{p−1} k^{p−3} ≡ p·B_{p−3} (mod p²)`.
  - This follows from Mathlib's `sum_range_pow`.
  - Every other term of the formula carries a factor `p²` and a denominator prime to `p`. This uses
    `bernoulli_den_coprime`: `p` does not divide the denominator of `Bᵢ` for `i < p − 1`, which
    follows from `vonStaudt_clausen`.
- **Step B (doubling `k ↦ 2k mod p`):** `3·H_{p−1,2} ≡ 2·Σ k^{p−3} (mod p²)`.
  - Doubling permutes `1, …, p−1` mod `p`. Write `2k = r_k + p·f_k` with `f_k = ⌊2k/p⌋`. Mod `p²`, this
    gives `4/r_k² = 1/k² + p·f_k/k³` and `r_k^{p−3} = (2k)^{p−3} − (p−3)(2k)^{p−4}·p·f_k`.
  - Sum both over `k`, with `F = Σ f_k/k³` and `P = Σ k^{p−3}`. Three Fermat facts are used:
    `2^{p−1} ≡ 1`, `P ≡ 0 (mod p)` and `k^{p−4} ≡ k^{−3}`. The two sums then give
    `3·H_{p−1,2} ≡ p·F` and `2·P ≡ p·F (mod p²)`. Eliminating `F` gives the claim.
- **Assembly:** `W ⇔ p³ ∣ H_{p−1} ⇔ p² ∣ H_{p−1,2} ⇔ p ∣ B_{p−3}`. The first step uses the pairing
  lemma; the other two use Steps B and A.

## References

- J. Wolstenholme, *On certain properties of prime numbers*, Quart. J. Pure Appl. Math. 5 (1862).
- J. W. L. Glaisher, *Congruences relating to the sums of product of the first n numbers and to
  other sums of product*, Quart. J. Math. 31 (1900), 1–35; and *On the residues of the sums of
  products of the first p−1 numbers, and their powers, to modulus p² or p³*, ibid., 321–353.
- K. L. Jensen, *Om talteoretiske Egenskaber ved de Bernoulliske Tal*, Nyt Tidsskr. Mat. B 26
  (1915), 73–83.
- L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Springer, 1997, ch. 5
  (Kummer's congruences, Voronoi's congruence, irregular primes).
- E. Lehmer, *On congruences involving Bernoulli numbers and the quotients of Fermat and Wilson*,
  Ann. of Math. 39 (1938), 350–360. Sums weighted by `⌊ak/p⌋`, of the kind used in Step B.
- R. Meštrović, *Wolstenholme's theorem: its generalizations and extensions in the last hundred
  and fifty years (1862–2012)*, arXiv:1111.3057.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.33.1`) and
Mathlib (`0df444a3`, the commit Formal Conjectures uses) are pinned.

```sh
lake exe cache get      # downloads compiled Mathlib
lake build              # compiles this project
bash scripts/check_axioms.sh
```

CI (`.github/workflows/ci.yml`) runs the same steps on every push from a clean clone.

## Authorship and use of AI

The formalization was written with Claude (Anthropic), under the direction of
José Cláudio da Silva Junior, who reviewed it. The proof route was cross-checked with ChatGPT.
All exported theorem declarations are kernel-checked, and the axiom audit reports only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). As with any formal proof, the results are relative
to the definitions used and the imported Mathlib theorems.

## License

Apache License 2.0. The statements in `FormalConjecturesCheck.lean` are copyright
The Formal Conjectures Authors, under the same license.
