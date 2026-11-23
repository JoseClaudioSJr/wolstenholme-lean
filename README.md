# Wolstenholme primes in Lean 4

[![CI](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions/workflows/ci.yml)

Lean 4 / Mathlib proofs of the two textbook characterisations of Wolstenholme primes stated in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/WolstenholmePrime.lean`), where they are currently `sorry`:

| Theorem | Statement |
|---|---|
| `wolstenholme_harmonic` | `IsWolstenholmePrime p ↔ p > 7 ∧ p.Prime ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num` |
| `wolstenholme_bernoulli` | `IsWolstenholmePrime p ↔ p > 7 ∧ p.Prime ∧ ↑p ∣ (bernoulli' (p - 3)).num` |

Here `IsWolstenholmePrime p` means `p > 7`, `p` is prime, and `C(2p−1, p−1) ≡ 1 (mod p⁴)`.

Mathlib's `bernoulli'` uses the convention `B₁ = +1/2`, while `bernoulli` uses `B₁ = −1/2`. They agree at
every even index, in particular at `p − 3` for odd `p`, so the statement is the classical one.

## Verification status

Verified. The CI run on a clean clone
([run 45191292172](https://github.com/JoseClaudioSJr/wolstenholme-lean/actions/runs/45191292172)) did three things:

1. It fetched the Mathlib cache for `0df444a3`.
2. It compiled both files with `import Mathlib`, with no errors or warnings.
3. It reported:

```
'WolstenholmePrime.wolstenholme_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]
'WolstenholmePrime.wolstenholme_bernoulli' depends on axioms: [propext, Classical.choice, Quot.sound]
'WolstenholmeHarmonic.wolstenholme_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]
'WolstenholmeHarmonic.wolstenholme_bernoulli' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both results are classical (Glaisher, 1900). What this repository adds is a complete
formalization: no `sorry`, only Lean's standard axioms, and no use of Kummer's congruence,
which Mathlib does not have.

## Files

- `PROOF.md`: the complete proof in ordinary mathematical notation, with no Lean, step by step
  and with the Lean name of each step.
- `WolstenholmeHarmonic.lean`: the proofs, about 1,100 lines. They are organised in reusable layers:
  generic symmetric-function identities, reduction of rationals into `ZMod m`, then the
  number theory.
- `FormalConjecturesCheck.lean`: the Formal Conjectures definition and both statements, copied
  verbatim in their own namespace (Apache-2.0, see the file header), each proved in one line from
  the main file.
- `scripts/check_axioms.sh`: fails unless all four theorems depend only on
  `propext`, `Classical.choice` and `Quot.sound`. This also catches any `sorry`.

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
All four theorem declarations are kernel-checked, and the axiom audit reports only Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). As with any formal proof, the results are relative
to the definitions used and the imported Mathlib theorems.

## License

Apache License 2.0. The statements in `FormalConjecturesCheck.lean` are copyright
The Formal Conjectures Authors, under the same license.
