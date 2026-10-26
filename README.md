# Bounds on the activity of Boolean circuits implementing Boolean operators: Lean 4 formalization

[![Lean Action CI](https://github.com/KalachevGleb/circuit-activity-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/KalachevGleb/circuit-activity-lean/actions/workflows/lean_action_ci.yml)

**English** | [Русский](README.ru.md)

This repository contains a complete formal proof, in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of the two theorems of

> G. V. Kalachev. *Bounds on the Activity of Boolean Circuits Implementing Boolean Operators*
> (Оценки активности схем из функциональных элементов, реализующих булевы операторы).
> Intelligent Systems. Theory and Applications, to appear. In Russian.

## The setting

A circuit over the basis $`B_0=\{\wedge_2,\vee_2,\neg\}`$ with $`n`$ inputs is an acyclic network of
gates; fan-out is unbounded, both inputs of a gate may come from the same source (two wires),
outputs are arbitrary signals. For an input $`x\in\{0,1\}^n`$:

* $`E(\Sigma,x)`$, the **power**, is the number of gates whose output is $`1`$;
* $`P(\Sigma,x)`$, the **P-activity**, is the number of gates with $`1`$ on the output or on at least
  one input;
* $`U(\Sigma,x)`$ is the number of wires (including wires from the inputs) carrying $`1`$.

$`\widehat M(\Sigma)=\max_xM(\Sigma,x)`$, $`M(\Sigma)`$ is the average over the uniform $`x`$;
$`M(F)=\min_{\Sigma=F}M(\Sigma)`$ and $`M(n,m)=\max_{F\colon\{0,1\}^n\to\{0,1\}^m}M(F)`$ are the Shannon
functions. "Almost all" means that the fraction of operators tends to $`1`$ as $`n\to\infty`$.
All logarithms are binary, $`n':=\max(2,\ n-\log\,\log(m+1))`$.

## The theorems

**Theorem 1.** Uniformly in $`1\le m\le2^{2^n}`$,
$`E(n,m)=\Theta(n+m\,\log\,n')`$ and $`\widehat E(n,m)=\Theta(n+m\,\log\,n')`$; the lower bound holds for
almost all operators.

**Theorem 2.** Uniformly in $`1\le m\le2^{2^n}`$,
$`\Omega(n\,\log\,n+m\,\log\,n')\le P(n,m)\le\widehat P(n,m)\le O(n^2+m\,\log\,n')`$; the lower bound holds for
almost all operators.

In Lean ([`PowerActivity/ThesesSpec.lean`](PowerActivity/ThesesSpec.lean),
[`PowerActivity/Theses.lean`](PowerActivity/Theses.lean)):

```lean
def ThesesThm1 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * (n + m * Real.logb 2 (nPrime n m)) ≤ C.Eav) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    c * (n + m * Real.logb 2 (nPrime n m)) ≤ EavSh n m ∧ EavSh n m ≤ EmaxSh n m ∧
      EmaxSh n m ≤ K * (n + m * Real.logb 2 (nPrime n m)))

def ThesesThm2 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Pav) ∧
  (∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    ∀ F : (Fin n → Bool) → Fin m → Bool, ∃ C : Circ n (Fin m), C.Realizes F ∧
      ∀ x, (C.P x : ℝ) ≤ K * (n ^ 2 + m * Real.logb 2 (nPrime n m))) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ PavSh n m ∧
      PavSh n m ≤ PmaxSh n m ∧ PmaxSh n m ≤ K * (n ^ 2 + m * Real.logb 2 (nPrime n m)))

theorem thesesThm1 : ThesesThm1
theorem thesesThm2 : ThesesThm2
```

The formal statements are slightly stronger than the text: the bounds on the Shannon functions hold
for all $`n\ge2`$ (not only asymptotically), and the upper bounds hold for every operator on every
input. The quadratic upper bound for $`\widehat P(n,1)`$, which the abstract cites from
O. M. Kasim-Zade (1992), is proved here with an explicit Goryashko-type circuit. Two remarks of the
abstract are also checked: the same bounds for the number of active wires (`thesesThm2U`) and
$`P(n,m),\widehat P(n,m)=\Theta(m\,\log\,n')`$ for $`n^2/\log\,n\le m\le2^{2^n}`$ (`thesesCorP`).

Intermediate results ([`PowerActivity/Spec.lean`](PowerActivity/Spec.lean),
[`PowerActivity/Main.lean`](PowerActivity/Main.lean)): `powerBound` (order $`n+m\,\log(n+1)`$ of the
power for $`1\le m\le2^n`$), `activityBound` and `wireBound` (for almost all Boolean functions every
circuit has $`P,U\ge cn\,\log\,n`$; $`\widehat P(n,1),\widehat U(n,1)=O(n^2)`$), `powerBoundGeneral`
(order $`n+M\,\log(1+\Delta)`$ of the power for every $`m`$, $`M=\min\{m,2^{2^n}\}`$,
$`\Delta=\max\{1,n-\log\,\log(M+1)\}`$).

## What has to be checked by a reader

Lean checks the proofs. To trust the result, it suffices to check that the definitions used in the
statements mean what the text says: [`Defs.lean`](PowerActivity/Defs.lean) (the model, about 250
lines) and `nPrime`, `ThesesThm1`, `ThesesThm2` in
[`ThesesSpec.lean`](PowerActivity/ThesesSpec.lean).

| Text | Lean |
| --- | --- |
| circuit over $`B_0`$ with $`n`$ inputs and outputs indexed by $`\kappa`$ | `Circ n κ` (list of gates in topological order; signal `j < n` is the input $`x_j`$, signal `n + i` is gate `i`) |
| value of a signal on input $`x`$ | `Circ.sig`, `Circ.val` |
| $`\Sigma`$ realizes $`F`$ | `Circ.Realizes F` |
| $`E(\Sigma,x)`$, $`P(\Sigma,x)`$, $`U(\Sigma,x)`$ | `Circ.E`, `Circ.P`, `Circ.U` |
| $`\widehat E(\Sigma)`$, $`E(\Sigma)`$ (and the same for $`P`$, $`U`$) | `Circ.Emax`, `Circ.Eav`, … |
| $`E(n,m)`$, $`\widehat E(n,m)`$, $`P(n,m)`$, … | `EavSh n m`, `EmaxSh n m`, `PavSh n m`, … |
| fraction of operators with a property | `frac n (Fin m) Q` |
| $`n'`$ | `nPrime n m` |

The file [`Verify.lean`](Verify.lean) checks that the theorems use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; in particular, there is no `sorry`.

## Building

Install Lean with [elan](https://github.com/leanprover/elan) (the version is fixed by
`lean-toolchain`: Lean 4.34.1, Mathlib v4.34.1), then

```sh
git clone https://github.com/KalachevGleb/circuit-activity-lean.git
cd circuit-activity-lean
lake exe cache get        # precompiled Mathlib
lake build                # checks all proofs
lake env lean Verify.lean # axiom check; prints nothing on success
```

The same steps run in GitHub Actions on every push
([`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)).

## Structure of the proof

| Modules | Content |
| --- | --- |
| `Defs`, `ThesesSpec`, `Spec` | The model; the statements of the abstract; intermediate statements and goals. |
| `Up*` | Upper bounds for the power: `minterms`, `decoder`, `block-upper`, `group-param`, `group-upper`; a Goryashko-type circuit with $`P,U=O(n^2)`$. |
| `Low*` | Lower bounds for the power: `parity`, `rev-layers`, `encoding`, `incompressible`, `layer-sum`, `large-delta`, `many-outputs`. |
| `Act*` | Lower bound for the activity: `entropy`, `wires`, `fanout`, `fwd-balls`, `cut-sum`, `harmonic`. |
| `Apx*` | Approximate circuit complexity: `approx-hard`, `cut-compress`. |
| `Assemble`, `Main` | Shannon functions, `saturation`, the intermediate results. |
| `Infl*`, `LayerU` | Almost all operators: $`E\ge cn`$ (influence of variables, generalizing `parity`); reverse layers for $`E`$ and $`U`$. |
| `Bal*` | Almost all operators: $`E,U\ge cm`$ (many distinct balanced outputs), uniformly in $`m\le2^{2^n}`$. |
| `OpP*` | $`P(\Sigma,x)=O(n^2+m\,\log(1+\Delta))`$ for every operator: the Goryashko decoder followed by the monotone part of the power construction. |
| `ThesesAssemble`, `Theses` | The theorems of the abstract. |

Comments in the code are in Russian and refer to the statements of the proof by short labels:

| Label | Statement |
| --- | --- |
| `entropy` | $`H(Z)\le\sum_ih_2(p_i)\le tA+q\,\log(1+2^{-t})`$ and $`H(Z)\le A\,\log(2q)+1`$ for a vector $`Z`$ of $`q`$ bits with $`A=\sum_i\Pr\{Z_i=1\}`$. |
| `parity` | Every circuit computing the parity of $`n\ge2`$ variables has $`E\ge n/4`$. |
| `wires` | $`U\le2P`$; if every gate lies on a path to the output, then $`U/2\le P\le2U+1`$. |
| `fanout` | Every circuit can be transformed into a circuit of the same operator with fan-out at most $`3`$ (inputs included) and $`U(\Sigma^\ast,x)\le3U(\Sigma,x)`$. |
| `minterms` | All minterms are computed by one circuit with power $`2n+O(1)`$ on every input. |
| `decoder` | Given the indicators of the values of a block of $`r`$ outputs, the block is decoded with additional power at most $`r\lceil\log\,r\rceil`$. |
| `block-upper` | $`E(\Sigma,x)\le2n+O(1)+n\lceil m/r\rceil+m\lceil\log\,r\rceil`$, $`r=\min\{m,n\}`$. |
| `rev-layers` | Balls and layers by the distance to the outputs: $`\lvert B_d\rvert,\lvert L_{d+1}\rvert\le m2^{d+1}`$, and $`F(x)=G_d(x,Z_d(x))`$ for the signals $`Z_d`$ of the layer $`L_{d+1}`$. |
| `encoding` | The number of operators having a circuit with $`S_d=\sum_{v\in L_{d+1}}h_2(p_v)\le S`$ is at most $`2^{NS+C_0m2^d(n+\log(m+1)+d+1)}`$, $`N=2^n`$. |
| `incompressible` | For almost all operators every circuit has $`S_d\ge m/2`$ for all small $`d`$. |
| `layer-sum` | $`S_d\le(d+4)A_d+m/4`$, hence $`E\ge\sum_dA_d=\Omega(m\,\log(n+1))`$. |
| `approx-hard` | For almost all $`f`$, every circuit agreeing with $`f`$ on $`3/4`$ of the inputs has at least $`a2^n/n`$ gates. |
| `fwd-balls` | Balls from the inputs with fan-out $`\le3`$: $`\lvert B_d\rvert\le\tfrac32n3^d`$, $`\lvert R_d\rvert\le3\lvert B_d\rvert`$; the cuts $`R_d`$ are pairwise disjoint. |
| `cut-sum` | $`U\ge\sum_dA_d`$, the sum of the expected numbers of active wires in the cuts. |
| `cut-compress` | $`L_{1/4}(f)\le C_4\lvert B_d\rvert2^{4H_d}`$, $`H_d`$ the entropy of the signals in the cut $`R_d`$. |
| `harmonic` | $`H_d\ge cn`$ for $`d\le c_0n`$, hence $`U=\Omega(n\,\log\,n)`$. |
| `saturation` | $`E(n,m)=E(n,M)`$, $`M=\min\{m,2^{2^n}\}`$. |
| `group-param` | The depth $`\ell`$ of the trees over groups satisfies $`\ell=\Theta(\Delta)`$. |
| `group-upper` | Indicators of all subsets of small groups of inputs give $`\widehat E(n,m)=O(n+m\,\log(1+\Delta))`$. |
| `large-delta` | For large $`\Delta`$, almost all operators have $`E=\Omega(m\,\log(1+\Delta))`$ in every circuit. |
| `many-outputs` | There is an operator every circuit of which has $`E\ge m/4`$. |

## Use of AI tools

The formalization of the proofs in Lean 4 was carried out with the help of the Claude Opus 5.5
model (Anthropic) in Claude Code.

## Citation and license

If you use this code, please cite the paper above (see also [`CITATION.cff`](CITATION.cff)).
The code is distributed under the Apache License 2.0 ([`LICENSE`](LICENSE)), the same license as
Mathlib.
