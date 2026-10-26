import PowerActivity.Spec

/-!
# Формулировки тезисов и вспомогательные цели

Утверждения тезисов:
* `ThesesThm1` — теорема 1 тезисов: равномерно по `1 ≤ m ≤ 2^{2^n}`
  `E(n,m) = Θ(n + m log n')`, `Ê(n,m) = Θ(n + m log n')`, `n' = max(2, n − log log(m+1))`;
  нижняя оценка — для почти всех операторов;
* `ThesesThm2` — теорема 2 тезисов: равномерно по `1 ≤ m ≤ 2^{2^n}`
  `Ω(n log n + m log n') ≤ P(n,m) ≤ O(n² + m log n')`; нижняя оценка — для почти всех операторов;
* `ThesesThm2U` — то же для числа активных проводов `U` (замечание в конце тезисов);
* `ThesesCorP` — следствие: при `n²/log n ≤ m ≤ 2^{2^n}` `P(n,m), P̂(n,m) = Θ(m log n')`.

Вспомогательные цели (сборка — `ThesesAssemble.lean`):
* `InflGoal` — для почти всех операторов любая схема имеет `E ≥ c n` (влияние переменных);
* `LayerGoal` — обратные слои «для почти всех» при большом `Δ`: `E, U ≥ c m log(1+Δ)`;
* `BalGoal` — различные сбалансированные выходы: для почти всех операторов `E, U ≥ c m`;
* `UpperPOpGoal` — `P̂(F) ≤ K(n² + m log(1+Δ))` для любого оператора.
-/

namespace PowerActivity

open Finset Filter Topology

/-- `n' = max(2, n − log log(m+1))`. -/
noncomputable def nPrime (n m : ℕ) : ℝ :=
  max 2 ((n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)))

/-! ## Утверждения тезисов -/

/-- Теорема 1 тезисов: нижняя оценка для почти всех операторов (равномерно по
`1 ≤ m ≤ 2^{2^n}`) и порядок функций Шеннона `E(n,m)`, `Ê(n,m)`. -/
def ThesesThm1 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * (n + m * Real.logb 2 (nPrime n m)) ≤ C.Eav) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    c * (n + m * Real.logb 2 (nPrime n m)) ≤ EavSh n m ∧ EavSh n m ≤ EmaxSh n m ∧
      EmaxSh n m ≤ K * (n + m * Real.logb 2 (nPrime n m)))

/-- Теорема 2 тезисов (`P`-активность операторов): нижняя оценка для почти всех операторов,
верхняя оценка на каждом наборе для любого оператора, порядок функций Шеннона. -/
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

/-- Теорема 2 тезисов для числа активных проводов `U` (замечание в конце тезисов). -/
def ThesesThm2U : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Uav) ∧
  (∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    ∀ F : (Fin n → Bool) → Fin m → Bool, ∃ C : Circ n (Fin m), C.Realizes F ∧
      ∀ x, (C.U x : ℝ) ≤ K * (n ^ 2 + m * Real.logb 2 (nPrime n m))) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ UavSh n m ∧
      UavSh n m ≤ UmaxSh n m ∧ UmaxSh n m ≤ K * (n ^ 2 + m * Real.logb 2 (nPrime n m)))

/-- Следствие теоремы 2 тезисов: при `n²/log n ≤ m ≤ 2^{2^n}`
`P(n,m) = Θ(m log n')` и `P̂(n,m) = Θ(m log n')`. -/
def ThesesCorP : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → (n : ℝ) ^ 2 ≤ m * Real.logb 2 n → m ≤ 2 ^ 2 ^ n →
    c * (m * Real.logb 2 (nPrime n m)) ≤ PavSh n m ∧ PavSh n m ≤ PmaxSh n m ∧
      PmaxSh n m ≤ K * (m * Real.logb 2 (nPrime n m))

/-! ## Вспомогательные цели -/

/-- Влияние переменных: для почти всех операторов любая схема имеет `E ≥ c n`
(обобщение `parity` с чётности на функции, у которых каждая переменная существенна
на заметной доле наборов). -/
def InflGoal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F → c * n ≤ C.Eav

/-- Обратные слои (`rev-layers`, `large-delta`) «для почти всех» операторов при большом `Δ`;
для `E` и для `U` (элементы слоёв `L_{d+1}`, `d ≥ 0`, имеют исходящие провода). -/
def LayerGoal : Prop :=
  ∃ c Δ₀ : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n → Δ₀ < Delta n m →
      1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c * m * Real.logb 2 (1 + Delta n m) ≤ C.Eav ∧ c * m * Real.logb 2 (1 + Delta n m) ≤ C.Uav

/-- Различные сбалансированные выходы: для почти всех операторов (равномерно по
`1 ≤ m ≤ 2^{2^n}`) любая схема имеет `E ≥ c m` и `U ≥ c m`. -/
def BalGoal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * m ≤ C.Eav ∧ c * m ≤ C.Uav

/-- Верхняя оценка `P`-активности операторов на каждом наборе:
дешифратор Горяшко (`P = O(n²)`) и монотонная часть схемы для мощности. -/
def UpperPOpGoal : Prop :=
  ∃ K : ℝ, ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n → ∀ F : (Fin n → Bool) → Fin m → Bool,
    ∃ C : Circ n (Fin m), C.Realizes F ∧
      ∀ x, (C.P x : ℝ) ≤ K * (n ^ 2 + m * Real.logb 2 (1 + Delta n m))

end PowerActivity
