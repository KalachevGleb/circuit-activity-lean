import PowerActivity.Defs

/-!
# Промежуточные теоремы и вспомогательные цели

Промежуточные теоремы (в терминах функций Шеннона модели `Defs`; из них и целей
`ThesesSpec.lean` выводятся теоремы тезисов):
* `PowerBound`: `c(n + m log(n+1)) ≤ E(n,m) ≤ Ê(n,m) ≤ C(n + m log(n+1))`,
  `n ≥ 2`, `1 ≤ m ≤ 2ⁿ`;
* `ActivityBound`: для почти всех `f` любая схема имеет `P(Σ) ≥ c n log n`;
  `Ω(n log n) ≤ P(n,1) ≤ P̂(n,1) ≤ O(n²)`; `WireBound` — то же для меры `U` (в тезисах `Q`);
* `PowerBoundGeneral`: `E(n,m) ≍ Ê(n,m) ≍ n + M log(1+Δ)` равномерно при `n ≥ 2`, `m ≥ 1`.

Цели — вспомогательные утверждения (доказываются в отдельных модулях, сборка — `Main.lean`):
* верхние оценки: `ExistsGoal`, `UpperBlockGoal`, `UpperGroupGoal`, `UpperPGoal`;
* нижние оценки мощности: `ParityGoal`, `LowerPowerGoal`, `ManyOutGoal`, `LowerGeneralGoal`;
* нижняя оценка активности: `ActLowerGoal` — при `ApproxHardGoal`, `CutCompressGoal`;
* приближённая сложность: `ApproxHardGoal`, `CutCompressGoal` (интерфейс: `Circ.wires`,
  `Circ.wsrc`, `Circ.outdeg`, `Circ.fwdBall`, `Circ.cut`, `Circ.cutVal`, `probZ`, `ent`, `L14`).
-/

namespace PowerActivity

open Finset Filter Topology

/-! ## Промежуточные теоремы -/

/-- Порядок мощности `E(n,m)`, `Ê(n,m)` — `n + m log(n+1)` при `n ≥ 2`, `1 ≤ m ≤ 2ⁿ`. -/
def PowerBound : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ n →
    c * (n + m * Real.logb 2 (n + 1)) ≤ EavSh n m ∧ EavSh n m ≤ EmaxSh n m ∧
      EmaxSh n m ≤ K * (n + m * Real.logb 2 (n + 1))

/-- `P`-активность функций: нижняя оценка для почти всех функций и порядок функций Шеннона. -/
def ActivityBound : Prop :=
  (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => frac n (Fin 1) fun F =>
      ∀ C : Circ n (Fin 1), C.Realizes F → c * n * Real.logb 2 n ≤ C.Pav) atTop (𝓝 1)) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      c * n * Real.logb 2 n ≤ PavSh n 1 ∧ PavSh n 1 ≤ PmaxSh n 1 ∧ PmaxSh n 1 ≤ K * n ^ 2)

/-- То же, что `ActivityBound`, для меры с учётом разветвления `U` (в тезисах — `Q`). -/
def WireBound : Prop :=
  (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => frac n (Fin 1) fun F =>
      ∀ C : Circ n (Fin 1), C.Realizes F → c * n * Real.logb 2 n ≤ C.Uav) atTop (𝓝 1)) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      c * n * Real.logb 2 n ≤ UavSh n 1 ∧ UavSh n 1 ≤ UmaxSh n 1 ∧ UmaxSh n 1 ≤ K * n ^ 2)

/-- Порядок мощности при любом `m ≥ 1`: `E(n,m) ≍ Ê(n,m) ≍ n + M log(1+Δ)`,
`M = min{m, 2^{2^n}}`. -/
def PowerBoundGeneral : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m →
    c * (n + Mcap n m * Real.logb 2 (1 + Delta n m)) ≤ EavSh n m ∧ EavSh n m ≤ EmaxSh n m ∧
      EmaxSh n m ≤ K * (n + Mcap n m * Real.logb 2 (1 + Delta n m))

/-! ## Верхние оценки (конструкции) -/

/-- Существование реализации любого оператора при `n ≥ 1`. -/
def ExistsGoal : Prop :=
  ∀ n m : ℕ, 1 ≤ n → ∀ F : (Fin n → Bool) → Fin m → Bool, ∃ C : Circ n (Fin m), C.Realizes F

/-- `block-upper`: при `r = min{m,n}` мощность на каждом наборе
не больше `2n + c₀ + n⌈m/r⌉ + m⌈log r⌉`. -/
def UpperBlockGoal : Prop :=
  ∃ c₀ : ℕ, ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → ∀ F : (Fin n → Bool) → Fin m → Bool,
    ∃ C : Circ n (Fin m), C.Realizes F ∧ ∀ x,
      C.E x ≤ 2 * n + c₀ + n * ((m + min m n - 1) / min m n) + m * Nat.clog 2 (min m n)

/-- `group-upper`: `Ê(n,m) = O(n + m log(1+Δ))` при `1 ≤ m ≤ 2^{2^n}`. -/
def UpperGroupGoal : Prop :=
  ∃ K : ℝ, ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n → ∀ F : (Fin n → Bool) → Fin m → Bool,
    ∃ C : Circ n (Fin m), C.Realizes F ∧ ∀ x, (C.E x : ℝ) ≤ K * (n + m * Real.logb 2 (1 + Delta n m))

/-- Квадратичная верхняя оценка `P`- и `U`-активности одной функции
(оценка известна: О. М. Касим-Заде, 1992; здесь — собственная конструкция). -/
def UpperPGoal : Prop :=
  ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ F : (Fin n → Bool) → Fin 1 → Bool,
    ∃ C : Circ n (Fin 1), C.Realizes F ∧ ∀ x, (C.P x : ℝ) ≤ K * n ^ 2 ∧ (C.U x : ℝ) ≤ K * n ^ 2

/-! ## Нижние оценки мощности -/

/-- `parity`: схема, у которой один из выходов — чётность `n ≥ 2` переменных, имеет `E ≥ n/4`. -/
def ParityGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (κ : Type) (C : Circ n κ) (k : κ), (∀ x, C.eval x k = parity x) →
    (n : ℝ) / 4 ≤ C.Eav

/-- `encoding`, `incompressible`, `layer-sum`: для почти всех операторов
(равномерно по `1 ≤ m ≤ 2ⁿ`) любая схема имеет `E ≥ c m log(n+1)`. -/
def LowerPowerGoal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F =>
      ∀ C : Circ n (Fin m), C.Realizes F → c * m * Real.logb 2 (n + 1) ≤ C.Eav

/-- `many-outputs`: при `n ≥ 2`, `1 ≤ m ≤ 2^{2^n}` есть оператор, у которого любая схема имеет
`E ≥ m/4`. -/
def ManyOutGoal : Prop :=
  ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n → ∃ F : (Fin n → Bool) → Fin m → Bool,
    ∀ C : Circ n (Fin m), C.Realizes F → (m : ℝ) / 4 ≤ C.Eav

/-- `large-delta` и `many-outputs`: нижняя оценка `Ω(m log(1+Δ))` при `1 ≤ m ≤ 2^{2^n}`. -/
def LowerGeneralGoal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    ∃ F : (Fin n → Bool) → Fin m → Bool, ∀ C : Circ n (Fin m), C.Realizes F →
      c * m * Real.logb 2 (1 + Delta n m) ≤ C.Eav

/-! ## Нижняя оценка активности -/

/-- Для почти всех функций любая схема имеет `U ≥ c n log n` и `P ≥ c n log n`. -/
def ActLowerGoal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ,
    1 - ε n ≤ frac n (Fin 1) fun F => ∀ C : Circ n (Fin 1), C.Realizes F →
      c * n * Real.logb 2 n ≤ C.Uav ∧ c * n * Real.logb 2 n ≤ C.Pav

namespace Circ

variable {n : ℕ} {κ : Type} (C : Circ n κ)

/-- Провода `𝓔(Σ)`: пары (номер элемента, номер его входа). -/
def wires : Finset (ℕ × ℕ) :=
  (range C.s).biUnion fun i => (range (C.gate i).srcs.length).image fun t => (i, t)

/-- Источник провода. -/
def wsrc (e : ℕ × ℕ) : ℕ := (C.gate e.1).srcs.getD e.2 0

/-- Исходящая степень сигнала `j` (входной вершины или элемента). -/
def outdeg (j : ℕ) : ℕ := (C.wires.filter fun e => C.wsrc e = j).card

/-- Шар `B_d = {v : ρ(v) ≤ d}` от входов (сигналы; входные вершины — `0, …, n-1`). -/
def fwdBall : ℕ → Finset ℕ
  | 0 => range n
  | d + 1 => fwdBall d ∪
      (((range C.s).filter fun i => ∃ j ∈ (C.gate i).srcs, j ∈ fwdBall d).image (n + ·))

/-- Разрез `R_d`: провода из `B_d` в его дополнение. -/
def cut (d : ℕ) : Finset (ℕ × ℕ) :=
  C.wires.filter fun e => C.wsrc e ∈ C.fwdBall d ∧ n + e.1 ∉ C.fwdBall d

/-- Сигналы на разрезе, `Z_d(x) = (s_e(x))_{e ∈ R_d}`. -/
def cutVal (d : ℕ) (x : Fin n → Bool) : C.cut d → Bool := fun e => C.sig x (C.wsrc e.1)

end Circ

/-- `P{Z(X) = z}` при `X`, равномерно распределённом на `{0,1}ⁿ`. -/
noncomputable def probZ {n : ℕ} {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) (z : α) : ℝ :=
  ((univ.filter fun x => Z x = z).card : ℝ) / 2 ^ n

/-- Энтропия `H(Z(X))` в битах. -/
noncomputable def ent {n : ℕ} {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) : ℝ :=
  -∑ z ∈ univ.image Z, probZ Z z * Real.logb 2 (probZ Z z)

/-- Схема `C` совпадает с `f` не менее чем на `3N/4` наборах. -/
def Approx14 {n : ℕ} (C : Circ n (Fin 1)) (F : (Fin n → Bool) → Fin 1 → Bool) : Prop :=
  3 * 2 ^ n ≤ 4 * (univ.filter fun x => C.eval x 0 = F x 0).card

/-- `L_{1/4}(f)`: наименьшее число элементов схемы, совпадающей с `f` не менее чем на `3N/4`
наборах (констант в базисе нет — они стоят элементов). -/
noncomputable def L14 {n : ℕ} (F : (Fin n → Bool) → Fin 1 → Bool) : ℕ :=
  sInf {s | ∃ C : Circ n (Fin 1), C.s = s ∧ Approx14 C F}

/-- `approx-hard`: для почти всех `f` любая схема, совпадающая с `f` на `3N/4` наборах, имеет
не меньше `a 2ⁿ/n` элементов (то есть `L_{1/4}(f) ≥ a 2ⁿ/n`). -/
def ApproxHardGoal : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ,
    1 - ε n ≤ frac n (Fin 1) fun F => ∀ C : Circ n (Fin 1), Approx14 C F → a * 2 ^ n / n ≤ (C.s : ℝ)

/-- `cut-compress`: для схемы `f` с исходящими степенями `≤ 3` и любого `d` есть схема,
совпадающая с `f` на `3N/4` наборах, из не более `C₄ b_d 2^{4H_d}` элементов
(то есть `L_{1/4}(f) ≤ C₄ b_d 2^{4H_d}`). -/
def CutCompressGoal : Prop :=
  ∃ C₄ : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ C : Circ n (Fin 1), (∀ j, C.outdeg j ≤ 3) →
    ∀ F, C.Realizes F → ∀ d : ℕ, ∃ C' : Circ n (Fin 1), Approx14 C' F ∧
      (C'.s : ℝ) ≤ C₄ * (C.fwdBall d).card * (2 : ℝ) ^ (4 * ent (C.cutVal d))

end PowerActivity
