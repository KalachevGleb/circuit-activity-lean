import Mathlib

/-!
# Модель: схемы из функциональных элементов и меры активности

Модель для тезисов Г. В. Калачева «Оценки активности схем из функциональных элементов,
реализующих булевы операторы».

Схема из функциональных элементов (СФЭ) над базисом `B₀ = {∧₂, ∨₂, ¬}` с `n` входами —
список элементов в топологическом порядке. Сигналы занумерованы натуральными числами:
`0, …, n-1` — входные переменные, `n + i` — выход `i`-го элемента. Элемент `i` берёт входы
из сигналов с номерами `< n + i` (ацикличность). Исходящая степень произвольна; оба входа
элемента могут идти от одного источника — это два провода. Выходы — выбранные сигналы
(в том числе входные переменные; несколько выходов могут совпадать), индексы выходов — тип `κ`
(для операторов `{0,1}ⁿ → {0,1}ᵐ` это `Fin m`). Констант в базисе нет: они реализуются
элементами (`x₁ ∧ ¬x₁`).

* `sig n gs x j` — значение сигнала `j` для списка элементов `gs` (для любого списка; охрана
  `a, b < j` у правильных схем выполнена всегда, поэтому функция тотальна и годится для
  подсчёта «сырых» описаний);
* `Circ n κ` — схема (`valid` — ацикличность), `Circ.Realizes F`;
* меры на наборе: `E` (мощность — число элементов с единицей на выходе), `U` (число проводов
  с единицей, включая провода от входов), `P` (`P`-активность — число элементов с единицей
  на входе или выходе); максимальная и средняя меры `Emax`, `Eav`, `Umax`, `Uav`, `Pmax`, `Pav`;
* `opMeas μ F = min_{Σ = F} μ(Σ)`, функции Шеннона `EavSh n m`, `EmaxSh`, `PavSh`, `PmaxSh`,
  `UavSh`, `UmaxSh`;
* `frac n κ Q` — доля операторов со свойством `Q` («почти все» — доля стремится к 1);
* `h2` — двоичная энтропия (в битах), `parity`, `Mcap`, `Delta` (для `PowerBoundGeneral`).
-/

namespace PowerActivity

open Finset

/-- Операции базиса `B₀`. -/
inductive Op
  | and | or | not
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Op := ⟨{.and, .or, .not}, by intro x; cases x <;> simp⟩

lemma Op.card : Fintype.card Op = 3 := rfl

/-- Функция элемента (для `not` второй аргумент не используется). -/
def Op.eval : Op → Bool → Bool → Bool
  | .and, u, v => u && v
  | .or, u, v => u || v
  | .not, u, _ => !u

/-- Элемент: операция и номера сигналов-источников его входов
(у `not` используется только `a`; в конструкциях берём `b = a`). -/
structure Gate where
  op : Op
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Источники входов элемента — по одному на провод. -/
def Gate.srcs (g : Gate) : List ℕ :=
  match g.op with
  | .not => [g.a]
  | _ => [g.a, g.b]

/-- Значение сигнала `j` для списка элементов `gs` на наборе `x`. -/
def sig (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) : Bool :=
  if h : j < n then x ⟨j, h⟩
  else
    match gs[j - n]? with
    | none => false
    | some g =>
      if _hab : g.a < j ∧ g.b < j then Op.eval g.op (sig n gs x g.a) (sig n gs x g.b)
      else false
termination_by j
decreasing_by all_goals omega

/-- Схема из функциональных элементов с `n` входами и выходами, занумерованными `κ`. -/
structure Circ (n : ℕ) (κ : Type) where
  gates : List Gate
  valid : ∀ i (h : i < gates.length), gates[i].a < n + i ∧ gates[i].b < n + i
  out : κ → ℕ
  out_lt : ∀ k, out k < n + gates.length

namespace Circ

variable {n : ℕ} {κ : Type} (C : Circ n κ)

/-- Число элементов `L(Σ)`. -/
def s : ℕ := C.gates.length

/-- Элемент номер `i` (вне диапазона — элемент по умолчанию). -/
def gate (i : ℕ) : Gate := C.gates.getD i default

/-- Сигнал `j` на наборе `x`. -/
def sig (x : Fin n → Bool) (j : ℕ) : Bool := PowerActivity.sig n C.gates x j

/-- Выход элемента `i`, `φ_i(x)`. -/
def val (x : Fin n → Bool) (i : ℕ) : Bool := C.sig x (n + i)

/-- Оператор, вычисляемый схемой. -/
def eval (x : Fin n → Bool) : κ → Bool := fun k => C.sig x (C.out k)

/-- Схема реализует оператор `F`. -/
def Realizes (F : (Fin n → Bool) → κ → Bool) : Prop := ∀ x, C.eval x = F x

/-- Мощность на наборе: `E(Σ,x) = Σ_v φ_v(x)`. -/
def E (x : Fin n → Bool) : ℕ := ((range C.s).filter fun i => C.val x i = true).card

/-- Число проводов с единицей: `U(Σ,x) = Σ_e s_e(x)` (провода от входов учитываются). -/
def U (x : Fin n → Bool) : ℕ := ∑ i ∈ range C.s, (C.gate i).srcs.countP (C.sig x)

/-- `P`-активность: число элементов с единицей на выходе или хотя бы на одном входе. -/
def P (x : Fin n → Bool) : ℕ :=
  ((range C.s).filter fun i => C.val x i = true ∨ ∃ j ∈ (C.gate i).srcs, C.sig x j = true).card

end Circ

/-- Максимум меры по наборам. -/
def maxM {n : ℕ} (μ : (Fin n → Bool) → ℕ) : ℕ := univ.sup μ

/-- Среднее меры при равномерном распределении на `{0,1}ⁿ`. -/
noncomputable def avgM {n : ℕ} (μ : (Fin n → Bool) → ℕ) : ℝ := (∑ x, (μ x : ℝ)) / 2 ^ n

namespace Circ

variable {n : ℕ} {κ : Type} (C : Circ n κ)

def Emax : ℕ := maxM C.E
noncomputable def Eav : ℝ := avgM C.E
def Umax : ℕ := maxM C.U
noncomputable def Uav : ℝ := avgM C.U
def Pmax : ℕ := maxM C.P
noncomputable def Pav : ℝ := avgM C.P

end Circ

/-- `M(F) = min_{Σ : Σ = F} M(Σ)` (инфимум; для `n ≥ 1` множество схем непусто). -/
noncomputable def opMeas {n : ℕ} {κ : Type} (μ : Circ n κ → ℝ) (F : (Fin n → Bool) → κ → Bool) : ℝ :=
  ⨅ C : {C : Circ n κ // C.Realizes F}, μ C.1

/-- Функция Шеннона `M(n,m) = max_{F : {0,1}ⁿ → {0,1}ᵐ} M(F)`. -/
noncomputable def shMeas (n m : ℕ) (μ : Circ n (Fin m) → ℝ) : ℝ :=
  ⨆ F : (Fin n → Bool) → Fin m → Bool, opMeas μ F

noncomputable def EavSh (n m : ℕ) : ℝ := shMeas n m fun C => C.Eav
noncomputable def EmaxSh (n m : ℕ) : ℝ := shMeas n m fun C => (C.Emax : ℝ)
noncomputable def PavSh (n m : ℕ) : ℝ := shMeas n m fun C => C.Pav
noncomputable def PmaxSh (n m : ℕ) : ℝ := shMeas n m fun C => (C.Pmax : ℝ)
noncomputable def UavSh (n m : ℕ) : ℝ := shMeas n m fun C => C.Uav
noncomputable def UmaxSh (n m : ℕ) : ℝ := shMeas n m fun C => (C.Umax : ℝ)

/-- Доля операторов `{0,1}ⁿ → {0,1}^κ` со свойством `Q`. -/
noncomputable def frac (n : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (Q : ((Fin n → Bool) → κ → Bool) → Prop) : ℝ :=
  (Nat.card {F // Q F} : ℝ) / (Nat.card ((Fin n → Bool) → κ → Bool) : ℝ)

/-- Двоичная энтропия в битах (`0 log 0 = 0`, так как `logb 2 0 = 0`). -/
noncomputable def h2 (p : ℝ) : ℝ := -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

/-- Чётность набора. -/
def parity {n : ℕ} (x : Fin n → Bool) : Bool := decide ((univ.filter fun i => x i = true).card % 2 = 1)

/-- `M = min{m, 2^{2^n}}` (`PowerBoundGeneral`). -/
def Mcap (n m : ℕ) : ℕ := min m (2 ^ 2 ^ n)

/-- `Δ = max{1, n − log log (M+1)}` (`PowerBoundGeneral`). -/
noncomputable def Delta (n m : ℕ) : ℝ := max 1 ((n : ℝ) - Real.logb 2 (Real.logb 2 ((Mcap n m : ℝ) + 1)))

/-! ## Базовые факты о сигналах -/

lemma sig_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {j : ℕ} (h : j < n) :
    sig n gs x j = x ⟨j, h⟩ := by
  rw [sig]; simp [h]

/-- Сигнал элемента правильного списка: значение операции на сигналах источников. -/
lemma sig_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {i : ℕ} (hi : i < gs.length)
    (ha : gs[i].a < n + i) (hb : gs[i].b < n + i) :
    sig n gs x (n + i) = Op.eval gs[i].op (sig n gs x gs[i].a) (sig n gs x gs[i].b) := by
  rw [sig]
  have h1 : ¬ n + i < n := by omega
  have h2 : n + i - n = i := by omega
  simp only [h1, dite_false, h2]
  rw [List.getElem?_eq_getElem hi]
  simp only
  rw [dif_pos ⟨ha, hb⟩]

/-- За пределами списка сигнал равен `false`. -/
lemma sig_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {j : ℕ} (h : n + gs.length ≤ j) :
    sig n gs x j = false := by
  rw [sig]
  have h1 : ¬ j < n := by omega
  simp only [h1, dite_false]
  rw [List.getElem?_eq_none (by omega)]

/-- Дописывание элементов не меняет прежних сигналов. -/
lemma sig_append {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) :
    ∀ j, j < n + gs.length → sig n (gs ++ hs) x j = sig n gs x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases h : j < n
    · rw [sig_lt _ _ h, sig_lt _ _ h]
    · have hi : j - n < gs.length := by omega
      rw [sig, sig]
      simp only [h, dite_false]
      rw [List.getElem?_append_left hi]
      cases hg : gs[j - n]? with
      | none => rfl
      | some g =>
        simp only
        by_cases hab : g.a < j ∧ g.b < j
        · rw [dif_pos hab, dif_pos hab, ih _ hab.1 (by omega), ih _ hab.2 (by omega)]
        · rw [dif_neg hab, dif_neg hab]

namespace Circ

variable {n : ℕ} {κ : Type} (C : Circ n κ)

lemma sig_input (x : Fin n → Bool) (i : Fin n) : C.sig x i = x i := by
  simp [Circ.sig, sig_lt _ _ i.2]

lemma val_eq (x : Fin n → Bool) {i : ℕ} (hi : i < C.s) :
    C.val x i = Op.eval (C.gate i).op (C.sig x (C.gate i).a) (C.sig x (C.gate i).b) := by
  have hv := C.valid i hi
  have hg : C.gate i = C.gates[i] := by
    simp [Circ.gate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hg]
  exact sig_gate C.gates x hi hv.1 hv.2

lemma gate_a_lt {i : ℕ} (hi : i < C.s) : (C.gate i).a < n + i := by
  have hg : C.gate i = C.gates[i] := by
    simp [Circ.gate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hg]; exact (C.valid i hi).1

lemma gate_b_lt {i : ℕ} (hi : i < C.s) : (C.gate i).b < n + i := by
  have hg : C.gate i = C.gates[i] := by
    simp [Circ.gate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hg]; exact (C.valid i hi).2

lemma Eav_le_Emax : C.Eav ≤ C.Emax := by
  unfold Eav Emax avgM maxM
  rw [div_le_iff₀ (by positivity)]
  calc ∑ x, (C.E x : ℝ) ≤ ∑ _x : Fin n → Bool, ((univ.sup C.E : ℕ) : ℝ) := by
        gcongr with x; exact_mod_cast Finset.le_sup (f := C.E) (Finset.mem_univ x)
    _ = (univ.sup C.E : ℕ) * 2 ^ n := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, mul_comm]

end Circ

end PowerActivity
