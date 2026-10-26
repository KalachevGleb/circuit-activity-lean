import PowerActivity.Defs

/-!
# Нижние оценки мощности: общие леммы о модели

(Имена в пространствах `Gate`, `Circ` — с префиксом `low`, чтобы не пересекаться
с другими модулями.)

* `Gate.lowA_mem`, `Gate.lowB_mem`, `Gate.low_srcs_len`, `Gate.low_mem_srcs` — источники элемента;
* `Gate.low_eval_congr` — значение элемента не зависит от второго аргумента у `¬`;
* `Circ.lowW C i` — число наборов, на которых элемент `i` выдаёт единицу (`N p_i`);
  `Circ.lowP C i = p_i`;
* `Circ.low_sum_E`, `Circ.low_Eav_eq`, `Circ.low_Eav_eq_sumP` — `Σ_x E(Σ,x) = Σ_i N p_i`,
  `E(Σ) = Σ_i p_i`.
-/

namespace PowerActivity

open Finset

lemma Gate.lowA_mem (g : Gate) : g.a ∈ g.srcs := by
  rcases g with ⟨op, a, b⟩; cases op <;> simp [Gate.srcs]

lemma Gate.lowB_mem (g : Gate) (h : g.op ≠ .not) : g.b ∈ g.srcs := by
  rcases g with ⟨op, a, b⟩; cases op <;> simp_all [Gate.srcs]

lemma Gate.low_srcs_len (g : Gate) : g.srcs.length ≤ 2 := by
  rcases g with ⟨op, a, b⟩; cases op <;> simp [Gate.srcs]

lemma Gate.low_mem_srcs {g : Gate} {j : ℕ} (h : j ∈ g.srcs) :
    j = g.a ∨ (g.op ≠ .not ∧ j = g.b) := by
  rcases g with ⟨op, a, b⟩; cases op <;> simp_all [Gate.srcs]

/-- У `¬` второй аргумент не используется. -/
lemma Gate.low_eval_congr (g : Gate) {u u' v v' : Bool} (hu : u = u')
    (hv : g.op ≠ .not → v = v') : Op.eval g.op u v = Op.eval g.op u' v' := by
  rcases g with ⟨op, a, b⟩; subst hu; cases op <;> simp_all [Op.eval]

namespace Circ

variable {n : ℕ} {κ : Type} (C : Circ n κ)

/-- Число наборов, на которых элемент `i` выдаёт единицу (вес таблицы `φ_i`, равный `N p_i`). -/
def lowW (i : ℕ) : ℕ := (univ.filter fun x : Fin n → Bool => C.val x i = true).card

lemma lowW_le (i : ℕ) : C.lowW i ≤ 2 ^ n := by
  unfold lowW
  calc _ ≤ (univ : Finset (Fin n → Bool)).card := card_filter_le _ _
    _ = 2 ^ n := by simp

lemma low_sum_E : ∑ x, C.E x = ∑ i ∈ range C.s, C.lowW i := by
  unfold Circ.E lowW
  simp only [card_filter]
  rw [Finset.sum_comm]

lemma low_Eav_eq : C.Eav = (∑ i ∈ range C.s, (C.lowW i : ℝ)) / 2 ^ n := by
  unfold Circ.Eav avgM
  congr 1
  rw [← Nat.cast_sum, ← Nat.cast_sum, low_sum_E]

/-- `p_i = P{φ_i(X) = 1}`. -/
noncomputable def lowP (i : ℕ) : ℝ := (C.lowW i : ℝ) / 2 ^ n

lemma lowP_nonneg (i : ℕ) : 0 ≤ C.lowP i := by unfold lowP; positivity

lemma lowP_le_one (i : ℕ) : C.lowP i ≤ 1 := by
  unfold lowP
  rw [div_le_one (by positivity)]
  exact_mod_cast C.lowW_le i

lemma low_Eav_eq_sumP : C.Eav = ∑ i ∈ range C.s, C.lowP i := by
  rw [low_Eav_eq, sum_div]; rfl

end Circ

end PowerActivity
