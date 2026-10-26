import PowerActivity.LowParity

/-!
# Тезисы, цель `InflGoal`: влияние переменных и мощность (обобщение `parity`)

Для функции `f` и переменной `x_t` положим `D_t(f) = #{x : f(x) ≠ f(x^{(t)})}` (`Infl.dif`).
Если выход `k` схемы — не входная вершина `x_t`, то при каждом `x` с `f(x) ≠ f(x^{(t)})`
хотя бы один элемент из `I_t` (получающих `x_t` напрямую) меняет выход (`exists_change`;
как в `parity` — через `Low.sig_flip_eq`), откуда `D_t(f) ≤ 2 Σ_{i ∈ I_t} N p_i` (`dif_le`).
Каждый элемент лежит не более чем в двух `I_t`, поэтому `Σ_t D_t(f) ≤ 4 Σ_i N p_i = 4 N E(Σ)`
(`sum_dif_le`).

* `Infl.out_ne_input` — при `n ≥ 2` и `D_t(f) > 0` для всех `t` выход — не входная вершина;
* `Infl.infl_lower` — если `n ≥ 2` и `4 D_t(f) > N` при всех `t`, то `E(Σ) ≥ n/16`.
-/

namespace PowerActivity

open Finset

namespace Infl

/-- `D_t(f)` — число наборов, на которых `f` меняется при инвертировании `t`-й координаты. -/
def dif {n : ℕ} (f : (Fin n → Bool) → Bool) (t : Fin n) : ℕ :=
  (univ.filter fun x => f x ≠ f (Low.flip x t)).card

variable {n : ℕ} {κ : Type} (C : Circ n κ)

/-- Если выход `k` — не вершина `x_t`, то при `f(x) ≠ f(x^{(t)})` некоторый элемент из `I_t`
меняет выход. -/
lemma exists_change (k : κ) (t : Fin n) (hout : C.out k ≠ (t : ℕ)) (x : Fin n → Bool)
    (hx : C.eval x k ≠ C.eval (Low.flip x t) k) :
    ∃ i ∈ (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs),
      C.val x i ≠ C.val (Low.flip x t) i := by
  by_contra hcon
  push Not at hcon
  exact hx (Low.sig_flip_eq C x t (fun i hi hit => hcon i (by simp [hi, hit])) (C.out k) hout)

/-- Элемент меняет выход при `x → x^{(t)}` не более чем на `2 N p_i` наборах. -/
lemma card_change_le (t : Fin n) (i : ℕ) :
    (univ.filter fun x => C.val x i ≠ C.val (Low.flip x t) i).card ≤ 2 * C.lowW i := by
  calc (univ.filter fun x => C.val x i ≠ C.val (Low.flip x t) i).card
      ≤ ((univ.filter fun x : Fin n → Bool => C.val x i = true) ∪
          (univ.filter fun x : Fin n → Bool => C.val (Low.flip x t) i = true)).card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        simp only [mem_union, mem_filter, mem_univ, true_and]
        cases h1 : C.val x i <;> cases h2 : C.val (Low.flip x t) i <;> simp_all
    _ ≤ _ := card_union_le _ _
    _ = 2 * C.lowW i := by rw [Low.lowW_flip]; unfold Circ.lowW; ring

/-- `D_t(f) ≤ 2 Σ_{i ∈ I_t} N p_i`, если выход `k` — не вершина `x_t`. -/
lemma dif_le (k : κ) (t : Fin n) (hout : C.out k ≠ (t : ℕ)) :
    dif (fun x => C.eval x k) t ≤
      ∑ i ∈ (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs), 2 * C.lowW i := by
  set I := (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs)
  unfold dif
  calc (univ.filter fun x => C.eval x k ≠ C.eval (Low.flip x t) k).card
      = ∑ _x ∈ univ.filter (fun x => C.eval x k ≠ C.eval (Low.flip x t) k), 1 :=
        card_eq_sum_ones _
    _ ≤ ∑ x ∈ univ.filter (fun x => C.eval x k ≠ C.eval (Low.flip x t) k),
          (I.filter fun i => C.val x i ≠ C.val (Low.flip x t) i).card := by
        apply sum_le_sum
        intro x hx
        rw [mem_filter] at hx
        obtain ⟨i, hi, hne⟩ := exists_change C k t hout x hx.2
        exact card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hne⟩⟩
    _ ≤ ∑ x : Fin n → Bool, (I.filter fun i => C.val x i ≠ C.val (Low.flip x t) i).card :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ i ∈ I, (univ.filter fun x => C.val x i ≠ C.val (Low.flip x t) i).card := by
        simp only [card_filter]
        rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ I, 2 * C.lowW i := sum_le_sum fun i _ => card_change_le C t i

/-- `Σ_t D_t(f) ≤ 4 Σ_i N p_i`, если выход `k` — не входная вершина. -/
lemma sum_dif_le (k : κ) (hout : ∀ t : Fin n, C.out k ≠ (t : ℕ)) :
    ∑ t : Fin n, dif (fun x => C.eval x k) t ≤ 4 * ∑ i ∈ range C.s, C.lowW i := by
  calc ∑ t : Fin n, dif (fun x => C.eval x k) t
      ≤ ∑ t : Fin n, ∑ i ∈ (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs),
            2 * C.lowW i := sum_le_sum fun t _ => dif_le C k t (hout t)
    _ = ∑ i ∈ range C.s, (univ.filter fun t : Fin n => (t : ℕ) ∈ (C.gate i).srcs).card *
          (2 * C.lowW i) := by
        simp only [sum_filter]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_filter, sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ range C.s, 2 * (2 * C.lowW i) :=
        sum_le_sum fun i _ => Nat.mul_le_mul_right _ (Low.card_srcs_le C i)
    _ = 4 * ∑ i ∈ range C.s, C.lowW i := by rw [mul_sum]; ring_nf

/-- Если `n ≥ 2` и `D_t(f) > 0` при всех `t`, то выход `k` — не входная вершина
(у проекции `x_t` при `t' ≠ t` `D_{t'} = 0`). -/
lemma out_ne_input (hn : 2 ≤ n) (k : κ) (hpos : ∀ t, 0 < dif (fun x => C.eval x k) t)
    (t : Fin n) : C.out k ≠ (t : ℕ) := by
  intro hot
  obtain ⟨t', htt⟩ : ∃ t' : Fin n, t ≠ t' := by
    by_cases h0 : (t : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have := congrArg Fin.val h
      simp only at this
      omega
    · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
      have := congrArg Fin.val h
      simp only at this
      omega
  have h0 := hpos t'
  unfold dif at h0
  obtain ⟨x, hx⟩ := card_pos.mp h0
  rw [mem_filter] at hx
  apply hx.2
  simp only [Circ.eval, hot, Circ.sig_input, Low.flip]
  rw [Function.update_of_ne htt]

/-- **Обобщение `parity`.** Если `n ≥ 2` и для координаты `k` при всех `t` выполнено
`4 D_t(f) > N`, то `E(Σ) ≥ n/16`. -/
theorem infl_lower (hn : 2 ≤ n) (k : κ) (h : ∀ t, 2 ^ n < 4 * dif (fun x => C.eval x k) t) :
    (n : ℝ) / 16 ≤ C.Eav := by
  have hout := out_ne_input C hn k (fun t => by
    have h1 := h t
    have h2 : 0 < 2 ^ n := by positivity
    omega)
  have h1 : n * 2 ^ n ≤ 4 * ∑ t : Fin n, dif (fun x => C.eval x k) t := by
    calc n * 2 ^ n = ∑ _t : Fin n, 2 ^ n := by simp
      _ ≤ ∑ t : Fin n, 4 * dif (fun x => C.eval x k) t := sum_le_sum fun t _ => (h t).le
      _ = 4 * ∑ t : Fin n, dif (fun x => C.eval x k) t := by rw [mul_sum]
  have key : n * 2 ^ n ≤ 16 * ∑ i ∈ range C.s, C.lowW i :=
    calc n * 2 ^ n ≤ 4 * ∑ t : Fin n, dif (fun x => C.eval x k) t := h1
      _ ≤ 4 * (4 * ∑ i ∈ range C.s, C.lowW i) := Nat.mul_le_mul_left 4 (sum_dif_le C k hout)
      _ = 16 * ∑ i ∈ range C.s, C.lowW i := by ring
  rw [Circ.low_Eav_eq, le_div_iff₀ (by positivity)]
  have : ((n * 2 ^ n : ℕ) : ℝ) ≤ ((16 * ∑ i ∈ range C.s, C.lowW i : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at this
  linarith

end Infl

end PowerActivity
