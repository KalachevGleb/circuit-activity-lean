import PowerActivity.Spec

/-!
# Типичное множество значений случайной величины

Неравенство Маркова для `-log P{Z = Z(X)}` (шаг доказательства `cut-compress`):
для любой `Z : {0,1}ⁿ → α` множество `T = {z : -log P{Z=z} ≤ 4H(Z)}` удовлетворяет
`|T| ≤ 2^{4H}` и `P{Z ∈ T} ≥ 3/4`. Случай `H = 0` разбирается той же оценкой
(тогда `T` — всё множество значений).
-/

namespace PowerActivity.Apx

open Finset

variable {n : ℕ} {α : Type} [DecidableEq α]

lemma probZ_nonneg (Z : (Fin n → Bool) → α) (z : α) : 0 ≤ probZ Z z := by
  unfold probZ; positivity

lemma probZ_pos (Z : (Fin n → Bool) → α) {z : α} (hz : z ∈ univ.image Z) : 0 < probZ Z z := by
  unfold probZ
  obtain ⟨x, -, hx⟩ := mem_image.1 hz
  have : 0 < (univ.filter fun y => Z y = z).card :=
    card_pos.2 ⟨x, by simp [hx]⟩
  positivity

lemma probZ_le_one (Z : (Fin n → Bool) → α) (z : α) : probZ Z z ≤ 1 := by
  unfold probZ
  rw [div_le_one (by positivity)]
  have : (univ.filter fun y => Z y = z).card ≤ 2 ^ n := by
    calc (univ.filter fun y => Z y = z).card ≤ (univ : Finset (Fin n → Bool)).card :=
          card_le_card (filter_subset _ _)
      _ = 2 ^ n := by simp
  exact_mod_cast this

lemma sum_probZ (Z : (Fin n → Bool) → α) : ∑ z ∈ univ.image Z, probZ Z z = 1 := by
  unfold probZ
  rw [← sum_div, div_eq_one_iff_eq (by positivity)]
  have h := card_eq_sum_card_image Z (univ : Finset (Fin n → Bool))
  have h2 : (univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [h2] at h
  exact_mod_cast h.symm

/-- Число наборов `x` с `Z x ∈ U` (для `U ⊆ image Z`) — сумма вероятностей, умноженная на `2ⁿ`. -/
lemma card_mem_eq (Z : (Fin n → Bool) → α) (U : Finset α) :
    ((univ.filter fun x => Z x ∈ U).card : ℝ) = 2 ^ n * ∑ z ∈ U, probZ Z z := by
  have h := card_eq_sum_card_fiberwise (f := Z) (s := univ.filter fun x => Z x ∈ U) (t := U)
    (by intro x hx; simpa using hx)
  rw [h]
  unfold probZ
  rw [← sum_div, mul_div_cancel₀ _ (by positivity)]
  push_cast
  apply sum_congr rfl
  intro z hz
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨h ▸ hz, h⟩

lemma negMulLogb_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ -(p * Real.logb 2 p) := by
  have := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) h0 h1
  nlinarith

lemma ent_eq (Z : (Fin n → Bool) → α) :
    ent Z = ∑ z ∈ univ.image Z, -(probZ Z z * Real.logb 2 (probZ Z z)) := by
  unfold ent; rw [sum_neg_distrib]

lemma ent_nonneg (Z : (Fin n → Bool) → α) : 0 ≤ ent Z := by
  rw [ent_eq]
  exact sum_nonneg fun z _ => negMulLogb_nonneg (probZ_nonneg Z z) (probZ_le_one Z z)

/-- Типичное множество: `|T| ≤ 2^{4H(Z)}` и `Z ∈ T` не менее чем на `3/4` наборов. -/
theorem exists_typical (Z : (Fin n → Bool) → α) :
    ∃ T : Finset α, (T.card : ℝ) ≤ (2 : ℝ) ^ (4 * ent Z) ∧
      3 * 2 ^ n ≤ 4 * (univ.filter fun x => Z x ∈ T).card := by
  set Im := univ.image Z with hIm
  set H := ent Z with hH
  set T := Im.filter fun z => -Real.logb 2 (probZ Z z) ≤ 4 * H with hT
  set U := Im.filter fun z => ¬ (-Real.logb 2 (probZ Z z) ≤ 4 * H) with hU
  refine ⟨T, ?_, ?_⟩
  · -- |T| ≤ 2^{4H}
    have hlow : ∀ z ∈ T, (2 : ℝ) ^ (-(4 * H)) ≤ probZ Z z := by
      intro z hz
      simp only [hT, mem_filter] at hz
      rw [← Real.le_logb_iff_rpow_le (by norm_num) (probZ_pos Z hz.1)]
      linarith [hz.2]
    have hsum : (T.card : ℝ) * (2 : ℝ) ^ (-(4 * H)) ≤ 1 := by
      calc (T.card : ℝ) * (2 : ℝ) ^ (-(4 * H)) = ∑ _z ∈ T, (2 : ℝ) ^ (-(4 * H)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ z ∈ T, probZ Z z := sum_le_sum hlow
        _ ≤ ∑ z ∈ Im, probZ Z z :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun z _ _ => probZ_nonneg Z z
        _ = 1 := sum_probZ Z
    have hp : (0 : ℝ) < (2 : ℝ) ^ (4 * H) := by positivity
    have hmul : (2 : ℝ) ^ (-(4 * H)) * (2 : ℝ) ^ (4 * H) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    calc (T.card : ℝ) = (T.card : ℝ) * (2 : ℝ) ^ (-(4 * H)) * (2 : ℝ) ^ (4 * H) := by
          rw [mul_assoc, hmul, mul_one]
      _ ≤ 1 * (2 : ℝ) ^ (4 * H) := mul_le_mul_of_nonneg_right hsum hp.le
      _ = (2 : ℝ) ^ (4 * H) := one_mul _
  · -- P{Z ∉ T} ≤ 1/4
    have hUsum : ∑ z ∈ U, probZ Z z ≤ 1 / 4 := by
      rcases U.eq_empty_or_nonempty with hUe | hUne
      · rw [hUe, sum_empty]; norm_num
      · have hlt : ∑ z ∈ U, probZ Z z * (4 * H) < ∑ z ∈ U, -(probZ Z z * Real.logb 2 (probZ Z z)) := by
          apply sum_lt_sum_of_nonempty hUne
          intro z hz
          simp only [hU, mem_filter] at hz
          have hp := probZ_pos Z hz.1
          have : 4 * H < -Real.logb 2 (probZ Z z) := lt_of_not_ge hz.2
          nlinarith
        have hle : ∑ z ∈ U, -(probZ Z z * Real.logb 2 (probZ Z z)) ≤ H := by
          rw [hH, ent_eq]
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun z _ _ =>
            negMulLogb_nonneg (probZ_nonneg Z z) (probZ_le_one Z z)
        rw [← sum_mul] at hlt
        have hS0 : 0 ≤ ∑ z ∈ U, probZ Z z := sum_nonneg fun z _ => probZ_nonneg Z z
        have hH0 : 0 ≤ H := ent_nonneg Z
        have h1 : (∑ z ∈ U, probZ Z z) * (4 * H) < H := lt_of_lt_of_le hlt hle
        have hHpos : 0 < H := by nlinarith
        nlinarith
    -- разбиение наборов: Z x ∈ T или Z x ∈ U
    have hsplit : (univ.filter fun x => Z x ∈ T).card + (univ.filter fun x => Z x ∈ U).card =
        2 ^ n := by
      rw [← card_union_of_disjoint]
      · have : (univ.filter fun x => Z x ∈ T) ∪ (univ.filter fun x => Z x ∈ U) = univ := by
          ext x
          simp only [mem_union, mem_filter, mem_univ, true_and, hT, hU, hIm, mem_image,
            exists_apply_eq_apply, iff_true]
          tauto
        rw [this]; simp
      · rw [disjoint_filter]
        intro x _ h1 h2
        simp only [hT, hU, mem_filter] at h1 h2
        exact h2.2 h1.2
    have hUc := card_mem_eq Z U
    have h4 : 4 * ((univ.filter fun x => Z x ∈ U).card : ℝ) ≤ 2 ^ n := by
      rw [hUc]
      have : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith
    have h4' : 4 * (univ.filter fun x => Z x ∈ U).card ≤ 2 ^ n := by exact_mod_cast h4
    omega

end PowerActivity.Apx
