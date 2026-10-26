import PowerActivity.Spec

/-!
# Энтропия и среднее число единиц (`entropy`)

Для `Z : {0,1}ⁿ → {0,1}^ι` (`ι` — конечный тип), `pᵢ = P{Zᵢ(X) = 1}`, `A = Σ pᵢ`, `q = |ι|`:

* `ent_le_sum_ent` — субаддитивность `H(Z) ≤ Σ H(Zᵢ)` (через `log y ≤ y − 1` для отношения
  произведения маргиналов к совместному распределению);
* `ent_bool` — для битовой величины `H(W) = h₂(P{W = 1})`;
* `h2_le` — `h₂(p) ≤ tp + log(1 + 2^{−t})` (вогнутость логарифма);
* `entropy_bound` — `H(Z) ≤ Σ h₂(pᵢ) ≤ tA + q log(1 + 2^{−t})` при `t ≥ 0`;
* `entropy_bound_simple` — `H(Z) ≤ A log(2q) + 1` (интересен случай `q ≥ 1`; при `q = 0`
  тоже верно, так как тогда `H(Z) = 0`).
-/

namespace PowerActivity

open Finset

namespace Act

variable {n : ℕ}

lemma card_univ_input : (univ : Finset (Fin n → Bool)).card = 2 ^ n := by
  simp

lemma probZ_nonneg {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) (z : α) :
    0 ≤ probZ Z z := by
  unfold probZ; positivity

lemma probZ_le_one {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) (z : α) :
    probZ Z z ≤ 1 := by
  unfold probZ
  rw [div_le_one (by positivity)]
  have h := Finset.card_le_card (Finset.filter_subset (fun x => Z x = z) univ)
  rw [card_univ_input] at h
  exact_mod_cast h

lemma probZ_pos {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) (x : Fin n → Bool) :
    0 < probZ Z (Z x) := by
  unfold probZ
  apply div_pos _ (by positivity)
  exact_mod_cast Finset.card_pos.2 ⟨x, by simp⟩

lemma probZ_eq_zero {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) (z : α)
    (hz : z ∉ univ.image Z) : probZ Z z = 0 := by
  unfold probZ
  have : univ.filter (fun x => Z x = z) = ∅ := by
    ext x
    simp only [mem_image, mem_univ, true_and, not_exists] at hz
    simp [hz x]
  simp [this]

/-- Сумма по образу с весами `P{Z = z}` равна среднему по наборам. -/
lemma sum_image_probZ_mul {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) (g : α → ℝ) :
    ∑ z ∈ univ.image Z, probZ Z z * g z = (∑ x, g (Z x)) / 2 ^ n := by
  rw [Finset.sum_comp g Z, Finset.sum_div]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [nsmul_eq_mul]; unfold probZ; ring

/-- `H(Z) = −E log P{Z = Z(X)}`. -/
lemma ent_eq_avg {α : Type} [DecidableEq α] (Z : (Fin n → Bool) → α) :
    ent Z = -(∑ x, Real.logb 2 (probZ Z (Z x))) / 2 ^ n := by
  unfold ent
  rw [sum_image_probZ_mul Z (fun z => Real.logb 2 (probZ Z z))]
  ring

/-- Энтропия как сумма по всем значениям (для конечного типа значений). -/
lemma ent_eq_sum_univ {α : Type} [Fintype α] [DecidableEq α] (Z : (Fin n → Bool) → α) :
    ent Z = -∑ z, probZ Z z * Real.logb 2 (probZ Z z) := by
  unfold ent
  congr 1
  apply Finset.sum_subset (subset_univ _)
  intro z _ hz
  rw [probZ_eq_zero Z z hz]; simp

lemma probZ_bool_add (W : (Fin n → Bool) → Bool) : probZ W true + probZ W false = 1 := by
  unfold probZ
  rw [← add_div, div_eq_one_iff_eq (by positivity)]
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n → Bool))) (fun x => W x = true)
  have h2 : univ.filter (fun x => ¬ W x = true) = univ.filter (fun x => W x = false) := by
    ext x; simp
  rw [h2, card_univ_input] at h
  exact_mod_cast h

/-- Энтропия битовой величины: `H(W) = h₂(P{W = 1})`. -/
lemma ent_bool (W : (Fin n → Bool) → Bool) : ent W = h2 (probZ W true) := by
  rw [ent_eq_sum_univ]
  have h := probZ_bool_add W
  have hf : probZ W false = 1 - probZ W true := by linarith
  rw [Fintype.sum_bool, hf]
  unfold h2
  ring

/-- Субаддитивность энтропии: `H(Z) ≤ Σᵢ H(Zᵢ)`. -/
theorem ent_le_sum_ent {ι : Type} [Fintype ι] [DecidableEq (ι → Bool)]
    (Z : (Fin n → Bool) → ι → Bool) : ent Z ≤ ∑ i, ent (fun x => Z x i) := by
  classical
  have hNpos : (0 : ℝ) < 2 ^ n := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- маргиналы и их произведение
  set q : ι → Bool → ℝ := fun i b => probZ (fun x => Z x i) b with hq
  set a : (ι → Bool) → ℝ := fun z => ∏ i, q i (z i) with ha
  have hqpos : ∀ x i, 0 < q i (Z x i) := fun x i => probZ_pos (fun x => Z x i) x
  have hapos : ∀ x, 0 < a (Z x) := fun x => Finset.prod_pos fun i _ => hqpos x i
  have ha0 : ∀ z, 0 ≤ a z := fun z =>
    Finset.prod_nonneg fun i _ => probZ_nonneg (fun x => Z x i) (z i)
  have hPpos : ∀ x, 0 < probZ Z (Z x) := fun x => probZ_pos Z x
  -- сумма произведений маргиналов по всем словам равна 1
  have hsum1 : ∑ z : ι → Bool, a z = 1 := by
    have e : ∑ z : ι → Bool, a z = ∏ i, ∑ b, q i b := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [e]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Fintype.sum_bool]
    exact probZ_bool_add (fun x => Z x i)
  -- `Σₓ a(Z x)/P(Z x) = 2ⁿ Σ_{z ∈ образ} a z ≤ 2ⁿ`
  have hratio : ∑ x, a (Z x) / probZ Z (Z x) ≤ 2 ^ n := by
    have e := sum_image_probZ_mul Z (fun z => a z / probZ Z z)
    have e2 : ∑ z ∈ univ.image Z, probZ Z z * (a z / probZ Z z) = ∑ z ∈ univ.image Z, a z := by
      refine Finset.sum_congr rfl fun z hz => ?_
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
      field_simp [(hPpos x).ne']
    rw [e2] at e
    have hle : ∑ z ∈ univ.image Z, a z ≤ 1 := by
      rw [← hsum1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => ha0 z
    have : (∑ x, a (Z x) / probZ Z (Z x)) = 2 ^ n * ∑ z ∈ univ.image Z, a z := by
      rw [e]; field_simp
    rw [this]
    nlinarith
  -- поточечная оценка `Σᵢ log qᵢ − log P ≤ a/P − 1`
  have hpt : ∀ x, ∑ i, Real.log (q i (Z x i)) - Real.log (probZ Z (Z x)) ≤
      a (Z x) / probZ Z (Z x) - 1 := by
    intro x
    rw [← Real.log_prod (fun i _ => (hqpos x i).ne'), ← Real.log_div (hapos x).ne' (hPpos x).ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hapos x) (hPpos x))
  -- сборка
  have hi : ∀ i, ent (fun x => Z x i) = -(∑ x, Real.log (q i (Z x i))) / Real.log 2 / 2 ^ n := by
    intro i
    rw [ent_eq_avg]
    unfold Real.logb
    rw [← Finset.sum_div]
    simp only [hq]
    ring
  have hL : ent Z = -(∑ x, Real.log (probZ Z (Z x))) / Real.log 2 / 2 ^ n := by
    rw [ent_eq_avg]; unfold Real.logb; rw [← Finset.sum_div]; ring
  have hR : ∑ i, ent (fun x => Z x i) =
      -(∑ x, ∑ i, Real.log (q i (Z x i))) / Real.log 2 / 2 ^ n := by
    simp_rw [hi]
    rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_comm]
  rw [hL, hR]
  apply div_le_div_of_nonneg_right _ hNpos.le
  apply div_le_div_of_nonneg_right _ hl2.le
  have hsumpt := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset (Fin n → Bool))) => hpt x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsumpt
  simp only [sum_const, card_univ_input, nsmul_eq_mul, mul_one] at hsumpt
  push_cast at hsumpt
  linarith

/-- `h₂(p) ≤ tp + log(1 + 2^{−t})` при `0 ≤ p ≤ 1`, `t ≥ 0`. -/
lemma h2_le (p t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    h2 p ≤ t * p + Real.logb 2 (1 + (2 : ℝ) ^ (-t)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set u : ℝ := (2 : ℝ) ^ (-t) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos two_pos _
  have hlogu : Real.log u = -t * Real.log 2 := Real.log_rpow two_pos _
  have hS : 0 ≤ Real.logb 2 (1 + u) := Real.logb_nonneg one_lt_two (by linarith)
  rcases hp0.eq_or_lt with rfl | hp0'
  · simp [h2]; exact hS
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp [h2]; linarith
  have hq : 0 < 1 - p := by linarith
  have key := strictConcaveOn_log_Ioi.concaveOn.2 (x := u / p) (y := 1 / (1 - p))
    (Set.mem_Ioi.2 (div_pos hu0 hp0')) (Set.mem_Ioi.2 (div_pos one_pos hq)) hp0'.le hq.le
    (by ring)
  simp only [smul_eq_mul] at key
  have e1 : p * (u / p) + (1 - p) * (1 / (1 - p)) = 1 + u := by
    field_simp; ring
  rw [e1, Real.log_div hu0.ne' hp0'.ne', Real.log_div one_ne_zero hq.ne', Real.log_one,
    hlogu] at key
  unfold h2 Real.logb
  rw [← sub_nonneg]
  have e2 : t * p + Real.log (1 + u) / Real.log 2 -
      (-p * (Real.log p / Real.log 2) - (1 - p) * (Real.log (1 - p) / Real.log 2)) =
      (Real.log (1 + u) - (p * (-t * Real.log 2 - Real.log p) + (1 - p) * (0 - Real.log (1 - p))))
        / Real.log 2 := by
    field_simp; ring
  rw [e2]
  exact div_nonneg (by linarith) hl2.le

/-- **`entropy`, первая оценка.** `H(Z) ≤ Σ h₂(pᵢ) ≤ tA + q log(1 + 2^{−t})` при `t ≥ 0`. -/
theorem entropy_bound {ι : Type} [Fintype ι] [DecidableEq (ι → Bool)]
    (Z : (Fin n → Bool) → ι → Bool) (t : ℝ) (ht : 0 ≤ t) :
    ent Z ≤ ∑ i, h2 (probZ (fun x => Z x i) true) ∧
    ∑ i, h2 (probZ (fun x => Z x i) true) ≤
      t * ∑ i, probZ (fun x => Z x i) true +
        Fintype.card ι * Real.logb 2 (1 + (2 : ℝ) ^ (-t)) := by
  constructor
  · calc ent Z ≤ ∑ i, ent (fun x => Z x i) := ent_le_sum_ent Z
      _ = ∑ i, h2 (probZ (fun x => Z x i) true) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact ent_bool (fun x => Z x i)
  · calc ∑ i, h2 (probZ (fun x => Z x i) true)
        ≤ ∑ i, (t * probZ (fun x => Z x i) true + Real.logb 2 (1 + (2 : ℝ) ^ (-t))) :=
          Finset.sum_le_sum fun i _ =>
            h2_le _ _ (probZ_nonneg _ _) (probZ_le_one _ _) ht
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]

/-- **`entropy`, вторая оценка.** `H(Z) ≤ A log(2q) + 1`
(интересен случай `q ≥ 1`; при `q = 0` правая часть равна `1`, а `H(Z) = 0`). -/
theorem entropy_bound_simple {ι : Type} [Fintype ι] [DecidableEq (ι → Bool)]
    (Z : (Fin n → Bool) → ι → Bool) :
    ent Z ≤ (∑ i, probZ (fun x => Z x i) true) * Real.logb 2 (2 * Fintype.card ι) + 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hq | hq
  · have := Fintype.card_eq_zero_iff.1 hq
    have h := (entropy_bound Z 0 le_rfl).1
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_mul, zero_add] at h ⊢
    linarith
  · set t := Real.logb 2 (2 * Fintype.card ι) with htdef
    have hq1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hq
    have ht : 0 ≤ t := Real.logb_nonneg one_lt_two (by linarith)
    obtain ⟨h1, h2'⟩ := entropy_bound Z t ht
    have hu : (2 : ℝ) ^ (-t) = 1 / (2 * Fintype.card ι) := by
      rw [Real.rpow_neg (by norm_num), htdef,
        Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      ring
    have hlog : (Fintype.card ι : ℝ) * Real.logb 2 (1 + (2 : ℝ) ^ (-t)) ≤ 1 := by
      rw [hu]
      unfold Real.logb
      have hlt := Real.log_le_sub_one_of_pos (x := 1 + 1 / (2 * (Fintype.card ι : ℝ)))
        (by positivity)
      have hl2 := Real.log_two_gt_d9
      have hl2p : 0 < Real.log 2 := Real.log_pos one_lt_two
      rw [mul_div_assoc', div_le_one hl2p]
      calc (Fintype.card ι : ℝ) * Real.log (1 + 1 / (2 * Fintype.card ι))
          ≤ Fintype.card ι * (1 / (2 * Fintype.card ι)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        _ = 1 / 2 := by field_simp
        _ ≤ Real.log 2 := by norm_num at hl2 ⊢; linarith
    rw [mul_comm] at h2'
    linarith

end Act

end PowerActivity
