import PowerActivity.ActCore

/-!
# Нижняя оценка активности одной функции: сводный модуль

Итог: `act_lower_of : ApproxHardGoal → CutCompressGoal → ActLowerGoal` — для почти всех функций
`f : {0,1}ⁿ → {0,1}` любая реализующая схема имеет `U(Σ) ≥ c n log n` и `P(Σ) ≥ c n log n`
с `c = ln 2 / 384` (`approx-hard` и `cut-compress` здесь — гипотезы, они доказаны в модулях `Apx*`).

Цепочка: `fanout` (исходящие степени `≤ 3`, `U(Σ*) = 3U(Σ)`) → `cut-compress` и `approx-hard` дают
`a 2ⁿ/n ≤ K|B_d| 2^{4H_d}` → с `fwd-balls`: `H_d ≥ n/8` при `d ≤ n/8` → `entropy`:
`H_d ≤ A_d log(2|R_d|) + 1` → `A_d ≥ (n/32)/(α + d)` → `cut-sum` и суммирование по `d`
(`harmonic`): `U(Σ*) ≥ n ln n/64` → `U(Σ) ≥ n ln n/192` → `wires`: `P(Σ) ≥ U(Σ)/2 ≥ n ln n/384`.

Удалять элементы, не лежащие на путях к выходу, для этой оценки не нужно: `fanout`,
`cut-compress` (в формулировке `CutCompressGoal`) и `U ≤ 2P` верны для любой схемы.
-/

namespace PowerActivity

open Finset Filter Topology

namespace Act

lemma frac_nonneg' {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (Q : ((Fin n → Bool) → κ → Bool) → Prop) : 0 ≤ frac n κ Q := by
  unfold frac; positivity

lemma frac_mono' {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    {Q Q' : ((Fin n → Bool) → κ → Bool) → Prop} (h : ∀ F, Q F → Q' F) :
    frac n κ Q ≤ frac n κ Q' := by
  unfold frac
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := Nat.card_mono (Set.toFinite {F | Q' F}) (fun F (hF : Q F) => h F hF)
  exact_mod_cast this

end Act

open Act

/-- **Нижняя оценка активности одной функции** (для `ActivityBound`, `WireBound` и теоремы 2
тезисов). При целях `approx-hard` и `cut-compress` для почти всех функций любая
реализующая схема имеет `U(Σ) ≥ c n log n` и `P(Σ) ≥ c n log n`, `c = ln 2/384`. -/
theorem act_lower_of (h9 : ApproxHardGoal) (h10 : CutCompressGoal) : ActLowerGoal := by
  obtain ⟨a, ha, ε₉, hε₉, h9n⟩ := h9
  obtain ⟨C₄, h10n⟩ := h10
  set K : ℝ := max C₄ 1 with hKdef
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K₁ : ℝ := 1 + Real.logb 2 K - Real.logb 2 a with hK₁
  -- порог по `n`
  have hev : ∀ᶠ n : ℕ in atTop, (16 : ℝ) ≤ n ∧ 8 * Real.logb 2 n + 4 * K₁ ≤ n ∧
      4 * Real.logb 2 n + 16 ≤ Real.sqrt n := by
    filter_upwards [ev_log_le_sqrt (max 8 (4 * K₁) + 16), eventually_ge_atTop 16] with n h1 h2
    have h16 : (16 : ℝ) ≤ n := by exact_mod_cast h2
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by linarith)
    have hm8 : (8 : ℝ) ≤ max 8 (4 * K₁) := le_max_left _ _
    have hmK : 4 * K₁ ≤ max 8 (4 * K₁) := le_max_right _ _
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
    have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by linarith)
    have hsn : Real.sqrt n ≤ n := by nlinarith
    refine ⟨h16, ?_, ?_⟩
    · nlinarith
    · nlinarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨Real.log 2 / 384, by positivity, fun n => if n < N₀ then 1 else ε₉ n, ?_, ?_⟩
  · apply hε₉.congr'
    filter_upwards [eventually_ge_atTop N₀] with n hn
    simp [not_lt.2 hn]
  · intro n
    by_cases hn : n < N₀
    · simp only [hn, ↓reduceIte, sub_self]
      exact frac_nonneg' _
    · simp only [hn, ↓reduceIte]
      refine (h9n n).trans (frac_mono' ?_)
      intro F hF C hC
      obtain ⟨hE2, hE1, hE3⟩ := hN₀ n (not_lt.1 hn)
      have hn1 : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
      have hC' : (fanout C).Realizes F := fun x => (fanout_eval C x).trans (hC x)
      have hH : ∀ d, a * 2 ^ n / n ≤
          K * ((fanout C).fwdBall d).card * (2 : ℝ) ^ (4 * ent ((fanout C).cutVal d)) := by
        intro d
        obtain ⟨C'', hap, hs⟩ := h10n n hn1 (fanout C) (fanout_outdeg C) F hC' d
        calc a * 2 ^ n / n ≤ C''.s := hF C'' hap
          _ ≤ C₄ * ((fanout C).fwdBall d).card * (2 : ℝ) ^ (4 * ent ((fanout C).cutVal d)) := hs
          _ ≤ K * ((fanout C).fwdBall d).card * (2 : ℝ) ^ (4 * ent ((fanout C).cutVal d)) := by
              gcongr; exact le_max_left _ _
      have hU := Uav_lower_core ha hK (fanout C) (fanout_outdeg C) hH hE1 hE2 hE3
      rw [fanout_Uav] at hU
      have hP := Uav_le_two_Pav C
      have hn0 : (0 : ℝ) < n := by linarith
      have hlog0 : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg hn0.le (Real.log_nonneg (by linarith))
      have hl : Real.log 2 / 384 * n * Real.logb 2 n = n * Real.log n / 384 := by
        unfold Real.logb; field_simp
      rw [hl]
      constructor <;> linarith

/-! ## Сводка утверждений о нижней оценке активности -/

section Summary

variable {n : ℕ} {κ : Type}

/-- `entropy`, первая оценка. -/
theorem act_entropy {ι : Type} [Fintype ι] [DecidableEq (ι → Bool)]
    (Z : (Fin n → Bool) → ι → Bool) (t : ℝ) (ht : 0 ≤ t) :
    ent Z ≤ ∑ i, h2 (probZ (fun x => Z x i) true) ∧
    ∑ i, h2 (probZ (fun x => Z x i) true) ≤
      t * ∑ i, probZ (fun x => Z x i) true +
        Fintype.card ι * Real.logb 2 (1 + (2 : ℝ) ^ (-t)) :=
  entropy_bound Z t ht

/-- `entropy`, вторая оценка. -/
theorem act_entropy_simple {ι : Type} [Fintype ι] [DecidableEq (ι → Bool)]
    (Z : (Fin n → Bool) → ι → Bool) :
    ent Z ≤ (∑ i, probZ (fun x => Z x i) true) * Real.logb 2 (2 * Fintype.card ι) + 1 :=
  entropy_bound_simple Z

/-- `wires`. -/
theorem act_wires_activity (C : Circ n κ) :
    (∀ x, C.U x ≤ 2 * C.P x) ∧
    ∀ k, OnPaths C k → ∀ x, C.U x ≤ 2 * C.P x ∧ C.P x ≤ 2 * C.U x + 1 :=
  wires_activity C

/-- `fanout` (с равенством `U(Σ*,x) = 3U(Σ,x)` для нашей конструкции). -/
theorem act_fanout_bound (C : Circ n κ) :
    ∃ C' : Circ n κ, (∀ x, C'.eval x = C.eval x) ∧ (∀ j, C'.outdeg j ≤ 3) ∧
      ∀ x, C'.U x = 3 * C.U x :=
  ⟨fanout C, fanout_eval C, fanout_outdeg C, fanout_U C⟩

/-- `fwd-balls`: `|B_d| ≤ (3/2) n 3^d`, `|R_d| ≤ 3|B_d|` при исходящих степенях `≤ 3`. -/
theorem act_ball_size (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3) (d : ℕ) :
    2 * (C.fwdBall d).card ≤ 3 * n * 3 ^ d ∧ (C.cut d).card ≤ 3 * (C.fwdBall d).card :=
  ⟨card_fwdBall_le C h3 d, cut_card_le C h3 d⟩

/-- Разрезы попарно не пересекаются. -/
theorem act_cut_disjoint (C : Circ n κ) {d d' : ℕ} (h : d ≠ d') :
    Disjoint (C.cut d) (C.cut d') :=
  cut_pairwiseDisjoint C {d, d'} (by simp) (by simp) h

/-- `cut-sum`: `U(Σ) ≥ Σ_{d<D} A_d`. -/
theorem act_cut_sum (C : Circ n κ) (D : ℕ) : ∑ d ∈ range D, cutA C d ≤ C.Uav :=
  Uav_ge_sum_cutA C D

/-- `H_d ≤ A_d log(2|R_d|) + 1`. -/
theorem act_ent_cut (C : Circ n κ) (d : ℕ) :
    ent (C.cutVal d) ≤ cutA C d * Real.logb 2 (2 * (C.cut d).card) + 1 :=
  ent_cut_le C d

end Summary

#print axioms act_lower_of
#print axioms act_entropy
#print axioms act_entropy_simple
#print axioms act_wires_activity
#print axioms act_fanout_bound
#print axioms act_ball_size
#print axioms act_cut_disjoint
#print axioms act_cut_sum
#print axioms act_ent_cut

end PowerActivity
