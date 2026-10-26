import PowerActivity.ActFanout

/-!
# Детерминированное ядро нижней оценки `U` (`harmonic`)

* `ev_log_le_sqrt` — `c(log n + 1) ≤ √n` для всех достаточно больших `n`;
* `log_sub_le_harmonic` — `ln(α + D) − ln α ≤ Σ_{d<D} 1/(α + d)` (сравнение с интегралом);
* `H_lower` — логарифмирование оценки `cut-compress` (основа оценки `H_d ≥ n/8`);
* `logb_two_card_le` — `log(2|R_d|) ≤ log n + 2d + 4` (из `fwd-balls`);
* `Uav_le_two_Pav` — `U(Σ) ≤ 2P(Σ)` (из `wires`);
* `Uav_lower_core` — для схемы с исходящими степенями `≤ 3`, для которой при всех `d`
  `a 2ⁿ/n ≤ K |B_d| 2^{4H_d}` (`cut-compress` и свойство функции из `approx-hard`), при достаточно
  большом `n` (условия `hE1`–`hE3`) выполнено `U(Σ*) ≥ n ln n / 64` (`H_d ≥ n/8`,
  `H_d ≤ A_d log(2|R_d|)+1` и суммирование по `d`).
-/

namespace PowerActivity

open Finset Filter Topology

namespace Act

/-- `c (log₂ n + 1) ≤ √n` для всех достаточно больших `n`. -/
lemma ev_log_le_sqrt (c : ℝ) : ∀ᶠ n : ℕ in atTop, c * (Real.logb 2 n + 1) ≤ Real.sqrt n := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num))
  have h3 : Tendsto (fun x : ℝ => c / Real.log 2 * (Real.log x / x ^ (1 / 2 : ℝ)) +
      c * (x ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) := by
    have := (h1.const_mul (c / Real.log 2)).add (h2.const_mul c)
    simpa using this
  have h4 : ∀ᶠ x : ℝ in atTop, c / Real.log 2 * (Real.log x / x ^ (1 / 2 : ℝ)) +
      c * (x ^ (1 / 2 : ℝ))⁻¹ < 1 := h3.eventually (eventually_lt_nhds one_pos)
  have h5 : ∀ᶠ x : ℝ in atTop, c * (Real.logb 2 x + 1) ≤ Real.sqrt x := by
    filter_upwards [h4, eventually_gt_atTop 0] with x hx hx0
    have hs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    rw [Real.sqrt_eq_rpow]
    have e : c * (Real.logb 2 x + 1) = (c / Real.log 2 * (Real.log x / x ^ (1 / 2 : ℝ)) +
        c * (x ^ (1 / 2 : ℝ))⁻¹) * x ^ (1 / 2 : ℝ) := by
      unfold Real.logb; field_simp
    rw [e]
    nlinarith
  exact tendsto_natCast_atTop_atTop.eventually h5

/-- Сравнение гармонической суммы с логарифмом. -/
lemma log_sub_le_harmonic (α : ℝ) (hα : 0 < α) (D : ℕ) :
    Real.log (α + D) - Real.log α ≤ ∑ d ∈ range D, 1 / (α + d) := by
  have e : Real.log (α + D) - Real.log α =
      ∑ d ∈ range D, (Real.log (α + ((d + 1 : ℕ) : ℝ)) - Real.log (α + d)) := by
    rw [Finset.sum_range_sub (fun d : ℕ => Real.log (α + d))]; simp
  rw [e]
  apply Finset.sum_le_sum
  intro d _
  have hd : 0 < α + d := by positivity
  rw [← Real.log_div (by positivity) hd.ne']
  have := Real.log_le_sub_one_of_pos (x := (α + ((d + 1 : ℕ) : ℝ)) / (α + d)) (by positivity)
  calc _ ≤ (α + ((d + 1 : ℕ) : ℝ)) / (α + d) - 1 := this
    _ = 1 / (α + d) := by push_cast; field_simp; ring

/-- Логарифмирование оценки `a 2ⁿ/n ≤ K b 2^{4H}` при `b ≤ 2n·4^d`. -/
lemma H_lower {n d : ℕ} {a K b H : ℝ} (ha : 0 < a) (hK : 0 < K) (hn : 1 ≤ n)
    (hb : b ≤ 2 * n * 4 ^ d) (h : a * 2 ^ n / n ≤ K * b * (2 : ℝ) ^ (4 * H)) :
    (n : ℝ) - 2 * Real.logb 2 n - 2 * d - (1 + Real.logb 2 K - Real.logb 2 a) ≤ 4 * H := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e4 : (2 : ℝ) * n * 4 ^ d = n * 2 ^ (2 * d + 1) := by
    rw [pow_succ, pow_mul]; norm_num; ring
  have h1 : a * 2 ^ n / n ≤ K * (n * 2 ^ (2 * d + 1)) * (2 : ℝ) ^ (4 * H) := by
    rw [← e4]
    refine h.trans ?_
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (4 * H) := by positivity
    gcongr
  have hpos : 0 < a * 2 ^ n / n := by positivity
  have h2 := Real.logb_le_logb_of_le (b := 2) one_lt_two hpos h1
  have hL : Real.logb 2 (a * 2 ^ n / n) = Real.logb 2 a + n - Real.logb 2 n := by
    rw [Real.logb_div (by positivity) hn0.ne', Real.logb_mul ha.ne' (by positivity),
      Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    ring
  have hR : Real.logb 2 (K * (n * 2 ^ (2 * d + 1)) * (2 : ℝ) ^ (4 * H)) =
      Real.logb 2 K + Real.logb 2 n + (2 * d + 1) + 4 * H := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul hK.ne' (by positivity),
      Real.logb_mul hn0.ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one one_lt_two,
      Real.logb_rpow two_pos (by norm_num)]
    push_cast; ring
  rw [hL, hR] at h2
  linarith

/-- `log₂(2q) ≤ log₂ n + 2d + 4` при `2q ≤ 9n·3^d`. -/
lemma logb_two_card_le {n d q : ℕ} (hn : 1 ≤ n) (hq : 2 * q ≤ 9 * n * 3 ^ d) :
    Real.logb 2 (2 * q) ≤ Real.logb 2 n + 4 + 2 * d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp; positivity
  · have h1 : (2 * q : ℝ) ≤ 9 * n * 3 ^ d := by exact_mod_cast hq
    have h2 : (9 : ℝ) * n * 3 ^ d ≤ n * 2 ^ (2 * d + 4) := by
      rw [pow_add, pow_mul]
      have : (3 : ℝ) ^ d ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
      have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
      norm_num
      nlinarith
    calc Real.logb 2 (2 * q) ≤ Real.logb 2 (n * 2 ^ (2 * d + 4)) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) (h1.trans h2)
      _ = Real.logb 2 n + (2 * d + 4) := by
          rw [Real.logb_mul hn0.ne' (by positivity), Real.logb_pow,
            Real.logb_self_eq_one one_lt_two]
          push_cast; ring
      _ = _ := by ring

variable {n : ℕ} {κ : Type}

/-- `U(Σ) ≤ 2P(Σ)` для средних (из `wires`). -/
lemma Uav_le_two_Pav (C : Circ n κ) : C.Uav ≤ 2 * C.Pav := by
  unfold Circ.Uav Circ.Pav avgM
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  exact_mod_cast U_le_two_P C x

/-- Детерминированное ядро оценки `harmonic`: `H_d ≥ n/8`, `H_d ≤ A_d log(2|R_d|) + 1` и
суммирование `A_d` по слоям `d = 0, …, ⌊n/8⌋`. -/
theorem Uav_lower_core {a K : ℝ} (ha : 0 < a) (hK : 0 < K)
    (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3)
    (hH : ∀ d, a * 2 ^ n / n ≤ K * (C.fwdBall d).card * (2 : ℝ) ^ (4 * ent (C.cutVal d)))
    (hE1 : 8 * Real.logb 2 n + 4 * (1 + Real.logb 2 K - Real.logb 2 a) ≤ n)
    (hE2 : (16 : ℝ) ≤ n) (hE3 : 4 * Real.logb 2 n + 16 ≤ Real.sqrt n) :
    (n : ℝ) * Real.log n / 64 ≤ C.Uav := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two (by linarith)
  set α : ℝ := (Real.logb 2 n + 4) / 2 with hα
  have hα0 : 0 < α := by positivity
  set D : ℕ := n / 8 + 1 with hD
  -- `H_d ≥ n/8`: энтропия на разрезе
  have hHd : ∀ d < D, (n : ℝ) / 8 ≤ ent (C.cutVal d) := by
    intro d hd
    have hd8 : (d : ℝ) ≤ n / 8 := by
      have h1 : d ≤ n / 8 := by omega
      have h2 : (d : ℝ) ≤ ((n / 8 : ℕ) : ℝ) := by exact_mod_cast h1
      exact h2.trans Nat.cast_div_le
    have hb : ((C.fwdBall d).card : ℝ) ≤ 2 * n * 4 ^ d := by
      have h := card_fwdBall_le C h3 d
      have h' : (2 : ℝ) * (C.fwdBall d).card ≤ 3 * n * 3 ^ d := by exact_mod_cast h
      have : (3 : ℝ) ^ d ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
      have h0 : (0 : ℝ) ≤ n := hn0.le
      nlinarith
    have := H_lower ha hK hn1 hb (hH d)
    linarith
  -- `A_d ≥ (n/32)/(α + d)`
  have hAd : ∀ d < D, (n : ℝ) / 32 / (α + d) ≤ cutA C d := by
    intro d hd
    have hH := hHd d hd
    have hent := ent_cut_le C d
    have hℓ : Real.logb 2 (2 * (C.cut d).card) ≤ Real.logb 2 n + 4 + 2 * d := by
      apply logb_two_card_le hn1
      have h1 := cut_card_le C h3 d
      have h2 := card_fwdBall_le C h3 d
      calc 2 * (C.cut d).card ≤ 3 * (2 * (C.fwdBall d).card) := by omega
        _ ≤ 3 * (3 * n * 3 ^ d) := Nat.mul_le_mul_left 3 h2
        _ = 9 * n * 3 ^ d := by ring
    have hA0 := cutA_nonneg C d
    have hM : ent (C.cutVal d) ≤ cutA C d * (Real.logb 2 n + 4 + 2 * d) + 1 :=
      hent.trans (by gcongr)
    have hpos : 0 < α + d := by positivity
    rw [div_le_iff₀ hpos]
    have hαd : α + d = (Real.logb 2 n + 4 + 2 * d) / 2 := by rw [hα]; ring
    rw [hαd]
    nlinarith
  -- `cut-sum` и сравнение гармонической суммы с логарифмом
  have hsum : ∑ d ∈ range D, (n : ℝ) / 32 / (α + d) ≤ C.Uav :=
    (Finset.sum_le_sum fun d hd => hAd d (mem_range.1 hd)).trans (Uav_ge_sum_cutA C D)
  have hharm := log_sub_le_harmonic α hα0 D
  have hsum' : ∑ d ∈ range D, (n : ℝ) / 32 / (α + d) = (n / 32) * ∑ d ∈ range D, 1 / (α + d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hlog : Real.log n / 2 ≤ Real.log (α + D) - Real.log α := by
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hsq0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have h1 : α * Real.sqrt n ≤ n / 8 := by
      have : α ≤ Real.sqrt n / 8 := by rw [hα]; linarith
      calc α * Real.sqrt n ≤ (Real.sqrt n / 8) * Real.sqrt n := by gcongr
        _ = n / 8 := by rw [div_mul_eq_mul_div, hs]
    have hD8 : (n : ℝ) / 8 ≤ D := by
      have h1 : n < 8 * (n / 8 + 1) := by omega
      have h2 : (n : ℝ) < 8 * (((n / 8 : ℕ) : ℝ) + 1) := by exact_mod_cast h1
      rw [hD]; push_cast; linarith
    have h3 : Real.sqrt n ≤ (α + D) / α := by
      rw [le_div_iff₀ hα0]; nlinarith
    have h4 : Real.log (Real.sqrt n) ≤ Real.log ((α + D) / α) := Real.log_le_log hsq0 h3
    rw [Real.log_sqrt hn0.le, Real.log_div (by positivity) hα0.ne'] at h4
    exact h4
  have hn32 : (0 : ℝ) ≤ n / 32 := by positivity
  calc (n : ℝ) * Real.log n / 64 = (n / 32) * (Real.log n / 2) := by ring
    _ ≤ (n / 32) * (Real.log (α + D) - Real.log α) := by gcongr
    _ ≤ (n / 32) * ∑ d ∈ range D, 1 / (α + d) := by gcongr
    _ = ∑ d ∈ range D, (n : ℝ) / 32 / (α + d) := hsum'.symm
    _ ≤ C.Uav := hsum

end Act

end PowerActivity
