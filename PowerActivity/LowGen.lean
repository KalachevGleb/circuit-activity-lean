import PowerActivity.LowL8
import PowerActivity.LowMany

/-!
# Нижняя оценка `Ω(m log(1+Δ))` при `1 ≤ m ≤ 2^{2^n}` (`large-delta`, `many-outputs`)

* `delta_facts` — при `Δ > 1`: `Δ = n − log log(m+1)`, `log(m+1) = 2^{n−Δ}`, `Δ ≤ n`;
* `overhead_delta` — при `d ≤ Δ/4`, `Δ ≥ 255` служебная часть описания из `encoding`,
  делённая на `m`, не больше `N/4` (часть с `n` — как в `incompressible`, часть с `log(m+1)` —
  через `2^d log(m+1) ≤ 2^{n − 3Δ/4}`);
* `lower_large_delta` — `large-delta` в форме существования: при `Δ > 255` есть оператор
  с `E(Σ) ≥ (m/16) log(1+Δ)` для всякой схемы;
* `Low.lowerGeneral : LowerGeneralGoal` с `c = 1/32` (при `Δ ≤ 255` — `many-outputs`).
-/

namespace PowerActivity

open Finset

namespace Low

/-- Свойства `Δ` при `Δ > 1` и `1 ≤ m ≤ 2^{2^n}`. -/
lemma delta_facts (n m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 2 ^ n) (hΔ : 1 < Delta n m) :
    Real.logb 2 ((m : ℝ) + 1) = (2 : ℝ) ^ ((n : ℝ) - Delta n m) ∧ Delta n m ≤ n := by
  have hM : Mcap n m = m := min_eq_left hm
  have hm1' : (2 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hl1 : 1 ≤ Real.logb 2 ((m : ℝ) + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]; exact hm1'
  have hD : Delta n m = (n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)) := by
    unfold Delta at hΔ ⊢
    rw [hM] at hΔ ⊢
    rcases le_total 1 ((n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1))) with h | h
    · exact max_eq_right h
    · rw [max_eq_left h] at hΔ; exact absurd hΔ (lt_irrefl 1)
  have hll : 0 ≤ Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)) := Real.logb_nonneg (by norm_num) hl1
  refine ⟨?_, by rw [hD]; linarith⟩
  rw [hD, show (n : ℝ) - ((n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1))) =
    Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)) by ring]
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]

/-- Служебная часть описания из `encoding` при `d ≤ Δ/4`. -/
lemma overhead_delta (n m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 2 ^ n) (hΔ : 255 < Delta n m)
    (d : ℕ) (hd : (d : ℝ) ≤ Delta n m / 4) :
    22 * (2 : ℝ) ^ d * (n + Real.logb 2 (m + 1) + d + 1) ≤ (2 ^ n : ℕ) / 4 := by
  obtain ⟨hl, hΔn⟩ := delta_facts n m hm1 hm (by linarith)
  set Δ := Delta n m
  have hn256 : 256 ≤ n := by
    have : (255 : ℝ) < n := lt_of_lt_of_le hΔ hΔn
    have : 255 < n := by exact_mod_cast this
    omega
  have hdn : d ≤ n / 4 := by
    have : (4 * d : ℝ) ≤ n := by linarith
    have : 4 * d ≤ n := by exact_mod_cast this
    omega
  have h1 := overhead_n n d (by omega) hdn
  -- `2^d log(m+1) ≤ 2^{n−8}`
  have h2 : (2 : ℝ) ^ d * Real.logb 2 ((m : ℝ) + 1) ≤ (2 : ℝ) ^ ((n : ℝ) - 8) := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have h3 : (2 : ℝ) ^ ((n : ℝ) - 8) = ((2 ^ n : ℕ) : ℝ) / 256 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]; push_cast; norm_num
  rw [h3] at h2
  have e : 22 * (2 : ℝ) ^ d * (n + Real.logb 2 (m + 1) + d + 1) =
      22 * (2 : ℝ) ^ d * (n + d + 1) + 22 * ((2 : ℝ) ^ d * Real.logb 2 ((m : ℝ) + 1)) := by ring
  rw [e]
  have hN : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
  linarith

/-- `large-delta` (существование): при `Δ > 255` есть оператор, у которого любая схема имеет
`E ≥ (m/16) log(1+Δ)`. -/
theorem lower_large_delta (n m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 2 ^ n)
    (hΔ : 255 < Delta n m) :
    ∃ F : (Fin n → Bool) → Fin m → Bool, ∀ C : Circ n (Fin m), C.Realizes F →
      1 / 16 * (m : ℝ) * Real.logb 2 (1 + Delta n m) ≤ C.Eav := by
  obtain ⟨_, hΔn⟩ := delta_facts n m hm1 hm (by linarith)
  set Δ := Delta n m with hΔdef
  have hΔ0 : 0 ≤ Δ / 4 := by linarith
  set D := ⌊Δ / 4⌋₊ with hDdef
  have hn256 : 256 ≤ n := by
    have : (255 : ℝ) < n := lt_of_lt_of_le hΔ hΔn
    have : 255 < n := by exact_mod_cast this
    omega
  have hDle : ∀ d ≤ D, (d : ℝ) ≤ Δ / 4 := by
    intro d hd
    calc (d : ℝ) ≤ D := by exact_mod_cast hd
      _ ≤ Δ / 4 := Nat.floor_le hΔ0
  have hDn : D ≤ n := by
    have : (D : ℝ) ≤ n := by linarith [hDle D le_rfl]
    exact_mod_cast this
  have h8 := incompressible_general n m D hm1 fun d hd => overhead_delta n m hm1 hm hΔ d (hDle d hd)
  have hexc := exc_le n m D (by omega) hm1 hDn
  have hfrac : 0 < frac n (Fin m) (Good n m D) := by
    have : (1 : ℝ) / n < 1 := by
      rw [div_lt_one (by positivity)]; exact_mod_cast (show 1 < n by omega)
    linarith
  have hne : 0 < Nat.card {F // Good n m D F} := by
    unfold frac at hfrac
    by_contra h
    push Not at h
    have : Nat.card {F // Good n m D F} = 0 := by omega
    rw [this] at hfrac
    simp at hfrac
  obtain ⟨⟨F, hF⟩⟩ := Nat.card_pos_iff.mp hne |>.1
  refine ⟨F, fun C hC => ?_⟩
  refine le_trans ?_ (good_Eav hF C hC)
  have hD' : Δ + 1 ≤ 4 * ((D : ℝ) + 5) := by
    have := Nat.lt_floor_add_one (Δ / 4)
    rw [← hDdef] at this
    linarith
  have h := harm_bound Δ D hΔ.le hD'
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- **Нижняя оценка для `PowerBoundGeneral`**: `E(Σ) ≥ (1/32) m log(1+Δ)` для некоторого
оператора при `n ≥ 2`, `1 ≤ m ≤ 2^{2^n}`. -/
theorem lowerGeneral : LowerGeneralGoal := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro n m _ hm1 hm
  have hΔ1 : 1 ≤ Delta n m := le_max_left _ _
  have hlog0 : 0 ≤ Real.logb 2 (1 + Delta n m) := Real.logb_nonneg (by norm_num) (by linarith)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hΔ : 255 < Delta n m
  · obtain ⟨F, hF⟩ := lower_large_delta n m hm1 hm hΔ
    refine ⟨F, fun C hC => le_trans ?_ (hF C hC)⟩
    nlinarith
  · push Not at hΔ
    obtain ⟨F, hF⟩ := many_out n m hm1 hm
    refine ⟨F, fun C hC => le_trans ?_ (hF C hC)⟩
    have h8 : Real.logb 2 (1 + Delta n m) ≤ 8 := by
      calc Real.logb 2 (1 + Delta n m) ≤ Real.logb 2 256 :=
            Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
        _ = 8 := by
            rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
    nlinarith

end Low

end PowerActivity
