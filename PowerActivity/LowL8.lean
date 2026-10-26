import PowerActivity.LowCount
import PowerActivity.Spec

/-!
# Несжимаемость (`incompressible`), сумма по слоям (`layer-sum`) и оценка `Ω(m log(n+1))`

* `Sd_le` — `layer-sum` в форме `S_d ≤ (d+4) A_d + m/4` (из `h₂(p) − tp ≤ log(1+2^{−t})`,
  `t = d+4`, и `|L_{d+1}| ≤ m 2^{d+1}`); `Ad_ge` — `A_d ≥ m/(4(d+4))` при `S_d ≥ m/2`;
* `Eav_ge_sum_Ad` — `layer-sum`: `E(Σ) ≥ Σ_{d ≤ D} A_d` (слои не пересекаются);
* `Good n m D F` — во всякой схеме `F` выполнено `S_d ≥ m/2` при всех `d ≤ D`;
  `good_Eav` — тогда `E(Σ) ≥ (m/4) Σ_{d ≤ D} 1/(d+4)`;
* `incompressible_general` — если служебная часть `C₀ m 2^d (n + log(m+1) + d + 1)` оценки
  `encoding` при `d ≤ D` не больше `mN/4`, то доля хороших операторов не меньше
  `1 − (D+1) 2^{−mN/4}`;
* `incompressible` — при `n ≥ 20`, `1 ≤ m ≤ 2ⁿ`, `D = ⌊n/4⌋` доля `≥ 1 − (⌊n/4⌋+1) 2^{−mN/4}`;
  `incompressible_explicit` — то же в явной форме `≥ 1 − (n+1) 2^{1−mN/4}`;
* `Low.lowerPower : LowerPowerGoal` (`c = 1/16`, `ε(n) = 1` при `n < 256`, `1/n` иначе).
-/

namespace PowerActivity

open Finset Filter Topology

namespace Low

variable {n m : ℕ}

/-- `layer-sum`: `S_d ≤ (d+4) A_d + m/4`. -/
theorem Sd_le (C : Circ n (Fin m)) (d : ℕ) : C.rvS d ≤ ((d : ℝ) + 4) * C.rvA d + (m : ℝ) / 4 := by
  set t : ℝ := Real.logb 2 (1 + ((2 : ℝ) ^ (d + 4))⁻¹)
  have h1 : C.rvS d - ((d : ℝ) + 4) * C.rvA d ≤ (C.rvLayer d).card * t := by
    unfold Circ.rvS Circ.rvA
    rw [mul_sum, ← sum_sub_distrib]
    calc ∑ i ∈ C.rvLayer d, (h2 (C.lowP i) - ((d : ℝ) + 4) * C.lowP i)
        ≤ ∑ _i ∈ C.rvLayer d, t := by
          apply sum_le_sum
          intro i _
          have := h2_sub_le (C.lowP_nonneg i) (C.lowP_le_one i) (d + 4)
          push_cast at this
          exact this
      _ = (C.rvLayer d).card * t := by rw [sum_const, nsmul_eq_mul]
  have ht0 : 0 ≤ t := Real.logb_nonneg (by norm_num) (by
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ (d + 4))⁻¹ := by positivity
    linarith)
  have h2' : t ≤ 2 * ((2 : ℝ) ^ (d + 4))⁻¹ := logb_one_add_le (by positivity)
  have h3 : ((C.rvLayer d).card : ℝ) ≤ m * 2 ^ (d + 1) := by exact_mod_cast C.card_rvLayer_le d
  have h4 : ((m : ℝ) * 2 ^ (d + 1)) * (2 * ((2 : ℝ) ^ (d + 4))⁻¹) = m / 4 := by
    rw [pow_add, pow_add]; field_simp; ring
  have hc : (0 : ℝ) ≤ (C.rvLayer d).card := Nat.cast_nonneg _
  have h5 : ((C.rvLayer d).card : ℝ) * t ≤ (m * 2 ^ (d + 1)) * (2 * ((2 : ℝ) ^ (d + 4))⁻¹) :=
    mul_le_mul h3 h2' ht0 (by positivity)
  linarith

/-- Из `S_d ≥ m/2` и `S_d ≤ (d+4) A_d + m/4`: `A_d ≥ m/(4(d+4))`. -/
theorem Ad_ge (C : Circ n (Fin m)) (d : ℕ) (h : (m : ℝ) / 2 ≤ C.rvS d) :
    (m : ℝ) / 4 * (1 / ((d : ℝ) + 4)) ≤ C.rvA d := by
  have := Sd_le C d
  have hd : (0 : ℝ) < (d : ℝ) + 4 := by positivity
  rw [mul_one_div, div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- `layer-sum`: `E(Σ) ≥ Σ_{d ≤ D} A_d`. -/
theorem Eav_ge_sum_Ad (C : Circ n (Fin m)) (D : ℕ) :
    ∑ d ∈ range (D + 1), C.rvA d ≤ C.Eav := by
  rw [Circ.low_Eav_eq_sumP]
  have hdisj : ((range (D + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint C.rvLayer :=
    fun d _ d' _ hne => C.rvLayer_disjoint hne
  unfold Circ.rvA
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨d, _, hid⟩ := mem_biUnion.mp hi
    exact C.rvLayer_sub_range d hid
  · intro i _ _; exact C.lowP_nonneg i

/-- Оператор хороший до глубины `D`: во всякой его схеме `S_d ≥ m/2` при `d ≤ D`. -/
def Good (n m D : ℕ) (F : (Fin n → Bool) → Fin m → Bool) : Prop :=
  ∀ C : Circ n (Fin m), C.Realizes F → ∀ d ≤ D, (m : ℝ) / 2 ≤ C.rvS d

/-- Для хорошего оператора `E(Σ) ≥ (m/4) Σ_{d ≤ D} 1/(d+4)`. -/
theorem good_Eav {D : ℕ} {F : (Fin n → Bool) → Fin m → Bool} (hG : Good n m D F)
    (C : Circ n (Fin m)) (hC : C.Realizes F) :
    (m : ℝ) / 4 * ∑ d ∈ range (D + 1), 1 / ((d : ℝ) + 4) ≤ C.Eav := by
  refine le_trans ?_ (Eav_ge_sum_Ad C D)
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  exact Ad_ge C d (hG C hC d (Nat.le_of_lt_succ (mem_range.mp hd)))

lemma card_ops (n m : ℕ) :
    (Fintype.card ((Fin n → Bool) → Fin m → Bool) : ℝ) = (2 : ℝ) ^ ((m : ℝ) * (2 ^ n : ℕ)) := by
  rw [← Nat.cast_mul, Real.rpow_natCast]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  rw [← pow_mul]

/-- **`incompressible` (общая форма).** Если при всех `d ≤ D` служебная часть описания
`C₀ m 2^d (n + log(m+1) + d + 1)` из `encoding` (`C₀ = 22`) не больше `mN/4`, то доля
операторов, у которых во всякой схеме `S_d ≥ m/2` при всех `d ≤ D`,
не меньше `1 − (D+1) 2^{−mN/4}`. -/
theorem incompressible_general (n m D : ℕ) (hm : 1 ≤ m)
    (H : ∀ d ≤ D, 22 * (2 : ℝ) ^ d * (n + Real.logb 2 (m + 1) + d + 1) ≤ (2 ^ n : ℕ) / 4) :
    1 - ((D : ℝ) + 1) * (2 : ℝ) ^ (-((m : ℝ) * (2 ^ n : ℕ) / 4)) ≤
      frac n (Fin m) (Good n m D) := by
  classical
  set X : ℝ := (m : ℝ) * (2 ^ n : ℕ) with hX
  have hNr : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
  -- плохие операторы покрываются множествами `badSet d (m/2)`
  have hsub : (univ.filter fun F => ¬ Good n m D F) ⊆
      (range (D + 1)).biUnion fun d => badSet n m d ((m : ℝ) / 2) := by
    intro F hF
    rw [mem_filter] at hF
    obtain ⟨_, hF⟩ := hF
    unfold Good at hF
    push Not at hF
    obtain ⟨C, hC, d, hd, hS⟩ := hF
    simp only [mem_biUnion, mem_range, badSet, mem_filter, mem_univ, true_and]
    exact ⟨d, by omega, C, hC, hS.le⟩
  have hbad_d : ∀ d ∈ range (D + 1),
      ((badSet n m d ((m : ℝ) / 2)).card : ℝ) ≤ (2 : ℝ) ^ (X * 3 / 4) := by
    intro d hd
    refine (encoding_bound n m d hm _).trans ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := H d (Nat.le_of_lt_succ (mem_range.mp hd))
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have := mul_le_mul_of_nonneg_left this hm0
    rw [hX]
    nlinarith
  have hbad : ((univ.filter fun F => ¬ Good n m D F).card : ℝ) ≤
      ((D : ℝ) + 1) * (2 : ℝ) ^ (X * 3 / 4) := by
    calc ((univ.filter fun F => ¬ Good n m D F).card : ℝ)
        ≤ (((range (D + 1)).biUnion fun d => badSet n m d ((m : ℝ) / 2)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ d ∈ range (D + 1), ((badSet n m d ((m : ℝ) / 2)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _d ∈ range (D + 1), (2 : ℝ) ^ (X * 3 / 4) := sum_le_sum hbad_d
      _ = ((D : ℝ) + 1) * (2 : ℝ) ^ (X * 3 / 4) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset ((Fin n → Bool) → Fin m → Bool)))
    (fun F => Good n m D F)
  have htot := card_ops n m
  rw [← hX] at htot
  have hpos : (0 : ℝ) < (2 : ℝ) ^ X := by positivity
  unfold frac
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card, htot]
  rw [card_univ] at hsplit
  have hsplit' : ((univ.filter fun F => Good n m D F).card : ℝ) =
      (2 : ℝ) ^ X - ((univ.filter fun F => ¬ Good n m D F).card : ℝ) := by
    rw [← htot, ← hsplit]; push_cast; ring
  rw [hsplit', le_div_iff₀ hpos]
  have e : (2 : ℝ) ^ (-(X / 4)) * (2 : ℝ) ^ X = (2 : ℝ) ^ (X * 3 / 4) := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  have e' : ((D : ℝ) + 1) * (2 : ℝ) ^ (-(X / 4)) * (2 : ℝ) ^ X =
      ((D : ℝ) + 1) * (2 : ℝ) ^ (X * 3 / 4) := by rw [mul_assoc, e]
  have hX4 : -((m : ℝ) * (2 ^ n : ℕ) / 4) = -(X / 4) := by rw [hX]
  rw [hX4]
  nlinarith

/-! ## Численные оценки -/

lemma nat_aux1 : ∀ a : ℕ, 5 ≤ a → 2112 * (a + 1) ≤ 2 ^ (3 * a) := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
    rw [show 3 * (a + 1) = 3 * a + 3 by ring, pow_add]
    omega

/-- `176 · 2^d (3n+3) ≤ 2ⁿ` при `n ≥ 20`, `d ≤ ⌊n/4⌋`. -/
lemma nat_aux2 (n d : ℕ) (hn : 20 ≤ n) (hd : d ≤ n / 4) : 176 * 2 ^ d * (3 * n + 3) ≤ 2 ^ n := by
  set a := n / 4 with ha
  have ha5 : 5 ≤ a := by omega
  have hna : n ≤ 4 * a + 3 := by omega
  have h4a : 4 * a ≤ n := by omega
  have h1 := nat_aux1 a ha5
  have h2 : 2 ^ d ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hd
  have h3 : 2 ^ (4 * a) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4a
  have h4 : 2 ^ (4 * a) = 2 ^ (3 * a) * 2 ^ a := by rw [← pow_add]; ring_nf
  calc 176 * 2 ^ d * (3 * n + 3) ≤ 176 * 2 ^ a * (12 * (a + 1)) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ h2); omega
    _ = 2112 * (a + 1) * 2 ^ a := by ring
    _ ≤ 2 ^ (3 * a) * 2 ^ a := Nat.mul_le_mul_right _ h1
    _ ≤ 2 ^ n := by rw [← h4]; exact h3

/-- `log(m+1) ≤ n+1` при `m ≤ 2ⁿ`. -/
lemma logb_le_of_le_pow {m n : ℕ} (hm : m ≤ 2 ^ n) : Real.logb 2 ((m : ℝ) + 1) ≤ n + 1 := by
  have h1 : (m : ℝ) + 1 ≤ (2 : ℝ) ^ ((n : ℝ) + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]
    have : (m : ℝ) ≤ 2 ^ n := by exact_mod_cast hm
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith
  calc Real.logb 2 ((m : ℝ) + 1) ≤ Real.logb 2 ((2 : ℝ) ^ ((n : ℝ) + 1)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    _ = n + 1 := Real.logb_rpow (by norm_num) (by norm_num)

/-- Часть служебной оценки без `log(m+1)`: `22 · 2^d (n + d + 1) ≤ N/8`. -/
lemma overhead_n (n d : ℕ) (hn : 20 ≤ n) (hd : d ≤ n / 4) :
    22 * (2 : ℝ) ^ d * (n + d + 1) ≤ (2 ^ n : ℕ) / 8 := by
  have h := nat_aux2 n d hn hd
  have h' : (176 : ℝ) * 2 ^ d * (3 * n + 3) ≤ (2 ^ n : ℕ) := by exact_mod_cast h
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast (Nat.div_le_self n 4).trans' hd
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- Условие `incompressible_general` при `D = ⌊n/4⌋`, `m ≤ 2ⁿ`, `n ≥ 20`. -/
lemma incompressible_hyp (n m : ℕ) (hn : 20 ≤ n) (hm : m ≤ 2 ^ n) :
    ∀ d ≤ n / 4, 22 * (2 : ℝ) ^ d * (n + Real.logb 2 (m + 1) + d + 1) ≤ (2 ^ n : ℕ) / 4 := by
  intro d hd
  have h1 := overhead_n n d hn hd
  have h2 := logb_le_of_le_pow hm
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast (Nat.div_le_self n 4).trans' hd
  have hp : (0 : ℝ) < 2 ^ d := by positivity
  have h3 : 22 * (2 : ℝ) ^ d * Real.logb 2 ((m : ℝ) + 1) ≤ 22 * (2 : ℝ) ^ d * (n + 1) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 22 * (2 : ℝ) ^ d * (n + 1) ≤ 22 * (2 : ℝ) ^ d * (n + d + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) (by positivity)
  nlinarith

/-- **`incompressible`.** При `n ≥ 20` и `1 ≤ m ≤ 2ⁿ` доля операторов, у которых во всякой схеме
`S_d ≥ m/2` при всех `0 ≤ d ≤ ⌊n/4⌋`, не меньше `1 − (⌊n/4⌋+1) 2^{−mN/4}`
(что не меньше `1 − (n+1) 2^{1−mN/4}`, см. `incompressible_explicit`). -/
theorem incompressible (n m : ℕ) (hn : 20 ≤ n) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ n) :
    1 - (((n / 4 : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (-((m : ℝ) * (2 ^ n : ℕ) / 4)) ≤
      frac n (Fin m) (Good n m (n / 4)) :=
  incompressible_general n m (n / 4) hm1 (incompressible_hyp n m hn hm)

/-- `incompressible` в явной форме: доля исключений не больше `(n+1) 2^{1−mN/4}`. -/
theorem incompressible_explicit (n m : ℕ) (hn : 20 ≤ n) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ n) :
    1 - ((n : ℝ) + 1) * (2 : ℝ) ^ (1 - (m : ℝ) * (2 ^ n : ℕ) / 4) ≤
      frac n (Fin m) (Good n m (n / 4)) := by
  refine le_trans ?_ (incompressible n m hn hm1 hm)
  have hD : ((n / 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n 4
  have hp : (2 : ℝ) ^ (-((m : ℝ) * (2 ^ n : ℕ) / 4)) ≤ (2 : ℝ) ^ (1 - (m : ℝ) * (2 ^ n : ℕ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((m : ℝ) * (2 ^ n : ℕ) / 4)) := by positivity
  have : (((n / 4 : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (-((m : ℝ) * (2 ^ n : ℕ) / 4)) ≤
      ((n : ℝ) + 1) * (2 : ℝ) ^ (1 - (m : ℝ) * (2 ^ n : ℕ) / 4) :=
    mul_le_mul (by linarith) hp hp0 (by positivity)
  linarith

/-- `8n ≤ 2ⁿ` при `n ≥ 6`. -/
lemma nat_aux3 : ∀ n : ℕ, 6 ≤ n → 8 * n ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- Доля исключений мала: `(D+1) 2^{−mN/4} ≤ 1/n` при `D ≤ n`, `n ≥ 6`, `m ≥ 1`. -/
lemma exc_le (n m D : ℕ) (hn : 6 ≤ n) (hm : 1 ≤ m) (hD : D ≤ n) :
    ((D : ℝ) + 1) * (2 : ℝ) ^ (-((m : ℝ) * (2 ^ n : ℕ) / 4)) ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h8 : ((8 * n : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast nat_aux3 n hn
  push_cast at h8
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hE : 2 * (n : ℝ) ≤ (m : ℝ) * (2 ^ n : ℕ) / 4 := by
    have : ((2 ^ n : ℕ) : ℝ) ≤ (m : ℝ) * (2 ^ n : ℕ) := by
      nlinarith [(Nat.cast_nonneg (2 ^ n) : (0 : ℝ) ≤ (2 ^ n : ℕ))]
    push_cast at this ⊢
    linarith
  have h2E : (2 : ℝ) ^ (2 * (n : ℝ)) ≤ (2 : ℝ) ^ ((m : ℝ) * (2 ^ n : ℕ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
  have h4n : (2 : ℝ) ^ (2 * (n : ℝ)) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← pow_add]
    ring_nf
  have hnn : n * (D + 1) ≤ 2 ^ n * 2 ^ n :=
    Nat.mul_le_mul (Nat.lt_two_pow_self).le (by have := (Nat.lt_two_pow_self (n := n)); omega)
  have hnn' : (n : ℝ) * ((D : ℝ) + 1) ≤ (2 : ℝ) ^ ((m : ℝ) * (2 ^ n : ℕ) / 4) := by
    have : (n : ℝ) * ((D : ℝ) + 1) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := by exact_mod_cast hnn
    rw [h4n] at h2E
    linarith
  rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hn0]
  linarith

/-- Гармоническая сумма: `log(1+X)/4 ≤ Σ_{d ≤ D} 1/(d+4)` при `X ≥ 255`, `X + 1 ≤ 4(D+5)`. -/
lemma harm_bound (X : ℝ) (D : ℕ) (hX : 255 ≤ X) (hD : X + 1 ≤ 4 * ((D : ℝ) + 5)) :
    Real.logb 2 (1 + X) / 4 ≤ ∑ d ∈ range (D + 1), 1 / ((d : ℝ) + 4) := by
  refine le_trans ?_ (log_le_sum_inv D)
  have hl : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hX1 : (0 : ℝ) < 1 + X := by linarith
  have h1 : Real.log (1 + X) - Real.log 4 ≤ Real.log ((D : ℝ) + 5) := by
    rw [← Real.log_div hX1.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have h256 : Real.log 256 ≤ Real.log (1 + X) := Real.log_le_log (by norm_num) (by linarith)
  have e256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log (1 + X) := Real.log_nonneg (by linarith)
  unfold Real.logb
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Нижняя оценка для хорошего оператора** (по `layer-sum`): `E(Σ) ≥ (m/16) log(n+1)`
при `n ≥ 255`. -/
theorem good_Eav_log {n m : ℕ} (hn : 255 ≤ n) {F : (Fin n → Bool) → Fin m → Bool}
    (hG : Good n m (n / 4) F) (C : Circ n (Fin m)) (hC : C.Realizes F) :
    1 / 16 * (m : ℝ) * Real.logb 2 ((n : ℝ) + 1) ≤ C.Eav := by
  refine le_trans ?_ (good_Eav hG C hC)
  have hX : (255 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (n : ℝ) + 1 ≤ 4 * (((n / 4 : ℕ) : ℝ) + 5) := by
    have : n ≤ 4 * (n / 4) + 3 := by omega
    have : (n : ℝ) ≤ 4 * ((n / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast this
    linarith
  have h := harm_bound (n : ℝ) (n / 4) hX hD
  rw [add_comm (1 : ℝ)] at h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

/-- **Нижняя оценка `Ω(m log(n+1))` для почти всех операторов** (`encoding`, `incompressible`,
`layer-sum`). -/
theorem lowerPower : LowerPowerGoal := by
  refine ⟨1 / 16, by norm_num, fun n => if n < 256 then 1 else 1 / (n : ℝ), ?_, ?_⟩
  · have h : (fun n : ℕ => if n < 256 then (1 : ℝ) else 1 / (n : ℝ)) =ᶠ[atTop]
        fun n : ℕ => 1 / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 256] with n hn
      simp [show ¬ n < 256 by omega]
    exact (tendsto_one_div_atTop_nhds_zero_nat).congr' h.symm
  · intro n m hm1 hm
    by_cases hn : n < 256
    · simp only [hn, ite_true, sub_self]
      unfold frac
      positivity
    · simp only [hn, ite_false]
      have hn' : 256 ≤ n := by omega
      have h8 := incompressible n m (by omega) hm1 hm
      have hexc := exc_le n m (n / 4) (by omega) hm1 (Nat.div_le_self n 4)
      refine le_trans (by linarith) (le_trans h8 ?_)
      unfold frac
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.card_mono (Set.toFinite _) fun F hF C hC =>
        good_Eav_log (by omega) hF C hC

end Low

end PowerActivity
