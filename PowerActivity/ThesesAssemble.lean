import PowerActivity.Main
import PowerActivity.ThesesSpec

/-!
# Сборка утверждений тезисов из вспомогательных целей

* `E ≤ P` поточечно (`Circ.E_le_P`), `E(n,m) ≤ P(n,m)`;
* доля операторов: пересечение (`frac_and`), свойство первой координаты (`frac_first`);
* `n' ≤ 1 + Δ ≤ n'²` при `m ≤ 2^{2^n}` (`nPrime_le_one_add_Delta`, `one_add_Delta_le_sq`);
  `log n ≤ 3 log n'` при `m ≤ 2ⁿ` (`logb_le_three_logb_nPrime`);
  `n² ≤ 25 m log n'` при `n² ≤ m log n`, `m ≥ 1` (`sq_le_mul_logb_nPrime`);
* `thesesThm1_of`, `thesesThm2_of`, `thesesThm2U_of`, `thesesCorP_of`.
-/

namespace PowerActivity

open Finset Filter Topology

/-! ## `E ≤ P` -/

namespace Circ

variable {n : ℕ} {κ : Type}

lemma E_le_P (C : Circ n κ) (x : Fin n → Bool) : C.E x ≤ C.P x := by
  unfold Circ.E Circ.P
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, Or.inl hi.2⟩

lemma Eav_le_Pav (C : Circ n κ) : C.Eav ≤ C.Pav := by
  unfold Circ.Eav Circ.Pav avgM
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun x _ => by exact_mod_cast C.E_le_P x

end Circ

lemma EavSh_le_PavSh (n m : ℕ) : EavSh n m ≤ PavSh n m :=
  shMeas_mono (fun C => avgM_nonneg C.E) fun C => C.Eav_le_Pav

/-! ## Доля операторов -/

lemma frac_and {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (Q₁ Q₂ : ((Fin n → Bool) → κ → Bool) → Prop) :
    frac n κ Q₁ + frac n κ Q₂ - 1 ≤ frac n κ (fun F => Q₁ F ∧ Q₂ F) := by
  classical
  unfold frac
  have hc : ∀ Q : ((Fin n → Bool) → κ → Bool) → Prop,
      Nat.card {F // Q F} = (univ.filter Q).card := fun Q => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hT : Nat.card ((Fin n → Bool) → κ → Bool) = (univ : Finset ((Fin n → Bool) → κ → Bool)).card := by
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  rw [hc, hc, hc, hT]
  have hpos : (0 : ℝ) < (univ : Finset ((Fin n → Bool) → κ → Bool)).card := by
    exact_mod_cast Finset.card_pos.mpr univ_nonempty
  have key : (univ.filter Q₁).card + (univ.filter Q₂).card ≤
      (univ.filter fun F => Q₁ F ∧ Q₂ F).card + (univ : Finset ((Fin n → Bool) → κ → Bool)).card := by
    rw [Finset.filter_and, ← Finset.card_union_add_card_inter]
    have := Finset.card_le_univ (univ.filter Q₁ ∪ univ.filter Q₂)
    simp only [Finset.card_univ] at this ⊢
    omega
  have keyR : ((univ.filter Q₁).card : ℝ) + (univ.filter Q₂).card ≤
      (univ.filter fun F => Q₁ F ∧ Q₂ F).card + (univ : Finset ((Fin n → Bool) → κ → Bool)).card := by
    exact_mod_cast key
  rw [← add_div, sub_le_iff_le_add, div_add_one (ne_of_gt hpos)]
  have hfin := div_le_div_of_nonneg_right keyR hpos.le
  convert hfin using 6

/-- Доля операторов, первая координата которых обладает свойством `Q`, равна доле функций
со свойством `Q`. -/
lemma frac_first {n m : ℕ} (hm : 1 ≤ m) (Q : ((Fin n → Bool) → Fin 1 → Bool) → Prop) :
    frac n (Fin m) (fun F => Q (fun x _ => F x ⟨0, hm⟩)) = frac n (Fin 1) Q := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let e : ((Fin n → Bool) → Fin (k + 1) → Bool) ≃
      ((Fin n → Bool) → Fin 1 → Bool) × ((Fin n → Bool) → Fin k → Bool) :=
    { toFun := fun F => (fun x _ => F x 0, fun x j => F x j.succ)
      invFun := fun p x => Fin.cons (p.1 x 0) (p.2 x)
      left_inv := fun F => by
        funext x i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext x i
          have : i = 0 := Subsingleton.elim _ _
          subst this
          simp
        · funext x j
          simp }
  have hsub : {F : (Fin n → Bool) → Fin (k + 1) → Bool // Q (fun x _ => F x ⟨0, hm⟩)} ≃
      {f // Q f} × ((Fin n → Bool) → Fin k → Bool) :=
    (e.subtypeEquiv (p := fun F => Q (fun x _ => F x ⟨0, hm⟩)) (q := fun p => Q p.1)
      (fun F => Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  unfold frac
  rw [Nat.card_congr hsub, Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  have hpos : (0 : ℝ) < Nat.card ((Fin n → Bool) → Fin k → Bool) := by
    exact_mod_cast Nat.card_pos
  push_cast
  rw [mul_div_mul_right _ _ (ne_of_gt hpos)]

/-! ## `n'` и `Δ` -/

lemma Delta_of_le {n m : ℕ} (hm : m ≤ 2 ^ 2 ^ n) :
    Delta n m = max 1 ((n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1))) := by
  unfold Delta; rw [Mcap_of_le hm]

lemma two_le_nPrime (n m : ℕ) : 2 ≤ nPrime n m := le_max_left _ _

lemma nPrime_le_one_add_Delta {n m : ℕ} (hm : m ≤ 2 ^ 2 ^ n) : nPrime n m ≤ 1 + Delta n m := by
  rw [Delta_of_le hm]; unfold nPrime
  set y := (n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1))
  exact max_le (by linarith [le_max_left 1 y]) (by linarith [le_max_right 1 y])

lemma one_add_Delta_le_sq {n m : ℕ} (hm : m ≤ 2 ^ 2 ^ n) : 1 + Delta n m ≤ nPrime n m ^ 2 := by
  rw [Delta_of_le hm]; unfold nPrime
  set y := (n : ℝ) - Real.logb 2 (Real.logb 2 ((m : ℝ) + 1))
  have hp : (2 : ℝ) ≤ max 2 y := le_max_left _ _
  have hle : max 1 y ≤ max 2 y := max_le (by linarith) (le_max_right _ _)
  nlinarith

lemma one_le_logb_nPrime (n m : ℕ) : 1 ≤ Real.logb 2 (nPrime n m) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith [two_le_nPrime n m])]
  simpa using two_le_nPrime n m

lemma logb_nPrime_nonneg (n m : ℕ) : 0 ≤ Real.logb 2 (nPrime n m) := by
  linarith [one_le_logb_nPrime n m]

lemma logb_nPrime_le {n m : ℕ} (hm : m ≤ 2 ^ 2 ^ n) :
    Real.logb 2 (nPrime n m) ≤ Real.logb 2 (1 + Delta n m) :=
  Real.logb_le_logb_of_le (by norm_num) (by linarith [two_le_nPrime n m])
    (nPrime_le_one_add_Delta hm)

lemma logb_one_add_Delta_le {n m : ℕ} (hm : m ≤ 2 ^ 2 ^ n) :
    Real.logb 2 (1 + Delta n m) ≤ 2 * Real.logb 2 (nPrime n m) := by
  have hp : (0 : ℝ) < nPrime n m := by linarith [two_le_nPrime n m]
  have hD : (0 : ℝ) < 1 + Delta n m := by
    have : (1 : ℝ) ≤ Delta n m := le_max_left _ _
    linarith
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hD (one_add_Delta_le_sq hm)
  rw [show nPrime n m ^ 2 = nPrime n m * nPrime n m by ring,
    Real.logb_mul (ne_of_gt hp) (ne_of_gt hp)] at h
  linarith

lemma nlogn_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * Real.logb 2 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact mul_nonneg (Nat.cast_nonneg n)
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast h))

/-- `n + 1 ≤ 2^{⌊n/2⌋}` при `n ≥ 6`. -/
lemma succ_le_two_pow_half : ∀ n : ℕ, 6 ≤ n → n + 1 ≤ 2 ^ (n / 2)
  | 0 | 1 | 2 | 3 | 4 | 5 => by intro h; omega
  | 6 => by intro; norm_num
  | 7 => by intro; norm_num
  | k + 8 => by
    intro _
    have ih := succ_le_two_pow_half (k + 6) (by omega)
    have h2 : (k + 8) / 2 = (k + 6) / 2 + 1 := by omega
    rw [h2, pow_succ]
    set t := 2 ^ ((k + 6) / 2)
    omega

/-- `log n ≤ 3 log n'` при `1 ≤ m ≤ 2ⁿ`, `n ≥ 2`. -/
lemma logb_le_three_logb_nPrime {n m : ℕ} (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ n) :
    Real.logb 2 n ≤ 3 * Real.logb 2 (nPrime n m) := by
  have hp : (0 : ℝ) < nPrime n m := by linarith [two_le_nPrime n m]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  -- достаточно `n ≤ n'^3`
  suffices hs : (n : ℝ) ≤ nPrime n m ^ 3 by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) hs
    rw [show nPrime n m ^ 3 = nPrime n m * (nPrime n m * nPrime n m) by ring,
      Real.logb_mul (ne_of_gt hp) (by positivity), Real.logb_mul (ne_of_gt hp) (ne_of_gt hp)] at h
    linarith
  rcases Nat.lt_or_ge n 9 with h9 | h9
  · have : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
    have h2 := two_le_nPrime n m
    have h8 : (2 : ℝ) ^ 3 ≤ nPrime n m ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    norm_num at h8
    linarith
  · -- `log log (m+1) ≤ log (n+1) ≤ n/2`
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hlog1 : Real.logb 2 ((m : ℝ) + 1) ≤ n + 1 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]
      have : ((m : ℝ) + 1) ≤ (2 : ℝ) ^ ((n : ℝ) + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]
        have : (m : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hm
        have : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        linarith
      exact this
    have hlogpos : 0 < Real.logb 2 ((m : ℝ) + 1) :=
      Real.logb_pos (by norm_num) (by linarith)
    have hlog2 : Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)) ≤ Real.logb 2 ((n : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) hlogpos hlog1
    have hhalf : Real.logb 2 ((n : ℝ) + 1) ≤ (n : ℝ) / 2 := by
      have hN := succ_le_two_pow_half n (by omega)
      have hNR : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n / 2 : ℕ) := by exact_mod_cast hN
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
      refine le_trans hNR ?_
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
      linarith
    have hy : (n : ℝ) / 2 ≤ nPrime n m := by
      unfold nPrime
      refine le_trans ?_ (le_max_right _ _)
      linarith
    have hn9 : (9 : ℝ) ≤ n := by exact_mod_cast h9
    have h3 : ((n : ℝ) / 2) ^ 3 ≤ nPrime n m ^ 3 := by
      apply pow_le_pow_left₀ (by linarith) hy
    have hsq : (8 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hcube : (n : ℝ) ≤ ((n : ℝ) / 2) ^ 3 := by
      have h0 : (0 : ℝ) ≤ n := by linarith
      have := mul_le_mul_of_nonneg_left hsq h0
      have e : ((n : ℝ) / 2) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 / 8 := by ring
      rw [e]
      linarith
    linarith

/-! ## Член `m log(1+Δ)` для почти всех операторов (слои и сбалансированные выходы) -/

theorem mterm_of (hL : LayerGoal) (hB : BalGoal) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
      1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c * m * Real.logb 2 (1 + Delta n m) ≤ C.Eav ∧
        c * m * Real.logb 2 (1 + Delta n m) ≤ C.Uav := by
  obtain ⟨cL, Δ₀, hcL, εL, hεL, hL⟩ := hL
  obtain ⟨cB, hcB, εB, hεB, hB⟩ := hB
  set Λ : ℝ := Real.logb 2 (1 + max Δ₀ 1) with hΛ
  have hΛpos : 0 < Λ := Real.logb_pos (by norm_num) (by linarith [le_max_right Δ₀ 1])
  refine ⟨min cL (cB / Λ), lt_min hcL (div_pos hcB hΛpos), fun n => |εL n| + |εB n|, ?_, ?_⟩
  · simpa using hεL.abs.add hεB.abs
  intro n m hm hmM
  have hL0 : 0 ≤ Real.logb 2 (1 + Delta n m) := logb_one_add_Delta_nonneg n m
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hΔ : Δ₀ < Delta n m
  · have hle : min cL (cB / Λ) * m * Real.logb 2 (1 + Delta n m) ≤
        cL * m * Real.logb 2 (1 + Delta n m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hm0) hL0
    have hfr := hL n m hm hmM hΔ
    refine le_trans ?_ (le_trans hfr (frac_mono ?_))
    · have := le_abs_self (εL n); have := abs_nonneg (εB n); linarith
    · intro F hF C hC
      exact ⟨le_trans hle (hF C hC).1, le_trans hle (hF C hC).2⟩
  · push_neg at hΔ
    have hlog : Real.logb 2 (1 + Delta n m) ≤ Λ := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · have : (1 : ℝ) ≤ Delta n m := le_max_left _ _
        linarith
      · linarith [le_max_left Δ₀ 1]
    have hle : min cL (cB / Λ) * m * Real.logb 2 (1 + Delta n m) ≤ cB * m := by
      calc min cL (cB / Λ) * m * Real.logb 2 (1 + Delta n m) ≤ (cB / Λ) * m * Λ := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (min_le_right _ _) hm0) hlog hL0
            positivity
        _ = cB * m := by field_simp
    have hfr := hB n m hm hmM
    refine le_trans ?_ (le_trans hfr (frac_mono ?_))
    · have := le_abs_self (εB n); have := abs_nonneg (εL n); linarith
    · intro F hF C hC
      exact ⟨le_trans hle (hF C hC).1, le_trans hle (hF C hC).2⟩

/-! ## Теорема 1 тезисов -/

theorem thesesThm1_of (hI : InflGoal) (hL : LayerGoal) (hB : BalGoal) (h3 : PowerBoundGeneral) :
    ThesesThm1 := by
  obtain ⟨cI, hcI, εI, hεI, hI⟩ := hI
  obtain ⟨cM, hcM, εM, hεM, hM⟩ := mterm_of hL hB
  refine ⟨⟨min cI cM / 2, by positivity, fun n => |εI n| + |εM n|, ?_, ?_⟩, ?_⟩
  · simpa using hεI.abs.add hεM.abs
  · intro n m hm hmM
    have hfa := frac_and (n := n) (κ := Fin m)
      (fun F => ∀ C : Circ n (Fin m), C.Realizes F → cI * n ≤ C.Eav)
      (fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        cM * m * Real.logb 2 (1 + Delta n m) ≤ C.Eav ∧
        cM * m * Real.logb 2 (1 + Delta n m) ≤ C.Uav)
    refine le_trans ?_ (le_trans hfa (frac_mono fun F hF C hC => ?_))
    · have := hI n m hm; have := hM n m hm hmM
      have := le_abs_self (εI n); have := le_abs_self (εM n); linarith
    · have e1 := hF.1 C hC
      have e2 := (hF.2 C hC).1
      have hlog := logb_nPrime_le hmM
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hL1 := logb_nPrime_nonneg n m
      have h1 : min cI cM ≤ cI := min_le_left _ _
      have h2 : min cI cM ≤ cM := min_le_right _ _
      have hmin0 : 0 ≤ min cI cM := le_min hcI.le hcM.le
      have a1 : min cI cM * n ≤ cI * n := mul_le_mul_of_nonneg_right h1 hn0
      have a2 : min cI cM * (m * Real.logb 2 (nPrime n m)) ≤
          cM * m * Real.logb 2 (1 + Delta n m) := by
        rw [← mul_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h2 hm0) hlog hL1 (by positivity)
      nlinarith
  · obtain ⟨c3, K3, hc3, hK3, h3⟩ := h3
    refine ⟨c3, 2 * K3, hc3, by positivity, fun n m hn hm hmM => ?_⟩
    obtain ⟨hlo, hmid, hup⟩ := h3 n m hn hm
    rw [Mcap_of_le hmM] at hlo hup
    have hlog := logb_nPrime_le hmM
    have hlog2 := logb_one_add_Delta_le hmM
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hL1 := logb_nPrime_nonneg n m
    refine ⟨le_trans ?_ hlo, hmid, le_trans hup ?_⟩
    · have : (m : ℝ) * Real.logb 2 (nPrime n m) ≤ m * Real.logb 2 (1 + Delta n m) :=
        mul_le_mul_of_nonneg_left hlog hm0
      nlinarith
    · have : (m : ℝ) * Real.logb 2 (1 + Delta n m) ≤ m * (2 * Real.logb 2 (nPrime n m)) :=
        mul_le_mul_of_nonneg_left hlog2 hm0
      nlinarith

/-! ## Первая координата: оценка `n log n` (`ActLowerGoal`) для операторов -/

/-- Для почти всех операторов (их первая координата — «трудная» функция) любая схема имеет
`U, P ≥ c n log n`. -/
theorem nlogn_of (hA : ActLowerGoal) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m →
      1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c * n * Real.logb 2 n ≤ C.Uav ∧ c * n * Real.logb 2 n ≤ C.Pav := by
  obtain ⟨c, hc, ε, hε, hA⟩ := hA
  refine ⟨c, hc, ε, hε, fun n m hm => ?_⟩
  have hAn := hA n
  rw [← frac_first hm] at hAn
  refine le_trans hAn (frac_mono fun F hF C hC => ?_)
  -- схема оператора `F` с одним выходом `0` реализует первую координату
  have h := hF (C.withOut (fun _ => C.out ⟨0, hm⟩) (fun _ => C.out_lt _)) (fun x => by
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    exact congrFun (hC x) ⟨0, hm⟩)
  exact h

/-! ## Теорема 2 тезисов -/

theorem thesesThm2_of (hE : ExistsGoal) (hA : ActLowerGoal) (hUP : UpperPOpGoal)
    (t1 : ThesesThm1) : ThesesThm2 := by
  obtain ⟨cA, hcA, εA, hεA, hA⟩ := nlogn_of hA
  obtain ⟨⟨c1, hc1, ε1, hε1, h1⟩, ⟨c1', K1, hc1', hK1, hsh1⟩⟩ := t1
  obtain ⟨K, hUP⟩ := hUP
  set c := min cA c1 / 2 with hcdef
  have hc : 0 < c := by positivity
  set ε : ℕ → ℝ := fun n => |εA n| + |ε1 n| with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := by simpa using hεA.abs.add hε1.abs
  -- нижняя оценка для почти всех
  have hlow : ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
      1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Pav := by
    intro n m hm hmM
    have hfa := frac_and (n := n) (κ := Fin m)
      (fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        cA * n * Real.logb 2 n ≤ C.Uav ∧ cA * n * Real.logb 2 n ≤ C.Pav)
      (fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c1 * (n + m * Real.logb 2 (nPrime n m)) ≤ C.Eav)
    refine le_trans ?_ (le_trans hfa (frac_mono fun F hF C hC => ?_))
    · have := hA n m hm; have := h1 n m hm hmM
      have := le_abs_self (εA n); have := le_abs_self (ε1 n)
      simp only [hεdef]; linarith
    · have e1 := (hF.1 C hC).2
      have e2 := le_trans (hF.2 C hC) C.Eav_le_Pav
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hL1 := logb_nPrime_nonneg n m
      have hnl := nlogn_nonneg n
      have hmin1 : min cA c1 ≤ cA := min_le_left _ _
      have hmin2 : min cA c1 ≤ c1 := min_le_right _ _
      have hmin0 : 0 ≤ min cA c1 := le_min hcA.le hc1.le
      have a1 : min cA c1 * (n * Real.logb 2 n) ≤ cA * n * Real.logb 2 n := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hmin1 hnl
      have a2 : min cA c1 * (m * Real.logb 2 (nPrime n m)) ≤
          c1 * (n + m * Real.logb 2 (nPrime n m)) := by
        have : min cA c1 * (m * Real.logb 2 (nPrime n m)) ≤ c1 * (m * Real.logb 2 (nPrime n m)) :=
          mul_le_mul_of_nonneg_right hmin2 (by positivity)
        nlinarith
      simp only [hcdef]
      nlinarith
  -- верхняя оценка на каждом наборе
  have hupx : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
      ∀ F : (Fin n → Bool) → Fin m → Bool, ∃ C : Circ n (Fin m), C.Realizes F ∧
        ∀ x, (C.P x : ℝ) ≤ 2 * max K 1 * (n ^ 2 + m * Real.logb 2 (nPrime n m)) := by
    intro n m hn hm hmM F
    obtain ⟨C, hC, hb⟩ := hUP n m hn hm hmM F
    refine ⟨C, hC, fun x => le_trans (hb x) ?_⟩
    have hlog2 := logb_one_add_Delta_le hmM
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hL1 := logb_nPrime_nonneg n m
    have hD0 := logb_one_add_Delta_nonneg n m
    have hX : (0 : ℝ) ≤ (n : ℝ) ^ 2 + m * Real.logb 2 (1 + Delta n m) := by positivity
    have hK : K ≤ max K 1 := le_max_left _ _
    have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
    have s1 : K * ((n : ℝ) ^ 2 + m * Real.logb 2 (1 + Delta n m)) ≤
        max K 1 * ((n : ℝ) ^ 2 + m * Real.logb 2 (1 + Delta n m)) :=
      mul_le_mul_of_nonneg_right hK hX
    have s2 : (m : ℝ) * Real.logb 2 (1 + Delta n m) ≤ m * (2 * Real.logb 2 (nPrime n m)) :=
      mul_le_mul_of_nonneg_left hlog2 hm0
    have hmL : 0 ≤ (m : ℝ) * Real.logb 2 (nPrime n m) := by positivity
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith
  refine ⟨⟨c, hc, ε, hε, hlow⟩, ⟨2 * max K 1, by positivity, hupx⟩, ?_⟩
  -- функции Шеннона при всех `n ≥ 2`
  obtain ⟨n₀, hn₀⟩ := eventually_lt_one hε
  set Λ : ℝ := Real.logb 2 n₀ + 1 with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ Real.logb 2 (n₀ : ℝ) := by
      rcases Nat.eq_zero_or_pos n₀ with h | h
      · simp [h]
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
    linarith
  refine ⟨min c (c1' / Λ), 2 * max K 1, lt_min hc (by positivity), by positivity,
    fun n m hn hm hmM => ⟨?_, PavSh_le_PmaxSh n m, ?_⟩⟩
  · have hn1 : 1 ≤ n := by omega
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hL1 := logb_nPrime_nonneg n m
    have hnl := nlogn_nonneg n
    have hX : 0 ≤ (n : ℝ) * Real.logb 2 n + m * Real.logb 2 (nPrime n m) := by positivity
    rcases le_or_gt n₀ n with h | h
    · have hpos : 0 < frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
          c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Pav := by
        have := hlow n m hm hmM; have := hn₀ n h; linarith
      obtain ⟨F, hF⟩ := exists_of_frac_pos hpos
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hX)
        (le_shMeas_of hE hn1 F hF)
    · -- малые `n`: `P ≥ E` и `n log n ≤ Λ n`
      have hlo := (hsh1 n m hn hm hmM).1
      have hlogn : Real.logb 2 (n : ℝ) ≤ Λ := by
        have : Real.logb 2 (n : ℝ) ≤ Real.logb 2 (n₀ : ℝ) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hn1)
            (by exact_mod_cast h.le)
        linarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have b1 : (n : ℝ) * Real.logb 2 n ≤ Λ * n := by
        rw [mul_comm Λ]; exact mul_le_mul_of_nonneg_left hlogn hn0
      have b2 : (m : ℝ) * Real.logb 2 (nPrime n m) ≤ Λ * (m * Real.logb 2 (nPrime n m)) := by
        have h0 : 0 ≤ (m : ℝ) * Real.logb 2 (nPrime n m) := by positivity
        nlinarith
      have hΛpos : 0 < Λ := by linarith
      calc min c (c1' / Λ) * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m))
          ≤ (c1' / Λ) * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hX
        _ ≤ (c1' / Λ) * (Λ * (n + m * Real.logb 2 (nPrime n m))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith
        _ = c1' * (n + m * Real.logb 2 (nPrime n m)) := by field_simp
        _ ≤ EavSh n m := hlo
        _ ≤ PavSh n m := EavSh_le_PavSh n m
  · refine shMeas_le_of (fun C => Nat.cast_nonneg _) fun F => ?_
    obtain ⟨C, hC, hb⟩ := hupx n m (by omega) hm hmM F
    exact ⟨C, hC, maxM_le hb⟩

/-! ## Теорема 2 тезисов для числа активных проводов `U` -/

theorem thesesThm2U_of (hE : ExistsGoal) (hA : ActLowerGoal) (hL : LayerGoal) (hB : BalGoal)
    (hUP : UpperPOpGoal) : ThesesThm2U := by
  obtain ⟨cA, hcA, εA, hεA, hA⟩ := nlogn_of hA
  obtain ⟨cM, hcM, εM, hεM, hM⟩ := mterm_of hL hB
  obtain ⟨K, hUP⟩ := hUP
  set c := min cA cM / 2 with hcdef
  have hc : 0 < c := by positivity
  set ε : ℕ → ℝ := fun n => |εA n| + |εM n| with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := by simpa using hεA.abs.add hεM.abs
  have hlow : ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
      1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Uav := by
    intro n m hm hmM
    have hfa := frac_and (n := n) (κ := Fin m)
      (fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        cA * n * Real.logb 2 n ≤ C.Uav ∧ cA * n * Real.logb 2 n ≤ C.Pav)
      (fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        cM * m * Real.logb 2 (1 + Delta n m) ≤ C.Eav ∧
        cM * m * Real.logb 2 (1 + Delta n m) ≤ C.Uav)
    refine le_trans ?_ (le_trans hfa (frac_mono fun F hF C hC => ?_))
    · have := hA n m hm; have := hM n m hm hmM
      have := le_abs_self (εA n); have := le_abs_self (εM n)
      simp only [hεdef]; linarith
    · have e1 := (hF.1 C hC).1
      have e2 := (hF.2 C hC).2
      have hlog := logb_nPrime_le hmM
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hL1 := logb_nPrime_nonneg n m
      have hnl := nlogn_nonneg n
      have hmin1 : min cA cM ≤ cA := min_le_left _ _
      have hmin2 : min cA cM ≤ cM := min_le_right _ _
      have hmin0 : 0 ≤ min cA cM := le_min hcA.le hcM.le
      have a1 : min cA cM * (n * Real.logb 2 n) ≤ cA * n * Real.logb 2 n := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hmin1 hnl
      have a2 : min cA cM * (m * Real.logb 2 (nPrime n m)) ≤
          cM * m * Real.logb 2 (1 + Delta n m) := by
        rw [← mul_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hmin2 hm0) hlog hL1 (by positivity)
      simp only [hcdef]
      nlinarith
  have hupx : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
      ∀ F : (Fin n → Bool) → Fin m → Bool, ∃ C : Circ n (Fin m), C.Realizes F ∧
        ∀ x, (C.U x : ℝ) ≤ 4 * max K 1 * (n ^ 2 + m * Real.logb 2 (nPrime n m)) := by
    intro n m hn hm hmM F
    obtain ⟨C, hC, hb⟩ := hUP n m hn hm hmM F
    refine ⟨C, hC, fun x => ?_⟩
    have hUP2 : (C.U x : ℝ) ≤ 2 * C.P x := by exact_mod_cast Act.U_le_two_P C x
    have hlog2 := logb_one_add_Delta_le hmM
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hL1 := logb_nPrime_nonneg n m
    have hD0 := logb_one_add_Delta_nonneg n m
    have hX : (0 : ℝ) ≤ (n : ℝ) ^ 2 + m * Real.logb 2 (1 + Delta n m) := by positivity
    have hK : K ≤ max K 1 := le_max_left _ _
    have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
    have s1 : K * ((n : ℝ) ^ 2 + m * Real.logb 2 (1 + Delta n m)) ≤
        max K 1 * ((n : ℝ) ^ 2 + m * Real.logb 2 (1 + Delta n m)) :=
      mul_le_mul_of_nonneg_right hK hX
    have s2 : (m : ℝ) * Real.logb 2 (1 + Delta n m) ≤ m * (2 * Real.logb 2 (nPrime n m)) :=
      mul_le_mul_of_nonneg_left hlog2 hm0
    have hmL : 0 ≤ (m : ℝ) * Real.logb 2 (nPrime n m) := by positivity
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := by positivity
    have := hb x
    nlinarith
  refine ⟨⟨c, hc, ε, hε, hlow⟩, ⟨4 * max K 1, by positivity, hupx⟩, ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_lt_one hε
  refine ⟨c, 4 * max K 1, hc, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max n₀ 1)] with n hn m hm hmM
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  refine ⟨?_, UavSh_le_UmaxSh n m, ?_⟩
  · have hpos : 0 < frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
        c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Uav := by
      have := hlow n m hm hmM; have := hn₀ n (le_trans (le_max_left _ _) hn); linarith
    obtain ⟨F, hF⟩ := exists_of_frac_pos hpos
    exact le_shMeas_of hE hn1 F hF
  · refine shMeas_le_of (fun C => Nat.cast_nonneg _) fun F => ?_
    obtain ⟨C, hC, hb⟩ := hupx n m hn1 hm hmM F
    exact ⟨C, hC, maxM_le hb⟩

/-! ## Следствие: `P(n,m) = Θ(m log n')` при `n²/log n ≤ m ≤ 2ⁿ` -/

/-- `n² ≤ 25 m log n'`, если `n² ≤ m log n` и `m ≥ 1`. Либо `log log(m+1) ≤ n/2`, и тогда
`n' ≥ n/2`, `log n ≤ 2 log n'`; либо `log(m+1) > 2^{n/2} ≥ 2 log(n+1)`, и тогда `m ≥ n²`. -/
lemma sq_le_mul_logb_nPrime {n m : ℕ} (hn : 2 ≤ n) (hm1 : 1 ≤ m)
    (hnm : (n : ℝ) ^ 2 ≤ m * Real.logb 2 n) :
    (n : ℝ) ^ 2 ≤ 25 * (m * Real.logb 2 (nPrime n m)) := by
  have hL1 := one_le_logb_nPrime n m
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmL : (1 : ℝ) ≤ m * Real.logb 2 (nPrime n m) := by nlinarith
  have hp : (0 : ℝ) < nPrime n m := by linarith [two_le_nPrime n m]
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · have h5 : (n : ℝ) ≤ 5 := by exact_mod_cast (by omega : n ≤ 5)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast h6
  by_cases hcase : Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)) ≤ (n : ℝ) / 2
  · -- `n' ≥ n/2`, поэтому `n ≤ n'²` и `log n ≤ 2 log n'`
    have hy : (n : ℝ) / 2 ≤ nPrime n m := by
      unfold nPrime
      exact le_trans (by linarith) (le_max_right _ _)
    have hsq : (n : ℝ) ≤ nPrime n m ^ 2 := by nlinarith
    have hlog : Real.logb 2 n ≤ 2 * Real.logb 2 (nPrime n m) := by
      have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) hsq
      rw [show nPrime n m ^ 2 = nPrime n m * nPrime n m by ring,
        Real.logb_mul (ne_of_gt hp) (ne_of_gt hp)] at h
      linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have := mul_le_mul_of_nonneg_left hlog hm0
    nlinarith
  · push_neg at hcase
    -- `log(m+1) > 2^{n/2} ≥ n + 1 > 2 log(n+1)`, откуда `m ≥ n²`
    have hlogpos : 0 < Real.logb 2 ((m : ℝ) + 1) := Real.logb_pos (by norm_num) (by linarith)
    have h1 : (2 : ℝ) ^ ((n : ℝ) / 2) < Real.logb 2 ((m : ℝ) + 1) := by
      rw [← Real.lt_logb_iff_rpow_lt (by norm_num) hlogpos]
      exact hcase
    have hNR : (n : ℝ) + 1 ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
      have hN : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (n / 2) : ℕ) : ℝ) := by
        exact_mod_cast succ_le_two_pow_half n h6
      push_cast at hN
      refine le_trans hN ?_
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
      linarith
    have hhalf : Real.logb 2 ((n : ℝ) + 1) ≤ (n : ℝ) / 2 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
      exact hNR
    have h2 : Real.logb 2 (((n : ℝ) + 1) * ((n : ℝ) + 1)) < Real.logb 2 ((m : ℝ) + 1) := by
      rw [Real.logb_mul (by positivity) (by positivity)]
      linarith
    have h3 : ((n : ℝ) + 1) * ((n : ℝ) + 1) < (m : ℝ) + 1 :=
      (Real.logb_lt_logb_iff (by norm_num) (by positivity) (by positivity)).mp h2
    have hmn : (n : ℝ) ^ 2 ≤ m := by nlinarith
    nlinarith

theorem thesesCorP_of (t2 : ThesesThm2) : ThesesCorP := by
  obtain ⟨-, -, ⟨c, K, hc, hK, hsh⟩⟩ := t2
  refine ⟨c, 26 * K, hc, by positivity, fun n m hn hnm hmM => ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    simp at hnm
    nlinarith
  obtain ⟨hlo, hmid, hup⟩ := hsh n m hn hm1 hmM
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hL1 := logb_nPrime_nonneg n m
  have hnl := nlogn_nonneg n
  have e1 := sq_le_mul_logb_nPrime hn hm1 hnm
  refine ⟨le_trans ?_ hlo, hmid, le_trans hup ?_⟩
  · have : (0 : ℝ) ≤ c * (n * Real.logb 2 n) := by positivity
    nlinarith
  · nlinarith

end PowerActivity
