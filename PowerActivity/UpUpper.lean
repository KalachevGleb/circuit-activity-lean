import PowerActivity.Spec
import PowerActivity.UpGen

/-!
# Верхние оценки: цели `ExistsGoal`, `UpperBlockGoal`, `UpperGroupGoal`

Всё — в пространстве имён `Up`; итоговые имена `exists_goal` и т. д. даёт `UpMain`.
* `Up.exists_goal_pf` — общая конструкция при `j = 0`, `r = 1`;
* `Up.upperBlock_goal_pf` — оценка `block-upper` с `c₀ = 2` (общая конструкция при `j = 0`,
  `r = min{m,n}`);
* `Up.upperGroup_goal_pf` — оценка `group-upper` с `K = 5`; параметры
  `j = min{n, ⌊log ⌊log (m+1)⌋⌋}` (группы размера `2^j ≤ log (m+1)`),
  `ℓ = max{1, n - j}` (глубина деревьев), `r = min{m, ℓ}`;
  ключевой шаг (`group-param`): `ℓ < 1 + Δ`, откуда `⌈log ℓ⌉ ≤ 2 log (1 + Δ)`.
-/

namespace PowerActivity

open Finset

namespace Up

/-- Существование реализации любого оператора при `n ≥ 1`. -/
theorem exists_goal_pf : ExistsGoal := by
  intro n m hn F
  obtain ⟨h, -⟩ := gen_spec (n := n) (m := m) 0 1 (by omega) (Nat.zero_le n) one_pos F
  exact ⟨_, h⟩

/-- `block-upper`: `E ≤ 2n + 2 + n⌈m/r⌉ + m⌈log r⌉`, `r = min{m,n}`. -/
theorem upperBlock_goal_pf : UpperBlockGoal := by
  refine ⟨2, ?_⟩
  intro n m hn hm F
  have hr : 0 < min m n := lt_min (by omega) (by omega)
  obtain ⟨h1, h2⟩ := gen_spec (n := n) (m := m) 0 (min m n) (by omega) (Nat.zero_le n) hr F
  refine ⟨_, h1, fun x => ?_⟩
  have h := h2 x
  simp only [pow_zero, pow_one, Nat.sub_zero] at h
  rw [Nat.mul_comm n]
  omega

/-! ## Оценка `group-upper` -/

/-- Логарифм группы: `j = min{n, ⌊log ⌊log (m+1)⌋⌋}`. -/
def jj (n m : ℕ) : ℕ := min n (Nat.log 2 (Nat.log 2 (m + 1)))

/-- Глубина деревьев `D_{B,v}`: `ℓ = max{1, n - j}`. -/
def ll (n m : ℕ) : ℕ := max 1 (n - jj n m)

/-- Целочисленная форма оценки `group-upper`: `E ≤ 3n + 1 + 3m + m⌈log ℓ⌉`. -/
theorem upperGroup_nat (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (F : (Fin n → Bool) → Fin m → Bool) :
    ∃ C : Circ n (Fin m), C.Realizes F ∧
      ∀ x, C.E x ≤ 3 * n + 1 + 3 * m + m * Nat.clog 2 (ll n m) := by
  have hj : jj n m ≤ n := min_le_left _ _
  have hl : 1 ≤ ll n m := le_max_left _ _
  have hr : 0 < min m (ll n m) := lt_min (by omega) (by omega)
  obtain ⟨h1, h2⟩ := gen_spec (n := n) (m := m) (jj n m) (min m (ll n m)) (by omega) hj hr F
  refine ⟨_, h1, fun x => ?_⟩
  -- группы малы: `2^{2^j} ≤ m + 1`
  have e1 : 2 ^ 2 ^ jj n m - 1 ≤ m := by
    have hlam : 0 < Nat.log 2 (m + 1) := Nat.log_pos (by norm_num) (by omega)
    have a1 : 2 ^ jj n m ≤ Nat.log 2 (m + 1) :=
      (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans
        (Nat.pow_log_le_self 2 (by omega))
    have a2 : 2 ^ 2 ^ jj n m ≤ m + 1 :=
      (Nat.pow_le_pow_right (by norm_num) a1).trans (Nat.pow_log_le_self 2 (by omega))
    omega
  -- деревья: `⌈m/r⌉ (n - j) ≤ 2m + n`
  have e2 : (m + min m (ll n m) - 1) / min m (ll n m) * (n - jj n m) ≤ 2 * m + n := by
    have hnl : n - jj n m ≤ ll n m := le_max_right _ _
    by_cases hlm : ll n m ≤ m
    · rw [min_eq_right hlm]
      have := Nat.div_mul_le_self (m + ll n m - 1) (ll n m)
      have := Nat.mul_le_mul_left ((m + ll n m - 1) / ll n m) hnl
      omega
    · rw [min_eq_left (by omega)]
      rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
      omega
  have e3 : m * Nat.clog 2 (min m (ll n m)) ≤ m * Nat.clog 2 (ll n m) :=
    Nat.mul_le_mul_left _ (Nat.clog_mono_right _ (min_le_right _ _))
  have := h2 x
  omega

lemma natCast_lt_logb {k : ℕ} {y : ℝ} (h : (2 : ℝ) ^ k < y) : (k : ℝ) < Real.logb 2 y := by
  have h0 : (0 : ℝ) < 2 ^ k := by positivity
  have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) h0 h
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

lemma logb_lt_natCast {k : ℕ} {y : ℝ} (hy : 0 < y) (h : y < (2 : ℝ) ^ k) :
    Real.logb 2 y < k := by
  have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hy h
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

/-- `group-param`: `ℓ < 1 + Δ`; отсюда `⌈log ℓ⌉ ≤ 2 log(1 + Δ)`; кроме того, `log(1 + Δ) ≥ 1`. -/
theorem clog_ll_le (n m : ℕ) (hm : 1 ≤ m) (hM : m ≤ 2 ^ 2 ^ n) :
    (Nat.clog 2 (ll n m) : ℝ) ≤ 2 * Real.logb 2 (1 + Delta n m) ∧
      1 ≤ Real.logb 2 (1 + Delta n m) := by
  have hD1 : 1 ≤ Delta n m := le_max_left _ _
  have hL : 1 ≤ Real.logb 2 (1 + Delta n m) := by
    have h2 : (2 : ℝ) ≤ 1 + Delta n m := by linarith
    have := (Real.logb_le_logb (b := 2) (by norm_num) (by norm_num) (by linarith)).2 h2
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  refine ⟨?_, hL⟩
  by_cases hjn : n ≤ Nat.log 2 (Nat.log 2 (m + 1))
  · have : ll n m = 1 := by unfold ll jj; rw [min_eq_left hjn]; simp
    rw [this, Nat.clog_one_right]
    simp only [Nat.cast_zero]
    linarith
  · push Not at hjn
    set lam := Nat.log 2 (m + 1) with hlam
    set j0 := Nat.log 2 lam with hj0
    have hll : ll n m = n - j0 := by
      unfold ll jj; rw [min_eq_right hjn.le]; omega
    -- `log (m+1) < 2^{j0+1}`
    have a1 : m + 1 < 2 ^ (lam + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have a2 : lam < 2 ^ (j0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have b1 : Real.logb 2 ((m : ℝ) + 1) < (lam + 1 : ℕ) :=
      logb_lt_natCast (by positivity) (by exact_mod_cast a1)
    have b2 : ((lam + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j0 + 1) := by exact_mod_cast a2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have b3 : 0 < Real.logb 2 ((m : ℝ) + 1) := Real.logb_pos (by norm_num) (by linarith)
    have b4 : Real.logb 2 (Real.logb 2 ((m : ℝ) + 1)) < (j0 + 1 : ℕ) :=
      logb_lt_natCast b3 (lt_of_lt_of_le b1 b2)
    have hMc : Mcap n m = m := min_eq_left hM
    have hD : (n : ℝ) - (j0 + 1 : ℕ) < Delta n m := by
      unfold Delta
      rw [hMc]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hlD : ((ll n m : ℕ) : ℝ) < 1 + Delta n m := by
      rw [hll, Nat.cast_sub (by omega)]
      push_cast at hD ⊢
      linarith
    -- `⌈log ℓ⌉ - 1 < log(1+Δ)`
    by_cases hl1 : ll n m = 1
    · rw [hl1, Nat.clog_one_right]; simp only [Nat.cast_zero]; linarith
    · have hl2 : 1 < ll n m := by have : 1 ≤ ll n m := le_max_left _ _; omega
      have c1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hl2
      have c2 : 0 < Nat.clog 2 (ll n m) := Nat.clog_pos (by norm_num) hl2
      have c3 : ((2 : ℝ) ^ (Nat.clog 2 (ll n m)).pred) < 1 + Delta n m :=
        lt_of_lt_of_le (by exact_mod_cast c1) hlD.le
      have c4 := natCast_lt_logb c3
      have c5 : ((Nat.clog 2 (ll n m)).pred : ℝ) = (Nat.clog 2 (ll n m) : ℝ) - 1 := by
        rw [Nat.pred_eq_sub_one, Nat.cast_sub (by omega)]; simp
      rw [c5] at c4
      linarith

/-- `group-upper`: `Ê(n,m) ≤ 5 (n + m log(1+Δ))` при `n ≥ 2`, `1 ≤ m ≤ 2^{2^n}`. -/
theorem upperGroup_goal_pf : UpperGroupGoal := by
  refine ⟨5, ?_⟩
  intro n m hn hm hM F
  obtain ⟨C, hC, hE⟩ := upperGroup_nat n m (by omega) hm F
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨hc, hL⟩ := clog_ll_le n m hm hM
  have h1 : (C.E x : ℝ) ≤ 3 * n + 1 + 3 * m + m * (Nat.clog 2 (ll n m) : ℝ) := by
    exact_mod_cast hE x
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (m : ℝ) * (Nat.clog 2 (ll n m) : ℝ) ≤ m * (2 * Real.logb 2 (1 + Delta n m)) :=
    mul_le_mul_of_nonneg_left hc hm0
  have h3 : (m : ℝ) * 1 ≤ m * Real.logb 2 (1 + Delta n m) := mul_le_mul_of_nonneg_left hL hm0
  nlinarith

end Up

end PowerActivity
