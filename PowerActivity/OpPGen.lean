import PowerActivity.OpPBase
import PowerActivity.UpUpper
import PowerActivity.ThesesSpec

/-!
# Верхняя оценка `P`-активности операторов: схема для любого оператора

Всё — в пространстве имён `PowerActivity.OpP`.

* `genW M` — общая конструкция `Up.genC` с произвольным ярусом минтермов `M`
  (`Up.genC = genW (Up.mtC n)` по определению, `genC_eq`);
* `genP = genW (mtP n)` — ярус минтермов заменён листьями схемы Горяшко;
* при одинаковых значениях выходов первых ярусов `genW M` и `genW M'` реализуют один оператор
  (`genW_eval`), а так как прочие ярусы состоят из `∨` (`P = E`),
  `P(genW M) + E(M') = P(M) + E(genW M')` (`genW_P`);
* `genP_spec`: `genP` реализует `F`, и на каждом наборе
  `P ≤ (2n² + n + 2) + (2n + 1 + (2^{2^j} − 1) + ⌈m/r⌉(n − j) + m⌈log r⌉)`;
* `upperPOp_nat`: при параметрах `j`, `r` из `group-upper` (`Up.jj`, `Up.ll`)
  `P ≤ 2n² + 4n + 3 + 3m + m⌈log ℓ⌉`;
* `upperPOp_goal_pf : UpperPOpGoal` с `K = 9`: `P(Σ,x) ≤ 9 (n² + m log(1+Δ))`.
-/

namespace PowerActivity

open Finset Up

namespace OpP

variable {n : ℕ}

/-- Общая конструкция `Up.genC` с ярусом минтермов `M` (входы яруса индикаторов подмножеств
питаются выходами `M`). -/
def genW {m : ℕ} (M : Circ n (Fin (2 ^ n + 1))) (j r : ℕ) (hj : j ≤ n) (hr : 0 < r)
    (F : (Fin n → Bool) → Fin m → Bool) : Circ n (Fin m) :=
  reout (comp (comp (comp M id (stB n j hj)) finProdFinEquiv.symm (stC n m j r F))
    (fD m r) (stD m r hr))
    fun c => (⟨c / r, div_lt_nb hr c.2⟩, ⟨c % r, Nat.mod_lt _ hr⟩)

lemma genC_eq {m : ℕ} (j r : ℕ) (hn : 0 < n) (hj : j ≤ n) (hr : 0 < r)
    (F : (Fin n → Bool) → Fin m → Bool) :
    genC n m j r hn hj hr F = genW (mtC n hn) j r hj hr F := rfl

section genW

variable {m : ℕ} {M M' : Circ n (Fin (2 ^ n + 1))} (j r : ℕ) (hj : j ≤ n) (hr : 0 < r)
  (F : (Fin n → Bool) → Fin m → Bool)

/-- Схемы `genW M` и `genW M'` с одинаковыми значениями выходов `M`, `M'` вычисляют одно и то же. -/
lemma genW_eval (hM : ∀ x t, M.eval x t = M'.eval x t) (x : Fin n → Bool) (c : Fin m) :
    (genW M j r hj hr F).eval x c = (genW M' j r hj hr F).eval x c := by
  simp only [genW, reout_eval, comp_eval, hM]

/-- Ярусы после минтермов состоят из `∨`, поэтому их `P`-активность равна мощности:
`P(genW M) + E(M') = P(M) + E(genW M')`. -/
lemma genW_P (hM : ∀ x t, M.eval x t = M'.eval x t) (x : Fin n → Bool) :
    (genW M j r hj hr F).P x + M'.E x = M.P x + (genW M' j r hj hr F).E x := by
  simp only [genW, reout_P, reout_E, comp_P, comp_E, P_eq_E (stB_or n j hj),
    P_eq_E (stC_or n m j r F), P_eq_E (stD_or m r hr), comp_eval, hM]
  omega

end genW

/-- Схема с малой `P`-активностью: ярус минтермов — листья схемы Горяшко. -/
noncomputable def genP (n m j r : ℕ) (hn : 0 < n) (hj : j ≤ n) (hr : 0 < r)
    (F : (Fin n → Bool) → Fin m → Bool) : Circ n (Fin m) :=
  genW (mtP n hn) j r hj hr F

lemma mtP_mtC (hn : 0 < n) (x : Fin n → Bool) (t : Fin (2 ^ n + 1)) :
    (mtP n hn).eval x t = (mtC n hn).eval x t := by
  rw [mtP_eval, (mtC_spec n hn x).1 t]

/-- Реализация `F` и поточечная оценка `P`-активности схемы `genP`. -/
theorem genP_spec {m : ℕ} (j r : ℕ) (hn : 0 < n) (hj : j ≤ n) (hr : 0 < r)
    (F : (Fin n → Bool) → Fin m → Bool) :
    (genP n m j r hn hj hr F).Realizes F ∧ ∀ x,
      (genP n m j r hn hj hr F).P x ≤ (2 * n * n + n + 2) +
        (2 * n + 1 + (2 ^ 2 ^ j - 1) + (m + r - 1) / r * (n - j) + m * Nat.clog 2 r) := by
  obtain ⟨h1, h2⟩ := gen_spec (n := n) (m := m) j r hn hj hr F
  rw [genC_eq] at h1 h2
  constructor
  · intro x
    funext c
    rw [genP, genW_eval j r hj hr F (mtP_mtC hn) x c]
    exact congrFun (h1 x) c
  · intro x
    have e1 := genW_P j r hj hr F (mtP_mtC hn) x
    have e2 := h2 x
    have e3 := mtP_P n hn x
    rw [genP]
    omega

/-- Целочисленная форма оценки: при параметрах `j`, `r` из `group-upper`
`P ≤ 2n² + 4n + 3 + 3m + m⌈log ℓ⌉`. -/
theorem upperPOp_nat (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (F : (Fin n → Bool) → Fin m → Bool) :
    ∃ C : Circ n (Fin m), C.Realizes F ∧
      ∀ x, C.P x ≤ 2 * n * n + 4 * n + 3 + 3 * m + m * Nat.clog 2 (ll n m) := by
  have hj : jj n m ≤ n := min_le_left _ _
  have hl : 1 ≤ ll n m := le_max_left _ _
  have hr : 0 < min m (ll n m) := lt_min (by omega) (by omega)
  obtain ⟨h1, h2⟩ := genP_spec (n := n) (m := m) (jj n m) (min m (ll n m)) (by omega) hj hr F
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

/-- Верхняя оценка `P`-активности операторов: `P(Σ,x) ≤ 9 (n² + m log(1+Δ))`
при `n ≥ 1`, `1 ≤ m ≤ 2^{2^n}`. -/
theorem upperPOp_goal_pf : UpperPOpGoal := by
  refine ⟨9, ?_⟩
  intro n m hn hm hM F
  obtain ⟨C, hC, hP⟩ := upperPOp_nat n m hn hm F
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨hc, hL⟩ := clog_ll_le n m hm hM
  have h1 : (C.P x : ℝ) ≤ 2 * n * n + 4 * n + 3 + 3 * m + m * (Nat.clog 2 (ll n m) : ℝ) := by
    exact_mod_cast hP x
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (m : ℝ) * (Nat.clog 2 (ll n m) : ℝ) ≤ m * (2 * Real.logb 2 (1 + Delta n m)) :=
    mul_le_mul_of_nonneg_left hc hm0
  have h3 : (m : ℝ) * 1 ≤ m * Real.logb 2 (1 + Delta n m) := mul_le_mul_of_nonneg_left hL hm0
  have h4 : (4 : ℝ) * n + 3 ≤ 7 * (n : ℝ) ^ 2 := by nlinarith
  nlinarith

end OpP

end PowerActivity
