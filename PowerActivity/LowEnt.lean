import PowerActivity.Defs

/-!
# Нижние оценки мощности: энтропийные оценки

* `h2_add_mul_logb_le` — `h₂(p) + p log a ≤ log(1+a)` при `p ∈ [0,1]`, `a > 0`;
  `h2_sub_le` — `h₂(p) − tp ≤ log(1+2^{−t})` (шаг доказательства `entropy`: максимум
  `h₂(p) − tp` равен `log(1+2^{−t})`);
* `logb_one_add_le` — `log(1+u) ≤ 2u` при `u ≥ 0` (из `ln(1+u) ≤ u`, `ln 2 > 1/2`);
* `card_tabSet_le` — число наборов таблиц `t : Fin q → ({0,1}ⁿ → {0,1})`
  с `Σ_v h₂(|t_v|/N) ≤ S` не больше `(N+1)^q 2^{NS}`
  (через `C(N,w) p^w (1−p)^{N−w} ≤ 1` при `p = w/N`);
* `log_le_sum_inv` — `ln(D+5) − ln 4 ≤ Σ_{d=0}^{D} 1/(d+4)`.
-/

namespace PowerActivity

open Finset

namespace Low

/-! ## Поточечная оценка для `h₂` -/

/-- `h₂(p) + p log a ≤ log(1+a)` (неравенство Гиббса для двух исходов). -/
theorem h2_add_mul_logb_le {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 < a) :
    h2 p + p * Real.logb 2 a ≤ Real.logb 2 (1 + a) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1a : 0 < 1 + a := by linarith
  have key : -p * Real.log p - (1 - p) * Real.log (1 - p) + p * Real.log a ≤
      Real.log (1 + a) := by
    rcases hp0.lt_or_eq with hp | hp
    · rcases hp1.lt_or_eq with hq | hq
      · have hq' : 0 < 1 - p := by linarith
        have e1 : Real.log (a / (p * (1 + a))) = Real.log a - Real.log p - Real.log (1 + a) := by
          rw [Real.log_div ha.ne' (by positivity), Real.log_mul hp.ne' h1a.ne']; ring
        have e2 : Real.log (1 / ((1 - p) * (1 + a))) = -Real.log (1 - p) - Real.log (1 + a) := by
          rw [one_div, Real.log_inv, Real.log_mul hq'.ne' h1a.ne']; ring
        have i1 := Real.log_le_sub_one_of_pos (x := a / (p * (1 + a))) (by positivity)
        have i2 := Real.log_le_sub_one_of_pos (x := 1 / ((1 - p) * (1 + a))) (by positivity)
        rw [e1] at i1
        rw [e2] at i2
        have j1 := mul_le_mul_of_nonneg_left i1 hp.le
        have j2 := mul_le_mul_of_nonneg_left i2 hq'.le
        have hz : p * (a / (p * (1 + a)) - 1) + (1 - p) * (1 / ((1 - p) * (1 + a)) - 1) = 0 := by
          field_simp; ring
        nlinarith
      · subst hq
        simp only [sub_self, Real.log_zero, mul_zero, Real.log_one, one_mul, zero_add]
        exact Real.log_le_log ha (by linarith)
    · subst hp
      simp only [neg_zero, zero_mul, sub_zero, Real.log_one, mul_zero, sub_self, add_zero]
      exact Real.log_nonneg (by linarith)
  unfold h2 Real.logb
  calc -p * (Real.log p / Real.log 2) - (1 - p) * (Real.log (1 - p) / Real.log 2) +
        p * (Real.log a / Real.log 2)
      = (-p * Real.log p - (1 - p) * Real.log (1 - p) + p * Real.log a) / Real.log 2 := by ring
    _ ≤ Real.log (1 + a) / Real.log 2 := div_le_div_of_nonneg_right key hl.le

/-- `h₂(p) − tp ≤ log(1 + 2^{−t})` при `p ∈ [0,1]`. -/
theorem h2_sub_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    h2 p - t * p ≤ Real.logb 2 (1 + ((2 : ℝ) ^ t)⁻¹) := by
  have h := h2_add_mul_logb_le hp0 hp1 (a := ((2 : ℝ) ^ t)⁻¹) (by positivity)
  rw [Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  linarith

/-- `log(1+u) ≤ 2u` при `u ≥ 0`. -/
theorem logb_one_add_le {u : ℝ} (hu : 0 ≤ u) : Real.logb 2 (1 + u) ≤ 2 * u := by
  have hl : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have h1 : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos (x := 1 + u) (by linarith); linarith
  have h0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-! ## Подсчёт таблиц с ограниченной суммой энтропий -/

/-- Вес таблицы `|f| = #{x : f(x) = 1}`. -/
def wt {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := (univ.filter fun x => f x = true).card

lemma wt_le {n : ℕ} (f : (Fin n → Bool) → Bool) : wt f ≤ 2 ^ n := by
  unfold wt
  calc _ ≤ (univ : Finset (Fin n → Bool)).card := card_filter_le _ _
    _ = 2 ^ n := by simp

/-- `Σ_f p^{|f|} (1−p)^{N−|f|} = 1`. -/
theorem sum_bernoulli (n : ℕ) (p : ℝ) :
    ∑ f : (Fin n → Bool) → Bool, p ^ wt f * (1 - p) ^ (2 ^ n - wt f) = 1 := by
  have hf : ∀ f : (Fin n → Bool) → Bool, p ^ wt f * (1 - p) ^ (2 ^ n - wt f) =
      ∏ x, (if f x = true then p else 1 - p) := by
    intro f
    rw [prod_ite, prod_const, prod_const]
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin n → Bool)))
      (fun x => f x = true)
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
    unfold wt
    congr 2
    omega
  simp_rw [hf]
  rw [← Fintype.prod_sum (fun (_ : Fin n → Bool) (b : Bool) => if b = true then p else 1 - p)]
  simp

/-- `2^{k log x} = x^k` при `x ≥ 0`, если `x = 0 → k = 0`. -/
lemma two_rpow_mul_logb {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : x = 0 → k = 0) :
    (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 x) = x ^ k := by
  rcases hx.lt_or_eq with hx | hx
  · rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx,
      Real.rpow_natCast]
  · subst hx; simp [hk rfl]

/-- `2^{−N h₂(w/N)} = p^w (1−p)^{N−w}` при `p = w/N`. -/
lemma two_rpow_neg_h2 (N w : ℕ) (hN : 0 < N) (hw : w ≤ N) :
    (2 : ℝ) ^ (-((N : ℝ) * h2 ((w : ℝ) / N))) =
      ((w : ℝ) / N) ^ w * (1 - (w : ℝ) / N) ^ (N - w) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hexp : -((N : ℝ) * h2 ((w : ℝ) / N)) =
      (w : ℝ) * Real.logb 2 ((w : ℝ) / N) +
        ((N - w : ℕ) : ℝ) * Real.logb 2 (1 - (w : ℝ) / N) := by
    unfold h2
    rw [Nat.cast_sub hw]
    field_simp
    ring
  rw [hexp, Real.rpow_add (by norm_num)]
  have hp0 : (0 : ℝ) ≤ (w : ℝ) / N := by positivity
  have hp1 : (w : ℝ) / N ≤ 1 := by rw [div_le_one hNr]; exact_mod_cast hw
  rw [two_rpow_mul_logb hp0 w ?_, two_rpow_mul_logb (by linarith) (N - w) ?_]
  · intro h
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hNr.ne'] at h
    have : w = N := by exact_mod_cast h
    omega
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h hNr.ne'

/-- Мера таблицы `μ(f) = 2^{−N h₂(|f|/N)}`. -/
noncomputable def tmu {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  (2 : ℝ) ^ (-((2 ^ n : ℕ) * h2 ((wt f : ℝ) / (2 ^ n : ℕ))))

lemma tmu_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : 0 < tmu f := by
  unfold tmu; positivity

/-- `Σ_f 2^{−N h₂(|f|/N)} ≤ N + 1`. -/
theorem sum_tmu_le (n : ℕ) : ∑ f : (Fin n → Bool) → Bool, tmu f ≤ 2 ^ n + 1 := by
  have hN : 0 < 2 ^ n := by positivity
  have hmaps : ∀ f ∈ (univ : Finset ((Fin n → Bool) → Bool)), wt f ∈ range (2 ^ n + 1) :=
    fun f _ => mem_range.mpr (Nat.lt_succ_of_le (wt_le f))
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ w ∈ range (2 ^ n + 1), ∑ f ∈ univ.filter (fun f => wt f = w), tmu f
      ≤ ∑ _w ∈ range (2 ^ n + 1), (1 : ℝ) := by
        apply sum_le_sum
        intro w hw
        have hw' : w ≤ 2 ^ n := Nat.le_of_lt_succ (mem_range.mp hw)
        have hp0 : (0 : ℝ) ≤ (w : ℝ) / (2 ^ n : ℕ) := by positivity
        have hp1 : (w : ℝ) / (2 ^ n : ℕ) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hw'
        calc ∑ f ∈ univ.filter (fun f => wt f = w), tmu f
            = ∑ f ∈ univ.filter (fun f => wt f = w),
                ((w : ℝ) / (2 ^ n : ℕ)) ^ wt f * (1 - (w : ℝ) / (2 ^ n : ℕ)) ^ (2 ^ n - wt f) := by
              apply sum_congr rfl
              intro f hf
              rw [(mem_filter.mp hf).2]
              unfold tmu
              rw [(mem_filter.mp hf).2, two_rpow_neg_h2 _ _ hN hw']
          _ ≤ ∑ f : (Fin n → Bool) → Bool,
                ((w : ℝ) / (2 ^ n : ℕ)) ^ wt f * (1 - (w : ℝ) / (2 ^ n : ℕ)) ^ (2 ^ n - wt f) := by
              apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              intro f _ _
              have : (0 : ℝ) ≤ 1 - (w : ℝ) / (2 ^ n : ℕ) := by linarith
              positivity
          _ = 1 := sum_bernoulli n _
    _ = 2 ^ n + 1 := by simp

/-- Наборы таблиц `t : Fin q → ({0,1}ⁿ → {0,1})` с `Σ_v h₂(|t_v|/N) ≤ S`. -/
noncomputable def tabSet (n q : ℕ) (S : ℝ) : Finset (Fin q → (Fin n → Bool) → Bool) :=
  univ.filter fun t => ∑ v, h2 ((wt (t v) : ℝ) / (2 ^ n : ℕ)) ≤ S

/-- Число наборов таблиц с суммой энтропий `≤ S` не больше `(N+1)^q 2^{NS}`. -/
theorem card_tabSet_le (n q : ℕ) (S : ℝ) :
    ((tabSet n q S).card : ℝ) ≤ ((2 : ℝ) ^ n + 1) ^ q * (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := by
  have hN : (0 : ℝ) ≤ (2 ^ n : ℕ) := by positivity
  have key : ∀ t ∈ tabSet n q S, (1 : ℝ) ≤ (2 : ℝ) ^ ((2 ^ n : ℕ) * S) * ∏ v, tmu (t v) := by
    intro t ht
    have hS := (mem_filter.mp ht).2
    unfold tmu
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_add (by norm_num), sum_neg_distrib,
      ← mul_sum]
    apply Real.one_le_rpow (by norm_num)
    have := mul_le_mul_of_nonneg_left hS hN
    linarith
  calc ((tabSet n q S).card : ℝ) = ∑ _t ∈ tabSet n q S, (1 : ℝ) := by simp
    _ ≤ ∑ t ∈ tabSet n q S, (2 : ℝ) ^ ((2 ^ n : ℕ) * S) * ∏ v, tmu (t v) := sum_le_sum key
    _ ≤ ∑ t : Fin q → (Fin n → Bool) → Bool, (2 : ℝ) ^ ((2 ^ n : ℕ) * S) * ∏ v, tmu (t v) := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
        intro t _ _
        exact mul_nonneg (by positivity) (prod_nonneg fun v _ => (tmu_pos _).le)
    _ = (2 : ℝ) ^ ((2 ^ n : ℕ) * S) * ∏ _v : Fin q, ∑ f : (Fin n → Bool) → Bool, tmu f := by
        rw [← mul_sum, Fintype.prod_sum]
    _ = (2 : ℝ) ^ ((2 ^ n : ℕ) * S) * (∑ f : (Fin n → Bool) → Bool, tmu f) ^ q := by
        rw [prod_const, card_univ, Fintype.card_fin]
    _ ≤ (2 : ℝ) ^ ((2 ^ n : ℕ) * S) * ((2 : ℝ) ^ n + 1) ^ q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (sum_nonneg fun f _ => (tmu_pos f).le) (sum_tmu_le n) q
    _ = ((2 : ℝ) ^ n + 1) ^ q * (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := mul_comm _ _

/-! ## Гармоническая сумма -/

/-- `ln(D+5) − ln 4 ≤ Σ_{d=0}^{D} 1/(d+4)`. -/
theorem log_le_sum_inv (D : ℕ) :
    Real.log ((D : ℝ) + 5) - Real.log 4 ≤ ∑ d ∈ range (D + 1), 1 / ((d : ℝ) + 4) := by
  induction D with
  | zero =>
    simp only [Nat.cast_zero, zero_add, range_one, sum_singleton]
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (x := 5 / 4) (by norm_num)
    norm_num at this ⊢; linarith
  | succ D ih =>
    rw [sum_range_succ]
    have hD : (0 : ℝ) < (D : ℝ) + 5 := by positivity
    have h := Real.log_le_sub_one_of_pos (x := ((D : ℝ) + 6) / ((D : ℝ) + 5)) (by positivity)
    rw [Real.log_div (by positivity) hD.ne'] at h
    have e : ((D : ℝ) + 6) / ((D : ℝ) + 5) - 1 = 1 / (((D + 1 : ℕ) : ℝ) + 4) := by
      push_cast; field_simp; ring
    push_cast at e ⊢
    have e6 : (D : ℝ) + 1 + 5 = (D : ℝ) + 6 := by ring
    rw [e6]
    linarith

end Low

end PowerActivity
