import PowerActivity.LowRepr

/-!
# Подсчёт описаний схем (утверждение `encoding`)

`badSet n m d S` — операторы `F : {0,1}ⁿ → {0,1}ᵐ`, у которых есть схема с `S_d ≤ S`.
Каждый такой оператор восстанавливается (`rv_decode_encode`) по описанию из `descSet q s S`
при `q = |L_{d+1}| ≤ M`, `s = |B_d| ≤ M`, `M = m 2^{d+1}` (оценки `rev-layers`).

* `card_descSet_le` — `|descSet| ≤ (3K²)^s K^m (N+1)^q 2^{NS}`, `K = n+q+s`;
* `encoding_count` — `|badSet| ≤ L^{11 m 2^d} 2^{NS}`, `L = 2ⁿ (m+1) 2^{d+2}` (`m ≥ 1`);
* `encoding_bound` — `encoding` в явном виде:
  `|badSet| ≤ 2^{NS + C₀ m 2^d (n + log(m+1) + d + 1)}`, `C₀ = 22`
  (то есть описание длины `≤ NS + C₀ m 2^d (n + log(m+1) + d + 1)`).
-/

namespace PowerActivity

open Finset

namespace Low

/-- Описания, у которых таблицы имеют сумму энтропий `≤ S`. -/
noncomputable def descSet (n m q s : ℕ) (S : ℝ) : Finset (Desc n m q s) :=
  univ ×ˢ univ ×ˢ tabSet n q S

lemma card_descSet_le (n m q s : ℕ) (S : ℝ) :
    ((descSet n m q s S).card : ℝ) ≤
      (((3 * (n + q + s) ^ 2) ^ s * (n + q + s) ^ m * (2 ^ n + 1) ^ q : ℕ) : ℝ) *
        (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := by
  have h1 : (descSet n m q s S).card =
      (3 * (n + q + s) ^ 2) ^ s * ((n + q + s) ^ m * (tabSet n q S).card) := by
    simp only [descSet, card_product, card_univ, Fintype.card_fun, Fintype.card_prod,
      Op.card, Fintype.card_fin]
    ring
  rw [h1]
  push_cast
  have h2 := card_tabSet_le n q S
  have hA : (0 : ℝ) ≤ (3 * ((n : ℝ) + q + s) ^ 2) ^ s * ((n : ℝ) + q + s) ^ m := by positivity
  calc (3 * ((n : ℝ) + q + s) ^ 2) ^ s * (((n : ℝ) + q + s) ^ m * ((tabSet n q S).card : ℝ))
      = (3 * ((n : ℝ) + q + s) ^ 2) ^ s * ((n : ℝ) + q + s) ^ m * ((tabSet n q S).card : ℝ) := by
        ring
    _ ≤ (3 * ((n : ℝ) + q + s) ^ 2) ^ s * ((n : ℝ) + q + s) ^ m *
          (((2 : ℝ) ^ n + 1) ^ q * (2 : ℝ) ^ ((2 ^ n : ℕ) * S)) :=
        mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by push_cast; ring

open Classical in
/-- Операторы, у которых есть схема с `S_d ≤ S`. -/
noncomputable def badSet (n m d : ℕ) (S : ℝ) : Finset ((Fin n → Bool) → Fin m → Bool) :=
  univ.filter fun F => ∃ C : Circ n (Fin m), C.Realizes F ∧ C.rvS d ≤ S

lemma badSet_sub (n m d : ℕ) (S : ℝ) :
    badSet n m d S ⊆ (range (m * 2 ^ (d + 1) + 1) ×ˢ range (m * 2 ^ (d + 1) + 1)).biUnion
      fun p => (descSet n m p.1 p.2 S).image decode := by
  intro F hF
  simp only [badSet, mem_filter, mem_univ, true_and] at hF
  obtain ⟨C, hC, hS⟩ := hF
  simp only [mem_biUnion, mem_product, mem_range, mem_image]
  refine ⟨((C.rvLayer d).card, (C.rvBall d).card),
    ⟨Nat.lt_succ_of_le (C.card_rvLayer_le d), Nat.lt_succ_of_le (C.card_rvBall_le d)⟩,
    C.rvEncode d, ?_, C.rv_decode_encode d hC⟩
  simp only [descSet, mem_product, mem_univ, true_and, tabSet, mem_filter]
  rw [C.rvEncode_tab_sum d]
  exact hS

/-- `L = 2ⁿ (m+1) 2^{d+2}`. -/
def Lb (n m d : ℕ) : ℕ := 2 ^ n * (m + 1) * 2 ^ (d + 2)

lemma Lb_ge (n m d : ℕ) : 4 * 2 ^ n * 2 ^ d ≤ Lb n m d := by
  unfold Lb
  rw [pow_add]
  have : 1 ≤ m + 1 := by omega
  calc 4 * 2 ^ n * 2 ^ d = 2 ^ n * 1 * (2 ^ d * 4) := by ring
    _ ≤ 2 ^ n * (m + 1) * (2 ^ d * 2 ^ 2) := by
        apply Nat.mul_le_mul (Nat.mul_le_mul_left _ this); norm_num

lemma Lb_pos (n m d : ℕ) : 1 ≤ Lb n m d := by
  have := Lb_ge n m d
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  nlinarith

lemma K_lt_Lb (n m d q s : ℕ) (hq : q ≤ m * 2 ^ (d + 1)) (hs : s ≤ m * 2 ^ (d + 1)) :
    n + q + s < Lb n m d := by
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have ha : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hM : m * 2 ^ (d + 1) = 2 * (m * 2 ^ d) := by rw [pow_succ]; ring
  rw [hM] at hq hs
  have hL : Lb n m d = 4 * (2 ^ n * m * 2 ^ d) + 4 * 2 ^ n * 2 ^ d := by
    unfold Lb; rw [pow_add]; ring
  rw [hL]
  have h1 : m * 2 ^ d ≤ 2 ^ n * m * 2 ^ d := by
    calc m * 2 ^ d = 1 * m * 2 ^ d := by ring
      _ ≤ 2 ^ n * m * 2 ^ d := by gcongr
  have h2 : 2 ^ n ≤ 4 * 2 ^ n * 2 ^ d := by
    calc 2 ^ n = 1 * 2 ^ n * 1 := by ring
      _ ≤ 4 * 2 ^ n * 2 ^ d := by gcongr; omega
  omega

lemma three_le_Lb (n m d : ℕ) : 3 ≤ Lb n m d := by
  have := Lb_ge n m d
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  nlinarith

lemma pow_add_one_le_Lb (n m d : ℕ) : 2 ^ n + 1 ≤ Lb n m d := by
  have := Lb_ge n m d
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  nlinarith

lemma K_le_Lb (n m d q s : ℕ) (hq : q ≤ m * 2 ^ (d + 1)) (hs : s ≤ m * 2 ^ (d + 1)) :
    n + q + s ≤ Lb n m d := (K_lt_Lb n m d q s hq hs).le

lemma M_succ_le_Lb (n m d : ℕ) : m * 2 ^ (d + 1) + 1 ≤ Lb n m d := by
  have h := K_lt_Lb n m d 0 (m * 2 ^ (d + 1)) (Nat.zero_le _) le_rfl
  omega

/-- Оценка одного слагаемого: `(3K²)^s K^m (N+1)^q ≤ L^{4M+m}`. -/
lemma term_le (n m d q s : ℕ) (hq : q ≤ m * 2 ^ (d + 1)) (hs : s ≤ m * 2 ^ (d + 1)) :
    (3 * (n + q + s) ^ 2) ^ s * (n + q + s) ^ m * (2 ^ n + 1) ^ q ≤
      Lb n m d ^ (4 * (m * 2 ^ (d + 1)) + m) := by
  set L := Lb n m d
  set M := m * 2 ^ (d + 1)
  have hL1 : 1 ≤ L := Lb_pos n m d
  have hK := K_le_Lb n m d q s hq hs
  have h3 : 3 * (n + q + s) ^ 2 ≤ L ^ 3 := by
    calc 3 * (n + q + s) ^ 2 ≤ L * L ^ 2 :=
          Nat.mul_le_mul (three_le_Lb n m d) (Nat.pow_le_pow_left hK 2)
      _ = L ^ 3 := by ring
  calc (3 * (n + q + s) ^ 2) ^ s * (n + q + s) ^ m * (2 ^ n + 1) ^ q
      ≤ (L ^ 3) ^ M * L ^ m * L ^ M := by
        apply Nat.mul_le_mul (Nat.mul_le_mul _ (Nat.pow_le_pow_left hK m))
        · calc (2 ^ n + 1) ^ q ≤ L ^ q := Nat.pow_le_pow_left (pow_add_one_le_Lb n m d) q
            _ ≤ L ^ M := Nat.pow_le_pow_right hL1 hq
        · calc (3 * (n + q + s) ^ 2) ^ s ≤ (L ^ 3) ^ s := Nat.pow_le_pow_left h3 s
            _ ≤ (L ^ 3) ^ M := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hL1) hs
    _ = L ^ (4 * M + m) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf

/-- **`encoding` (подсчёт).** При `m ≥ 1` число операторов, у которых есть схема с `S_d ≤ S`,
не больше `L^{11 m 2^d} 2^{NS}`, `L = 2ⁿ (m+1) 2^{d+2}`. -/
theorem encoding_count (n m d : ℕ) (hm : 1 ≤ m) (S : ℝ) :
    ((badSet n m d S).card : ℝ) ≤
      ((Lb n m d ^ (11 * m * 2 ^ d) : ℕ) : ℝ) * (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := by
  set M := m * 2 ^ (d + 1)
  set L := Lb n m d
  have hL1 : 1 ≤ L := Lb_pos n m d
  have hX : (0 : ℝ) ≤ (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := by positivity
  have hsum : ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
      (3 * (n + p.1 + p.2) ^ 2) ^ p.2 * (n + p.1 + p.2) ^ m * (2 ^ n + 1) ^ p.1 ≤
        L ^ (11 * m * 2 ^ d) := by
    calc ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
          (3 * (n + p.1 + p.2) ^ 2) ^ p.2 * (n + p.1 + p.2) ^ m * (2 ^ n + 1) ^ p.1
        ≤ ∑ _p ∈ range (M + 1) ×ˢ range (M + 1), L ^ (4 * M + m) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_product, mem_range] at hp
          exact term_le n m d p.1 p.2 (by omega) (by omega)
      _ = (M + 1) ^ 2 * L ^ (4 * M + m) := by
          rw [sum_const, card_product, card_range, smul_eq_mul]; ring
      _ ≤ L ^ 2 * L ^ (4 * M + m) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (M_succ_le_Lb n m d) 2)
      _ = L ^ (4 * M + m + 2) := by rw [← pow_add]; ring_nf
      _ ≤ L ^ (11 * m * 2 ^ d) := by
          apply Nat.pow_le_pow_right hL1
          have h2d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
          have hM : M = 2 * (m * 2 ^ d) := by simp only [M]; rw [pow_succ]; ring
          have : 1 ≤ m * 2 ^ d := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have : m ≤ m * 2 ^ d := Nat.le_mul_of_pos_right m (by positivity)
          rw [hM]; nlinarith
  calc ((badSet n m d S).card : ℝ)
      ≤ ((((range (M + 1) ×ˢ range (M + 1)).biUnion
          fun p => (descSet n m p.1 p.2 S).image decode).card : ℕ) : ℝ) := by
        exact_mod_cast card_le_card (badSet_sub n m d S)
    _ ≤ ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
          (((descSet n m p.1 p.2 S).image decode).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ p ∈ range (M + 1) ×ˢ range (M + 1), ((descSet n m p.1 p.2 S).card : ℝ) := by
        apply sum_le_sum; intro p _; exact_mod_cast card_image_le
    _ ≤ ∑ p ∈ range (M + 1) ×ˢ range (M + 1),
          (((3 * (n + p.1 + p.2) ^ 2) ^ p.2 * (n + p.1 + p.2) ^ m * (2 ^ n + 1) ^ p.1 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := by
        apply sum_le_sum; intro p _; exact card_descSet_le n m p.1 p.2 S
    _ = ((∑ p ∈ range (M + 1) ×ˢ range (M + 1),
          (3 * (n + p.1 + p.2) ^ 2) ^ p.2 * (n + p.1 + p.2) ^ m * (2 ^ n + 1) ^ p.1 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((2 ^ n : ℕ) * S) := by
        rw [← sum_mul, Nat.cast_sum]
    _ ≤ ((L ^ (11 * m * 2 ^ d) : ℕ) : ℝ) * (2 : ℝ) ^ ((2 ^ n : ℕ) * S) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsum) hX

/-- `L^e ≤ 2^{2e (n + log(m+1) + d + 1)}`. -/
lemma Lb_pow_le (n m d e : ℕ) :
    ((Lb n m d ^ e : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (2 * (e : ℝ) * (n + Real.logb 2 (m + 1) + d + 1)) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlog : 0 ≤ Real.logb 2 ((m : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hL : ((Lb n m d : ℕ) : ℝ) = (2 : ℝ) ^ ((n : ℝ) + Real.logb 2 (m + 1) + d + 2) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hm1]
    unfold Lb
    push_cast
    rw [Real.rpow_natCast, Real.rpow_natCast, pow_add]
    norm_num
    ring
  push_cast
  rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **`encoding` (явная форма).** Число операторов `F : {0,1}ⁿ → {0,1}ᵐ` (`m ≥ 1`), у которых есть
схема с `S_d ≤ S`, не больше `2^{NS + C₀ m 2^d (n + log(m+1) + d + 1)}` с `C₀ = 22`. -/
theorem encoding_bound (n m d : ℕ) (hm : 1 ≤ m) (S : ℝ) :
    ((badSet n m d S).card : ℝ) ≤
      (2 : ℝ) ^ ((2 ^ n : ℕ) * S + 22 * m * 2 ^ d * (n + Real.logb 2 (m + 1) + d + 1)) := by
  refine (encoding_count n m d hm S).trans ?_
  rw [Real.rpow_add (by norm_num), mul_comm ((2 : ℝ) ^ ((2 ^ n : ℕ) * S))]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  refine (Lb_pow_le n m d (11 * m * 2 ^ d)).trans (le_of_eq ?_)
  push_cast
  ring_nf

end Low

end PowerActivity
