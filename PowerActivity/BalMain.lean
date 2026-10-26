import PowerActivity.BalCount
import PowerActivity.BalCirc
import PowerActivity.ApxCount
import PowerActivity.ThesesSpec

/-!
# Тезисы, цель `BalGoal`: различные сбалансированные выходы почти всех операторов

Пусть `N = 2ⁿ`, `K = 2^N` — число булевых функций. Функция *хорошая* (`Good`), если она
не проекция и сбалансирована (`N/4 < |g| < 3N/4`); плохие функции — `badSet n`.
Для оператора `F` координаты `coord F : Fin m → Fn n`; `goodVals (badSet n) (coord F)` —
различные хорошие координатные функции.

* `card_badSet_le` — при `n ≥ 10` плохих функций не больше `B = 2^{N−n}`
  (несбалансированные лежат в шарах Хэмминга радиуса `N/4` вокруг констант —
  `Apx.card_ball_le`; проекций `n`);
* `card_bad_mul_le` — при `n ≥ 10`, `1 ≤ m ≤ K` доля кортежей с `|goodVals| ≤ t = ⌊m/16⌋`
  не больше `8/2ⁿ`. Подсчёт `card_few_le` даёт `2^m K^t (B+t)^{m−t}`; два режима:
  `t ≤ B` — доля `≤ (8B/K)^{m−t} ≤ 8B/K = 8/2ⁿ`; `t > B` — доля `≤ (16t/K)^{m−t} 2^{−(m−t)}
  ≤ 2^{−(m−t)} ≤ 2^{−n}` (здесь `m − t ≥ t > B ≥ n`);
* `bal_goal : BalGoal` — `c = 1/64`, `ε(n) = 8·2^{−n}` при `n ≥ 10` (`ε(n) = 1` при `n < 10`):
  если хороших координат больше `⌊m/16⌋`, то `m ≤ 16|S|` и любая схема имеет
  `E(Σ) ≥ |S|/4 ≥ m/64`, `U(Σ) ≥ m/64` (`le_Eav_Uav`).

В `many-outputs` (`Low.many_out`) оценка `E ≥ m/4` получена для одного специального
оператора; здесь та же идея (разные непроекции реализуются разными элементами) применена
к почти всем операторам, с константой `1/64` вместо `1/4`, и дополнительно к мере `U`.
-/

namespace PowerActivity.Bal

open Finset Filter Topology Low

/-- Хорошая функция: непроекция с `N/4 < |g| < 3N/4`. -/
def Good {n : ℕ} (g : Fn n) : Prop := ¬ IsProj g ∧ Balanced g

open Classical in
/-- Плохие функции: проекции и несбалансированные функции. -/
noncomputable def badSet (n : ℕ) : Finset (Fn n) := univ.filter fun g => ¬ Good g

lemma mem_badSet {n : ℕ} {g : Fn n} : g ∈ badSet n ↔ ¬ Good g := by
  classical
  unfold badSet
  rw [mem_filter]
  simp

/-- Координатные функции оператора. -/
def coord {n m : ℕ} (F : (Fin n → Bool) → Fin m → Bool) : Fin m → Fn n := fun k x => F x k

lemma card_Fn (n : ℕ) : Fintype.card (Fn n) = 2 ^ 2 ^ n := by
  simp [Fn]

/-! ## Число плохих функций -/

/-- Вложение функций в операторы с одним выходом (для шаров Хэмминга `Apx.ball`). -/
def toOp {n : ℕ} (g : Fn n) : (Fin n → Bool) → Fin 1 → Bool := fun x _ => g x

lemma toOp_injective {n : ℕ} : Function.Injective (toOp (n := n)) := by
  intro g g' h
  funext x
  exact congrFun (congrFun h x) 0

/-- Функций с `|g| ≤ N/4` не больше `4^N / 3^{N − ⌊N/4⌋}`. -/
lemma card_light_le (n : ℕ) :
    (univ.filter fun g : Fn n => 4 * wt g ≤ 2 ^ n).card * 3 ^ (2 ^ n - 2 ^ n / 4) ≤
      4 ^ 2 ^ n := by
  have h1 : (univ.filter fun g : Fn n => 4 * wt g ≤ 2 ^ n).card ≤
      (Apx.ball (fun _ : Fin n → Bool => false)).card := by
    apply card_le_card_of_injOn toOp
    · intro g hg
      rw [mem_coe, mem_filter] at hg
      rw [mem_coe, Apx.ball, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hf : (univ.filter fun x => false = toOp g x 0) = univ.filter fun x => (!g x) = true := by
        ext x
        cases h : g x <;> simp [toOp, h]
      rw [hf]
      have h1 := wt_add_wt_not g
      have h2 : wt (fun x => !g x) = (univ.filter fun x => (!g x) = true).card := rfl
      have h3 := hg.2
      omega
    · exact toOp_injective.injOn
  calc _ ≤ (Apx.ball (fun _ : Fin n → Bool => false)).card * 3 ^ (2 ^ n - 2 ^ n / 4) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 4 ^ 2 ^ n := Apx.card_ball_le _

/-- Функций с `|g| ≥ 3N/4` не больше `4^N / 3^{N − ⌊N/4⌋}`. -/
lemma card_heavy_le (n : ℕ) :
    (univ.filter fun g : Fn n => 3 * 2 ^ n ≤ 4 * wt g).card * 3 ^ (2 ^ n - 2 ^ n / 4) ≤
      4 ^ 2 ^ n := by
  have h1 : (univ.filter fun g : Fn n => 3 * 2 ^ n ≤ 4 * wt g).card ≤
      (Apx.ball (fun _ : Fin n → Bool => true)).card := by
    apply card_le_card_of_injOn toOp
    · intro g hg
      rw [mem_coe, mem_filter] at hg
      rw [mem_coe, Apx.ball, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hf : (univ.filter fun x => true = toOp g x 0) = univ.filter fun x => g x = true := by
        ext x
        cases h : g x <;> simp [toOp, h]
      rw [hf]
      exact hg.2
    · exact toOp_injective.injOn
  calc _ ≤ (Apx.ball (fun _ : Fin n → Bool => true)).card * 3 ^ (2 ^ n - 2 ^ n / 4) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 4 ^ 2 ^ n := Apx.card_ball_le _

/-- При `n ≥ 10` плохих функций не больше `2^{N−n}`. -/
theorem card_badSet_le {n : ℕ} (hn : 10 ≤ n) : (badSet n).card ≤ 2 ^ (2 ^ n - n) := by
  classical
  set N := 2 ^ n with hN
  set light := univ.filter fun g : Fn n => 4 * wt g ≤ 2 ^ n with hlight
  set heavy := univ.filter fun g : Fn n => 3 * 2 ^ n ≤ 4 * wt g with hheavy
  have hsub : badSet n ⊆ (univ.image (proj (n := n)) ∪ light) ∪ heavy := by
    intro g hg
    rw [mem_badSet] at hg
    unfold Good Balanced at hg
    by_cases hp : IsProj g
    · obtain ⟨t, rfl⟩ := hp
      exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_univ _)))
    · have h : 4 * wt g ≤ 2 ^ n ∨ 3 * 2 ^ n ≤ 4 * wt g := by
        by_contra hc
        push Not at hc
        exact hg ⟨hp, by omega, by omega⟩
      rcases h with h | h
      · exact mem_union_left _ (mem_union_right _ (by rw [hlight, mem_filter]; exact ⟨mem_univ _, h⟩))
      · exact mem_union_right _ (by rw [hheavy, mem_filter]; exact ⟨mem_univ _, h⟩)
  have hproj : (univ.image (proj (n := n))).card ≤ n := by
    calc _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
  -- арифметика: `N = 16 P`, `P = 2^{n−4} ≥ n`
  set P := 2 ^ (n - 4) with hP
  have hNP : N = 16 * P := by
    rw [hN, hP, show n = (n - 4) + 4 by omega, pow_add]
    simp only [show n - 4 + 4 - 4 = n - 4 by omega]
    ring
  have hnP : n ≤ P := by
    have := Apx.add_four_le_two_pow (m := n - 4) (by omega)
    omega
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have h3 : 2 ^ (19 * P) ≤ 3 ^ (12 * P) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  have hN4 : N - N / 4 = 12 * P := by omega
  have h4N : 4 ^ N = 2 ^ (13 * P) * 2 ^ (19 * P) := by
    rw [hNP, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    ring_nf
  -- каждое из множеств `light`, `heavy` — не больше `2^{13P}`
  have hcap : ∀ s : ℕ, s * 3 ^ (N - N / 4) ≤ 4 ^ N → s ≤ 2 ^ (13 * P) := by
    intro s hs
    rw [hN4, h4N] at hs
    have : s * 2 ^ (19 * P) ≤ 2 ^ (13 * P) * 2 ^ (19 * P) :=
      le_trans (Nat.mul_le_mul_left _ h3) hs
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have hl : light.card ≤ 2 ^ (13 * P) := hcap _ (card_light_le n)
  have hh : heavy.card ≤ 2 ^ (13 * P) := hcap _ (card_heavy_le n)
  have hnpow : n ≤ 2 ^ (13 * P) := by
    have := Nat.lt_two_pow_self (n := 13 * P)
    omega
  calc (badSet n).card ≤ ((univ.image (proj (n := n)) ∪ light) ∪ heavy).card := card_le_card hsub
    _ ≤ (univ.image (proj (n := n)) ∪ light).card + heavy.card := card_union_le _ _
    _ ≤ (univ.image (proj (n := n))).card + light.card + heavy.card := by
        gcongr
        exact card_union_le _ _
    _ ≤ 2 ^ (13 * P) + 2 ^ (13 * P) + 2 ^ (13 * P) := by omega
    _ ≤ 2 ^ (13 * P) * 2 ^ 2 := by omega
    _ = 2 ^ (13 * P + 2) := by rw [pow_add]
    _ ≤ 2 ^ (N - n) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## Доля кортежей с малым числом хороших значений -/

/-- При `n ≥ 10`, `1 ≤ m ≤ 2^N` кортежей `G : Fin m → Fn n` с не более чем `⌊m/16⌋`
различными хорошими значениями не больше `8 K^m / 2ⁿ`. -/
theorem card_bad_mul_le {n m : ℕ} (hn : 10 ≤ n) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 2 ^ n) :
    (univ.filter fun G : Fin m → Fn n => (goodVals (badSet n) G).card ≤ m / 16).card * 2 ^ n ≤
      8 * (2 ^ 2 ^ n) ^ m := by
  set N := 2 ^ n with hN
  set K := 2 ^ N with hK
  set B := 2 ^ (N - n) with hB
  set t := m / 16 with ht
  set A := (univ.filter fun G : Fin m → Fn n => (goodVals (badSet n) G).card ≤ t) with hA
  have hcardK : Fintype.card (Fn n) = K := card_Fn n
  have hL : (badSet n).card ≤ B := card_badSet_le hn
  have h16 : 16 * t ≤ m := by omega
  have htm : t ≤ m := by omega
  have hnN : 16 * n ≤ N := by
    have h1 := Apx.add_four_le_two_pow (m := n - 4) (by omega)
    have h2 : N = 2 ^ (n - 4) * 2 ^ 4 := by
      rw [hN, ← pow_add]
      congr 1
      omega
    omega
  have hBn : B * 2 ^ n = K := by
    rw [hB, hK, ← pow_add]
    congr 1
    omega
  have h8n : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8B : 8 * B ≤ K := by
    rw [← hBn, mul_comm 8 B]
    exact Nat.mul_le_mul_left _ h8n
  have hnB : n ≤ B := by
    have h1 := Nat.lt_two_pow_self (n := N - n)
    omega
  have h4 : 2 ^ m ≤ 4 ^ (m - t) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases le_or_gt t B with htB | htB
  · -- режим 1: `t ≤ B`, доля не больше `(8B/K)^{m−t} ≤ 8B/K`
    have hc := card_few_le (badSet n) hL htm (by rw [hcardK]; omega)
    rw [hcardK] at hc
    have h2 : (B + t) ^ (m - t) ≤ (2 * B) ^ (m - t) := Nat.pow_le_pow_left (by omega) _
    have h3 : (8 * B) ^ (m - t - 1) ≤ K ^ (m - t - 1) := Nat.pow_le_pow_left h8B _
    calc A.card * 2 ^ n ≤ 2 ^ m * K ^ t * (B + t) ^ (m - t) * 2 ^ n := Nat.mul_le_mul_right _ hc
      _ ≤ 4 ^ (m - t) * K ^ t * (2 * B) ^ (m - t) * 2 ^ n := by gcongr
      _ = K ^ t * (4 * (2 * B)) ^ (m - t) * 2 ^ n := by rw [mul_pow 4 (2 * B)]; ring
      _ = K ^ t * ((8 * B) ^ (m - t - 1) * (8 * B)) * 2 ^ n := by
          rw [← pow_succ, show m - t - 1 + 1 = m - t by omega, show 4 * (2 * B) = 8 * B by ring]
      _ ≤ K ^ t * (K ^ (m - t - 1) * (8 * B)) * 2 ^ n := by gcongr
      _ = 8 * (K ^ t * K ^ (m - t - 1) * (B * 2 ^ n)) := by ring
      _ = 8 * K ^ m := by
          rw [hBn, ← pow_add, ← pow_succ, show t + (m - t - 1) + 1 = m by omega]
  · -- режим 2: `t > B`, доля не больше `2^{−(m−t)} ≤ 2^{−n}`
    have hc := card_few_le (badSet n) hL htm (by rw [hcardK]; omega)
    rw [hcardK] at hc
    have h2 : (B + t) ^ (m - t) ≤ (2 * t) ^ (m - t) := Nat.pow_le_pow_left (by omega) _
    have hnmt : 2 ^ n ≤ 2 ^ (m - t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (16 * t) ^ (m - t) ≤ K ^ (m - t) := Nat.pow_le_pow_left (by omega) _
    calc A.card * 2 ^ n ≤ 2 ^ m * K ^ t * (B + t) ^ (m - t) * 2 ^ n := Nat.mul_le_mul_right _ hc
      _ ≤ 4 ^ (m - t) * K ^ t * (2 * t) ^ (m - t) * 2 ^ (m - t) := by gcongr
      _ = K ^ t * (4 * (2 * t) * 2) ^ (m - t) := by
          rw [mul_pow (4 * (2 * t)) 2, mul_pow 4 (2 * t)]
          ring
      _ = K ^ t * (16 * t) ^ (m - t) := by rw [show 4 * (2 * t) * 2 = 16 * t by ring]
      _ ≤ K ^ t * K ^ (m - t) := by gcongr
      _ = K ^ m := by rw [← pow_add, show t + (m - t) = m by omega]
      _ ≤ 8 * K ^ m := by omega

/-! ## Итог -/

/-- Оператор с более чем `⌊m/16⌋` различными хорошими координатами: любая схема имеет
`E(Σ) ≥ m/64` и `U(Σ) ≥ m/64`. -/
theorem good_of_many {n m : ℕ} (F : (Fin n → Bool) → Fin m → Bool)
    (hF : m / 16 < (goodVals (badSet n) (coord F)).card) (C : Circ n (Fin m))
    (hC : C.Realizes F) : 1 / 64 * (m : ℝ) ≤ C.Eav ∧ 1 / 64 * (m : ℝ) ≤ C.Uav := by
  set S := goodVals (badSet n) (coord F) with hS
  have hmem : ∀ g ∈ S, (∃ k, coord F k = g) ∧ Good g := by
    intro g hg
    rw [hS, goodVals, mem_filter, mem_image] at hg
    obtain ⟨⟨k, _, hk⟩, hb⟩ := hg
    exact ⟨⟨k, hk⟩, by rw [mem_badSet] at hb; push Not at hb; exact hb⟩
  apply le_Eav_Uav C S
  · intro g hg
    obtain ⟨⟨k, hk⟩, hgood⟩ := hmem g hg
    apply exists_gate_of_out C (k := k) _ hgood.1
    intro x
    rw [← hk, hC x]
    rfl
  · intro g hg
    exact (hmem g hg).2.2
  · omega

end PowerActivity.Bal

namespace PowerActivity

open Finset Filter Topology Low Bal

/-- **Цель `BalGoal`**: для почти всех операторов `F : {0,1}ⁿ → {0,1}ᵐ` (равномерно по
`1 ≤ m ≤ 2^{2^n}`) любая схема имеет `E(Σ) ≥ m/64` и `U(Σ) ≥ m/64`;
доля исключений не больше `8·2^{−n}` при `n ≥ 10`. -/
theorem bal_goal : BalGoal := by
  refine ⟨1 / 64, by norm_num, fun n => if n < 10 then 1 else 8 * (1 / 2 : ℝ) ^ n, ?_, ?_⟩
  · have h : Tendsto (fun n : ℕ => 8 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 8
      simpa using this
    apply h.congr'
    filter_upwards [eventually_ge_atTop 10] with n hn
    simp [show ¬ n < 10 by omega]
  · intro n m hm1 hm
    classical
    by_cases hn : n < 10
    · simp only [hn, ↓reduceIte, sub_self]
      unfold frac
      positivity
    · simp only [hn, ↓reduceIte]
      have hn' : 10 ≤ n := by omega
      set Q : ((Fin n → Bool) → Fin m → Bool) → Prop := fun F =>
        ∀ C : Circ n (Fin m), C.Realizes F → 1 / 64 * (m : ℝ) ≤ C.Eav ∧ 1 / 64 * (m : ℝ) ≤ C.Uav
        with hQ
      set A := (univ.filter fun G : Fin m → Fn n => (goodVals (badSet n) G).card ≤ m / 16)
        with hA
      have hbc : A.card * 2 ^ n ≤ 8 * (2 ^ 2 ^ n) ^ m := card_bad_mul_le hn' hm1 hm
      -- плохие операторы переходят в плохие кортежи координат
      have hsub : (univ.filter fun F => ¬ Q F).card ≤ A.card := by
        calc (univ.filter fun F => ¬ Q F).card
            ≤ (univ.filter fun F : (Fin n → Bool) → Fin m → Bool =>
                (goodVals (badSet n) (coord F)).card ≤ m / 16).card := by
              apply card_le_card
              intro F hF
              rw [mem_filter] at hF ⊢
              refine ⟨mem_univ _, ?_⟩
              by_contra hc
              push Not at hc
              exact hF.2 (fun C hC => good_of_many F hc C hC)
          _ = A.card := by
              apply card_equiv (Equiv.piComm fun (_ : Fin n → Bool) (_ : Fin m) => Bool)
              intro F
              simp only [hA, mem_filter, mem_univ, true_and]
              rfl
      have htot : Fintype.card ((Fin n → Bool) → Fin m → Bool) = (2 ^ 2 ^ n) ^ m := by
        rw [Fintype.card_congr (Equiv.piComm fun (_ : Fin n → Bool) (_ : Fin m) => Bool)]
        simp only [Fintype.card_pi, Fintype.card_bool, prod_const, card_univ, Fintype.card_fin]
      have hsplit := card_filter_add_card_filter_not
        (s := (univ : Finset ((Fin n → Bool) → Fin m → Bool))) Q
      rw [card_univ, htot] at hsplit
      unfold frac
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, htot, Fintype.card_subtype]
      have hpos : (0 : ℝ) < ((2 ^ 2 ^ n) ^ m : ℕ) := by positivity
      rw [le_div_iff₀ hpos]
      have e1 : ((univ.filter Q).card : ℝ) =
          ((2 ^ 2 ^ n) ^ m : ℕ) - ((univ.filter fun F => ¬ Q F).card : ℝ) := by
        rw [← hsplit]
        push_cast
        ring
      have e2 : ((univ.filter fun F => ¬ Q F).card : ℝ) * 2 ^ n ≤ 8 * ((2 ^ 2 ^ n) ^ m : ℕ) := by
        have : (univ.filter fun F => ¬ Q F).card * 2 ^ n ≤ 8 * (2 ^ 2 ^ n) ^ m :=
          le_trans (Nat.mul_le_mul_right _ hsub) hbc
        exact_mod_cast this
      rw [e1]
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have : ((univ.filter fun F => ¬ Q F).card : ℝ) ≤
          8 * ((2 ^ 2 ^ n) ^ m : ℕ) * (1 / 2) ^ n := by
        rw [one_div_pow, mul_one_div, le_div_iff₀ h2n]
        exact e2
      nlinarith

end PowerActivity
