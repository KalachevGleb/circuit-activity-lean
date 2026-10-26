import PowerActivity.ApxBasic

/-!
# Приближённая сложность почти всех функций (`approx-hard`)

Подсчёт: схема с `≤ S` элементами и одним выходом вычисляет функцию некоторого «кода»
`(Fin S → Op × Fin K × Fin K) × Fin K`, `K = n + S` (кодов `(3K²)^S·K`); шар Хэмминга
радиуса `N/4` содержит не более `4^N / 3^{3N/4}` функций (оценка
`Σ_{|D| ≤ N/4} 1 ≤ 3^{-(N-N/4)} Σ_D 3^{N-|D|} = 4^N / 3^{N - N/4}`).
При `a = 1/64`, `n ≥ 10` доля «плохих» функций не больше `2^{-n}`.
-/

namespace PowerActivity.Apx

open Finset Filter Topology

/-- Код схемы: `S` элементов (операция и два источника `< K`) и номер выхода `< K`. -/
abbrev Code (S K : ℕ) := (Fin S → Op × Fin K × Fin K) × Fin K

/-- Список элементов кода. -/
def Code.gates {S K : ℕ} (c : Code S K) : List Gate :=
  List.ofFn fun i : Fin S => (⟨(c.1 i).1, (c.1 i).2.1, (c.1 i).2.2⟩ : Gate)

/-- Функция, вычисляемая кодом (определена для любого кода). -/
def Code.fn {n S : ℕ} (c : Code S (n + S)) : (Fin n → Bool) → Bool :=
  fun x => sig n c.gates x c.2

lemma card_code (S K : ℕ) : Fintype.card (Code S K) = (3 * K * K) ^ S * K := by
  simp only [Code, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Op.card,
    prod_const, card_univ]
  ring

/-- Каждая схема с не более чем `S` элементами (при `n ≥ 1`) вычисляет функцию
некоторого кода. -/
lemma exists_code {n : ℕ} (hn : 1 ≤ n) (C : Circ n (Fin 1)) {S : ℕ} (hS : C.s ≤ S) :
    ∃ c : Code S (n + S), c.fn = fun x => C.eval x 0 := by
  refine ⟨(fun i => if h : (i : ℕ) < C.s then
      ((C.gate i).op, ⟨(C.gate i).a, by have := C.gate_a_lt h; omega⟩,
        ⟨(C.gate i).b, by have := C.gate_b_lt h; omega⟩)
    else (Op.and, ⟨0, by omega⟩, ⟨0, by omega⟩),
    ⟨C.out 0, by have := C.out_lt 0; unfold Circ.s at hS; omega⟩), ?_⟩
  funext x
  simp only [Code.fn, Circ.eval, Circ.sig]
  apply sig_congr_prefix _ _ x C.s
  · intro i hi
    have hiS : i < S := lt_of_lt_of_le hi hS
    have hi' : i < C.gates.length := hi
    rw [Code.gates, List.getElem?_ofFn, List.getElem?_eq_getElem hi']
    simp only [hiS, dite_true, Option.some.injEq]
    simp only [dif_pos hi]
    simp [Circ.gate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  · exact C.out_lt 0

/-- Шар Хэмминга: функции `F`, совпадающие с `g` не менее чем на `3N/4` наборах. -/
def ball {n : ℕ} (g : (Fin n → Bool) → Bool) : Finset ((Fin n → Bool) → Fin 1 → Bool) :=
  univ.filter fun F => 3 * 2 ^ n ≤ 4 * (univ.filter fun x => g x = F x 0).card

/-- Мощность шара: `|ball g| · 3^{N - N/4} ≤ 4^N`. -/
lemma card_ball_le {n : ℕ} (g : (Fin n → Bool) → Bool) :
    (ball g).card * 3 ^ (2 ^ n - 2 ^ n / 4) ≤ 4 ^ 2 ^ n := by
  classical
  set N := 2 ^ n with hN
  have hcard : Fintype.card (Fin n → Bool) = N := by simp [hN]
  let φ : ((Fin n → Bool) → Fin 1 → Bool) → Finset (Fin n → Bool) :=
    fun F => univ.filter fun x => ¬ (g x = F x 0)
  let D : Finset (Finset (Fin n → Bool)) := univ.filter fun s => 4 * s.card ≤ N
  have hinj : Set.InjOn φ (ball g) := by
    intro F _ F' _ hFF
    funext x i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have hx := congrArg (fun s => x ∈ s) hFF
    simp only [φ, mem_filter, mem_univ, true_and, eq_iff_iff] at hx
    cases h1 : g x <;> cases h2 : F x 0 <;> cases h3 : F' x 0 <;> simp_all
  have hmaps : ∀ F ∈ ball g, φ F ∈ D := by
    intro F hF
    simp only [ball, mem_filter, mem_univ, true_and] at hF
    simp only [D, mem_filter, mem_univ, true_and, φ]
    have := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin n → Bool))) (fun x => g x = F x 0)
    rw [card_univ, hcard] at this
    omega
  have h1 : (ball g).card ≤ D.card := card_le_card_of_injOn φ hmaps hinj
  have h2 : D.card * 3 ^ (N - N / 4) ≤ 4 ^ N := by
    calc D.card * 3 ^ (N - N / 4) = ∑ s ∈ D, 3 ^ (N - N / 4) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ ∑ s ∈ D, 1 ^ s.card * 3 ^ (N - s.card) := by
          apply sum_le_sum
          intro s hs
          simp only [D, mem_filter, mem_univ, true_and] at hs
          rw [one_pow, one_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ∑ s : Finset (Fin n → Bool), 1 ^ s.card * 3 ^ (N - s.card) :=
          sum_le_sum_of_subset (subset_univ _)
      _ = 4 ^ N := by
          have := Fintype.sum_pow_mul_eq_add_pow (Fin n → Bool) (1 : ℕ) 3
          rw [hcard] at this
          rw [this]
  calc (ball g).card * 3 ^ (N - N / 4) ≤ D.card * 3 ^ (N - N / 4) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 4 ^ N := h2

/-- `n + 4 ≤ 2^n` при `n ≥ 6`. -/
lemma add_four_le_two_pow {m : ℕ} (hm : 6 ≤ m) : m + 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

open Classical in
/-- Ядро оценки `approx-hard`: при `n ≥ 10` функций, приближаемых (`Approx14`) схемой с
`64 n L(Σ) < 2ⁿ`, не больше `2^N / 2^n`. -/
theorem bad_count {n : ℕ} (hn : 10 ≤ n) :
    (univ.filter fun F : (Fin n → Bool) → Fin 1 → Bool =>
        ∃ C : Circ n (Fin 1), Approx14 C F ∧ 64 * n * C.s < 2 ^ n).card * 2 ^ n ≤
      2 ^ 2 ^ n := by
  set N := 2 ^ n with hN
  set S := N / (64 * n) with hSdef
  set K := n + S with hK
  set Bad := (univ.filter fun F : (Fin n → Bool) → Fin 1 → Bool =>
        ∃ C : Circ n (Fin 1), Approx14 C F ∧ 64 * n * C.s < 2 ^ n) with hBad
  let G : Finset ((Fin n → Bool) → Bool) := (univ : Finset (Code S (n + S))).image Code.fn
  have hsub : Bad ⊆ G.biUnion ball := by
    intro F hF
    simp only [hBad, mem_filter, mem_univ, true_and] at hF
    obtain ⟨C, hA, hs⟩ := hF
    have hCS : C.s ≤ S := by
      rw [hSdef, Nat.le_div_iff_mul_le (by positivity)]
      rw [← hN] at hs
      nlinarith
    obtain ⟨c, hc⟩ := exists_code (by omega) C hCS
    rw [mem_biUnion]
    refine ⟨c.fn, mem_image_of_mem _ (mem_univ _), ?_⟩
    simp only [ball, mem_filter, mem_univ, true_and]
    rw [hc]
    exact hA
  have hG : G.card ≤ (3 * K * K) ^ S * K := by
    calc G.card ≤ (univ : Finset (Code S (n + S))).card := card_image_le
      _ = (3 * K * K) ^ S * K := by rw [card_univ, card_code]
  -- оценка числа плохих функций
  have hB1 : Bad.card * 3 ^ (N - N / 4) ≤ (3 * K * K) ^ S * K * 4 ^ N := by
    calc Bad.card * 3 ^ (N - N / 4) ≤ (G.biUnion ball).card * 3 ^ (N - N / 4) :=
          Nat.mul_le_mul_right _ (card_le_card hsub)
      _ ≤ (∑ g ∈ G, (ball g).card) * 3 ^ (N - N / 4) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ g ∈ G, (ball g).card * 3 ^ (N - N / 4) := by rw [sum_mul]
      _ ≤ ∑ _g ∈ G, 4 ^ N := sum_le_sum fun g _ => card_ball_le g
      _ = G.card * 4 ^ N := by rw [sum_const, smul_eq_mul]
      _ ≤ (3 * K * K) ^ S * K * 4 ^ N := Nat.mul_le_mul_right _ hG
  -- арифметика: N = 16 P, P = 2^(n-4) ≥ n
  set P := 2 ^ (n - 4) with hP
  have hNP : N = 16 * P := by
    rw [hN, hP, show n = (n - 4) + 4 by omega, pow_add]
    simp only [show n - 4 + 4 - 4 = n - 4 by omega]
    ring
  have hnP : n ≤ P := by
    have := add_four_le_two_pow (m := n - 4) (by omega)
    omega
  have hSP : 4 * n * S ≤ P := by
    have : S * (64 * n) ≤ N := Nat.div_mul_le_self _ _
    nlinarith
  have hKN : K ≤ N := by
    have : S ≤ P := by nlinarith
    omega
  have hKK : 3 * K * K ≤ 4 ^ (n + 1) := by
    have : K * K ≤ N * N := Nat.mul_le_mul hKN hKN
    have h4 : 4 ^ n = N * N := by rw [hN, ← mul_pow]; norm_num
    rw [pow_succ, h4]
    nlinarith
  have hpow1 : (3 * K * K) ^ S ≤ 2 ^ P := by
    calc (3 * K * K) ^ S ≤ (4 ^ (n + 1)) ^ S := Nat.pow_le_pow_left hKK _
      _ = 2 ^ (2 * (n + 1) * S) := by rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
      _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hK2 : K ≤ 2 ^ n := hKN
  have h3 : 2 ^ (19 * P) ≤ 3 ^ (12 * P) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  have hN4 : N - N / 4 = 12 * P := by omega
  have h4N : 4 ^ N = 2 ^ (32 * P) := by
    rw [hNP, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have key : (3 * K * K) ^ S * K * 4 ^ N * 2 ^ n ≤ 2 ^ N * 3 ^ (N - N / 4) := by
    rw [hN4, h4N]
    calc (3 * K * K) ^ S * K * 2 ^ (32 * P) * 2 ^ n ≤ 2 ^ P * 2 ^ n * 2 ^ (32 * P) * 2 ^ n := by
          gcongr
      _ = 2 ^ (33 * P + 2 * n) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (16 * P + 19 * P) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ (16 * P) * 2 ^ (19 * P) := pow_add _ _ _
      _ ≤ 2 ^ (16 * P) * 3 ^ (12 * P) := Nat.mul_le_mul_left _ h3
      _ = 2 ^ N * 3 ^ (12 * P) := by rw [hNP]
  have hpos : 0 < 3 ^ (N - N / 4) := by positivity
  have : Bad.card * 2 ^ n * 3 ^ (N - N / 4) ≤ 2 ^ N * 3 ^ (N - N / 4) := by
    calc Bad.card * 2 ^ n * 3 ^ (N - N / 4) = Bad.card * 3 ^ (N - N / 4) * 2 ^ n := by ring
      _ ≤ (3 * K * K) ^ S * K * 4 ^ N * 2 ^ n := Nat.mul_le_mul_right _ hB1
      _ ≤ 2 ^ N * 3 ^ (N - N / 4) := key
  exact Nat.le_of_mul_le_mul_right this hpos

end PowerActivity.Apx

namespace PowerActivity

open Finset Filter Topology Apx

/-- **`approx-hard`**: при `a = 1/64` для почти всех `f` любая схема,
совпадающая с `f` не менее чем на `3N/4` наборах, имеет не меньше `a 2ⁿ/n` элементов;
доля исключений не больше `2^{-n}` при `n ≥ 10`. -/
theorem approxHard_goal : ApproxHardGoal := by
  refine ⟨1 / 64, by norm_num, fun n => if n < 10 then 1 else (1 / 2 : ℝ) ^ n, ?_, ?_⟩
  · apply (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).congr'
    filter_upwards [eventually_ge_atTop 10] with n hn
    simp [show ¬ n < 10 by omega]
  · intro n
    classical
    by_cases hn : n < 10
    · simp only [hn, if_true, sub_self]
      unfold frac
      positivity
    · simp only [hn, if_false]
      have hn' : 10 ≤ n := by omega
      set Good : ((Fin n → Bool) → Fin 1 → Bool) → Prop := fun F =>
        ∀ C : Circ n (Fin 1), Approx14 C F → 1 / 64 * 2 ^ n / n ≤ (C.s : ℝ) with hGood
      have hbc := bad_count hn'
      set Bad := (univ.filter fun F : (Fin n → Bool) → Fin 1 → Bool =>
        ∃ C : Circ n (Fin 1), Approx14 C F ∧ 64 * n * C.s < 2 ^ n) with hBad
      have hsub : (univ.filter fun F => ¬ Good F) ⊆ Bad := by
        intro F hF
        simp only [mem_filter, mem_univ, true_and, hGood, not_forall, not_le] at hF
        obtain ⟨C, hA, hlt⟩ := hF
        simp only [hBad, mem_filter, mem_univ, true_and]
        refine ⟨C, hA, ?_⟩
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        rw [lt_div_iff₀ hnpos] at hlt
        have : ((64 * n * C.s : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
          push_cast; nlinarith
        exact_mod_cast this
      have htot : Fintype.card ((Fin n → Bool) → Fin 1 → Bool) = 2 ^ 2 ^ n := by
        simp
      have hsplit := card_filter_add_card_filter_not
        (s := (univ : Finset ((Fin n → Bool) → Fin 1 → Bool))) Good
      rw [card_univ, htot] at hsplit
      have hbad : (univ.filter fun F => ¬ Good F).card * 2 ^ n ≤ 2 ^ 2 ^ n :=
        le_trans (Nat.mul_le_mul_right _ (card_le_card hsub)) hbc
      unfold frac
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, htot, Fintype.card_subtype]
      have hpos : (0 : ℝ) < 2 ^ 2 ^ n := by positivity
      rw [le_div_iff₀ (by positivity)]
      have e1 : ((univ.filter Good).card : ℝ) =
          (2 ^ 2 ^ n : ℕ) - ((univ.filter fun F => ¬ Good F).card : ℝ) := by
        rw [← hsplit]; push_cast; ring
      have e2 : ((univ.filter fun F => ¬ Good F).card : ℝ) * 2 ^ n ≤ ((2 ^ 2 ^ n : ℕ) : ℝ) := by
        exact_mod_cast hbad
      rw [e1]
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have : ((univ.filter fun F => ¬ Good F).card : ℝ) ≤ ((2 ^ 2 ^ n : ℕ) : ℝ) * (1 / 2) ^ n := by
        rw [one_div_pow, mul_one_div, le_div_iff₀ h2n]
        exact e2
      nlinarith

end PowerActivity
