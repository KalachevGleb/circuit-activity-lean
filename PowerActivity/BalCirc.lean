import PowerActivity.LowMany

/-!
# Тезисы, цель `BalGoal`: нижняя оценка `E` и `U` через различные сбалансированные выходы

Функция `g` *сбалансирована* (`Balanced`), если `N/4 < |g| < 3N/4`, `N = 2ⁿ`.
Пусть `S` — множество различных функций, каждая из которых вычисляется некоторым элементом
схемы (выход-непроекция всегда реализуется элементом — `exists_gate_of_out`). Разные функции
реализуются разными элементами, поэтому
* `E`: `Σ_x E(Σ,x) ≥ Σ_{g∈S} |g| > |S| N/4`;
* `U`: в элемент типа `∧`/`∨` с единицей на выходе и в элемент типа `¬` с нулём на выходе
  входит провод с единицей (`one_le_countP`); входные провода разных элементов различны,
  поэтому `Σ_x U(Σ,x) ≥ Σ_{g∈S} min(|g|, N−|g|) > |S| N/4`.

Итог — `card_mul_le_sum`: `|S|·N ≤ 4 Σ_x E(Σ,x)` и `|S|·N ≤ 4 Σ_x U(Σ,x)`, то есть
`E(Σ) ≥ |S|/4`, `U(Σ) ≥ |S|/4` (`card_le_Eav_Uav`).
-/

namespace PowerActivity.Bal

open Finset Low

variable {n : ℕ} {κ : Type}

/-- Сбалансированная функция: `N/4 < |g| < 3N/4`. -/
def Balanced (g : Fn n) : Prop := 2 ^ n < 4 * wt g ∧ 4 * wt g < 3 * 2 ^ n

/-- Выход схемы, вычисляющий непроекцию, — элемент. -/
lemma exists_gate_of_out (C : Circ n κ) {g : Fn n} {k : κ} (hk : ∀ x, C.eval x k = g x)
    (hg : ¬ IsProj g) : ∃ i, i < C.s ∧ ∀ x, C.val x i = g x := by
  have hout : n ≤ C.out k := by
    by_contra hlt
    push Not at hlt
    apply hg
    refine ⟨⟨C.out k, hlt⟩, ?_⟩
    funext x
    rw [← hk x]
    simp [Circ.eval, Circ.sig, sig_lt _ _ hlt, proj]
  refine ⟨C.out k - n, ?_, ?_⟩
  · have := C.out_lt k
    unfold Circ.s
    omega
  · intro x
    simp only [Circ.val]
    rw [show n + (C.out k - n) = C.out k by omega]
    exact hk x

/-- В элемент `∧`/`∨` с единицей на выходе и в элемент `¬` с нулём на выходе входит
провод с единицей. -/
lemma one_le_countP (C : Circ n κ) {i : ℕ} (hi : i < C.s) (x : Fin n → Bool)
    (h : (C.val x i = true ∧ (C.gate i).op ≠ Op.not) ∨
      (C.val x i = false ∧ (C.gate i).op = Op.not)) :
    1 ≤ (C.gate i).srcs.countP (C.sig x) := by
  rw [C.val_eq x hi] at h
  unfold Gate.srcs
  rcases hop : (C.gate i).op with _ | _ | _ <;> rw [hop] at h <;>
    simp [Op.eval, List.countP_cons] at h ⊢
  · simp [h.1]
  · rcases h with h | h <;> simp [h]
  · simp [h]

/-- Сумма по наборам меры вида `Σ_{i<s} φ(x,i)` не меньше суммы по элементам,
реализующим функции из `S` (элементы различны). -/
lemma sum_image_le (s : ℕ) (φ : (Fin n → Bool) → ℕ → ℕ) (S : Finset (Fn n)) (idx : Fn n → ℕ)
    (hlt : ∀ g ∈ S, idx g < s) (hinj : Set.InjOn idx S) :
    ∑ g ∈ S, ∑ x, φ x (idx g) ≤ ∑ x, ∑ i ∈ range s, φ x i := by
  rw [sum_comm (s := (univ : Finset (Fin n → Bool))), ← sum_image (f := fun i => ∑ x, φ x i) hinj]
  apply sum_le_sum_of_subset
  intro i hi
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hi
  exact mem_range.mpr (hlt g hg)

/-- Число наборов, где элемент `i` (вычисляющий сбалансированную `g`) имеет входной провод
с единицей, больше `N/4`. -/
lemma lt_sum_countP (C : Circ n κ) {i : ℕ} (hi : i < C.s) {g : Fn n}
    (hval : ∀ x, C.val x i = g x) (hb : Balanced g) :
    2 ^ n < 4 * ∑ x, (C.gate i).srcs.countP (C.sig x) := by
  have hw := wt_add_wt_not g
  unfold Balanced at hb
  by_cases hop : (C.gate i).op = Op.not
  · have h1 : wt (fun x => !g x) ≤ ∑ x, (C.gate i).srcs.countP (C.sig x) := by
      unfold wt
      rw [card_filter]
      apply sum_le_sum
      intro x _
      split_ifs with hx
      · apply one_le_countP C hi x
        right
        refine ⟨?_, hop⟩
        rw [hval x]
        simpa using hx
      · exact Nat.zero_le _
    omega
  · have h1 : wt g ≤ ∑ x, (C.gate i).srcs.countP (C.sig x) := by
      unfold wt
      rw [card_filter]
      apply sum_le_sum
      intro x _
      split_ifs with hx
      · apply one_le_countP C hi x
        left
        exact ⟨by rw [hval x]; exact hx, hop⟩
      · exact Nat.zero_le _
    omega

/-- Главная оценка: `|S|·N ≤ 4 Σ_x E(Σ,x)` и `|S|·N ≤ 4 Σ_x U(Σ,x)`, если каждая функция
из `S` сбалансирована и вычисляется некоторым элементом схемы. -/
theorem card_mul_le_sum (C : Circ n κ) (S : Finset (Fn n))
    (hS : ∀ g ∈ S, ∃ i, i < C.s ∧ ∀ x, C.val x i = g x) (hb : ∀ g ∈ S, Balanced g) :
    S.card * 2 ^ n ≤ 4 * ∑ x, C.E x ∧ S.card * 2 ^ n ≤ 4 * ∑ x, C.U x := by
  classical
  choose! idx hidx hval using hS
  have hinj : Set.InjOn idx S := by
    intro g hg g' hg' h
    funext x
    rw [← hval g hg x, ← hval g' hg' x, h]
  constructor
  · have e : ∀ x, C.E x = ∑ i ∈ range C.s, if C.val x i = true then 1 else 0 := by
      intro x
      unfold Circ.E
      rw [card_filter]
    calc S.card * 2 ^ n = ∑ _g ∈ S, 2 ^ n := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ g ∈ S, 4 * ∑ x, (if C.val x (idx g) = true then 1 else 0) := by
          apply sum_le_sum
          intro g hg
          rw [← card_filter]
          have hf : (univ.filter fun x => C.val x (idx g) = true) =
              univ.filter fun x => g x = true := by
            ext x
            simp [hval g hg x]
          rw [hf]
          exact (hb g hg).1.le
      _ = 4 * ∑ g ∈ S, ∑ x, (if C.val x (idx g) = true then 1 else 0) := by rw [mul_sum]
      _ ≤ 4 * ∑ x, ∑ i ∈ range C.s, (if C.val x i = true then 1 else 0) := by
          gcongr
          exact sum_image_le C.s (fun x i => if C.val x i = true then 1 else 0) S idx hidx hinj
      _ = 4 * ∑ x, C.E x := by simp_rw [e]
  · calc S.card * 2 ^ n = ∑ _g ∈ S, 2 ^ n := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ g ∈ S, 4 * ∑ x, (C.gate (idx g)).srcs.countP (C.sig x) := by
          apply sum_le_sum
          intro g hg
          exact (lt_sum_countP C (hidx g hg) (hval g hg) (hb g hg)).le
      _ = 4 * ∑ g ∈ S, ∑ x, (C.gate (idx g)).srcs.countP (C.sig x) := by rw [mul_sum]
      _ ≤ 4 * ∑ x, ∑ i ∈ range C.s, (C.gate i).srcs.countP (C.sig x) := by
          gcongr
          exact sum_image_le C.s (fun x i => (C.gate i).srcs.countP (C.sig x)) S idx hidx hinj
      _ = 4 * ∑ x, C.U x := rfl

/-- Следствие: `m ≤ 16 |S|` влечёт `E(Σ) ≥ m/64` и `U(Σ) ≥ m/64`. -/
theorem le_Eav_Uav (C : Circ n κ) (S : Finset (Fn n))
    (hS : ∀ g ∈ S, ∃ i, i < C.s ∧ ∀ x, C.val x i = g x) (hb : ∀ g ∈ S, Balanced g)
    {m : ℕ} (hm : m ≤ 16 * S.card) :
    1 / 64 * (m : ℝ) ≤ C.Eav ∧ 1 / 64 * (m : ℝ) ≤ C.Uav := by
  obtain ⟨hE, hU⟩ := card_mul_le_sum C S hS hb
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hm' : (m : ℝ) ≤ 16 * S.card := by exact_mod_cast hm
  have hE' : (S.card : ℝ) * 2 ^ n ≤ 4 * ∑ x, (C.E x : ℝ) := by exact_mod_cast hE
  have hU' : (S.card : ℝ) * 2 ^ n ≤ 4 * ∑ x, (C.U x : ℝ) := by exact_mod_cast hU
  unfold Circ.Eav Circ.Uav avgM
  constructor
  · rw [le_div_iff₀ hN]
    nlinarith
  · rw [le_div_iff₀ hN]
    nlinarith

end PowerActivity.Bal
