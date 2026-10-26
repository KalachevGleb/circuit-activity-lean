import PowerActivity.LowBasic
import PowerActivity.Spec

/-!
# Схема чётности: `E(Σ) ≥ n/4` (утверждение `parity`)

`I_t` — элементы, получающие переменную `x_t` хотя бы на один вход. При переходе `x → x^{(t)}`
(инвертирование `t`-й координаты) хотя бы один элемент из `I_t` меняет выход
(`exists_change`), иначе по топологическому порядку сохраняются все сигналы, кроме `x_t`
(`sig_flip_eq`). Отсюда `N ≤ Σ_{i ∈ I_t} #{x : φ_i(x) ≠ φ_i(x^{(t)})} ≤ 2 Σ_{i ∈ I_t} N p_i`;
каждый элемент лежит не более чем в двух `I_t`, суммирование по `t` даёт `n N ≤ 4 Σ_i N p_i`.

* `Low.parity_lower` (итог `parity_goal : ParityGoal` — в `LowMain`).
-/

namespace PowerActivity

open Finset

namespace Low

/-- Инвертирование `t`-й координаты. -/
def flip {n : ℕ} (x : Fin n → Bool) (t : Fin n) : Fin n → Bool := Function.update x t (!x t)

lemma flip_flip {n : ℕ} (x : Fin n → Bool) (t : Fin n) : flip (flip x t) t = x := by
  unfold flip
  rw [Function.update_idem]
  simp

/-- Перестановка наборов `x ↦ x^{(t)}`. -/
def flipPerm {n : ℕ} (t : Fin n) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun x => flip x t) (fun x => flip_flip x t)

lemma card_true_flip {n : ℕ} (x : Fin n → Bool) (t : Fin n) :
    (univ.filter fun i => flip x t i = true).card % 2 ≠
      (univ.filter fun i => x i = true).card % 2 := by
  cases hxt : x t
  · have hA' : (univ.filter fun i => flip x t i = true) =
        insert t (univ.filter fun i => x i = true) := by
      ext i
      rw [mem_filter, mem_insert, mem_filter]
      simp only [mem_univ, true_and, flip]
      by_cases hit : i = t
      · subst hit; simp [hxt]
      · simp [hit]
    have htA : t ∉ (univ.filter fun i => x i = true) := by simp [hxt]
    rw [hA', card_insert_of_notMem htA]
    omega
  · have hA' : (univ.filter fun i => flip x t i = true) =
        (univ.filter fun i => x i = true).erase t := by
      ext i
      rw [mem_filter, mem_erase, mem_filter]
      simp only [mem_univ, true_and, flip]
      by_cases hit : i = t
      · subst hit; simp [hxt]
      · simp [hit]
    have htA : t ∈ (univ.filter fun i => x i = true) := by simp [hxt]
    rw [hA', card_erase_of_mem htA]
    have : 1 ≤ (univ.filter fun i => x i = true).card := card_pos.mpr ⟨t, htA⟩
    omega

lemma parity_flip {n : ℕ} (x : Fin n → Bool) (t : Fin n) : parity (flip x t) = !parity x := by
  have h := card_true_flip x t
  unfold parity
  set a := (univ.filter fun i => flip x t i = true).card
  set b := (univ.filter fun i => x i = true).card
  by_cases hb : b % 2 = 1
  · have ha : ¬ a % 2 = 1 := by omega
    simp [ha, hb]
  · have ha : a % 2 = 1 := by omega
    simp [ha, hb]

variable {n : ℕ} {κ : Type} (C : Circ n κ)

/-- Если на переходе `x → x^{(t)}` не меняется ни один элемент из `I_t`, то не меняется
ни один сигнал, кроме самой переменной `x_t`. -/
lemma sig_flip_eq (x : Fin n → Bool) (t : Fin n)
    (h : ∀ i < C.s, (t : ℕ) ∈ (C.gate i).srcs → C.val x i = C.val (flip x t) i) :
    ∀ j, j ≠ (t : ℕ) → C.sig x j = C.sig (flip x t) j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjt
    by_cases hjn : j < n
    · simp only [Circ.sig, sig_lt _ _ hjn, flip]
      rw [Function.update_of_ne]
      intro heq; apply hjt; rw [← heq]
    · by_cases hjs : j < n + C.s
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
        have hi : i < C.s := by omega
        by_cases ht : (t : ℕ) ∈ (C.gate i).srcs
        · exact h i hi ht
        · have e1 := C.val_eq x hi
          have e2 := C.val_eq (flip x t) hi
          simp only [Circ.val] at e1 e2
          rw [e1, e2]
          have ha := C.gate_a_lt hi
          have hb := C.gate_b_lt hi
          apply Gate.low_eval_congr
          · apply ih _ ha
            intro hat; apply ht; rw [← hat]; exact Gate.lowA_mem _
          · intro hop
            apply ih _ hb
            intro hbt; apply ht; rw [← hbt]; exact Gate.lowB_mem _ hop
      · have hge : n + C.gates.length ≤ j := by unfold Circ.s at hjs; omega
        simp only [Circ.sig, sig_ge _ _ hge]

/-- Выход, вычисляющий чётность `n ≥ 2` переменных, не является входной вершиной. -/
lemma out_ne_input (hn : 2 ≤ n) (k : κ) (hk : ∀ x, C.eval x k = parity x) (t : Fin n) :
    C.out k ≠ (t : ℕ) := by
  intro hot
  obtain ⟨t', htt⟩ : ∃ t' : Fin n, t ≠ t' := by
    by_cases h0 : (t : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have := congrArg Fin.val h
      simp only at this
      omega
    · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
      have := congrArg Fin.val h
      simp only at this
      omega
  have h1 := hk (fun i => decide (i = t'))
  have hev : C.eval (fun i => decide (i = t')) k = decide (t = t') := by
    simp only [Circ.eval, hot, Circ.sig_input]
  have hpar : parity (fun i : Fin n => decide (i = t')) = true := by
    unfold parity
    have : (univ.filter fun i : Fin n => decide (i = t') = true) = {t'} := by
      ext i; simp
    rw [this]; simp
  rw [hev, hpar] at h1
  simp [htt] at h1

/-- При каждом `x` хотя бы один элемент из `I_t` меняет выход. -/
lemma exists_change (hn : 2 ≤ n) (k : κ) (hk : ∀ x, C.eval x k = parity x)
    (x : Fin n → Bool) (t : Fin n) :
    ∃ i ∈ (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs),
      C.val x i ≠ C.val (flip x t) i := by
  by_contra hcon
  push Not at hcon
  have h := sig_flip_eq C x t (fun i hi hit => hcon i (by simp [hi, hit]))
    (C.out k) (out_ne_input C hn k hk t)
  have h1 := hk x
  have h2 := hk (flip x t)
  simp only [Circ.eval] at h1 h2
  rw [h, h2, parity_flip] at h1
  cases parity x <;> simp at h1

lemma lowW_flip (t : Fin n) (i : ℕ) :
    (univ.filter fun x : Fin n → Bool => C.val (flip x t) i = true).card = C.lowW i := by
  unfold Circ.lowW
  simp only [card_filter]
  exact Equiv.sum_comp (flipPerm t) (fun x => if C.val x i = true then 1 else 0)

lemma card_srcs_le (i : ℕ) :
    (univ.filter fun t : Fin n => (t : ℕ) ∈ (C.gate i).srcs).card ≤ 2 := by
  calc (univ.filter fun t : Fin n => (t : ℕ) ∈ (C.gate i).srcs).card
      ≤ (C.gate i).srcs.toFinset.card := by
        apply card_le_card_of_injOn (fun t : Fin n => (t : ℕ))
        · intro t ht
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht
          simpa using ht
        · intro a _ b _ hab; exact Fin.ext hab
    _ ≤ (C.gate i).srcs.length := List.toFinset_card_le _
    _ ≤ 2 := Gate.low_srcs_len _

/-- Для каждой переменной: `N ≤ 2 Σ_{i ∈ I_t} N p_i`. -/
lemma pow_le_sum_It (hn : 2 ≤ n) (k : κ) (hk : ∀ x, C.eval x k = parity x) (t : Fin n) :
    2 ^ n ≤ ∑ i ∈ (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs), 2 * C.lowW i := by
  set I := (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs)
  calc 2 ^ n = ∑ _x : Fin n → Bool, 1 := by simp
    _ ≤ ∑ x : Fin n → Bool, (I.filter fun i => C.val x i ≠ C.val (flip x t) i).card := by
        apply sum_le_sum
        intro x _
        obtain ⟨i, hi, hne⟩ := exists_change C hn k hk x t
        exact card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, hne⟩⟩
    _ = ∑ i ∈ I, (univ.filter fun x => C.val x i ≠ C.val (flip x t) i).card := by
        simp only [card_filter]
        rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ I, 2 * C.lowW i := by
        apply sum_le_sum
        intro i _
        calc (univ.filter fun x => C.val x i ≠ C.val (flip x t) i).card
            ≤ ((univ.filter fun x : Fin n → Bool => C.val x i = true) ∪
                (univ.filter fun x : Fin n → Bool => C.val (flip x t) i = true)).card := by
              apply card_le_card
              intro x hx
              simp only [mem_filter, mem_univ, true_and] at hx
              simp only [mem_union, mem_filter, mem_univ, true_and]
              cases h1 : C.val x i <;> cases h2 : C.val (flip x t) i <;> simp_all
          _ ≤ _ := card_union_le _ _
          _ = 2 * C.lowW i := by rw [lowW_flip]; unfold Circ.lowW; ring

/-- **`parity`.** Если один из выходов схемы — чётность `n ≥ 2` переменных, то `E(Σ) ≥ n/4`. -/
theorem parity_lower (hn : 2 ≤ n) (k : κ) (hk : ∀ x, C.eval x k = parity x) :
    (n : ℝ) / 4 ≤ C.Eav := by
  have key : n * 2 ^ n ≤ 4 * ∑ i ∈ range C.s, C.lowW i := by
    calc n * 2 ^ n = ∑ _t : Fin n, 2 ^ n := by simp
      _ ≤ ∑ t : Fin n, ∑ i ∈ (range C.s).filter (fun i => (t : ℕ) ∈ (C.gate i).srcs),
            2 * C.lowW i := sum_le_sum fun t _ => pow_le_sum_It C hn k hk t
      _ = ∑ i ∈ range C.s, (univ.filter fun t : Fin n => (t : ℕ) ∈ (C.gate i).srcs).card *
            (2 * C.lowW i) := by
          simp only [sum_filter]
          rw [Finset.sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [← sum_filter, sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ range C.s, 2 * (2 * C.lowW i) :=
          sum_le_sum fun i _ => Nat.mul_le_mul_right _ (card_srcs_le C i)
      _ = 4 * ∑ i ∈ range C.s, C.lowW i := by rw [mul_sum]; ring_nf
  rw [Circ.low_Eav_eq, le_div_iff₀ (by positivity)]
  have : ((n * 2 ^ n : ℕ) : ℝ) ≤ ((4 * ∑ i ∈ range C.s, C.lowW i : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast at this
  linarith

end Low

end PowerActivity
