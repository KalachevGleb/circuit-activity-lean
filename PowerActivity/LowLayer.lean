import PowerActivity.LowBasic

/-!
# Обратные слои `B_d`, `L_{d+1}` и их размеры (утверждение `rev-layers`)

(Префикс `rv` — «обратные» шары и слои; имена не пересекаются с другими модулями.)

* `Circ.rvPreds T` — элементы, сигнал которых идёт на вход элемента из `T`;
* `Circ.rvBall d` — обратный шар `B_d = {v : dist(v, Out) ≤ d}` (элементы, от которых выход
  недостижим, не попадают ни в один шар; удалять их не нужно);
* `Circ.rvLayer d = B_{d+1} \ B_d` — слой `L_{d+1}`;
* `rev-layers`: `card_rvBall_le : |B_d| ≤ m 2^{d+1}`, `card_rvLayer_le : |L_{d+1}| ≤ m 2^{d+1}`;
* `rv_pred_mem` — источник входа элемента из `B_d` лежит среди входов или в `B_{d+1}`;
* `rvLayer_disjoint` — слои попарно не пересекаются.
-/

namespace PowerActivity

open Finset

namespace Circ

variable {n m : ℕ} (C : Circ n (Fin m))

/-- Предшественники множества элементов `T`. -/
def rvPreds (T : Finset ℕ) : Finset ℕ :=
  (range C.s).filter fun i => ∃ i' ∈ T, n + i ∈ (C.gate i').srcs

/-- Обратный шар `B_d`: элементы на расстоянии `≤ d` от выходов. -/
def rvBall : ℕ → Finset ℕ
  | 0 => (range C.s).filter fun i => ∃ k, C.out k = n + i
  | d + 1 => rvBall d ∪ C.rvPreds (rvBall d)

/-- Слой `L_{d+1} = B_{d+1} \ B_d` (элементы на расстоянии ровно `d+1` от выходов). -/
def rvLayer (d : ℕ) : Finset ℕ := C.rvBall (d + 1) \ C.rvBall d

/-- `rvShell 0 = B_0`, `rvShell (d+1) = L_{d+1}`. -/
def rvShell : ℕ → Finset ℕ
  | 0 => C.rvBall 0
  | d + 1 => C.rvLayer d

lemma rvPreds_mono {T T' : Finset ℕ} (h : T ⊆ T') : C.rvPreds T ⊆ C.rvPreds T' := by
  intro i hi
  simp only [rvPreds, mem_filter] at hi ⊢
  obtain ⟨hi, i', hi', hsrc⟩ := hi
  exact ⟨hi, i', h hi', hsrc⟩

lemma rvBall_sub_range (d : ℕ) : C.rvBall d ⊆ range C.s := by
  induction d with
  | zero => exact filter_subset _ _
  | succ d ih => exact union_subset ih (filter_subset _ _)

lemma rvBall_lt {d i : ℕ} (h : i ∈ C.rvBall d) : i < C.s :=
  mem_range.mp (C.rvBall_sub_range d h)

lemma rvBall_sub_succ (d : ℕ) : C.rvBall d ⊆ C.rvBall (d + 1) := subset_union_left

lemma rvBall_mono {d d' : ℕ} (h : d ≤ d') : C.rvBall d ⊆ C.rvBall d' := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (C.rvBall_sub_succ _)

lemma rvPreds_sub_succ (d : ℕ) : C.rvPreds (C.rvBall d) ⊆ C.rvBall (d + 1) := subset_union_right

lemma card_rvPreds_le (T : Finset ℕ) : (C.rvPreds T).card ≤ 2 * T.card := by
  have hsub : C.rvPreds T ⊆ T.biUnion fun i' => (C.gate i').srcs.toFinset.image (· - n) := by
    intro i hi
    simp only [rvPreds, mem_filter] at hi
    obtain ⟨_, i', hi', hsrc⟩ := hi
    simp only [mem_biUnion, mem_image, List.mem_toFinset]
    exact ⟨i', hi', n + i, hsrc, by omega⟩
  calc (C.rvPreds T).card
      ≤ (T.biUnion fun i' => (C.gate i').srcs.toFinset.image (· - n)).card := card_le_card hsub
    _ ≤ ∑ i' ∈ T, ((C.gate i').srcs.toFinset.image (· - n)).card := card_biUnion_le
    _ ≤ ∑ _i' ∈ T, 2 := by
        apply sum_le_sum
        intro i' _
        calc _ ≤ (C.gate i').srcs.toFinset.card := card_image_le
          _ ≤ (C.gate i').srcs.length := List.toFinset_card_le _
          _ ≤ 2 := Gate.low_srcs_len _
    _ = 2 * T.card := by rw [sum_const, smul_eq_mul, mul_comm]

lemma card_rvBall_zero_le : (C.rvBall 0).card ≤ m := by
  have hsub : C.rvBall 0 ⊆ univ.image fun k : Fin m => C.out k - n := by
    intro i hi
    simp only [rvBall, mem_filter] at hi
    obtain ⟨_, k, hk⟩ := hi
    simp only [mem_image, mem_univ, true_and]
    exact ⟨k, by omega⟩
  calc (C.rvBall 0).card ≤ (univ.image fun k : Fin m => C.out k - n).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin m)).card := card_image_le
    _ = m := by simp

lemma rvShell_succ_sub (d : ℕ) : C.rvShell (d + 1) ⊆ C.rvPreds (C.rvShell d) := by
  intro i hi
  simp only [rvShell, rvLayer, mem_sdiff] at hi
  obtain ⟨hi1, hi2⟩ := hi
  have hp : i ∈ C.rvPreds (C.rvBall d) := by
    simp only [rvBall, mem_union] at hi1
    rcases hi1 with h | h
    · exact absurd h hi2
    · exact h
  simp only [rvPreds, mem_filter] at hp
  obtain ⟨his, i', hi', hsrc⟩ := hp
  cases d with
  | zero => exact mem_filter.mpr ⟨his, i', hi', hsrc⟩
  | succ d =>
    refine mem_filter.mpr ⟨his, i', ?_, hsrc⟩
    simp only [rvShell, rvLayer, mem_sdiff]
    refine ⟨hi', fun hd => hi2 ?_⟩
    exact C.rvPreds_sub_succ d (mem_filter.mpr ⟨his, i', hd, hsrc⟩)

lemma card_rvShell_le (d : ℕ) : (C.rvShell d).card ≤ m * 2 ^ d := by
  induction d with
  | zero => simpa [rvShell] using C.card_rvBall_zero_le
  | succ d ih =>
    calc (C.rvShell (d + 1)).card ≤ (C.rvPreds (C.rvShell d)).card :=
          card_le_card (C.rvShell_succ_sub d)
      _ ≤ 2 * (C.rvShell d).card := C.card_rvPreds_le _
      _ ≤ 2 * (m * 2 ^ d) := Nat.mul_le_mul_left _ ih
      _ = m * 2 ^ (d + 1) := by ring

/-- `rev-layers`: `|L_{d+1}| ≤ m 2^{d+1}`. -/
lemma card_rvLayer_le (d : ℕ) : (C.rvLayer d).card ≤ m * 2 ^ (d + 1) := C.card_rvShell_le (d + 1)

/-- `rev-layers`: `|B_d| ≤ m 2^{d+1}`. -/
lemma card_rvBall_le (d : ℕ) : (C.rvBall d).card ≤ m * 2 ^ (d + 1) := by
  induction d with
  | zero => have := C.card_rvBall_zero_le; simp; omega
  | succ d ih =>
    calc (C.rvBall (d + 1)).card ≤ (C.rvBall (d + 1) \ C.rvBall d).card + (C.rvBall d).card :=
          card_le_card_sdiff_add_card
      _ ≤ m * 2 ^ (d + 1) + m * 2 ^ (d + 1) := add_le_add (C.card_rvLayer_le d) ih
      _ = m * 2 ^ (d + 1 + 1) := by ring

lemma rv_src_lt {i : ℕ} (hi : i < C.s) {a : ℕ} (ha : a ∈ (C.gate i).srcs) : a < n + i := by
  rcases Gate.low_mem_srcs ha with h | ⟨_, h⟩
  · rw [h]; exact C.gate_a_lt hi
  · rw [h]; exact C.gate_b_lt hi

/-- Источник входа элемента из `B_d` — вход схемы или элемент из `B_{d+1}`. -/
lemma rv_pred_mem {d i : ℕ} (hi : i ∈ C.rvBall d) {a : ℕ} (ha : a ∈ (C.gate i).srcs)
    (hn : n ≤ a) : a - n ∈ C.rvBall (d + 1) := by
  apply C.rvPreds_sub_succ d
  have his := C.rvBall_lt hi
  have hlt := C.rv_src_lt his ha
  refine mem_filter.mpr ⟨mem_range.mpr (by omega), i, hi, ?_⟩
  rwa [show n + (a - n) = a by omega]

lemma rv_out_mem (k : Fin m) : C.out k < n ∨ (n ≤ C.out k ∧ C.out k - n ∈ C.rvBall 0) := by
  by_cases h : C.out k < n
  · exact Or.inl h
  · refine Or.inr ⟨by omega, ?_⟩
    have := C.out_lt k
    exact mem_filter.mpr ⟨mem_range.mpr (by unfold Circ.s; omega), k, by omega⟩

lemma rv_not_mem_layer {d i : ℕ} (h : i ∈ C.rvBall d) : i ∉ C.rvLayer d := by
  simp [rvLayer, h]

lemma rv_mem_ball_of_not_layer {d i : ℕ} (h : i ∈ C.rvBall (d + 1)) (h' : i ∉ C.rvLayer d) :
    i ∈ C.rvBall d := by
  by_contra hc
  exact h' (mem_sdiff.mpr ⟨h, hc⟩)

lemma rvLayer_sub_range (d : ℕ) : C.rvLayer d ⊆ range C.s :=
  (sdiff_subset).trans (C.rvBall_sub_range _)

lemma rvLayer_disjoint {d d' : ℕ} (h : d ≠ d') : Disjoint (C.rvLayer d) (C.rvLayer d') := by
  wlog hlt : d < d' generalizing d d'
  · exact (this (Ne.symm h) (by omega)).symm
  rw [disjoint_left]
  intro i hi hi'
  have h1 : i ∈ C.rvBall d' := C.rvBall_mono (by omega) (sdiff_subset hi)
  exact (mem_sdiff.mp hi').2 h1

end Circ

end PowerActivity
