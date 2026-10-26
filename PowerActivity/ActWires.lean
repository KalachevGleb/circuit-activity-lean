import PowerActivity.ActEnt

/-!
# Провода (`wires`), шары от входов и разрезы (`fwd-balls`, `cut-sum`)

* `U_eq_card`, `outdeg_eq` — `U(Σ,x)` и исходящая степень как подсчёт проводов `Circ.wires`;
* `wires`: `U_le_two_P` (`U ≤ 2P` для любой схемы), `P_le_U_add_E`, `E_le_U_add_one`
  (`E ≤ U + 1`, если каждый элемент лежит на пути к выходу), `wires_activity`;
  «лежит на ориентированном пути к выходу» — `Reach C (n+i) (C.out k)`;
* `fwd-balls`: `card_fwdBall_le` — `2|B_d| ≤ 3n·3^d` и `cut_card_le` —
  `|R_d| ≤ 3|B_d|` при исходящих степенях `≤ 3`;
* `cut_disjoint` — попарная непересекаемость разрезов `R_d`;
* `cut-sum`: `Uav_ge_sum_cutA` — `U(Σ) ≥ Σ_{d<D} A_d`;
* `ent_cut_le` — `H_d ≤ A_d log(2|R_d|) + 1` (вторая оценка `entropy` для `Z_d`).
-/

namespace PowerActivity

open Finset

namespace Act

variable {n : ℕ} {κ : Type}

lemma srcs_length_le (g : Gate) : g.srcs.length ≤ 2 := by
  unfold Gate.srcs; split <;> simp

lemma card_range_filter_getD (l : List ℕ) (p : ℕ → Bool) :
    ((range l.length).filter fun t => p (l.getD t 0) = true).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ', List.countP_cons, ← ih,
      Finset.card_filter]
    simp

lemma mem_wires (C : Circ n κ) {e : ℕ × ℕ} :
    e ∈ C.wires ↔ e.1 < C.s ∧ e.2 < (C.gate e.1).srcs.length := by
  obtain ⟨i, t⟩ := e
  unfold Circ.wires
  simp only [mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨hi, ht⟩; exact ⟨i, hi, t, ht, rfl, rfl⟩

lemma wsrc_eq (C : Circ n κ) {i t : ℕ} (ht : t < (C.gate i).srcs.length) :
    C.wsrc (i, t) = (C.gate i).srcs[t] := by
  unfold Circ.wsrc; exact List.getD_eq_getElem _ _ ht

lemma wsrc_mem (C : Circ n κ) {e : ℕ × ℕ} (he : e ∈ C.wires) :
    C.wsrc e ∈ (C.gate e.1).srcs := by
  rw [mem_wires] at he
  obtain ⟨i, t⟩ := e
  rw [wsrc_eq C he.2]
  exact List.getElem_mem _

/-- Число проводов, источник которых удовлетворяет `p`. -/
lemma card_wires_filter (C : Circ n κ) (p : ℕ → Bool) :
    (C.wires.filter fun e => p (C.wsrc e) = true).card =
      ∑ i ∈ range C.s, (C.gate i).srcs.countP p := by
  unfold Circ.wires
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_image, Finset.card_image_of_injective]
    · rw [← card_range_filter_getD]; rfl
    · intro t t' h; simpa using h
  · intro i _ j _ hij
    simp only [Function.onFun]
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨t', -, h⟩ := Finset.mem_image.1 h2
    exact hij (congrArg Prod.fst h).symm

/-- `U(Σ,x)` — число проводов с единицей. -/
lemma U_eq_card (C : Circ n κ) (x : Fin n → Bool) :
    C.U x = (C.wires.filter fun e => C.sig x (C.wsrc e) = true).card := by
  rw [card_wires_filter]; rfl

/-- Исходящая степень как число вхождений в списки источников. -/
lemma outdeg_eq (C : Circ n κ) (j : ℕ) :
    C.outdeg j = ∑ i ∈ range C.s, (C.gate i).srcs.countP (fun k => decide (k = j)) := by
  rw [← card_wires_filter]
  unfold Circ.outdeg
  simp only [decide_eq_true_eq]

/-! ## Провода и активность (`wires`) -/

/-- `wires`, первая часть: `U(Σ,x) ≤ 2P(Σ,x)` для любой схемы. -/
theorem U_le_two_P (C : Circ n κ) (x : Fin n → Bool) : C.U x ≤ 2 * C.P x := by
  unfold Circ.U Circ.P
  rw [Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · have := (List.countP_le_length (p := C.sig x)).trans (srcs_length_le (C.gate i)); omega
  · push Not at h
    have : (C.gate i).srcs.countP (C.sig x) = 0 := by
      rw [List.countP_eq_zero]; intro j hj; simpa using h.2 j hj
    omega

/-- `P ≤ U + E`. -/
lemma P_le_U_add_E (C : Circ n κ) (x : Fin n → Bool) : C.P x ≤ C.U x + C.E x := by
  unfold Circ.P
  rw [Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  have hE : ((range C.s).filter fun i => C.val x i = true).card = C.E x := rfl
  have hU : ((range C.s).filter fun i => ∃ j ∈ (C.gate i).srcs, C.sig x j = true).card ≤ C.U x := by
    unfold Circ.U
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · exact List.countP_pos_iff.2 h
    · exact Nat.zero_le _
  omega

/-- Сигнал `j` соединён ориентированным путём (по проводам) с сигналом `k`. -/
inductive Reach (C : Circ n κ) : ℕ → ℕ → Prop
  | refl (j : ℕ) : Reach C j j
  | step {j k : ℕ} (i : ℕ) (hi : i < C.s) (hj : j ∈ (C.gate i).srcs) (h : Reach C (n + i) k) :
      Reach C j k

/-- Каждый элемент схемы лежит на ориентированном пути к выходу `k`. -/
def OnPaths (C : Circ n κ) (k : κ) : Prop := ∀ i < C.s, Reach C (n + i) (C.out k)

lemma reach_cases (C : Circ n κ) {j k : ℕ} (h : Reach C j k) :
    j = k ∨ ∃ i, i < C.s ∧ j ∈ (C.gate i).srcs := by
  cases h with
  | refl => left; rfl
  | step i hi hj _ => right; exact ⟨i, hi, hj⟩

/-- `E ≤ U + 1`, если каждый элемент лежит на пути к выходу `k`. -/
lemma E_le_U_add_one (C : Circ n κ) (k : κ) (hp : OnPaths C k) (x : Fin n → Bool) :
    C.E x ≤ C.U x + 1 := by
  unfold Circ.E
  rw [← Finset.card_filter_add_card_filter_not
    (s := (range C.s).filter fun i => C.val x i = true) (fun i => n + i = C.out k)]
  have h1 : (((range C.s).filter fun i => C.val x i = true).filter
      fun i => n + i = C.out k).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [mem_filter] at ha hb
    omega
  have h2 : (((range C.s).filter fun i => C.val x i = true).filter
      fun i => ¬ n + i = C.out k).card ≤ C.U x := by
    rw [U_eq_card]
    apply Finset.card_le_card_of_surjOn (fun e => C.wsrc e - n)
    intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨his, hv⟩, hne⟩ := hi
    rcases reach_cases C (hp i his) with h | ⟨i', hi', hj⟩
    · exact absurd h hne
    · obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.1 hj
      have hw : C.wsrc (i', t) = n + i := by rw [wsrc_eq C ht]; exact hte
      refine ⟨(i', t), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨(mem_wires C).2 ⟨hi', ht⟩, ?_⟩
        rw [hw]; exact hv
      · show C.wsrc (i', t) - n = i
        omega
  omega

/-- **`wires`.** `U ≤ 2P` для любой схемы; если каждый элемент лежит на ориентированном пути
к выходу `k` (для схемы с одним выходом — к выходу), то `U/2 ≤ P ≤ 2U + 1`. -/
theorem wires_activity (C : Circ n κ) :
    (∀ x, C.U x ≤ 2 * C.P x) ∧
    ∀ k, OnPaths C k → ∀ x, C.U x ≤ 2 * C.P x ∧ C.P x ≤ 2 * C.U x + 1 := by
  refine ⟨U_le_two_P C, fun k hp x => ⟨U_le_two_P C x, ?_⟩⟩
  have h1 := P_le_U_add_E C x
  have h2 := E_le_U_add_one C k hp x
  omega

/-! ## Шары от входов, сферы, разрезы (`fwd-balls`) -/

lemma fwdBall_succ_sub (C : Circ n κ) (d : ℕ) : C.fwdBall d ⊆ C.fwdBall (d + 1) := by
  rw [Circ.fwdBall]; exact subset_union_left

lemma fwdBall_mono (C : Circ n κ) {d d' : ℕ} (h : d ≤ d') : C.fwdBall d ⊆ C.fwdBall d' :=
  monotone_nat_of_le_succ (fun d => fwdBall_succ_sub C d) h

lemma mem_fwdBall_succ_iff (C : Circ n κ) {d v : ℕ} :
    v ∈ C.fwdBall (d + 1) ↔ v ∈ C.fwdBall d ∨
      ∃ i, (i < C.s ∧ ∃ j ∈ (C.gate i).srcs, j ∈ C.fwdBall d) ∧ n + i = v := by
  rw [Circ.fwdBall]; simp

lemma mem_fwdBall_succ (C : Circ n κ) {d i j : ℕ} (hi : i < C.s) (hj : j ∈ (C.gate i).srcs)
    (hb : j ∈ C.fwdBall d) : n + i ∈ C.fwdBall (d + 1) :=
  (mem_fwdBall_succ_iff C).2 (Or.inr ⟨i, ⟨hi, j, hj, hb⟩, rfl⟩)

lemma card_fwdBall_zero (C : Circ n κ) : (C.fwdBall 0).card = n := by
  simp [Circ.fwdBall]

/-- Сферы `S_d = B_d \ B_{d-1}` (`S_0 = B_0` — входы). -/
def sph (C : Circ n κ) : ℕ → Finset ℕ
  | 0 => C.fwdBall 0
  | d + 1 => C.fwdBall (d + 1) \ C.fwdBall d

/-- Число проводов с источником в `S` не больше суммы исходящих степеней. -/
lemma card_wires_from_le (C : Circ n κ) (S : Finset ℕ) :
    (C.wires.filter fun e => C.wsrc e ∈ S).card ≤ ∑ j ∈ S, C.outdeg j := by
  calc _ ≤ (S.biUnion fun j => C.wires.filter fun e => C.wsrc e = j).card := by
        apply card_le_card
        intro e he
        simp only [mem_filter] at he
        simp only [mem_biUnion, mem_filter]
        exact ⟨C.wsrc e, he.2, he.1, rfl⟩
    _ ≤ _ := card_biUnion_le

lemma card_wires_from_le3 (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3) (S : Finset ℕ) :
    (C.wires.filter fun e => C.wsrc e ∈ S).card ≤ 3 * S.card := by
  refine (card_wires_from_le C S).trans ?_
  calc ∑ j ∈ S, C.outdeg j ≤ ∑ _j ∈ S, 3 := Finset.sum_le_sum fun j _ => h3 j
    _ = 3 * S.card := by rw [sum_const, smul_eq_mul, mul_comm]

lemma card_sph_succ_le (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3) (d : ℕ) :
    (sph C (d + 1)).card ≤ 3 * (sph C d).card := by
  set T := (range C.s).filter fun i => ∃ j ∈ (C.gate i).srcs, j ∈ sph C d with hT
  have hsub : sph C (d + 1) ⊆ T.image (n + ·) := by
    intro v hv
    simp only [sph, mem_sdiff] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rcases (mem_fwdBall_succ_iff C).1 hv1 with h | ⟨i, ⟨hi, j, hj, hjb⟩, rfl⟩
    · exact absurd h hv2
    · apply mem_image_of_mem
      simp only [hT, mem_filter, mem_range]
      refine ⟨hi, j, hj, ?_⟩
      cases d with
      | zero => simpa [sph] using hjb
      | succ d' =>
        simp only [sph, mem_sdiff]
        exact ⟨hjb, fun hj' => hv2 (mem_fwdBall_succ C hi hj hj')⟩
  have hTc : T.card ≤ (C.wires.filter fun e => C.wsrc e ∈ sph C d).card := by
    apply card_le_card_of_surjOn (fun e => e.1)
    intro i hi
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi, j, hj, hjs⟩ := hi
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hj
    refine ⟨(i, t), ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(mem_wires C).2 ⟨hi, ht⟩, ?_⟩
    rw [wsrc_eq C ht]; exact hjs
  calc (sph C (d + 1)).card ≤ (T.image (n + ·)).card := card_le_card hsub
    _ ≤ T.card := card_image_le
    _ ≤ _ := hTc
    _ ≤ 3 * (sph C d).card := card_wires_from_le3 C h3 _

lemma card_sph_le (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3) (d : ℕ) :
    (sph C d).card ≤ n * 3 ^ d := by
  induction d with
  | zero => simp [sph, card_fwdBall_zero]
  | succ d ih =>
    calc (sph C (d + 1)).card ≤ 3 * (sph C d).card := card_sph_succ_le C h3 d
      _ ≤ 3 * (n * 3 ^ d) := by omega
      _ = n * 3 ^ (d + 1) := by ring

lemma card_fwdBall_succ (C : Circ n κ) (d : ℕ) :
    (C.fwdBall (d + 1)).card = (C.fwdBall d).card + (sph C (d + 1)).card := by
  simp only [sph]
  rw [← card_sdiff_add_card_eq_card (fwdBall_succ_sub C d)]
  ring

/-- **`fwd-balls`, первая часть.** `|B_d| ≤ (3/2)·n·3^d` при исходящих степенях `≤ 3`. -/
theorem card_fwdBall_le (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3) (d : ℕ) :
    2 * (C.fwdBall d).card ≤ 3 * n * 3 ^ d := by
  induction d with
  | zero => rw [card_fwdBall_zero]; omega
  | succ d ih =>
    rw [card_fwdBall_succ]
    have h := card_sph_le C h3 (d + 1)
    rw [pow_succ] at h ⊢
    nlinarith

lemma mem_cut (C : Circ n κ) {d : ℕ} {e : ℕ × ℕ} :
    e ∈ C.cut d ↔ e ∈ C.wires ∧ C.wsrc e ∈ C.fwdBall d ∧ n + e.1 ∉ C.fwdBall d := by
  unfold Circ.cut; simp only [mem_filter]

/-- **`fwd-balls`, вторая часть.** `|R_d| ≤ 3|B_d|`. -/
theorem cut_card_le (C : Circ n κ) (h3 : ∀ j, C.outdeg j ≤ 3) (d : ℕ) :
    (C.cut d).card ≤ 3 * (C.fwdBall d).card := by
  refine (card_le_card ?_).trans (card_wires_from_le3 C h3 (C.fwdBall d))
  intro e he
  rw [mem_cut] at he
  simp only [mem_filter]
  exact ⟨he.1, he.2.1⟩

/-- Разрезы `R_d` попарно не пересекаются. -/
theorem cut_disjoint (C : Circ n κ) {d d' : ℕ} (h : d < d') : Disjoint (C.cut d) (C.cut d') := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  rw [mem_cut] at h1 h2
  have hw := (mem_wires C).1 h1.1
  have hb := mem_fwdBall_succ C hw.1 (wsrc_mem C h1.1) h1.2.1
  exact h2.2.2 (fwdBall_mono C h hb)

lemma cut_pairwiseDisjoint (C : Circ n κ) (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint C.cut := by
  intro d _ d' _ hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact cut_disjoint C h
  · exact (cut_disjoint C h).symm

/-! ## Сумма по разрезам (`cut-sum`) -/

/-- `A_d = Σ_{e ∈ R_d} P{s_e(X) = 1}`. -/
noncomputable def cutA (C : Circ n κ) (d : ℕ) : ℝ :=
  ∑ e ∈ C.cut d, probZ (fun x => C.sig x (C.wsrc e)) true

lemma cutA_nonneg (C : Circ n κ) (d : ℕ) : 0 ≤ cutA C d :=
  Finset.sum_nonneg fun _ _ => probZ_nonneg _ _

lemma Uav_eq_sum_wires (C : Circ n κ) :
    C.Uav = ∑ e ∈ C.wires, probZ (fun x => C.sig x (C.wsrc e)) true := by
  unfold Circ.Uav avgM probZ
  rw [← Finset.sum_div]
  congr 1
  have h : ∑ x, C.U x = ∑ e ∈ C.wires, (univ.filter fun x => C.sig x (C.wsrc e) = true).card := by
    simp_rw [U_eq_card, Finset.card_filter]
    exact Finset.sum_comm
  exact_mod_cast h

/-- **`cut-sum`.** `U(Σ) ≥ Σ_{d < D} A_d`. -/
theorem Uav_ge_sum_cutA (C : Circ n κ) (D : ℕ) : ∑ d ∈ range D, cutA C d ≤ C.Uav := by
  rw [Uav_eq_sum_wires]
  unfold cutA
  rw [← Finset.sum_biUnion (cut_pairwiseDisjoint C _)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [mem_biUnion] at he
    obtain ⟨d, _, hd⟩ := he
    exact ((mem_cut C).1 hd).1
  · intro e _ _; exact probZ_nonneg _ _

lemma cutA_eq (C : Circ n κ) (d : ℕ) :
    ∑ i : C.cut d, probZ (fun x => C.cutVal d x i) true = cutA C d := by
  unfold cutA Circ.cutVal
  exact Finset.sum_coe_sort (C.cut d) (fun e => probZ (fun x => C.sig x (C.wsrc e)) true)

/-- `H_d ≤ A_d log(2|R_d|) + 1` (вторая оценка `entropy` для `Z_d`). -/
theorem ent_cut_le (C : Circ n κ) (d : ℕ) :
    ent (C.cutVal d) ≤ cutA C d * Real.logb 2 (2 * (C.cut d).card) + 1 := by
  have h := entropy_bound_simple (C.cutVal d)
  rw [cutA_eq, Fintype.card_coe] at h
  exact h

end Act

end PowerActivity
