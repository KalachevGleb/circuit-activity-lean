import PowerActivity.ApxBasic

/-!
# Гибридное вычисление при подстановке значений на разрез

Для схемы `C`, множества сигналов `B` и назначения `zf : ℕ × ℕ → Bool` проводам
`hyb C B zf x j` — значение сигнала `j`, если на каждом проводе `(i, t)` из `B` в дополнение `B`
(источник в `B`, элемент `n + i ∉ B`) вместо настоящего сигнала подставлено `zf (i, t)`.
Для `B = fwdBall d` это в точности провода разреза `cut d`.

* `hyb_eq_sig_of_cut` — если `zf` совпадает с настоящими сигналами на разрезе, то `hyb = sig`;
* `hyb_eq_sig_of_check` — если `hyb` на источниках разреза совпадает с `zf`, то `hyb = sig`
  (единственность согласованного вычисления; используется в доказательстве `cut-compress`);
* `hyb_indep` — вне `B = fwdBall d` значение `hyb` не зависит от `x` (тоже для `cut-compress`).
* оценки `|I_d| ≤ |B_d|`, `|R_d| ≤ 3|B_d|` (при исходящих степенях `≤ 3`), `1 ≤ |B_d|`.
-/

namespace PowerActivity.Apx

open Finset

variable {n : ℕ} {κ : Type}

/-- Гибридное вычисление: провода из `B` в дополнение заменены значениями `zf`. -/
def hyb (C : Circ n κ) (B : Finset ℕ) (zf : ℕ × ℕ → Bool) (x : Fin n → Bool) (j : ℕ) : Bool :=
  if h : j < n then x ⟨j, h⟩
  else
    match C.gates[j - n]? with
    | none => false
    | some g =>
      if _hab : g.a < j ∧ g.b < j then
        Op.eval g.op (if g.a ∈ B ∧ j ∉ B then zf (j - n, 0) else hyb C B zf x g.a)
          (if g.b ∈ B ∧ j ∉ B then zf (j - n, 1) else hyb C B zf x g.b)
      else false
termination_by j
decreasing_by all_goals omega

lemma gate_eq_getElem (C : Circ n κ) {i : ℕ} (hi : i < C.s) : C.gate i = C.gates[i] := by
  simp [Circ.gate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma hyb_lt (C : Circ n κ) (B : Finset ℕ) (zf : ℕ × ℕ → Bool) (x : Fin n → Bool) {j : ℕ}
    (h : j < n) : hyb C B zf x j = x ⟨j, h⟩ := by
  rw [hyb]; simp [h]

lemma hyb_ge (C : Circ n κ) (B : Finset ℕ) (zf : ℕ × ℕ → Bool) (x : Fin n → Bool) {j : ℕ}
    (h : n + C.s ≤ j) : hyb C B zf x j = false := by
  rw [hyb]
  have h1 : ¬ j < n := by omega
  simp only [h1, dite_false]
  rw [List.getElem?_eq_none (by unfold Circ.s at h; omega)]

lemma hyb_gate (C : Circ n κ) (B : Finset ℕ) (zf : ℕ × ℕ → Bool) (x : Fin n → Bool) {i : ℕ}
    (hi : i < C.s) :
    hyb C B zf x (n + i) = Op.eval (C.gate i).op
      (if (C.gate i).a ∈ B ∧ n + i ∉ B then zf (i, 0) else hyb C B zf x (C.gate i).a)
      (if (C.gate i).b ∈ B ∧ n + i ∉ B then zf (i, 1) else hyb C B zf x (C.gate i).b) := by
  have ha := C.gate_a_lt hi
  have hb := C.gate_b_lt hi
  rw [hyb]
  have h1 : ¬ n + i < n := by omega
  have h2 : n + i - n = i := by omega
  simp only [h1, dite_false, h2]
  rw [List.getElem?_eq_getElem hi]
  simp only
  rw [← gate_eq_getElem C hi, dif_pos ⟨ha, hb⟩]

/-- Сигнал элемента схемы (форма `val_eq` для сигнала `n + i`). -/
lemma sig_gate' (C : Circ n κ) (x : Fin n → Bool) {i : ℕ} (hi : i < C.s) :
    C.sig x (n + i) = Op.eval (C.gate i).op (C.sig x (C.gate i).a) (C.sig x (C.gate i).b) :=
  C.val_eq x hi

lemma sig_ge' (C : Circ n κ) (x : Fin n → Bool) {j : ℕ} (h : n + C.s ≤ j) : C.sig x j = false :=
  sig_ge _ _ h

/-- Конгруэнтность `Op.eval`: второй аргумент важен только для `∧`, `∨`. -/
lemma Op.eval_congr {op : Op} {u u' v v' : Bool} (hu : u = u') (hv : op ≠ .not → v = v') :
    Op.eval op u v = Op.eval op u' v' := by
  cases op with
  | and => rw [hu, hv (by simp)]
  | or => rw [hu, hv (by simp)]
  | not => simp [Op.eval, hu]

/-! ## Провода и разрез -/

lemma mem_wires (C : Circ n κ) (e : ℕ × ℕ) :
    e ∈ C.wires ↔ e.1 < C.s ∧ e.2 < (C.gate e.1).srcs.length := by
  obtain ⟨i, t⟩ := e
  simp only [Circ.wires, mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', t', ht', rfl, rfl⟩; exact ⟨hi', ht'⟩
  · rintro ⟨hi, ht⟩; exact ⟨i, hi, t, ht, rfl, rfl⟩

lemma srcs_length_pos (g : Gate) : 0 < g.srcs.length := by
  unfold Gate.srcs; cases g.op <;> simp

lemma srcs_length_of_ne (g : Gate) (h : g.op ≠ .not) : g.srcs.length = 2 := by
  unfold Gate.srcs; cases hg : g.op <;> simp_all

lemma srcs_length_le (g : Gate) : g.srcs.length ≤ 2 := by
  unfold Gate.srcs; cases g.op <;> simp

lemma wsrc_zero (C : Circ n κ) (i : ℕ) : C.wsrc (i, 0) = (C.gate i).a := by
  unfold Circ.wsrc Gate.srcs; cases (C.gate i).op <;> simp

lemma wsrc_one (C : Circ n κ) (i : ℕ) (h : (C.gate i).op ≠ .not) :
    C.wsrc (i, 1) = (C.gate i).b := by
  unfold Circ.wsrc Gate.srcs; cases hg : (C.gate i).op <;> simp_all

lemma wire_zero_mem (C : Circ n κ) {i : ℕ} (hi : i < C.s) : (i, 0) ∈ C.wires :=
  (mem_wires C _).2 ⟨hi, srcs_length_pos _⟩

lemma wire_one_mem (C : Circ n κ) {i : ℕ} (hi : i < C.s) (h : (C.gate i).op ≠ .not) :
    (i, 1) ∈ C.wires :=
  (mem_wires C _).2 ⟨hi, by simp [srcs_length_of_ne _ h]⟩

/-- Источник провода предшествует элементу. -/
lemma wsrc_lt (C : Circ n κ) {e : ℕ × ℕ} (he : e ∈ C.wires) : C.wsrc e < n + e.1 := by
  obtain ⟨i, t⟩ := e
  rw [mem_wires] at he
  obtain ⟨hi, ht⟩ := he
  have ha := C.gate_a_lt hi
  have hb := C.gate_b_lt hi
  have h2 := srcs_length_le (C.gate i)
  simp only at ht ⊢
  rcases Nat.lt_or_ge t 1 with h | h
  · have : t = 0 := by omega
    subst this; rw [wsrc_zero]; exact ha
  · have ht1 : t = 1 := by omega
    subst ht1
    have hne : (C.gate i).op ≠ .not := by
      intro hn
      unfold Gate.srcs at ht
      rw [hn] at ht
      simp at ht
    rw [wsrc_one C i hne]; exact hb

lemma mem_cut (C : Circ n κ) (d : ℕ) (e : ℕ × ℕ) :
    e ∈ C.cut d ↔ e ∈ C.wires ∧ C.wsrc e ∈ C.fwdBall d ∧ n + e.1 ∉ C.fwdBall d := by
  simp [Circ.cut]

lemma fwdBall_mono (C : Circ n κ) (d : ℕ) : C.fwdBall d ⊆ C.fwdBall (d + 1) := by
  rw [Circ.fwdBall]; exact subset_union_left

lemma lt_mem_fwdBall (C : Circ n κ) (d : ℕ) {j : ℕ} (hj : j < n) : j ∈ C.fwdBall d := by
  induction d with
  | zero => simp [Circ.fwdBall, hj]
  | succ d ih => exact fwdBall_mono C d ih

lemma one_le_card_fwdBall (C : Circ n κ) (d : ℕ) (hn : 1 ≤ n) : 1 ≤ (C.fwdBall d).card :=
  card_pos.2 ⟨0, lt_mem_fwdBall C d (by omega)⟩

/-! ## Свойства гибридного вычисления для `B = fwdBall d` -/

section Ball

variable (C : Circ n κ) (d : ℕ)

/-- Если `zf` совпадает с настоящими сигналами на проводах разреза, то `hyb = sig`. -/
lemma hyb_eq_sig_of_cut (zf : ℕ × ℕ → Bool) (x : Fin n → Bool)
    (hz : ∀ e ∈ C.cut d, zf e = C.sig x (C.wsrc e)) :
    ∀ j, hyb C (C.fwdBall d) zf x j = C.sig x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjn : j < n
    · rw [hyb_lt _ _ _ _ hjn]; exact (C.sig_input x ⟨j, hjn⟩).symm
    by_cases hjs : n + C.s ≤ j
    · rw [hyb_ge _ _ _ _ hjs, sig_ge' _ _ hjs]
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
    have hi : i < C.s := by omega
    have ha := C.gate_a_lt hi
    have hb := C.gate_b_lt hi
    rw [hyb_gate _ _ _ _ hi, sig_gate' _ _ hi]
    apply Op.eval_congr
    · split_ifs with hc
      · rw [hz (i, 0) ((mem_cut C d _).2 ⟨wire_zero_mem C hi, by rw [wsrc_zero]; exact hc.1, hc.2⟩),
          wsrc_zero]
      · exact ih _ ha
    · intro hne
      split_ifs with hc
      · rw [hz (i, 1) ((mem_cut C d _).2 ⟨wire_one_mem C hi hne,
          by rw [wsrc_one C i hne]; exact hc.1, hc.2⟩), wsrc_one C i hne]
      · exact ih _ hb

/-- Если `hyb` на источниках проводов разреза совпадает с `zf`, то `hyb = sig`
(единственность согласованного вычисления). -/
lemma hyb_eq_sig_of_check (zf : ℕ × ℕ → Bool) (x : Fin n → Bool)
    (hz : ∀ e ∈ C.cut d, hyb C (C.fwdBall d) zf x (C.wsrc e) = zf e) :
    ∀ j, hyb C (C.fwdBall d) zf x j = C.sig x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjn : j < n
    · rw [hyb_lt _ _ _ _ hjn]; exact (C.sig_input x ⟨j, hjn⟩).symm
    by_cases hjs : n + C.s ≤ j
    · rw [hyb_ge _ _ _ _ hjs, sig_ge' _ _ hjs]
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
    have hi : i < C.s := by omega
    have ha := C.gate_a_lt hi
    have hb := C.gate_b_lt hi
    rw [hyb_gate _ _ _ _ hi, sig_gate' _ _ hi]
    apply Op.eval_congr
    · split_ifs with hc
      · have := hz (i, 0) ((mem_cut C d _).2 ⟨wire_zero_mem C hi,
          by rw [wsrc_zero]; exact hc.1, hc.2⟩)
        rw [wsrc_zero] at this
        rw [← this]; exact ih _ ha
      · exact ih _ ha
    · intro hne
      split_ifs with hc
      · have := hz (i, 1) ((mem_cut C d _).2 ⟨wire_one_mem C hi hne,
          by rw [wsrc_one C i hne]; exact hc.1, hc.2⟩)
        rw [wsrc_one C i hne] at this
        rw [← this]; exact ih _ hb
      · exact ih _ hb

/-- Вне шара значение `hyb` не зависит от входного набора. -/
lemma hyb_indep (zf : ℕ × ℕ → Bool) (x y : Fin n → Bool) :
    ∀ j, j ∉ C.fwdBall d → hyb C (C.fwdBall d) zf x j = hyb C (C.fwdBall d) zf y j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjB
    have hjn : ¬ j < n := fun h => hjB (lt_mem_fwdBall C d h)
    by_cases hjs : n + C.s ≤ j
    · rw [hyb_ge _ _ _ _ hjs, hyb_ge _ _ _ _ hjs]
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
    have hi : i < C.s := by omega
    have ha := C.gate_a_lt hi
    have hb := C.gate_b_lt hi
    rw [hyb_gate _ _ _ _ hi, hyb_gate _ _ _ _ hi]
    congr 1
    · by_cases hB : (C.gate i).a ∈ C.fwdBall d
      · simp [hB, hjB]
      · simp only [hB, false_and, if_false]; exact ih _ ha hB
    · by_cases hB : (C.gate i).b ∈ C.fwdBall d
      · simp [hB, hjB]
      · simp only [hB, false_and, if_false]; exact ih _ hb hB

/-- Внутренние элементы: номера `i < L(Σ)` с `n + i ∈ B_d`. -/
def inner : Finset ℕ := (range C.s).filter fun i => n + i ∈ C.fwdBall d

lemma mem_inner {i : ℕ} : i ∈ inner C d ↔ i < C.s ∧ n + i ∈ C.fwdBall d := by
  simp [inner]

lemma card_inner_le : (inner C d).card ≤ (C.fwdBall d).card := by
  apply card_le_card_of_injOn (fun i => n + i)
  · intro i hi; exact ((mem_inner C d).1 hi).2
  · intro i _ j _ h; simp only at h; omega

/-- `|R_d| ≤ 3|B_d|` при исходящих степенях `≤ 3`. -/
lemma card_cut_le (hdeg : ∀ j, C.outdeg j ≤ 3) : (C.cut d).card ≤ 3 * (C.fwdBall d).card := by
  classical
  have hsub : C.cut d ⊆ (C.fwdBall d).biUnion fun j => C.wires.filter fun e => C.wsrc e = j := by
    intro e he
    rw [mem_cut] at he
    rw [mem_biUnion]
    exact ⟨C.wsrc e, he.2.1, by simp [he.1]⟩
  calc (C.cut d).card ≤ _ := card_le_card hsub
    _ ≤ (C.fwdBall d).card * 3 := by
        apply card_biUnion_le_card_mul
        intro j _
        exact hdeg j
    _ = 3 * (C.fwdBall d).card := by ring

end Ball

end PowerActivity.Apx
