import PowerActivity.Defs

/-!
# Верхние оценки: библиотека построения схем

Все определения — в пространстве имён `PowerActivity.Up` (чтобы не пересекаться с другими
модулями).

* `Up.app` — дописывание схемы `C₂` с `k` входами, входы которой питаются сигналами
  `feed j` схемы `C₁` (элементы `C₂` перенумерованы и стоят после элементов `C₁`);
* `Up.withOut`, `Up.reout` — смена выходов;
* `Up.compR`, `Up.comp` — последовательная композиция, `Up.sel` — выбор входов,
  `Up.par2`, `Up.parF` — параллельная композиция на тех же входах;
* `Up.layer` — слой элементов, все входы которых — входы схемы.

Для каждой операции доказаны формулы для выходов и аддитивность мер `E`, `U`, `P`;
кроме того, `E ≤ L`, `P ≤ L`, `U ≤ 2P` и обнуление монотонных схем на нулевом наборе.
-/

namespace PowerActivity

open Finset

namespace Up

/-- Перенумерация ссылок дописываемой схемы: вход `r < k` идёт от сигнала `feed r`,
элемент `i` становится сигналом `base + i`. -/
def remap (base k : ℕ) (feed : Fin k → ℕ) (r : ℕ) : ℕ :=
  if h : r < k then feed ⟨r, h⟩ else base + (r - k)

/-- Перенумерованный элемент. -/
def remapG (base k : ℕ) (feed : Fin k → ℕ) (g : Gate) : Gate :=
  ⟨g.op, remap base k feed g.a, remap base k feed g.b⟩

lemma remap_lt {base k i : ℕ} {feed : Fin k → ℕ} (hf : ∀ j, feed j < base) {r : ℕ}
    (hr : r < k + i) : remap base k feed r < base + i := by
  unfold remap
  split_ifs with h
  · exact lt_of_lt_of_le (hf _) (Nat.le_add_right _ _)
  · omega

lemma remap_of_lt {base k : ℕ} {feed : Fin k → ℕ} {r : ℕ} (h : r < k) :
    remap base k feed r = feed ⟨r, h⟩ := by simp [remap, h]

lemma remap_add {base k : ℕ} {feed : Fin k → ℕ} (i : ℕ) :
    remap base k feed (k + i) = base + i := by simp [remap]

lemma srcs_remapG (base k : ℕ) (feed : Fin k → ℕ) (g : Gate) :
    (remapG base k feed g).srcs = g.srcs.map (remap base k feed) := by
  rcases g with ⟨op, a, b⟩
  cases op <;> rfl

lemma mem_srcs {g : Gate} {j : ℕ} (h : j ∈ g.srcs) : j = g.a ∨ j = g.b := by
  rcases g with ⟨op, a, b⟩
  cases op <;> simp [Gate.srcs] at h <;> tauto

lemma srcs_length_le (g : Gate) : g.srcs.length ≤ 2 := by
  rcases g with ⟨op, a, b⟩
  cases op <;> simp [Gate.srcs]

/-- Не более одной единицы в наборе. -/
def AtMostOne {α : Type} (y : α → Bool) : Prop := ∀ i j, y i = true → y j = true → i = j

lemma AtMostOne.comp {α β : Type} {y : α → Bool} (hy : AtMostOne y) {f : β → α}
    (hf : Function.Injective f) : AtMostOne (fun b => y (f b)) :=
  fun _ _ h1 h2 => hf (hy _ _ h1 h2)

variable {n : ℕ} {ι κ κ' : Type}

/-! ## Общие факты о мерах -/

lemma sig_of_lt (C : Circ n κ) (x : Fin n → Bool) {j : ℕ} (h : j < n) :
    C.sig x j = x ⟨j, h⟩ := sig_lt _ _ h

lemma E_eq_sum (C : Circ n κ) (x : Fin n → Bool) :
    C.E x = ∑ i ∈ range C.s, if C.val x i = true then 1 else 0 := by
  unfold Circ.E; rw [Finset.card_filter]

lemma P_eq_sum (C : Circ n κ) (x : Fin n → Bool) :
    C.P x = ∑ i ∈ range C.s,
      if (C.val x i = true ∨ ∃ j ∈ (C.gate i).srcs, C.sig x j = true) then 1 else 0 := by
  unfold Circ.P; rw [Finset.card_filter]

lemma srcs_lt (C : Circ n κ) {i : ℕ} (hi : i < C.s) {j : ℕ} (hj : j ∈ (C.gate i).srcs) :
    j < n + i := by
  rcases mem_srcs hj with rfl | rfl
  · exact C.gate_a_lt hi
  · exact C.gate_b_lt hi

lemma E_le_s (C : Circ n κ) (x : Fin n → Bool) : C.E x ≤ C.s := by
  unfold Circ.E
  exact (card_filter_le _ _).trans (by simp)

lemma P_le_s (C : Circ n κ) (x : Fin n → Bool) : C.P x ≤ C.s := by
  unfold Circ.P
  exact (card_filter_le _ _).trans (by simp)

lemma U_le_two_P (C : Circ n κ) (x : Fin n → Bool) : C.U x ≤ 2 * C.P x := by
  rw [P_eq_sum, Finset.mul_sum]
  unfold Circ.U
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · exact (List.countP_le_length).trans ((srcs_length_le _).trans (by norm_num))
  · push Not at h
    have : (C.gate i).srcs.countP (C.sig x) = 0 := by
      rw [List.countP_eq_zero]
      intro j hj
      simp [h.2 j hj]
    omega

/-- Все элементы — `∧` или `∨` (монотонная схема). -/
def Mono (C : Circ n κ) : Prop := ∀ g ∈ C.gates, g.op ≠ .not

lemma gate_mem (C : Circ n κ) {i : ℕ} (hi : i < C.s) : C.gate i ∈ C.gates := by
  have hg : C.gate i = C.gates[i] := by
    simp [Circ.gate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hg]; exact List.getElem_mem _

/-- На нулевом наборе все сигналы монотонной схемы нулевые. -/
lemma Mono.sig_zero {C : Circ n κ} (hC : Mono C) {x : Fin n → Bool} (hx : ∀ i, x i = false) :
    ∀ j, C.sig x j = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h1 : j < n
    · simp [Circ.sig, sig_lt _ _ h1, hx]
    · by_cases h2 : j < n + C.s
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
        have hi : i < C.s := by omega
        have e := C.val_eq x hi
        unfold Circ.val at e
        rw [e, ih _ (by have := C.gate_a_lt hi; omega), ih _ (by have := C.gate_b_lt hi; omega)]
        have hop := hC _ (gate_mem C hi)
        revert hop
        cases (C.gate i).op <;> simp [Op.eval]
      · simp [Circ.sig, Circ.s] at h2 ⊢
        exact sig_ge _ _ (by omega)

lemma Mono.E_zero {C : Circ n κ} (hC : Mono C) {x : Fin n → Bool} (hx : ∀ i, x i = false) :
    C.E x = 0 := by
  rw [E_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp [Circ.val, hC.sig_zero hx]

lemma Mono.P_zero {C : Circ n κ} (hC : Mono C) {x : Fin n → Bool} (hx : ∀ i, x i = false) :
    C.P x = 0 := by
  rw [P_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp [Circ.val, hC.sig_zero hx]

/-! ## Дописывание схемы -/

/-- Дописывание схемы `C2` с `k` входами; вход `j` схемы `C2` питается сигналом `feed j`
схемы `C1`. Выходы — выходы обеих схем. -/
def app (C1 : Circ n ι) (k : ℕ) (feed : Fin k → ℕ) (hf : ∀ j, feed j < n + C1.s)
    (C2 : Circ k κ) : Circ n (ι ⊕ κ) where
  gates := C1.gates ++ C2.gates.map (remapG (n + C1.s) k feed)
  valid := by
    intro i h
    simp only [List.length_append, List.length_map] at h
    rw [List.getElem_append]
    split_ifs with hi
    · exact C1.valid i hi
    · simp only [List.getElem_map, remapG]
      have hv := C2.valid (i - C1.gates.length) (by omega)
      have h1 := remap_lt (i := i - C1.gates.length) hf hv.1
      have h2 := remap_lt (i := i - C1.gates.length) hf hv.2
      simp only [Circ.s] at h1 h2 ⊢
      constructor <;> omega
  out := Sum.elim C1.out (fun c => remap (n + C1.s) k feed (C2.out c))
  out_lt := by
    intro c
    cases c with
    | inl c => have := C1.out_lt c; simp; omega
    | inr c =>
      have := remap_lt (i := C2.gates.length) hf (C2.out_lt c)
      simp [Circ.s] at this ⊢; omega

section app

variable (C1 : Circ n ι) (k : ℕ) (feed : Fin k → ℕ) (hf : ∀ j, feed j < n + C1.s)
  (C2 : Circ k κ)

lemma app_s : (app C1 k feed hf C2).s = C1.s + C2.s := by simp [app, Circ.s]

lemma app_gates :
    (app C1 k feed hf C2).gates = C1.gates ++ C2.gates.map (remapG (n + C1.s) k feed) :=
  rfl

lemma app_gate_old {i : ℕ} (hi : i < C1.s) : (app C1 k feed hf C2).gate i = C1.gate i := by
  simp only [Circ.gate, app_gates, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi]

lemma app_gate_new {i : ℕ} (hi : i < C2.s) :
    (app C1 k feed hf C2).gate (C1.s + i) = remapG (n + C1.s) k feed (C2.gate i) := by
  simp only [Circ.gate, app_gates, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [Circ.s])]
  simp only [Circ.s, Nat.add_sub_cancel_left, List.getElem?_map]
  rw [List.getElem?_eq_getElem hi]
  simp

lemma sig_app_old (x : Fin n → Bool) {j : ℕ} (hj : j < n + C1.s) :
    (app C1 k feed hf C2).sig x j = C1.sig x j :=
  sig_append _ _ x j hj

lemma sig_app_new (x : Fin n → Bool) :
    ∀ r, r < k + C2.s → (app C1 k feed hf C2).sig x (remap (n + C1.s) k feed r) =
      C2.sig (fun j => C1.sig x (feed j)) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    by_cases hrk : r < k
    · rw [remap_of_lt hrk, sig_app_old C1 k feed hf C2 x (hf _)]
      simp [Circ.sig, sig_lt _ _ hrk]
    · obtain ⟨i, rfl⟩ : ∃ i, r = k + i := ⟨r - k, by omega⟩
      have hi : i < C2.s := by omega
      rw [remap_add]
      have e1 := (app C1 k feed hf C2).val_eq x (i := C1.s + i) (by rw [app_s]; omega)
      unfold Circ.val at e1
      rw [show n + C1.s + i = n + (C1.s + i) by omega, e1, app_gate_new C1 k feed hf C2 hi]
      have e2 := C2.val_eq (fun j => C1.sig x (feed j)) hi
      unfold Circ.val at e2
      rw [e2]
      simp only [remapG]
      have ha := C2.gate_a_lt hi
      have hb := C2.gate_b_lt hi
      rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega)]

lemma val_app_old (x : Fin n → Bool) {i : ℕ} (hi : i < C1.s) :
    (app C1 k feed hf C2).val x i = C1.val x i := by
  unfold Circ.val
  exact sig_app_old C1 k feed hf C2 x (by omega)

lemma val_app_new (x : Fin n → Bool) {i : ℕ} (hi : i < C2.s) :
    (app C1 k feed hf C2).val x (C1.s + i) = C2.val (fun j => C1.sig x (feed j)) i := by
  unfold Circ.val
  have := sig_app_new C1 k feed hf C2 x (k + i) (by omega)
  rw [remap_add] at this
  rw [show n + (C1.s + i) = n + C1.s + i by omega, this]

lemma app_eval_inl (x : Fin n → Bool) (c : ι) :
    (app C1 k feed hf C2).eval x (Sum.inl c) = C1.eval x c :=
  sig_app_old C1 k feed hf C2 x (C1.out_lt c)

lemma app_eval_inr (x : Fin n → Bool) (c : κ) :
    (app C1 k feed hf C2).eval x (Sum.inr c) = C2.eval (fun j => C1.sig x (feed j)) c :=
  sig_app_new C1 k feed hf C2 x _ (C2.out_lt c)

lemma E_app (x : Fin n → Bool) :
    (app C1 k feed hf C2).E x = C1.E x + C2.E (fun j => C1.sig x (feed j)) := by
  rw [E_eq_sum, E_eq_sum, E_eq_sum, app_s, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [val_app_old C1 k feed hf C2 x hi]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [val_app_new C1 k feed hf C2 x hi]

lemma U_app (x : Fin n → Bool) :
    (app C1 k feed hf C2).U x = C1.U x + C2.U (fun j => C1.sig x (feed j)) := by
  unfold Circ.U
  rw [app_s, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    rw [app_gate_old C1 k feed hf C2 hi]
    apply List.countP_congr
    intro j hj
    rw [sig_app_old C1 k feed hf C2 x (by have := srcs_lt C1 hi hj; omega)]
  · apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    rw [app_gate_new C1 k feed hf C2 hi, srcs_remapG, List.countP_map]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp]
    rw [sig_app_new C1 k feed hf C2 x j (by have := srcs_lt C2 hi hj; omega)]

lemma P_app (x : Fin n → Bool) :
    (app C1 k feed hf C2).P x = C1.P x + C2.P (fun j => C1.sig x (feed j)) := by
  rw [P_eq_sum, P_eq_sum, P_eq_sum, app_s, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ∀ j ∈ (C1.gate i).srcs, (app C1 k feed hf C2).sig x j = C1.sig x j := by
      intro j hj
      exact sig_app_old C1 k feed hf C2 x (by have := srcs_lt C1 hi hj; omega)
    rw [val_app_old C1 k feed hf C2 x hi, app_gate_old C1 k feed hf C2 hi]
    congr 1
    apply propext
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, by rw [← h1 j hj, h]⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, by rw [h1 j hj, h]⟩
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ∀ j ∈ (C2.gate i).srcs, (app C1 k feed hf C2).sig x (remap (n + C1.s) k feed j) =
        C2.sig (fun j => C1.sig x (feed j)) j := by
      intro j hj
      exact sig_app_new C1 k feed hf C2 x j (by have := srcs_lt C2 hi hj; omega)
    rw [val_app_new C1 k feed hf C2 x hi, app_gate_new C1 k feed hf C2 hi, srcs_remapG]
    congr 1
    apply propext
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl h
      · obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
        exact Or.inr ⟨j', hj', by rw [← h1 j' hj', h]⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, List.mem_map_of_mem hj, by rw [h1 j hj, h]⟩

end app

lemma Mono.app {C1 : Circ n ι} {k : ℕ} {feed : Fin k → ℕ} (hf : ∀ j, feed j < n + C1.s)
    {C2 : Circ k κ} (h1 : Mono C1) (h2 : Mono C2) :
    Mono (app C1 k feed hf C2) := by
  intro g hg
  rw [app_gates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact h1 g hg
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact h2 g' hg'

/-! ## Смена выходов -/

/-- Та же схема с другими выходами (произвольными сигналами). -/
def withOut (C : Circ n κ) (o : κ' → ℕ) (ho : ∀ c, o c < n + C.s) : Circ n κ' :=
  ⟨C.gates, C.valid, o, ho⟩

section withOut
variable (C : Circ n κ) (o : κ' → ℕ) (ho : ∀ c, o c < n + C.s)

@[simp] lemma withOut_s : (withOut C o ho).s = C.s := rfl
@[simp] lemma withOut_sig : (withOut C o ho).sig = C.sig := rfl
@[simp] lemma withOut_E : (withOut C o ho).E = C.E := rfl
@[simp] lemma withOut_U : (withOut C o ho).U = C.U := rfl
@[simp] lemma withOut_P : (withOut C o ho).P = C.P := rfl
@[simp] lemma withOut_gates : (withOut C o ho).gates = C.gates := rfl
lemma withOut_eval (x : Fin n → Bool) (c : κ') : (withOut C o ho).eval x c = C.sig x (o c) := rfl

end withOut

lemma Mono.withOut {C : Circ n κ} {o : κ' → ℕ} (ho : ∀ c, o c < n + C.s) (h : Mono C) :
    Mono (withOut C o ho) := h

/-- Переобозначение выходов. -/
def reout (C : Circ n κ) (g : κ' → κ) : Circ n κ' :=
  withOut C (fun c => C.out (g c)) (fun _ => C.out_lt _)

section reout
variable (C : Circ n κ) (g : κ' → κ)

@[simp] lemma reout_s : (reout C g).s = C.s := rfl
@[simp] lemma reout_sig : (reout C g).sig = C.sig := rfl
@[simp] lemma reout_E : (reout C g).E = C.E := rfl
@[simp] lemma reout_U : (reout C g).U = C.U := rfl
@[simp] lemma reout_P : (reout C g).P = C.P := rfl
@[simp] lemma reout_gates : (reout C g).gates = C.gates := rfl
@[simp] lemma reout_eval (x : Fin n → Bool) (c : κ') : (reout C g).eval x c = C.eval x (g c) :=
  rfl

end reout

lemma Mono.reout {C : Circ n κ} (g : κ' → κ) (h : Mono C) : Mono (reout C g) := h

/-! ## Последовательная композиция -/

/-- Последовательная композиция: входы `C2` питаются сигналами `feed` схемы `C1`;
выходы — выходы `C2`. Прежние сигналы `C1` сохраняют номера. -/
def compR (C1 : Circ n ι) (k : ℕ) (feed : Fin k → ℕ) (hf : ∀ j, feed j < n + C1.s)
    (C2 : Circ k κ) : Circ n κ :=
  reout (app C1 k feed hf C2) Sum.inr

section compR
variable (C1 : Circ n ι) (k : ℕ) (feed : Fin k → ℕ) (hf : ∀ j, feed j < n + C1.s)
  (C2 : Circ k κ)

lemma compR_s : (compR C1 k feed hf C2).s = C1.s + C2.s := app_s C1 k feed hf C2

lemma compR_eval (x : Fin n → Bool) (c : κ) :
    (compR C1 k feed hf C2).eval x c = C2.eval (fun j => C1.sig x (feed j)) c := by
  unfold compR
  rw [reout_eval]
  exact sig_app_new C1 k feed hf C2 x _ (C2.out_lt c)

lemma compR_sig_old (x : Fin n → Bool) {j : ℕ} (hj : j < n + C1.s) :
    (compR C1 k feed hf C2).sig x j = C1.sig x j := sig_app_old C1 k feed hf C2 x hj

lemma compR_E (x : Fin n → Bool) :
    (compR C1 k feed hf C2).E x = C1.E x + C2.E (fun j => C1.sig x (feed j)) :=
  E_app C1 k feed hf C2 x

lemma compR_P (x : Fin n → Bool) :
    (compR C1 k feed hf C2).P x = C1.P x + C2.P (fun j => C1.sig x (feed j)) :=
  P_app C1 k feed hf C2 x

end compR

lemma Mono.compR {C1 : Circ n ι} {k : ℕ} {feed : Fin k → ℕ} (hf : ∀ j, feed j < n + C1.s)
    {C2 : Circ k κ} (h1 : Mono C1) (h2 : Mono C2) :
    Mono (compR C1 k feed hf C2) := Mono.reout _ (Mono.app hf h1 h2)

/-- Последовательная композиция по выходам: вход `j` схемы `C2` — выход `f j` схемы `C1`. -/
def comp {k : ℕ} (C1 : Circ n ι) (f : Fin k → ι) (C2 : Circ k κ) : Circ n κ :=
  compR C1 k (fun j => C1.out (f j)) (fun _ => C1.out_lt _) C2

section comp
variable {k : ℕ} (C1 : Circ n ι) (f : Fin k → ι) (C2 : Circ k κ)

lemma comp_s : (comp C1 f C2).s = C1.s + C2.s := compR_s _ _ _ _ _

lemma comp_eval (x : Fin n → Bool) (c : κ) :
    (comp C1 f C2).eval x c = C2.eval (fun j => C1.eval x (f j)) c :=
  compR_eval _ _ _ _ _ x c

lemma comp_sig_old (x : Fin n → Bool) {j : ℕ} (hj : j < n + C1.s) :
    (comp C1 f C2).sig x j = C1.sig x j := compR_sig_old _ _ _ _ _ x hj

lemma comp_E (x : Fin n → Bool) :
    (comp C1 f C2).E x = C1.E x + C2.E (fun j => C1.eval x (f j)) :=
  compR_E _ _ _ _ _ x

lemma comp_P (x : Fin n → Bool) :
    (comp C1 f C2).P x = C1.P x + C2.P (fun j => C1.eval x (f j)) :=
  compR_P _ _ _ _ _ x

lemma comp_E_le (x : Fin n → Bool) : (comp C1 f C2).E x ≤ C1.E x + C2.s := by
  rw [comp_E]; have := E_le_s C2 (fun j => C1.eval x (f j)); omega

lemma comp_P_le (x : Fin n → Bool) : (comp C1 f C2).P x ≤ C1.P x + C2.s := by
  rw [comp_P]; have := P_le_s C2 (fun j => C1.eval x (f j)); omega

end comp

lemma Mono.comp {k : ℕ} {C1 : Circ n ι} (f : Fin k → ι) {C2 : Circ k κ} (h1 : Mono C1)
    (h2 : Mono C2) : Mono (comp C1 f C2) := Mono.compR _ h1 h2

/-- Схема без элементов и без выходов. -/
def empty (n : ℕ) : Circ n Empty := ⟨[], by simp, fun e => e.elim, fun e => e.elim⟩

lemma empty_sig (x : Fin n → Bool) (j : Fin n) : (empty n).sig x j = x j := by
  simp [Circ.sig, sig_lt _ _ j.2]

/-- Выбор входов: вход `j` схемы `C` — вход `f j` новой схемы. -/
def sel {k : ℕ} (C : Circ k κ) (f : Fin k → Fin n) : Circ n κ :=
  compR (empty n) k (fun j => (f j).val) (fun j => by simp [empty, Circ.s]) C

section sel
variable {k : ℕ} (C : Circ k κ) (f : Fin k → Fin n)

lemma sel_eval (x : Fin n → Bool) (c : κ) : (sel C f).eval x c = C.eval (fun j => x (f j)) c := by
  unfold sel
  rw [compR_eval]
  simp only [empty_sig]

lemma sel_E (x : Fin n → Bool) : (sel C f).E x = C.E (fun j => x (f j)) := by
  unfold sel
  rw [compR_E]
  simp only [empty_sig]
  have : (empty n).E x = 0 := by rw [E_eq_sum]; simp [empty, Circ.s]
  omega

lemma sel_P (x : Fin n → Bool) : (sel C f).P x = C.P (fun j => x (f j)) := by
  unfold sel
  rw [compR_P]
  simp only [empty_sig]
  have : (empty n).P x = 0 := by rw [P_eq_sum]; simp [empty, Circ.s]
  omega

end sel

lemma Mono.sel {k : ℕ} {C : Circ k κ} (f : Fin k → Fin n) (h : Mono C) : Mono (sel C f) :=
  Mono.compR _ (by intro g hg; simp [empty] at hg) h

/-! ## Параллельная композиция -/

/-- Две схемы на одних и тех же входах. -/
def par2 (C1 : Circ n ι) (C2 : Circ n κ) : Circ n (ι ⊕ κ) :=
  app C1 n (fun j => j.val) (fun j => by omega) C2

section par2
variable (C1 : Circ n ι) (C2 : Circ n κ)

lemma par2_in (x : Fin n → Bool) : (fun j : Fin n => C1.sig x j.val) = x := by
  funext j; exact C1.sig_input x j

lemma par2_eval_inl (x : Fin n → Bool) (c : ι) : (par2 C1 C2).eval x (Sum.inl c) = C1.eval x c :=
  sig_app_old C1 n _ _ C2 x (C1.out_lt c)

lemma par2_eval_inr (x : Fin n → Bool) (c : κ) : (par2 C1 C2).eval x (Sum.inr c) = C2.eval x c := by
  have := sig_app_new C1 n (fun j => j.val) (fun j => by omega) C2 x _ (C2.out_lt c)
  rw [par2_in] at this
  exact this

lemma par2_E (x : Fin n → Bool) : (par2 C1 C2).E x = C1.E x + C2.E x := by
  unfold par2; rw [E_app, par2_in]

lemma par2_P (x : Fin n → Bool) : (par2 C1 C2).P x = C1.P x + C2.P x := by
  unfold par2; rw [P_app, par2_in]

end par2

lemma Mono.par2 {C1 : Circ n ι} {C2 : Circ n κ} (h1 : Mono C1) (h2 : Mono C2) :
    Mono (par2 C1 C2) := Mono.app _ h1 h2

/-- Параллельная композиция семейства схем с общим типом выходов. -/
def parF : (q : ℕ) → (Fin q → Circ n κ) → Circ n (Fin q × κ)
  | 0, _ => ⟨[], by simp, fun p => p.1.elim0, fun p => p.1.elim0⟩
  | q + 1, C => reout (par2 (parF q fun i => C i.castSucc) (C (Fin.last q)))
      (fun p => Fin.lastCases (motive := fun _ => (Fin q × κ) ⊕ κ) (Sum.inr p.2)
        (fun i => Sum.inl (i, p.2)) p.1)

lemma parF_eval : ∀ (q : ℕ) (C : Fin q → Circ n κ) (x : Fin n → Bool) (i : Fin q) (c : κ),
    (parF q C).eval x (i, c) = (C i).eval x c
  | 0, _, _, i, _ => i.elim0
  | q + 1, C, x, i, c => by
    simp only [parF, reout_eval]
    induction i using Fin.lastCases with
    | last => simp [par2_eval_inr]
    | cast i => simp [par2_eval_inl, parF_eval q]

lemma parF_E : ∀ (q : ℕ) (C : Fin q → Circ n κ) (x : Fin n → Bool),
    (parF q C).E x = ∑ i, (C i).E x
  | 0, _, _ => by rw [E_eq_sum]; simp [parF, Circ.s]
  | q + 1, C, x => by
    simp only [parF, reout_E, par2_E, parF_E q, Fin.sum_univ_castSucc]

/-! ## Слой элементов над входами -/

/-- Слой из `w` элементов, все входы которых — входы схемы; выход `i` — элемент `i`. -/
def layer (k w : ℕ) (op : Fin w → Op) (a b : Fin w → Fin k) : Circ k (Fin w) where
  gates := List.ofFn fun i => (⟨op i, a i, b i⟩ : Gate)
  valid := by
    intro i h
    simp only [List.getElem_ofFn]
    constructor <;> omega
  out := fun i => k + i
  out_lt := by intro i; simp

section layer
variable (k w : ℕ) (op : Fin w → Op) (a b : Fin w → Fin k)

lemma layer_s : (layer k w op a b).s = w := by simp [layer, Circ.s]

lemma layer_gate (i : Fin w) : (layer k w op a b).gate i = ⟨op i, a i, b i⟩ := by
  simp [Circ.gate, layer, List.getD_eq_getElem?_getD]

lemma layer_val (y : Fin k → Bool) (i : Fin w) :
    (layer k w op a b).val y i = (op i).eval (y (a i)) (y (b i)) := by
  rw [Circ.val_eq _ _ (by rw [layer_s]; exact i.2), layer_gate]
  simp only [Circ.sig_input]

lemma layer_eval (y : Fin k → Bool) (i : Fin w) :
    (layer k w op a b).eval y i = (op i).eval (y (a i)) (y (b i)) :=
  layer_val k w op a b y i

lemma layer_E (y : Fin k → Bool) :
    (layer k w op a b).E y =
      (univ.filter fun i : Fin w => (op i).eval (y (a i)) (y (b i)) = true).card := by
  rw [E_eq_sum, layer_s, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [layer_val]

end layer

lemma Mono.layer {k w : ℕ} {op : Fin w → Op} (a b : Fin w → Fin k) (h : ∀ i, op i ≠ .not) :
    Mono (layer k w op a b) := by
  intro g hg
  have hg' : g ∈ List.ofFn (fun i => (⟨op i, a i, b i⟩ : Gate)) := hg
  rw [List.mem_ofFn] at hg'
  obtain ⟨i, rfl⟩ := hg'
  exact h i

end Up

end PowerActivity
