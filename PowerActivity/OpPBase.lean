import PowerActivity.UpGen
import PowerActivity.UpP

/-!
# Верхняя оценка `P`-активности операторов: основа

Всё — в пространстве имён `PowerActivity.OpP`.

* `OrOnly C` — все элементы схемы `C` — элементы `∨`. У такой схемы `P = E` на каждом наборе
  (`P_eq_E`): элемент `∨` имеет единицу на входе тогда и только тогда, когда у него единица
  на выходе. Замкнутость относительно операций `UpBase` (`OrOnly.app`, `OrOnly.comp`,
  `OrOnly.sel`, `OrOnly.par2`, `OrOnly.parF`, …).
* Ярусы общей конструкции `UpGen` после минтермов состоят только из `∨`:
  `subC_or`, `orT_or`, `dec_or`, `stB_or`, `stC_or`, `stD_or`.
* `mtP n` — все минтермы `Q_t` и константа `0` (выход `2ⁿ`) на основе схемы Горяшко
  `Up.leaves` (вместо схемы минтермов `Up.mtC` из `minterms`): те же значения `Up.mtVal`
  (`mtP_eval`), `P ≤ 2n² + n + 2` на каждом наборе (`mtP_P`).
-/

namespace PowerActivity

open Finset Up

namespace OpP

variable {n : ℕ} {ι κ : Type}

/-! ## Схемы из элементов `∨` -/

/-- Все элементы схемы — `∨`. -/
def OrOnly (C : Circ n κ) : Prop := ∀ g ∈ C.gates, g.op = .or

/-- У схемы из элементов `∨` `P`-активность равна мощности на каждом наборе. -/
lemma P_eq_E {C : Circ n κ} (h : OrOnly C) (x : Fin n → Bool) : C.P x = C.E x := by
  unfold Circ.P Circ.E
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_range] at hi
  have hop := h _ (gate_mem C hi)
  rw [C.val_eq x hi]
  generalize C.gate i = g at hop ⊢
  rcases g with ⟨op, a, b⟩
  simp only at hop
  subst hop
  simp [Gate.srcs, Op.eval]

lemma OrOnly.app {C1 : Circ n ι} {k : ℕ} {feed : Fin k → ℕ} (hf : ∀ j, feed j < n + C1.s)
    {C2 : Circ k κ} (h1 : OrOnly C1) (h2 : OrOnly C2) :
    OrOnly (app C1 k feed hf C2) := by
  intro g hg
  rw [app_gates, List.mem_append] at hg
  rcases hg with hg | hg
  · exact h1 g hg
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact h2 g' hg'

lemma OrOnly.withOut {κ' : Type} {C : Circ n κ} {o : κ' → ℕ} (ho : ∀ c, o c < n + C.s)
    (h : OrOnly C) : OrOnly (withOut C o ho) := h

lemma OrOnly.reout {κ' : Type} {C : Circ n κ} (g : κ' → κ) (h : OrOnly C) :
    OrOnly (reout C g) := h

lemma OrOnly.compR {C1 : Circ n ι} {k : ℕ} {feed : Fin k → ℕ} (hf : ∀ j, feed j < n + C1.s)
    {C2 : Circ k κ} (h1 : OrOnly C1) (h2 : OrOnly C2) : OrOnly (compR C1 k feed hf C2) :=
  OrOnly.reout _ (OrOnly.app hf h1 h2)

lemma OrOnly.comp {k : ℕ} {C1 : Circ n ι} (f : Fin k → ι) {C2 : Circ k κ} (h1 : OrOnly C1)
    (h2 : OrOnly C2) : OrOnly (comp C1 f C2) := OrOnly.compR _ h1 h2

lemma OrOnly.sel {k : ℕ} {C : Circ k κ} (f : Fin k → Fin n) (h : OrOnly C) :
    OrOnly (sel C f) :=
  OrOnly.compR _ (by intro g hg; simp [empty] at hg) h

lemma OrOnly.par2 {C1 : Circ n ι} {C2 : Circ n κ} (h1 : OrOnly C1) (h2 : OrOnly C2) :
    OrOnly (par2 C1 C2) := OrOnly.app _ h1 h2

lemma OrOnly.parF : ∀ (q : ℕ) (C : Fin q → Circ n κ), (∀ i, OrOnly (C i)) → OrOnly (parF q C)
  | 0, _, _ => by
    intro g hg
    change g ∈ ([] : List Gate) at hg
    simp at hg
  | q + 1, C, h => OrOnly.reout _ (OrOnly.par2 (OrOnly.parF q _ fun i => h _) (h _))

lemma OrOnly.layer {k w : ℕ} {op : Fin w → Op} (a b : Fin w → Fin k) (h : ∀ i, op i = .or) :
    OrOnly (layer k w op a b) := by
  intro g hg
  have hg' : g ∈ List.ofFn (fun i => (⟨op i, a i, b i⟩ : Gate)) := hg
  rw [List.mem_ofFn] at hg'
  obtain ⟨i, rfl⟩ := hg'
  exact h i

/-! ## Ярусы общей конструкции состоят из `∨` -/

lemma orGate_or : OrOnly orGate := OrOnly.reout _ (OrOnly.layer _ _ (fun _ => rfl))

lemma orStep_or {k1 k2 k : ℕ} (h : k1 + k2 = k) {T1 : Circ k1 Unit} {T2 : Circ k2 Unit}
    (h1 : OrOnly T1) (h2 : OrOnly T2) : OrOnly (orStep h T1 T2) := by
  unfold orStep
  exact OrOnly.comp _ (OrOnly.par2 (OrOnly.sel _ h1) (OrOnly.sel _ h2)) orGate_or

/-- Дерево `∨` состоит из элементов `∨`. -/
lemma orT_or : ∀ (k : ℕ) (hk : 0 < k), OrOnly (orT k hk) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [orT]
    split_ifs with h
    · intro g hg; simp [leaf] at hg
    · exact orStep_or _ (ih _ (by omega) _) (ih _ (by omega) _)

/-- Схема индикаторов подмножеств группы состоит из элементов `∨`. -/
lemma subC_or (g : ℕ) : OrOnly (subC g) := by
  intro gt hg
  have hg' : gt ∈ List.ofFn (fun p : Fin (2 ^ g - 1) => subGate g p) := hg
  rw [List.mem_ofFn] at hg'
  obtain ⟨p, rfl⟩ := hg'
  rfl

lemma decStage1_or (r1 r2 r : ℕ) (h : r1 + r2 = r) : OrOnly (decStage1 r1 r2 r h) := by
  unfold decStage1
  exact OrOnly.par2 (OrOnly.parF _ _ fun _ => OrOnly.sel _ (orT_or _ _))
    (OrOnly.parF _ _ fun _ => OrOnly.sel _ (orT_or _ _))

lemma decStep_or {r1 r2 r : ℕ} (h : r1 + r2 = r) {D1 : Circ (2 ^ r1) (Fin r1)}
    {D2 : Circ (2 ^ r2) (Fin r2)} (h1 : OrOnly D1) (h2 : OrOnly D2) :
    OrOnly (decStep h D1 D2) := by
  unfold decStep decStage2
  exact OrOnly.reout _ (OrOnly.comp _ (decStage1_or _ _ _ h)
    (OrOnly.par2 (OrOnly.sel _ h1) (OrOnly.sel _ h2)))

/-- Рекурсивный декодер (`decoder`) состоит из элементов `∨`. -/
lemma dec_or : ∀ r, OrOnly (dec r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => intro g hg; simp [dec] at hg
    | 1, _ => intro g hg; simp [dec] at hg
    | r + 2, ih =>
      rw [dec]
      exact decStep_or _ (ih _ (by omega)) (ih _ (by omega))

lemma stB_or (n j : ℕ) (hj : j ≤ n) : OrOnly (stB n j hj) := by
  unfold stB
  exact OrOnly.parF _ _ fun _ => OrOnly.sel _ (subC_or _)

lemma stC_or (n m j r : ℕ) (F : (Fin n → Bool) → Fin m → Bool) : OrOnly (stC n m j r F) := by
  unfold stC
  exact OrOnly.parF _ _ fun _ => OrOnly.parF _ _ fun _ => OrOnly.sel _ (orT_or _ _)

lemma stD_or (m r : ℕ) (hr : 0 < r) : OrOnly (stD m r hr) := by
  unfold stD
  exact OrOnly.parF _ _ fun _ => OrOnly.reout _ (OrOnly.sel _ (dec_or _))

/-! ## Минтермы на основе схемы Горяшко -/

/-- Номер «старшим битом вперёд» через первый бит. -/
lemma bmask_succ' : ∀ (k : ℕ) (z : ℕ → Bool),
    bmask z (k + 1) = (if z 0 then 2 ^ k else 0) + bmask (fun i => z (i + 1)) k
  | 0, z => by cases h : z 0 <;> simp [bmask, h]
  | k + 1, z => by
    have ih := bmask_succ' k z
    have e1 : bmask z (k + 1 + 1) = 2 * bmask z (k + 1) + (if z (k + 1) then 1 else 0) := rfl
    have e2 : bmask (fun i => z (i + 1)) (k + 1) =
        2 * bmask (fun i => z (i + 1)) k + (if z (k + 1) then 1 else 0) := rfl
    rw [e1, e2, ih, pow_succ]
    split_ifs <;> ring

/-- Номера листов схемы Горяшко и номера минтермов схемы `Up.mtC` совпадают. -/
lemma idxH_eq_bmask : ∀ (k : ℕ) (z : ℕ → Bool), idxH z k = bmask z k
  | 0, _ => rfl
  | k + 1, z => by
    rw [bmask_succ', ← idxH_eq_bmask k]
    rfl

lemma zIdx_lt' (n : ℕ) (hn : 0 < n) : zIdx n hn < n + (leaves n hn).s := by
  have := zIdx_lt n hn
  have := leaves_s n hn
  omega

/-- Все минтермы `Q_t`, `t < 2ⁿ`, и константа `0` (выход `2ⁿ`) — листья схемы Горяшко. -/
def mtP (n : ℕ) (hn : 0 < n) : Circ n (Fin (2 ^ n + 1)) :=
  withOut (leaves n hn)
    (fun t => if h : (t : ℕ) < 2 ^ n then (leaves n hn).out ⟨t, h⟩ else zIdx n hn)
    (by
      intro t
      split_ifs
      · exact (leaves n hn).out_lt _
      · exact zIdx_lt' n hn)

/-- Значения выходов `mtP` — те же, что у схемы минтермов `Up.mtC`. -/
lemma mtP_eval (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) (t : Fin (2 ^ n + 1)) :
    (mtP n hn).eval x t = mtVal x t := by
  simp only [mtP, withOut_eval, mtVal]
  split_ifs with h
  · have := leaves_eval n hn x ⟨t, h⟩
    simp only [Circ.eval] at this
    rw [this, idxH_eq_bmask]
    rfl
  · exact leaves_zero n hn x

/-- `P`-активность схемы минтермов `mtP`: `P ≤ 2n² + n + 2` на каждом наборе. -/
lemma mtP_P (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) : (mtP n hn).P x ≤ 2 * n * n + n + 2 := by
  change (leaves n hn).P x ≤ _
  rw [leaves, comp_P, pBase_eval]
  have h1 := P_le_s (pBase n hn) x
  rw [pBase_s] at h1
  have h2 := (tC_spec n true (xb x)).2
  omega

end OpP

end PowerActivity
