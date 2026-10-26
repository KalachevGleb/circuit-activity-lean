import PowerActivity.ApxHyb

/-!
# Схема из оценки `cut-compress`

Для схемы `C` с одним выходом, радиуса `d` и списка назначений `zs` проводам разреза
строится схема `C'`:

* элементы `n, n+1, n+2` — `¬x₀`, константа `1 = x₀ ∨ ¬x₀`, константа `0 = x₀ ∧ ¬x₀`;
* для каждого `z ∈ zs` — блок ширины `W = |I_d| + 2|R_d| + 2`:
  копии внутренних элементов (`I_d` — элементы шара `B_d`, в исходном порядке; источники вне
  шара заменены константами, которые вычисляет внешняя часть по `z`), для каждого провода
  разреза проверка `s_e = z_e` и накопление конъюнкции `J_z`, элемент `J_z ∧ f_z`, элемент
  накопления дизъюнкции по блокам.

Итог (`build`): `C'(x) = 1 ⟺ (∃ z ∈ zs, Z_d(x) = z) ∧ f(x) = 1`, `L(C') = 3 + |zs| W`.
-/

namespace PowerActivity.Apx

open Finset

noncomputable section

/-! ## Перенумерация конечного множества натуральных чисел -/

/-- `t`-й по возрастанию элемент `s`. -/
def enumF (s : Finset ℕ) (t : ℕ) : ℕ :=
  if h : t < s.card then ((s.orderIsoOfFin rfl ⟨t, h⟩ : s) : ℕ) else 0

/-- Номер элемента `i ∈ s` в порядке возрастания. -/
def rankF (s : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i ∈ s then (((s.orderIsoOfFin rfl).symm ⟨i, h⟩ : Fin s.card) : ℕ) else 0

lemma rankF_lt {s : Finset ℕ} {i : ℕ} (h : i ∈ s) : rankF s i < s.card := by
  unfold rankF; rw [dif_pos h]; exact Fin.isLt _

lemma enumF_mem {s : Finset ℕ} {t : ℕ} (h : t < s.card) : enumF s t ∈ s := by
  unfold enumF; rw [dif_pos h]; exact Subtype.property _

lemma enumF_rankF {s : Finset ℕ} {i : ℕ} (h : i ∈ s) : enumF s (rankF s i) = i := by
  unfold enumF
  rw [dif_pos (rankF_lt h)]
  have e : (⟨rankF s i, rankF_lt h⟩ : Fin s.card) = (s.orderIsoOfFin rfl).symm ⟨i, h⟩ := by
    ext; simp [rankF, h]
  rw [e, OrderIso.apply_symm_apply]

lemma rankF_enumF {s : Finset ℕ} {t : ℕ} (h : t < s.card) : rankF s (enumF s t) = t := by
  unfold rankF
  rw [dif_pos (enumF_mem h)]
  have e : (⟨enumF s t, enumF_mem h⟩ : s) = s.orderIsoOfFin rfl ⟨t, h⟩ := by
    ext; simp [enumF, h]
  rw [e, OrderIso.symm_apply_apply]

lemma rankF_lt_rankF {s : Finset ℕ} {i j : ℕ} (hi : i ∈ s) (hj : j ∈ s) (hij : i < j) :
    rankF s i < rankF s j := by
  unfold rankF
  rw [dif_pos hi, dif_pos hj]
  have h : (⟨i, hi⟩ : s) < ⟨j, hj⟩ := hij
  exact Fin.lt_iff_val_lt_val.1 ((s.orderIsoOfFin rfl).symm.lt_iff_lt.2 h)

/-! ## Блок для одного значения `z` -/

section Build

variable {n : ℕ} (C : Circ n (Fin 1)) (d : ℕ)

/-- Число внутренних элементов `|I_d|`. -/
def mI : ℕ := (inner C d).card
/-- Число проводов разреза `|R_d|`. -/
def rR : ℕ := (C.cut d).card
/-- Ширина блока. -/
def Wd : ℕ := mI C d + 2 * rR C d + 2

lemma Wd_pos : 0 < Wd C d := by unfold Wd; omega

/-- `q`-й провод разреза. -/
def wire (q : ℕ) : ℕ × ℕ := (C.cut d).toList.getD q (0, 0)

lemma wire_mem {q : ℕ} (hq : q < rR C d) : wire C d q ∈ C.cut d := by
  unfold wire
  have hl : q < (C.cut d).toList.length := by rw [length_toList]; exact hq
  rw [List.getD_eq_getElem _ _ hl]
  exact mem_toList.1 (List.getElem_mem hl)

lemma exists_wire {e : ℕ × ℕ} (he : e ∈ C.cut d) : ∃ q, q < rR C d ∧ wire C d q = e := by
  obtain ⟨q, hq, hqe⟩ := List.mem_iff_getElem.1 (mem_toList.2 he)
  refine ⟨q, by rw [length_toList] at hq; exact hq, ?_⟩
  unfold wire
  rw [List.getD_eq_getElem _ _ hq, hqe]

/-- Опорный набор для вычисления внешних констант. -/
def x0 : Fin n → Bool := fun _ => false

/-- Номер сигнала-источника в блоке с началом `base`: вход, копия внутреннего элемента
или константа (`n + 1` — единица, `n + 2` — нуль) — значение внешней части по `zf`. -/
def smap (zf : ℕ × ℕ → Bool) (base a : ℕ) : ℕ :=
  if a ∈ C.fwdBall d then (if a < n then a else base + rankF (inner C d) (a - n))
  else if hyb C (C.fwdBall d) zf x0 a then n + 1 else n + 2

/-- Элемент блока с началом `base` на позиции `t`. -/
def bgate (zf : ℕ × ℕ → Bool) (base t : ℕ) : Gate :=
  if t < mI C d then
    ⟨(C.gate (enumF (inner C d) t)).op, smap C d zf base (C.gate (enumF (inner C d) t)).a,
      smap C d zf base (C.gate (enumF (inner C d) t)).b⟩
  else if t < mI C d + 2 * rR C d then
    if (t - mI C d) % 2 = 0 then
      ⟨if zf (wire C d ((t - mI C d) / 2)) then .and else .not,
        smap C d zf base (C.wsrc (wire C d ((t - mI C d) / 2))),
        smap C d zf base (C.wsrc (wire C d ((t - mI C d) / 2)))⟩
    else ⟨.and, if t - mI C d = 1 then n + 1 else base + t - 2, base + t - 1⟩
  else if t = mI C d + 2 * rR C d then
    ⟨.and, if rR C d = 0 then n + 1 else base + t - 1, smap C d zf base (C.out 0)⟩
  else ⟨.or, base - 1, base + t - 1⟩

lemma bgate_copy (zf : ℕ × ℕ → Bool) (base : ℕ) {t : ℕ} (ht : t < mI C d) :
    bgate C d zf base t = ⟨(C.gate (enumF (inner C d) t)).op,
      smap C d zf base (C.gate (enumF (inner C d) t)).a,
      smap C d zf base (C.gate (enumF (inner C d) t)).b⟩ := by
  unfold bgate; rw [if_pos ht]

lemma bgate_chk (zf : ℕ × ℕ → Bool) (base : ℕ) {q : ℕ} (hq : q < rR C d) :
    bgate C d zf base (mI C d + 2 * q) = ⟨if zf (wire C d q) then .and else .not,
      smap C d zf base (C.wsrc (wire C d q)), smap C d zf base (C.wsrc (wire C d q))⟩ := by
  unfold bgate
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  have : (mI C d + 2 * q - mI C d) / 2 = q := by omega
  rw [this]

lemma bgate_acc (zf : ℕ × ℕ → Bool) (base : ℕ) {q : ℕ} (hq : q < rR C d) :
    bgate C d zf base (mI C d + 2 * q + 1) =
      ⟨.and, if q = 0 then n + 1 else base + (mI C d + 2 * (q - 1) + 1),
        base + (mI C d + 2 * q)⟩ := by
  unfold bgate
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
  by_cases hq0 : q = 0
  · rw [if_pos (by omega), if_pos hq0]
    congr 1
  · rw [if_neg (by omega), if_neg hq0]
    congr 1
    omega

lemma bgate_res (zf : ℕ × ℕ → Bool) (base : ℕ) :
    bgate C d zf base (mI C d + 2 * rR C d) =
      ⟨.and, if rR C d = 0 then n + 1 else base + (mI C d + 2 * (rR C d - 1) + 1),
        smap C d zf base (C.out 0)⟩ := by
  unfold bgate
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  by_cases hr : rR C d = 0
  · rw [if_pos hr, if_pos hr]
  · rw [if_neg hr, if_neg hr]
    congr 1
    omega

lemma bgate_tot (zf : ℕ × ℕ → Bool) (base : ℕ) :
    bgate C d zf base (mI C d + 2 * rR C d + 1) =
      ⟨.or, base - 1, base + (mI C d + 2 * rR C d)⟩ := by
  unfold bgate
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1

/-! ### Правильность (ацикличность) блока -/

lemma smap_lt (zf : ℕ × ℕ → Bool) {base a k : ℕ} (hbase : n + 3 ≤ base)
    (h : a ∈ C.fwdBall d → n ≤ a → rankF (inner C d) (a - n) < k) :
    smap C d zf base a < base + k := by
  unfold smap
  split_ifs with h1 h2 h3
  · omega
  · have := h h1 (by omega); omega
  · omega
  · omega

lemma sub_mem_inner {a : ℕ} (haB : a ∈ C.fwdBall d) (han : n ≤ a) (has : a < n + C.s) :
    a - n ∈ inner C d :=
  (mem_inner C d).2 ⟨by omega, by rwa [show n + (a - n) = a by omega]⟩

lemma bgate_valid (zf : ℕ × ℕ → Bool) {base t : ℕ} (hbase : n + 3 ≤ base) (ht : t < Wd C d) :
    (bgate C d zf base t).a < base + t ∧ (bgate C d zf base t).b < base + t := by
  unfold Wd at ht
  by_cases h1 : t < mI C d
  · rw [bgate_copy C d zf base h1]
    have hiI : enumF (inner C d) t ∈ inner C d := enumF_mem h1
    have hi := (mem_inner C d).1 hiI
    have hrank : rankF (inner C d) (enumF (inner C d) t) = t := rankF_enumF h1
    have key : ∀ a, a < n + enumF (inner C d) t → a ∈ C.fwdBall d → n ≤ a →
        rankF (inner C d) (a - n) < t := by
      intro a ha haB han
      rw [← hrank]
      exact rankF_lt_rankF (sub_mem_inner C d haB han (by omega)) hiI (by omega)
    exact ⟨smap_lt C d zf hbase (key _ (C.gate_a_lt hi.1)),
      smap_lt C d zf hbase (key _ (C.gate_b_lt hi.1))⟩
  by_cases h2 : t < mI C d + 2 * rR C d
  · obtain ⟨q, hq⟩ : ∃ q, t = mI C d + 2 * q ∨ t = mI C d + 2 * q + 1 :=
      ⟨(t - mI C d) / 2, by omega⟩
    rcases hq with rfl | rfl
    · have hq' : q < rR C d := by omega
      rw [bgate_chk C d zf base hq']
      have hw := (mem_cut C d _).1 (wire_mem C d hq')
      have hlt := wsrc_lt C hw.1
      have hw1 := ((mem_wires C _).1 hw.1).1
      have key : C.wsrc (wire C d q) ∈ C.fwdBall d → n ≤ C.wsrc (wire C d q) →
          rankF (inner C d) (C.wsrc (wire C d q) - n) < mI C d + 2 * q := by
        intro haB han
        have := rankF_lt (sub_mem_inner C d haB han (by omega))
        unfold mI; omega
      exact ⟨smap_lt C d zf hbase key, smap_lt C d zf hbase key⟩
    · have hq' : q < rR C d := by omega
      rw [bgate_acc C d zf base hq']
      constructor
      · dsimp only; split_ifs <;> omega
      · dsimp only; omega
  by_cases h3 : t = mI C d + 2 * rR C d
  · subst h3
    rw [bgate_res C d zf base]
    constructor
    · dsimp only; split_ifs <;> omega
    · apply smap_lt C d zf hbase
      intro haB han
      have := rankF_lt (sub_mem_inner C d haB han (C.out_lt 0))
      unfold mI; omega
  · have h4 : t = mI C d + 2 * rR C d + 1 := by omega
    subst h4
    rw [bgate_tot C d zf base]
    constructor <;> dsimp only <;> omega

/-! ### Значения сигналов блока -/

/-- Предположения о значениях сигналов (`V`) в блоке с началом `base` для назначения `zf`. -/
structure BlockHyp (zf : ℕ × ℕ → Bool) (base : ℕ) (V : ℕ → Bool) (x : Fin n → Bool) :
    Prop where
  hx : ∀ j (h : j < n), V j = x ⟨j, h⟩
  h1 : V (n + 1) = true
  h0 : V (n + 2) = false
  hbase : n + 3 ≤ base
  hV : ∀ t, t < Wd C d → V (base + t) =
    Op.eval (bgate C d zf base t).op (V (bgate C d zf base t).a) (V (bgate C d zf base t).b)

variable {C d} {zf : ℕ × ℕ → Bool} {base : ℕ} {V : ℕ → Bool} {x : Fin n → Bool}

lemma smap_val (H : BlockHyp C d zf base V x) {i : ℕ} (hi : i ≤ C.s)
    (hcopy : ∀ i' ∈ inner C d, i' < i →
      V (base + rankF (inner C d) i') = hyb C (C.fwdBall d) zf x (n + i'))
    {a : ℕ} (ha : a < n + i) : V (smap C d zf base a) = hyb C (C.fwdBall d) zf x a := by
  unfold smap
  by_cases haB : a ∈ C.fwdBall d
  · rw [if_pos haB]
    by_cases han : a < n
    · rw [if_pos han, H.hx a han, hyb_lt _ _ _ _ han]
    · rw [if_neg han]
      have hmem := sub_mem_inner C d haB (by omega) (by omega)
      rw [hcopy _ hmem (by omega), show n + (a - n) = a by omega]
  · rw [if_neg haB]
    have hind := hyb_indep C d zf x0 x a haB
    rw [← hind]
    cases hh : hyb C (C.fwdBall d) zf x0 a
    · simp [H.h0]
    · simp [H.h1]

/-- Копии внутренних элементов вычисляют гибридные значения. -/
lemma copy_val (H : BlockHyp C d zf base V x) :
    ∀ i ∈ inner C d, V (base + rankF (inner C d) i) = hyb C (C.fwdBall d) zf x (n + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiI
    have hi := (mem_inner C d).1 hiI
    have ht : rankF (inner C d) i < mI C d := rankF_lt hiI
    have hc : ∀ i' ∈ inner C d, i' < i →
        V (base + rankF (inner C d) i') = hyb C (C.fwdBall d) zf x (n + i') :=
      fun i' h1 h2 => ih i' h2 h1
    rw [H.hV _ (by unfold Wd; omega), bgate_copy C d zf base ht, enumF_rankF hiI,
      hyb_gate _ _ _ _ hi.1]
    dsimp only
    simp only [hi.2, not_true_eq_false, and_false, ↓reduceIte]
    rw [smap_val H (le_of_lt hi.1) hc (C.gate_a_lt hi.1),
      smap_val H (le_of_lt hi.1) hc (C.gate_b_lt hi.1)]

lemma smap_val_all (H : BlockHyp C d zf base V x) {a : ℕ} (ha : a < n + C.s) :
    V (smap C d zf base a) = hyb C (C.fwdBall d) zf x a :=
  smap_val H le_rfl (fun i' hi' _ => copy_val H i' hi') ha

/-- Проверка провода разреза. -/
lemma chk_val (H : BlockHyp C d zf base V x) {q : ℕ} (hq : q < rR C d) :
    V (base + (mI C d + 2 * q)) = true ↔
      hyb C (C.fwdBall d) zf x (C.wsrc (wire C d q)) = zf (wire C d q) := by
  have hw := (mem_cut C d _).1 (wire_mem C d hq)
  have hlt := wsrc_lt C hw.1
  have hw1 := ((mem_wires C _).1 hw.1).1
  have hc := smap_val_all H (a := C.wsrc (wire C d q)) (by omega)
  rw [H.hV _ (by unfold Wd; omega), bgate_chk C d zf base hq]
  dsimp only
  rw [hc]
  cases hz : zf (wire C d q) <;>
    cases hh : hyb C (C.fwdBall d) zf x (C.wsrc (wire C d q)) <;> simp [Op.eval]

/-- Накопленная конъюнкция проверок. -/
lemma acc_val (H : BlockHyp C d zf base V x) :
    ∀ q, q < rR C d → (V (base + (mI C d + 2 * q + 1)) = true ↔
      ∀ q', q' ≤ q → hyb C (C.fwdBall d) zf x (C.wsrc (wire C d q')) = zf (wire C d q')) := by
  intro q
  induction q with
  | zero =>
    intro hq
    rw [H.hV _ (by unfold Wd; omega), bgate_acc C d zf base hq]
    dsimp only
    rw [if_pos rfl, H.h1]
    simp only [Op.eval, Bool.true_and]
    rw [chk_val H hq]
    constructor
    · intro h q' hq'
      have : q' = 0 := by omega
      subst this; exact h
    · intro h; exact h 0 le_rfl
  | succ q ih =>
    intro hq
    rw [H.hV _ (by unfold Wd; omega), bgate_acc C d zf base hq]
    dsimp only
    rw [if_neg (by omega), show q + 1 - 1 = q by omega]
    simp only [Op.eval, Bool.and_eq_true]
    rw [ih (by omega), chk_val H hq]
    constructor
    · rintro ⟨h1, h2⟩ q' hq'
      rcases Nat.lt_or_ge q' (q + 1) with h | h
      · exact h1 q' (by omega)
      · have : q' = q + 1 := by omega
        subst this; exact h2
    · intro h; exact ⟨fun q' hq' => h q' (by omega), h (q + 1) le_rfl⟩

/-- Элемент `J_z ∧ f_z`. -/
lemma res_val (H : BlockHyp C d zf base V x) :
    V (base + (mI C d + 2 * rR C d)) = true ↔
      (∀ e ∈ C.cut d, hyb C (C.fwdBall d) zf x (C.wsrc e) = zf e) ∧
        hyb C (C.fwdBall d) zf x (C.out 0) = true := by
  have hall : (∀ e ∈ C.cut d, hyb C (C.fwdBall d) zf x (C.wsrc e) = zf e) ↔
      ∀ q, q < rR C d → hyb C (C.fwdBall d) zf x (C.wsrc (wire C d q)) = zf (wire C d q) := by
    constructor
    · intro h q hq; exact h _ (wire_mem C d hq)
    · intro h e he
      obtain ⟨q, hq, rfl⟩ := exists_wire C d he
      exact h q hq
  rw [H.hV _ (by unfold Wd; omega), bgate_res C d zf base]
  dsimp only
  rw [smap_val_all H (C.out_lt 0), hall]
  by_cases hr : rR C d = 0
  · rw [if_pos hr, H.h1]
    simp only [Op.eval, Bool.true_and]
    constructor
    · intro h; exact ⟨fun q hq => by omega, h⟩
    · intro h; exact h.2
  · rw [if_neg hr]
    simp only [Op.eval, Bool.and_eq_true]
    rw [acc_val H (rR C d - 1) (by omega)]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun q hq => h1 q (by omega), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun q hq => h1 q (by omega), h2⟩

/-- Элемент накопления дизъюнкции. -/
lemma tot_val (H : BlockHyp C d zf base V x) :
    V (base + (mI C d + 2 * rR C d + 1)) =
      (V (base - 1) || V (base + (mI C d + 2 * rR C d))) := by
  rw [H.hV _ (by unfold Wd; omega), bgate_tot C d zf base]
  rfl

/-! ## Вся схема -/

variable (C d)

/-- Элементы построенной схемы. -/
def bigG (zs : List (ℕ × ℕ → Bool)) (i : ℕ) : Gate :=
  if i = 0 then ⟨.not, 0, 0⟩
  else if i = 1 then ⟨.or, 0, n⟩
  else if i = 2 then ⟨.and, 0, n⟩
  else bgate C d (zs.getD ((i - 3) / Wd C d) (fun _ => false))
    (n + 3 + (i - 3) / Wd C d * Wd C d) ((i - 3) % Wd C d)

lemma bigG_block (zs : List (ℕ × ℕ → Bool)) {k t : ℕ} (ht : t < Wd C d) :
    bigG C d zs (3 + k * Wd C d + t) =
      bgate C d (zs.getD k (fun _ => false)) (n + 3 + k * Wd C d) t := by
  unfold bigG
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hW := Wd_pos C d
  have e : 3 + k * Wd C d + t - 3 = t + k * Wd C d := by omega
  rw [e, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt ht, zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

lemma bigG_valid (hn : 1 ≤ n) (zs : List (ℕ × ℕ → Bool)) :
    ∀ i, i < 3 + zs.length * Wd C d →
      (bigG C d zs i).a < n + i ∧ (bigG C d zs i).b < n + i := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0; simp [bigG]; omega
  by_cases h1 : i = 1
  · subst h1; simp [bigG]
  by_cases h2 : i = 2
  · subst h2; simp [bigG]
  have hW := Wd_pos C d
  obtain ⟨k, t, ht, rfl⟩ : ∃ k t, t < Wd C d ∧ i = 3 + k * Wd C d + t := by
    refine ⟨(i - 3) / Wd C d, (i - 3) % Wd C d, Nat.mod_lt _ hW, ?_⟩
    have := Nat.div_add_mod (i - 3) (Wd C d)
    rw [mul_comm] at this
    omega
  rw [bigG_block C d zs ht]
  have := bgate_valid C d (zs.getD k (fun _ => false)) (base := n + 3 + k * Wd C d)
    (by omega) ht
  constructor <;> omega

/-- **Построение для `cut-compress`.** Для любого списка `zs` назначений проводам разреза `R_d`
есть схема из `3 + |zs| (|I_d| + 2|R_d| + 2)` элементов, выход которой равен
`[∃ z ∈ zs, Z_d(x) = z] ∧ f(x)`. -/
theorem build (hn : 1 ≤ n) (zs : List (ℕ × ℕ → Bool)) :
    ∃ C' : Circ n (Fin 1),
      C'.s = 3 + zs.length * ((inner C d).card + 2 * (C.cut d).card + 2) ∧
      ∀ x, (C'.eval x 0 = true ↔
        (∃ z ∈ zs, ∀ e ∈ C.cut d, C.sig x (C.wsrc e) = z e) ∧ C.sig x (C.out 0) = true) := by
  refine ⟨ofFnCirc n (3 + zs.length * Wd C d) (bigG C d zs) (bigG_valid C d hn zs)
    (n + 2 + zs.length * Wd C d) (by omega), ?_, ?_⟩
  · rw [ofFnCirc_s]; rfl
  intro x
  rw [ofFnCirc_eval]
  set V := sig n (List.ofFn fun k : Fin (3 + zs.length * Wd C d) => bigG C d zs k) x with hVdef
  have hval : ∀ i, i < 3 + zs.length * Wd C d →
      V (n + i) = Op.eval (bigG C d zs i).op (V (bigG C d zs i).a) (V (bigG C d zs i).b) :=
    fun i hi => sig_ofFn (bigG C d zs) (bigG_valid C d hn zs) x hi
  have hx : ∀ j (h : j < n), V j = x ⟨j, h⟩ := fun j h => sig_lt _ _ h
  have hx0 := hx 0 (by omega)
  have hVn : V n = !x ⟨0, by omega⟩ := by
    have := hval 0 (by omega)
    rw [add_zero] at this
    rw [this]
    simp [bigG, Op.eval, hx0]
  have hv1 : V (n + 1) = true := by
    rw [hval 1 (by omega)]
    simp [bigG, Op.eval, hx0, hVn]
  have hv0 : V (n + 2) = false := by
    rw [hval 2 (by omega)]
    simp [bigG, Op.eval, hx0, hVn]
  have hblock : ∀ k, k < zs.length →
      BlockHyp C d (zs.getD k (fun _ => false)) (n + 3 + k * Wd C d) V x := by
    intro k hk
    refine ⟨hx, hv1, hv0, by omega, ?_⟩
    intro t ht
    have h1 : (k + 1) * Wd C d ≤ zs.length * Wd C d := Nat.mul_le_mul_right _ hk
    rw [add_mul, one_mul] at h1
    have := hval (3 + k * Wd C d + t) (by omega)
    rw [bigG_block C d zs ht] at this
    rw [show n + 3 + k * Wd C d + t = n + (3 + k * Wd C d + t) by omega, this]
  have hWd : Wd C d = mI C d + 2 * rR C d + 2 := rfl
  have hchain : ∀ k, k ≤ zs.length → (V (n + 2 + k * Wd C d) = true ↔
      ∃ k', k' < k ∧ ((∀ e ∈ C.cut d, hyb C (C.fwdBall d) (zs.getD k' (fun _ => false)) x
          (C.wsrc e) = zs.getD k' (fun _ => false) e) ∧
        hyb C (C.fwdBall d) (zs.getD k' (fun _ => false)) x (C.out 0) = true)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [zero_mul, add_zero, hv0, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro k' hk'
      omega
    | succ k ih =>
      intro hk
      have H := hblock k (by omega)
      have e1 : n + 2 + (k + 1) * Wd C d =
          (n + 3 + k * Wd C d) + (mI C d + 2 * rR C d + 1) := by
        rw [add_mul, one_mul]; omega
      have e2 : n + 3 + k * Wd C d - 1 = n + 2 + k * Wd C d := by omega
      rw [e1, tot_val H, e2, Bool.or_eq_true, ih (by omega), res_val H]
      constructor
      · rintro (⟨k', hk', h⟩ | h)
        · exact ⟨k', by omega, h⟩
        · exact ⟨k, by omega, h⟩
      · rintro ⟨k', hk', h⟩
        rcases Nat.lt_or_ge k' k with h' | h'
        · exact Or.inl ⟨k', h', h⟩
        · have : k' = k := by omega
          subst this; exact Or.inr h
  rw [hchain zs.length le_rfl]
  constructor
  · rintro ⟨k', hk', hcheck, hout⟩
    have hz : zs.getD k' (fun _ => false) ∈ zs := by
      rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
    have hhs := hyb_eq_sig_of_check C d _ x hcheck
    refine ⟨⟨_, hz, fun e he => ?_⟩, ?_⟩
    · rw [← hhs]; exact hcheck e he
    · rw [← hhs]; exact hout
  · rintro ⟨⟨z, hz, hcut⟩, hout⟩
    obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hz
    refine ⟨k', hk', ?_⟩
    rw [List.getD_eq_getElem _ _ hk']
    have hhs := hyb_eq_sig_of_cut C d zs[k'] x (fun e he => (hcut e he).symm)
    refine ⟨fun e he => ?_, ?_⟩
    · rw [hhs]; exact hcut e he
    · rw [hhs]; exact hout

end Build

end

end PowerActivity.Apx
