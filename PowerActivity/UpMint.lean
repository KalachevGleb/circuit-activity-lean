import PowerActivity.UpTree

/-!
# Верхние оценки: минтермы (`minterms`) и индикаторы подмножеств группы (`group-upper`)

* `bmask`, `idx` — номер набора (старший бит — `x₁`); `mask` — маска (младший бит — первый),
  `testBit_mask`.
* `mtC n` — схема всех минтермов `Q_t = [idx x = t]`, `t < 2ⁿ`, и константы `0`
  (выход `2ⁿ`); мощность на каждом наборе `≤ 2n + 1` (`mtC_spec`, `minterms`).
* `subC g` — индикаторы всех подмножеств группы из `g` точек: выход `u < 2^g` — дизъюнкция
  входов `s` с `s`-м битом `u` (вход `g` — константа `0`); схема монотонна (`subC_eval`).
-/

namespace PowerActivity

open Finset

namespace Up

/-- Номер «старшим битом вперёд»: `bmask P (i+1) = 2 · bmask P i + [P i]`. -/
def bmask (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * bmask P i + (if P i then 1 else 0)

lemma bmask_lt (P : ℕ → Bool) : ∀ i, bmask P i < 2 ^ i
  | 0 => by simp [bmask]
  | i + 1 => by
    have := bmask_lt P i
    simp only [bmask, pow_succ]
    split_ifs <;> omega

lemma bmask_eq_iff (P Q : ℕ → Bool) : ∀ i, bmask P i = bmask Q i ↔ ∀ p < i, P p = Q p
  | 0 => by simp [bmask]
  | i + 1 => by
    simp only [bmask]
    constructor
    · intro h
      have h2 : bmask P i = bmask Q i ∧ P i = Q i := by
        cases hP : P i <;> cases hQ : Q i <;> simp [hP, hQ] at h ⊢ <;> omega
      intro p hp
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact (bmask_eq_iff P Q i).1 h2.1 p hp
      · exact h2.2
    · intro h
      rw [(bmask_eq_iff P Q i).2 (fun p hp => h p (by omega)), h i (by omega)]

/-- Биты набора как функция номера координаты. -/
def xb {n : ℕ} (x : Fin n → Bool) (p : ℕ) : Bool := if h : p < n then x ⟨p, h⟩ else false

/-- Номер набора `x ∈ {0,1}ⁿ`. -/
def idx {n : ℕ} (x : Fin n → Bool) : ℕ := bmask (xb x) n

lemma idx_lt {n : ℕ} (x : Fin n → Bool) : idx x < 2 ^ n := bmask_lt _ _

lemma idx_inj {n : ℕ} {x y : Fin n → Bool} (h : idx x = idx y) : x = y := by
  funext i
  have := (bmask_eq_iff _ _ n).1 h i i.2
  simpa [xb] using this

/-- Маска «младшим битом вперёд»: бит `p` маски равен `P p` при `p < i`. -/
def mask (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => mask P i + (if P i then 2 ^ i else 0)

lemma mask_lt (P : ℕ → Bool) : ∀ i, mask P i < 2 ^ i
  | 0 => by simp [mask]
  | i + 1 => by
    have := mask_lt P i
    simp only [mask, pow_succ]
    split_ifs <;> omega

lemma testBit_two_pow_add {L v s : ℕ} (hv : v < 2 ^ L) :
    (2 ^ L + v).testBit s = (v.testBit s || decide (s = L)) := by
  rcases lt_trichotomy s L with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [Nat.ne_of_lt h]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hv]; simp
  · have h1 : 2 ^ L + v < 2 ^ s := by
      calc 2 ^ L + v < 2 ^ L + 2 ^ L := by omega
        _ = 2 ^ (L + 1) := by ring
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h
    have h2 : v < 2 ^ s := lt_of_le_of_lt (Nat.le_add_left _ _) h1
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [Nat.ne_of_gt h]

lemma testBit_mask (P : ℕ → Bool) : ∀ i p, (mask P i).testBit p = (decide (p < i) && P p)
  | 0, p => by simp [mask]
  | i + 1, p => by
    have ih := testBit_mask P i p
    have hl := mask_lt P i
    simp only [mask]
    split_ifs with hP
    · rw [Nat.add_comm, testBit_two_pow_add hl, ih]
      by_cases hp : p = i
      · subst hp; simp [hP]
      · by_cases hpi : p < i
        · simp [hpi, hp, show p < i + 1 by omega]
        · simp [hpi, hp, show ¬ p < i + 1 by omega]
    · rw [Nat.add_zero, ih]
      by_cases hp : p = i
      · subst hp; simp [hP]
      · by_cases hpi : p < i
        · simp [hpi, show p < i + 1 by omega]
        · simp [hpi, show ¬ p < i + 1 by omega]

variable {n : ℕ} {ι κ : Type}

/-! ## Все минтермы (`minterms`) -/

/-- Инверторы `¬x_i`. -/
def invC (n : ℕ) : Circ n (Fin n) := layer n n (fun _ => .not) id id

lemma invC_s (n : ℕ) : (invC n).s = n := layer_s _ _ _ _ _

lemma invC_eval (x : Fin n → Bool) (i : Fin n) : (invC n).eval x i = !x i := by
  simp [invC, layer_eval, Op.eval]

/-- Константы: `x₀ ∨ ¬x₀` и `x₀ ∧ ¬x₀`. -/
def constC : Circ 2 (Fin 2) := layer 2 2 ![.or, .and] (fun _ => 0) (fun _ => 1)

lemma constC_eval (y : Fin 2 → Bool) (hy : y 1 = !y 0) :
    constC.eval y 0 = true ∧ constC.eval y 1 = false := by
  simp only [constC, layer_eval]
  rw [hy]
  cases y 0 <;> simp [Op.eval]

lemma constC_E (y : Fin 2 → Bool) (hy : y 1 = !y 0) : constC.E y ≤ 1 := by
  have h := constC_eval y hy
  rw [constC, layer_E]
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' : a = 0 := by
    by_contra hne
    have : a = 1 := by fin_cases a <;> simp_all
    subst this
    have := h.2
    simp only [constC, layer_eval] at this
    rw [this] at ha
    exact Bool.false_ne_true ha
  have hb' : b = 0 := by
    by_contra hne
    have : b = 1 := by fin_cases b <;> simp_all
    subst this
    have := h.2
    simp only [constC, layer_eval] at this
    rw [this] at hb
    exact Bool.false_ne_true hb
  rw [ha', hb']

/-- Инверторы и константы. Выходы: `inl 0` — константа `1`, `inr (inl i)` — `¬x_i`,
`inr (inr ())` — константа `0`. -/
def baseC (n : ℕ) (hn : 0 < n) : Circ n (Fin 1 ⊕ (Fin n ⊕ Unit)) :=
  reout (app (invC n) 2 ![0, n] (by intro j; rw [invC_s]; fin_cases j <;> simp <;> omega) constC)
    (Sum.elim (fun _ => Sum.inr 0) (Sum.elim Sum.inl (fun _ => Sum.inr 1)))

lemma baseC_in (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (fun j : Fin 2 => (invC n).sig x (![0, n] j)) 1 = !(fun j : Fin 2 => (invC n).sig x (![0, n] j)) 0 := by
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [sig_of_lt _ _ hn]
  have := invC_eval x ⟨0, hn⟩
  simp only [Circ.eval, invC, layer] at this ⊢
  simpa using this

lemma baseC_spec (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (baseC n hn).eval x (Sum.inl 0) = true ∧
    (∀ i, (baseC n hn).eval x (Sum.inr (Sum.inl i)) = !x i) ∧
    (baseC n hn).eval x (Sum.inr (Sum.inr ())) = false ∧
    (baseC n hn).E x ≤ n + 1 := by
  have hc := constC_eval (fun j : Fin 2 => (invC n).sig x (![0, n] j)) (baseC_in n hn x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [baseC, reout_eval, Sum.elim_inl]
    rw [app_eval_inr]; exact hc.1
  · intro i
    simp only [baseC, reout_eval, Sum.elim_inr, Sum.elim_inl]
    rw [app_eval_inl, invC_eval]
  · simp only [baseC, reout_eval, Sum.elim_inr]
    rw [app_eval_inr]; exact hc.2
  · simp only [baseC, reout_E]
    rw [E_app]
    have h1 := E_le_s (invC n) x
    rw [invC_s] at h1
    have h2 := constC_E (fun j : Fin 2 => (invC n).sig x (![0, n] j)) (baseC_in n hn x)
    omega

/-- Слой префиксов длины `i+1`: элемент `t'` равен
`[префикс длины i = ⌊t'/2⌋] ∧ (x_i при нечётном t', иначе ¬x_i)`.
Входы: `t < 2^i` — индикаторы префиксов длины `i`; `2^i` — `x_i`; `2^i+1` — `¬x_i`. -/
def preLayer (i : ℕ) : Circ (2 ^ i + 2) (Fin (2 ^ (i + 1))) :=
  layer (2 ^ i + 2) (2 ^ (i + 1)) (fun _ => .and)
    (fun t => ⟨t / 2, by
      have := t.2; have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
      omega⟩)
    (fun t => if t.val % 2 = 1 then ⟨2 ^ i, by omega⟩ else ⟨2 ^ i + 1, by omega⟩)

lemma preLayer_eval (i : ℕ) (P : ℕ → Bool) (y : Fin (2 ^ i + 2) → Bool)
    (hy1 : ∀ t : Fin (2 ^ i + 2), (t : ℕ) < 2 ^ i → y t = decide (bmask P i = t))
    (hy2 : y ⟨2 ^ i, by omega⟩ = P i) (hy3 : y ⟨2 ^ i + 1, by omega⟩ = !P i)
    (t : Fin (2 ^ (i + 1))) :
    (preLayer i).eval y t = decide (bmask P (i + 1) = t) := by
  have ht : (t : ℕ) < 2 * 2 ^ i := by
    have := t.2; have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
    omega
  simp only [preLayer, layer_eval, Op.eval]
  rw [hy1 _ (by simp; omega)]
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  have hb : bmask P (i + 1) = 2 * bmask P i + (if P i then 1 else 0) := rfl
  rw [hb]
  by_cases h1 : (t : ℕ) % 2 = 1
  · simp only [h1, ↓reduceIte]
    rw [hy2]
    by_cases hP : P i = true
    · rw [hP]
      simp only [↓reduceIte, and_true]
      constructor <;> intro h <;> omega
    · rw [Bool.not_eq_true] at hP
      rw [hP]
      simp only [Bool.false_eq_true, ↓reduceIte, and_false, false_iff]
      omega
  · simp only [h1, ↓reduceIte]
    rw [hy3]
    by_cases hP : P i = true
    · rw [hP]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, and_false, false_iff]
      omega
    · rw [Bool.not_eq_true] at hP
      rw [hP]
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, and_true]
      constructor <;> intro h <;> omega

lemma preLayer_E (i : ℕ) (P : ℕ → Bool) (y : Fin (2 ^ i + 2) → Bool)
    (hy1 : ∀ t : Fin (2 ^ i + 2), (t : ℕ) < 2 ^ i → y t = decide (bmask P i = t))
    (hy2 : y ⟨2 ^ i, by omega⟩ = P i) (hy3 : y ⟨2 ^ i + 1, by omega⟩ = !P i) :
    (preLayer i).E y ≤ 1 := by
  have he := preLayer_eval i P y hy1 hy2 hy3
  rw [preLayer, layer_E]
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' := he a
  have hb' := he b
  simp only [preLayer, layer_eval] at ha' hb'
  rw [ha'] at ha
  rw [hb'] at hb
  simp only [decide_eq_true_eq] at ha hb
  ext; omega

/-- Номер литерала для слоя `i` (при `i < n` — сама переменная `x_i`). -/
def lit (n i : ℕ) : ℕ := min i (n - 1)

lemma lit_lt {n : ℕ} (hn : 0 < n) (i : ℕ) : lit n i < n := by unfold lit; omega

/-- Подача входов слоя префиксов от схемы префиксов длины `i`. -/
def preFeed {n i : ℕ} (hn : 0 < n) (C : Circ n (Fin (2 ^ i) ⊕ (Fin n ⊕ Unit))) :
    Fin (2 ^ i + 2) → ℕ :=
  fun j => if h : (j : ℕ) < 2 ^ i then C.out (Sum.inl ⟨j, h⟩)
    else if (j : ℕ) = 2 ^ i then lit n i else C.out (Sum.inr (Sum.inl ⟨lit n i, lit_lt hn i⟩))

lemma preFeed_lt {n i : ℕ} (hn : 0 < n) (C : Circ n (Fin (2 ^ i) ⊕ (Fin n ⊕ Unit)))
    (j : Fin (2 ^ i + 2)) : preFeed hn C j < n + C.s := by
  unfold preFeed
  split_ifs
  · exact C.out_lt _
  · have := lit_lt hn i; omega
  · exact C.out_lt _

/-- Индикаторы всех префиксов длины `i` (выходы `inl t`), инверторы и константа `0`. -/
def preC (n : ℕ) (hn : 0 < n) : (i : ℕ) → Circ n (Fin (2 ^ i) ⊕ (Fin n ⊕ Unit))
  | 0 => reout (baseC n hn) (Sum.elim (fun _ => Sum.inl 0) Sum.inr)
  | i + 1 => reout (app (preC n hn i) (2 ^ i + 2) (preFeed hn (preC n hn i)) (preFeed_lt hn _)
      (preLayer i)) (Sum.elim Sum.inr (fun a => Sum.inl (Sum.inr a)))

lemma preC_spec (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    ∀ i, i ≤ n →
      (∀ t : Fin (2 ^ i), (preC n hn i).eval x (Sum.inl t) = decide (bmask (xb x) i = t)) ∧
      (∀ j, (preC n hn i).eval x (Sum.inr (Sum.inl j)) = !x j) ∧
      (preC n hn i).eval x (Sum.inr (Sum.inr ())) = false ∧
      (preC n hn i).E x ≤ n + 1 + i
  | 0, _ => by
    obtain ⟨b1, b2, b3, b4⟩ := baseC_spec n hn x
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t
      have ht : (t : ℕ) = 0 := by have := t.2; simp at this; omega
      simp only [preC, reout_eval, Sum.elim_inl]
      rw [b1, ht]; simp [bmask]
    · intro j; simp only [preC, reout_eval, Sum.elim_inr]; exact b2 j
    · simp only [preC, reout_eval, Sum.elim_inr]; exact b3
    · simp only [preC, reout_E]; omega
  | i + 1, hi => by
    obtain ⟨a1, a2, a3, a4⟩ := preC_spec n hn x i (by omega)
    have hlit : lit n i = i := by unfold lit; omega
    have hy1 : ∀ t : Fin (2 ^ i + 2), (t : ℕ) < 2 ^ i →
        (preC n hn i).sig x (preFeed hn (preC n hn i) t) = decide (bmask (xb x) i = t) := by
      intro t ht
      simp only [preFeed, ht]
      exact a1 ⟨t, ht⟩
    have hy2 : (preC n hn i).sig x (preFeed hn (preC n hn i) ⟨2 ^ i, by omega⟩) = xb x i := by
      simp only [preFeed, lt_irrefl]
      simp only [↓reduceDIte, ↓reduceIte]
      rw [hlit, sig_of_lt _ _ (by omega)]
      simp [xb, show i < n by omega]
    have hy3 : (preC n hn i).sig x (preFeed hn (preC n hn i) ⟨2 ^ i + 1, by omega⟩) =
        !xb x i := by
      simp only [preFeed, show ¬ (2 ^ i + 1 < 2 ^ i) by omega,
        show ¬ (2 ^ i + 1 = 2 ^ i) by omega]
      simp only [↓reduceDIte, ↓reduceIte]
      have := a2 ⟨lit n i, lit_lt hn i⟩
      simp only [Circ.eval] at this
      rw [this]
      simp [xb, hlit, show i < n by omega]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t
      simp only [preC, reout_eval, Sum.elim_inl]
      rw [app_eval_inr]
      exact preLayer_eval i (xb x) _ hy1 hy2 hy3 t
    · intro j
      simp only [preC, reout_eval, Sum.elim_inr]
      rw [app_eval_inl]; exact a2 j
    · simp only [preC, reout_eval, Sum.elim_inr]
      rw [app_eval_inl]; exact a3
    · simp only [preC, reout_E]
      rw [E_app]
      have := preLayer_E i (xb x) _ hy1 hy2 hy3
      omega

/-- `minterms`: все минтермы `Q_t`, `t < 2ⁿ`, и константа `0` (выход `2ⁿ`). -/
def mtC (n : ℕ) (hn : 0 < n) : Circ n (Fin (2 ^ n + 1)) :=
  reout (preC n hn n) fun t =>
    if h : (t : ℕ) < 2 ^ n then Sum.inl ⟨t, h⟩ else Sum.inr (Sum.inr ())

/-- Значения выходов схемы минтермов. -/
def mtVal {n : ℕ} (x : Fin n → Bool) (t : Fin (2 ^ n + 1)) : Bool :=
  if (t : ℕ) < 2 ^ n then decide (idx x = t) else false

/-- `minterms`: значения и мощность `≤ 2n + 1` на каждом наборе. -/
theorem mtC_spec (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (∀ t, (mtC n hn).eval x t = mtVal x t) ∧ (mtC n hn).E x ≤ 2 * n + 1 := by
  obtain ⟨a1, -, a3, a4⟩ := preC_spec n hn x n le_rfl
  refine ⟨?_, ?_⟩
  · intro t
    simp only [mtC, reout_eval, mtVal]
    split_ifs with h
    · rw [a1]; rfl
    · exact a3
  · simp only [mtC, reout_E]; omega

/-! ## Индикаторы подмножеств группы -/

/-- Элемент `p` схемы подмножеств: `S_{p+1} = S_{p+1-2^L} ∨ Q_L`, `L = ⌊log (p+1)⌋`. -/
def subGate (g p : ℕ) : Gate := ⟨.or, g + (p + 1 - 2 ^ Nat.log 2 (p + 1)), Nat.log 2 (p + 1)⟩

/-- Индикаторы подмножеств группы из `g` точек: входы `s < g` — минтермы точек группы,
вход `g` — константа `0`; выход `u < 2^g` — сигнал `g + u`. -/
def subC (g : ℕ) : Circ (g + 1) (Fin (2 ^ g)) where
  gates := List.ofFn fun p : Fin (2 ^ g - 1) => subGate g p
  valid := by
    intro i h
    simp only [List.getElem_ofFn, subGate]
    have h1 : 1 ≤ 2 ^ Nat.log 2 (i + 1) := Nat.one_le_two_pow
    have h2 : Nat.log 2 (i + 1) < i + 1 := Nat.log_lt_self 2 (by omega)
    constructor <;> omega
  out := fun u => g + u
  out_lt := by
    intro u
    have := u.2
    have : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    simp only [List.length_ofFn]
    omega

lemma subC_s (g : ℕ) : (subC g).s = 2 ^ g - 1 := by simp [subC, Circ.s]

lemma subC_gate (g : ℕ) {p : ℕ} (hp : p < 2 ^ g - 1) : (subC g).gate p = subGate g p := by
  simp [Circ.gate, subC, List.getD_eq_getElem?_getD, hp]

lemma subC_mono (g : ℕ) : Mono (subC g) := by
  intro gt hg
  have hg' : gt ∈ List.ofFn (fun p : Fin (2 ^ g - 1) => subGate g p) := hg
  rw [List.mem_ofFn] at hg'
  obtain ⟨p, rfl⟩ := hg'
  simp [subGate]

lemma testBit_log {u s : ℕ} (hu : 0 < u) :
    u.testBit s = ((u - 2 ^ Nat.log 2 u).testBit s || decide (s = Nat.log 2 u)) := by
  have h1 : 2 ^ Nat.log 2 u ≤ u := Nat.pow_log_le_self 2 (by omega)
  have h2 : u < 2 ^ (Nat.log 2 u + 1) := Nat.lt_pow_succ_log_self (by norm_num) u
  have h3 : u - 2 ^ Nat.log 2 u < 2 ^ Nat.log 2 u := by rw [pow_succ] at h2; omega
  conv_lhs => rw [show u = 2 ^ Nat.log 2 u + (u - 2 ^ Nat.log 2 u) by omega]
  exact testBit_two_pow_add h3

lemma subC_sig (g : ℕ) (y : Fin (g + 1) → Bool) (hy : y (Fin.last g) = false) :
    ∀ u, u < 2 ^ g → (subC g).sig y (g + u) =
      decide (∃ s : Fin g, u.testBit s = true ∧ y s.castSucc = true) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · simp only [Nat.add_zero]
      rw [sig_of_lt _ _ (by omega : g < g + 1)]
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_and, exists_false, decide_false]
      exact hy
    · have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
      have hp : u - 1 < 2 ^ g - 1 := by omega
      have e := (subC g).val_eq y (i := u - 1) (by rw [subC_s]; exact hp)
      unfold Circ.val at e
      rw [show g + u = g + 1 + (u - 1) by omega, e, subC_gate g hp]
      simp only [subGate, show u - 1 + 1 = u by omega, Op.eval]
      have hL : Nat.log 2 u < g := Nat.log_lt_of_lt_pow (by omega) hu
      have hle : 2 ^ Nat.log 2 u ≤ u := Nat.pow_log_le_self 2 (by omega)
      have hpos' : 0 < 2 ^ Nat.log 2 u := Nat.two_pow_pos _
      rw [ih _ (by omega) (by omega), sig_of_lt _ _ (by omega)]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨s, hs1, hs2⟩ | h)
        · exact ⟨s, by rw [testBit_log hpos]; simp [hs1], hs2⟩
        · exact ⟨⟨Nat.log 2 u, hL⟩, by rw [testBit_log hpos]; simp, h⟩
      · rintro ⟨s, hs1, hs2⟩
        rw [testBit_log hpos] at hs1
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hs1
        rcases hs1 with hs1 | hs1
        · exact Or.inl ⟨s, hs1, hs2⟩
        · right
          have e : (⟨Nat.log 2 u, by omega⟩ : Fin (g + 1)) = s.castSucc :=
            Fin.ext (by simp [hs1])
          rw [e]; exact hs2

/-- Индикаторы подмножеств: значения выходов. -/
theorem subC_eval (g : ℕ) (y : Fin (g + 1) → Bool) (hy : y (Fin.last g) = false)
    (u : Fin (2 ^ g)) :
    (subC g).eval y u = decide (∃ s : Fin g, (u : ℕ).testBit s = true ∧ y s.castSucc = true) :=
  subC_sig g y hy u u.2

end Up

end PowerActivity
