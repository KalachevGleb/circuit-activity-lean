import PowerActivity.ActWires

/-!
# Исходящие степени не больше 3 (`fanout`): `U(Σ*,x) ≤ 3U(Σ,x)`

Конструкция (хватило бы цепочки из `r − 2` копий; цепочка из `r` копий проще и даёт ту же
оценку). Для каждого сигнала `v` с `r` исходящими проводами строится цепочка из `r` копий
`c₁ = v ∧ v`, `c_{k+1} = c_k ∧ c_k`, и `k`-й прежний провод из `v` берётся от `c_k`.
У `v` остаётся `≤ 2` исходящих провода, у каждой копии — `≤ 3`; проводов становится ровно `3r`,
все со значением `v`, поэтому `U(Σ*,x) = 3U(Σ,x)` (равенство).
Копия для провода ставится непосредственно перед элементом, которому этот провод ведёт
(топологический порядок другой, чем «копии сразу после источника», граф тот же).

Схема строится однопроходным «компилятором» `run` по списку элементов: состояние хранит новый
список элементов `gs`, новый номер `pos j` каждого старого сигнала и конец цепочки копий
`last j`. Корректность (`Inv`) доказывается индукцией по списку: совпадение сигналов,
ацикличность, `cnt ≤ 3` (число проводов из сигнала), `cnt (last j) ≤ 1`, инъективность `last`,
`U' = 3U`.
-/

namespace PowerActivity

open Finset

namespace Act

namespace Fan

variable {n : ℕ}

/-- Ацикличность списка элементов (как `Circ.valid`). -/
def ValidL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (h : i < gs.length), gs[i].a < n + i ∧ gs[i].b < n + i

lemma validL_nil : ValidL n [] := fun i h => absurd h (by simp)

lemma validL_snoc {gs : List Gate} {c : Gate} :
    ValidL n (gs ++ [c]) ↔ ValidL n gs ∧ c.a < n + gs.length ∧ c.b < n + gs.length := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at this
    · have := h gs.length (by simp)
      simpa using this
  · rintro ⟨h1, ha, hb⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i gs.length with h | h
    · rw [List.getElem_append_left h]; exact h1 i h
    · have : i = gs.length := by omega
      subst this; simp [ha, hb]

lemma validL_mem {gs : List Gate} (h : ValidL n gs) {g : Gate} (hg : g ∈ gs) :
    g.a < n + gs.length ∧ g.b < n + gs.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have := h i hi; omega

lemma srcs_lt {g : Gate} {m : ℕ} (ha : g.a < m) (hb : g.b < m) : ∀ j ∈ g.srcs, j < m := by
  unfold Gate.srcs; split <;> simp_all

lemma sig_snoc (gs : List Gate) (c : Gate) (x : Fin n → Bool) (ha : c.a < n + gs.length)
    (hb : c.b < n + gs.length) :
    sig n (gs ++ [c]) x (n + gs.length) = Op.eval c.op (sig n gs x c.a) (sig n gs x c.b) := by
  have h := sig_gate (gs ++ [c]) x (i := gs.length) (by simp) (by simpa using ha)
    (by simpa using hb)
  rw [h]
  simp only [List.getElem_concat_length]
  rw [sig_append gs [c] x _ ha, sig_append gs [c] x _ hb]

/-- Число проводов, выходящих из сигнала `p`. -/
def cnt (gs : List Gate) (p : ℕ) : ℕ :=
  (gs.map fun g => g.srcs.countP (fun k => decide (k = p))).sum

/-- `U` для списка элементов. -/
def Ul (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : ℕ :=
  (gs.map fun g => g.srcs.countP (sig n gs x)).sum

lemma cnt_nil (p : ℕ) : cnt [] p = 0 := rfl

lemma cnt_snoc (gs : List Gate) (c : Gate) (p : ℕ) :
    cnt (gs ++ [c]) p = cnt gs p + c.srcs.countP (fun k => decide (k = p)) := by
  simp [cnt]

lemma cnt_eq_zero {gs : List Gate} (h : ValidL n gs) {p : ℕ} (hp : n + gs.length ≤ p) :
    cnt gs p = 0 := by
  unfold cnt
  apply List.sum_eq_zero
  intro m hm
  simp only [List.mem_map] at hm
  obtain ⟨g, hg, rfl⟩ := hm
  rw [List.countP_eq_zero]
  intro j hj
  have := srcs_lt (validL_mem h hg).1 (validL_mem h hg).2 j hj
  simp only [decide_eq_true_eq]
  omega

lemma Ul_nil (x : Fin n → Bool) : Ul n [] x = 0 := rfl

lemma Ul_snoc {gs : List Gate} (h : ValidL n gs) (c : Gate) (ha : c.a < n + gs.length)
    (hb : c.b < n + gs.length) (x : Fin n → Bool) :
    Ul n (gs ++ [c]) x = Ul n gs x + c.srcs.countP (sig n gs x) := by
  unfold Ul
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro g hg
    apply List.countP_congr
    intro j hj
    have hj' := srcs_lt (validL_mem h hg).1 (validL_mem h hg).2 j hj
    rw [sig_append gs [c] x j hj']
  · apply List.countP_congr
    intro j hj
    rw [sig_append gs [c] x j (srcs_lt ha hb j hj)]

lemma srcs_bin {g : Gate} (h : g.op ≠ .not) : g.srcs = [g.a, g.b] := by
  unfold Gate.srcs; cases hg : g.op <;> simp_all

lemma srcs_not {g : Gate} (h : g.op = .not) : g.srcs = [g.a] := by
  unfold Gate.srcs; simp [h]

lemma countP_pair (a b : ℕ) (q : ℕ → Bool) :
    [a, b].countP q = (if q a = true then 1 else 0) + (if q b = true then 1 else 0) := by
  simp [List.countP_cons]; omega

lemma countP_single (a : ℕ) (q : ℕ → Bool) :
    [a].countP q = (if q a = true then 1 else 0) := by
  simp [List.countP_cons]

/-- `U` схемы — это `Ul` её списка элементов. -/
lemma sum_range_getD (l : List Gate) (f : Gate → ℕ) :
    ∑ i ∈ range l.length, f (l.getD i default) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih]; ring

/-! ## Компилятор -/

/-- Состояние: новый список элементов, концы цепочек копий, новые номера старых сигналов,
число обработанных старых элементов. -/
structure St where
  gs : List Gate
  last : ℕ → ℕ
  pos : ℕ → ℕ
  k : ℕ

def init : St := ⟨[], id, id, 0⟩

/-- Шаг для элемента `¬a`: копия `c = last(a) ∧ last(a)`, затем `¬c`. -/
def stepNot (n : ℕ) (st : St) (g : Gate) : St :=
  ⟨st.gs ++ [⟨.and, st.last g.a, st.last g.a⟩] ++
      [⟨.not, n + st.gs.length, n + st.gs.length⟩],
    Function.update (Function.update st.last g.a (n + st.gs.length)) (n + st.k)
      (n + st.gs.length + 1),
    Function.update st.pos (n + st.k) (n + st.gs.length + 1),
    st.k + 1⟩

/-- Шаг для элемента `a ∘ b` (`∘ ∈ {∧, ∨}`): копии `c₁ = last(a) ∧ last(a)`,
`c₂ = last'(b) ∧ last'(b)` (`last'` уже учитывает `c₁`, что важно при `a = b`), затем `c₁ ∘ c₂`. -/
def stepBin (n : ℕ) (st : St) (g : Gate) : St :=
  ⟨st.gs ++ [⟨.and, st.last g.a, st.last g.a⟩] ++
      [⟨.and, Function.update st.last g.a (n + st.gs.length) g.b,
        Function.update st.last g.a (n + st.gs.length) g.b⟩] ++
      [⟨g.op, n + st.gs.length, n + st.gs.length + 1⟩],
    Function.update (Function.update (Function.update st.last g.a (n + st.gs.length)) g.b
      (n + st.gs.length + 1)) (n + st.k) (n + st.gs.length + 2),
    Function.update st.pos (n + st.k) (n + st.gs.length + 2),
    st.k + 1⟩

def step (n : ℕ) (st : St) (g : Gate) : St :=
  if g.op = .not then stepNot n st g else stepBin n st g

def run (n : ℕ) (gs : List Gate) : St := gs.foldl (step n) init

/-- Инвариант компилятора после обработки списка `old`. -/
structure Inv (n : ℕ) (old : List Gate) (st : St) : Prop where
  hk : st.k = old.length
  valid : ValidL n st.gs
  pos_lt : ∀ j < n + old.length, st.pos j < n + st.gs.length
  last_lt : ∀ j < n + old.length, st.last j < n + st.gs.length
  sig_pos : ∀ x j, j < n + old.length → sig n st.gs x (st.pos j) = sig n old x j
  sig_last : ∀ x j, j < n + old.length → sig n st.gs x (st.last j) = sig n old x j
  inj : ∀ j j', j < n + old.length → j' < n + old.length → st.last j = st.last j' → j = j'
  cnt_le : ∀ p, cnt st.gs p ≤ 3
  cnt_last : ∀ j < n + old.length, cnt st.gs (st.last j) ≤ 1
  ul : ∀ x, Ul n st.gs x = 3 * Ul n old x

lemma inv_init : Inv n [] init where
  hk := rfl
  valid := validL_nil
  pos_lt := fun j hj => hj
  last_lt := fun j hj => hj
  sig_pos := fun _ _ _ => rfl
  sig_last := fun _ _ _ => rfl
  inj := fun _ _ _ _ h => h
  cnt_le := fun _ => by simp [init, cnt_nil]
  cnt_last := fun _ _ => by simp [init, cnt_nil]
  ul := fun _ => rfl

lemma inv_stepNot {old : List Gate} {st : St} {g : Gate} (hvo : ValidL n old)
    (I : Inv n old st) (hop : g.op = .not)
    (ha : g.a < n + old.length) (hb : g.b < n + old.length) :
    Inv n (old ++ [g]) (stepNot n st g) := by
  obtain ⟨hk, hv, hpos, hlast, hsp, hsl, hinj, hcnt, hcl, hul⟩ := I
  unfold stepNot
  rw [hk]
  set N := n + old.length with hN
  set L := n + st.gs.length with hL
  set A := st.last g.a with hA
  have hAL : A < L := hlast _ ha
  have hlen1 : (st.gs ++ [(⟨.and, A, A⟩ : Gate)]).length = st.gs.length + 1 := by simp
  have hv1 : ValidL n (st.gs ++ [⟨.and, A, A⟩]) := validL_snoc.2 ⟨hv, hAL, hAL⟩
  have hv2 : ValidL n (st.gs ++ [⟨.and, A, A⟩] ++ [⟨.not, L, L⟩]) :=
    validL_snoc.2 ⟨hv1, by dsimp only; rw [hlen1]; omega, by dsimp only; rw [hlen1]; omega⟩
  have hlen2 : (st.gs ++ [(⟨.and, A, A⟩ : Gate)] ++ [(⟨.not, L, L⟩ : Gate)]).length =
      st.gs.length + 2 := by simp
  -- сигналы
  have hS1L : ∀ x, sig n (st.gs ++ [⟨.and, A, A⟩]) x L = sig n old x g.a := by
    intro x
    rw [sig_snoc st.gs _ x hAL hAL]
    simp only [Op.eval, Bool.and_self]
    exact hsl x _ ha
  have hS2 : ∀ x j, j < L →
      sig n (st.gs ++ [⟨.and, A, A⟩] ++ [⟨.not, L, L⟩]) x j = sig n st.gs x j := by
    intro x j hj
    rw [sig_append _ [_] x j (by rw [hlen1]; omega), sig_append _ [_] x j hj]
  have hS2L : ∀ x, sig n (st.gs ++ [⟨.and, A, A⟩] ++ [⟨.not, L, L⟩]) x L = sig n old x g.a := by
    intro x
    rw [sig_append _ [_] x L (by rw [hlen1]; omega), hS1L]
  have hS2L1 : ∀ x, sig n (st.gs ++ [⟨.and, A, A⟩] ++ [⟨.not, L, L⟩]) x (L + 1) =
      !sig n old x g.a := by
    intro x
    have e : L + 1 = n + (st.gs ++ [(⟨.and, A, A⟩ : Gate)]).length := by rw [hlen1]; omega
    rw [e, sig_snoc (st.gs ++ [(⟨.and, A, A⟩ : Gate)]) ⟨.not, L, L⟩ x
      (by dsimp only; rw [hlen1]; omega)
      (by dsimp only; rw [hlen1]; omega)]
    simp only [Op.eval]
    rw [hS1L]
  have hold : ∀ x j, j < N → sig n (old ++ [g]) x j = sig n old x j :=
    fun x j hj => sig_append old [g] x j hj
  have holdN : ∀ x, sig n (old ++ [g]) x N = !sig n old x g.a := by
    intro x; rw [hN, sig_snoc old g x ha hb, hop]; rfl
  -- число проводов из сигнала
  have hc2 : ∀ p, cnt (st.gs ++ [⟨.and, A, A⟩] ++ [⟨.not, L, L⟩]) p =
      cnt st.gs p + (if A = p then 2 else 0) + (if L = p then 1 else 0) := by
    intro p
    rw [cnt_snoc, cnt_snoc]
    simp only [Gate.srcs, countP_pair, countP_single, decide_eq_true_eq]
    split_ifs <;> omega
  have hcL : cnt st.gs L = 0 := cnt_eq_zero hv le_rfl
  have hcL1 : cnt st.gs (L + 1) = 0 := cnt_eq_zero hv (by omega)
  have hlen : (old ++ [g]).length = old.length + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · simp
  · exact hv2
  · intro j hj
    rw [hlen] at hj
    rw [hlen2, Function.update_apply]
    split_ifs with h1
    · omega
    · have := hpos j (by omega); omega
  · intro j hj
    rw [hlen] at hj
    rw [hlen2, Function.update_apply, Function.update_apply]
    split_ifs with h1 h2
    · omega
    · omega
    · have := hlast j (by omega); omega
  · intro x j hj
    rw [hlen] at hj
    rw [Function.update_apply]
    split_ifs with h1
    · rw [hS2L1, h1, holdN]
    · have hj' : j < N := by omega
      rw [hS2 x _ (hpos j hj'), hsp x j hj', hold x j hj']
  · intro x j hj
    rw [hlen] at hj
    rw [Function.update_apply, Function.update_apply]
    split_ifs with h1 h2
    · rw [hS2L1, h1, holdN]
    · rw [hS2L, h2, hold x g.a ha]
    · have hj' : j < N := by omega
      rw [hS2 x _ (hlast j hj'), hsl x j hj', hold x j hj']
  · intro j j' hj hj' heq
    rw [hlen] at hj hj'
    simp only [Function.update_apply] at heq
    split_ifs at heq with h1 h2 h3 h4 h5 h6 h7 h8 <;>
      first
      | omega
      | exact hinj j j' (by omega) (by omega) heq
      | (have h9 := hlast j' (by omega); omega)
      | (have h9 := hlast j (by omega); omega)
  · intro p
    rw [hc2]
    by_cases hpA : A = p
    · subst hpA
      have h1 : cnt st.gs A ≤ 1 := hcl g.a ha
      rw [ite_eq_left rfl, ite_eq_right (by omega)]; omega
    · by_cases hpL : L = p
      · subst hpL; rw [ite_eq_right hpA, ite_eq_left rfl]; omega
      · rw [ite_eq_right hpA, ite_eq_right hpL]; have := hcnt p; omega
  · intro j hj
    rw [hlen] at hj
    by_cases h1 : j = N
    · have hl : Function.update (Function.update st.last g.a L) N (L + 1) j = L + 1 := by
        rw [h1, Function.update_self]
      rw [hl, hc2, ite_eq_right (by omega), ite_eq_right (by omega), hcL1]; omega
    · by_cases h2 : j = g.a
      · have hl : Function.update (Function.update st.last g.a L) N (L + 1) j = L := by
          rw [Function.update_of_ne h1, h2, Function.update_self]
        rw [hl, hc2, ite_eq_right (by omega), ite_eq_left rfl, hcL]
      · have hj' : j < N := by omega
        have hl : Function.update (Function.update st.last g.a L) N (L + 1) j = st.last j := by
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
        have e1 : ¬ A = st.last j := fun e => h2 (hinj g.a j ha hj' e).symm
        have e2 : ¬ L = st.last j := by have := hlast j hj'; omega
        rw [hl, hc2, ite_eq_right e1, ite_eq_right e2]
        have := hcl j hj'; omega
  · intro x
    rw [Ul_snoc hv1 ⟨.not, L, L⟩ (by dsimp only; rw [hlen1]; omega)
        (by dsimp only; rw [hlen1]; omega),
      Ul_snoc hv _ hAL hAL, Ul_snoc hvo g ha hb, srcs_not hop, hul]
    simp only [Gate.srcs, countP_pair, countP_single]
    rw [hS1L, hsl x _ ha]
    split_ifs <;> omega

lemma inv_stepBin {old : List Gate} {st : St} {g : Gate} (hvo : ValidL n old)
    (I : Inv n old st) (hop : g.op ≠ .not)
    (ha : g.a < n + old.length) (hb : g.b < n + old.length) :
    Inv n (old ++ [g]) (stepBin n st g) := by
  obtain ⟨hk, hv, hpos, hlast, hsp, hsl, hinj, hcnt, hcl, hul⟩ := I
  unfold stepBin
  rw [hk]
  set N := n + old.length with hN
  set L := n + st.gs.length with hL
  set A := st.last g.a with hA
  set B := Function.update st.last g.a L g.b with hB
  have hAL : A < L := hlast _ ha
  have hBv : B = if g.b = g.a then L else st.last g.b := by rw [hB, Function.update_apply]
  have hBL : B ≤ L := by
    rw [hBv]; split_ifs
    · exact le_rfl
    · exact (hlast _ hb).le
  set c1 : Gate := ⟨.and, A, A⟩ with hc1
  set c2 : Gate := ⟨.and, B, B⟩ with hc2
  set c3 : Gate := ⟨g.op, L, L + 1⟩ with hc3
  have hl1 : (st.gs ++ [c1]).length = st.gs.length + 1 := by simp
  have hl2 : (st.gs ++ [c1] ++ [c2]).length = st.gs.length + 2 := by simp
  have hl3 : (st.gs ++ [c1] ++ [c2] ++ [c3]).length = st.gs.length + 3 := by simp
  have hv1 : ValidL n (st.gs ++ [c1]) := validL_snoc.2 ⟨hv, hAL, hAL⟩
  have hv2 : ValidL n (st.gs ++ [c1] ++ [c2]) :=
    validL_snoc.2 ⟨hv1, by rw [hl1]; show B < _; omega, by rw [hl1]; show B < _; omega⟩
  have hv3 : ValidL n (st.gs ++ [c1] ++ [c2] ++ [c3]) :=
    validL_snoc.2 ⟨hv2, by rw [hl2]; show L < _; omega, by rw [hl2]; show L + 1 < _; omega⟩
  have hs1 : c1.srcs = [A, A] := rfl
  have hs2 : c2.srcs = [B, B] := rfl
  have hs3 : c3.srcs = [L, L + 1] := srcs_bin (g := c3) hop
  -- сигналы
  have hS1L : ∀ x, sig n (st.gs ++ [c1]) x L = sig n old x g.a := by
    intro x
    rw [sig_snoc st.gs c1 x hAL hAL]
    simp only [hc1, Op.eval, Bool.and_self]
    exact hsl x _ ha
  have hS1 : ∀ x j, j < L → sig n (st.gs ++ [c1]) x j = sig n st.gs x j :=
    fun x j hj => sig_append _ [c1] x j hj
  have hS1B : ∀ x, sig n (st.gs ++ [c1]) x B = sig n old x g.b := by
    intro x
    rw [hBv]; split_ifs with h
    · rw [hS1L, h]
    · rw [hS1 x _ (hlast _ hb), hsl x _ hb]
  have hS2 : ∀ x j, j < L + 1 → sig n (st.gs ++ [c1] ++ [c2]) x j = sig n (st.gs ++ [c1]) x j :=
    fun x j hj => sig_append _ [c2] x j (by rw [hl1]; omega)
  have hS2L1 : ∀ x, sig n (st.gs ++ [c1] ++ [c2]) x (L + 1) = sig n old x g.b := by
    intro x
    have e : L + 1 = n + (st.gs ++ [c1]).length := by rw [hl1]; omega
    rw [e, sig_snoc (st.gs ++ [c1]) c2 x (by rw [hl1]; show B < _; omega)
      (by rw [hl1]; show B < _; omega)]
    simp only [hc2, Op.eval, Bool.and_self]
    exact hS1B x
  have hS3 : ∀ x j, j < L + 2 →
      sig n (st.gs ++ [c1] ++ [c2] ++ [c3]) x j = sig n (st.gs ++ [c1] ++ [c2]) x j :=
    fun x j hj => sig_append _ [c3] x j (by rw [hl2]; omega)
  have hS3L2 : ∀ x, sig n (st.gs ++ [c1] ++ [c2] ++ [c3]) x (L + 2) =
      Op.eval g.op (sig n old x g.a) (sig n old x g.b) := by
    intro x
    have e : L + 2 = n + (st.gs ++ [c1] ++ [c2]).length := by rw [hl2]; omega
    rw [e, sig_snoc (st.gs ++ [c1] ++ [c2]) c3 x (by rw [hl2]; show L < _; omega)
      (by rw [hl2]; show L + 1 < _; omega)]
    show Op.eval g.op (sig n (st.gs ++ [c1] ++ [c2]) x L)
      (sig n (st.gs ++ [c1] ++ [c2]) x (L + 1)) = _
    rw [hS2 x L (by omega), hS1L, hS2L1]
  have hS3L : ∀ x, sig n (st.gs ++ [c1] ++ [c2] ++ [c3]) x L = sig n old x g.a := by
    intro x; rw [hS3 x L (by omega), hS2 x L (by omega), hS1L]
  have hS3L1 : ∀ x, sig n (st.gs ++ [c1] ++ [c2] ++ [c3]) x (L + 1) = sig n old x g.b := by
    intro x; rw [hS3 x _ (by omega), hS2L1]
  have hS3lt : ∀ x j, j < L → sig n (st.gs ++ [c1] ++ [c2] ++ [c3]) x j = sig n st.gs x j := by
    intro x j hj; rw [hS3 x j (by omega), hS2 x j (by omega), hS1 x j hj]
  have hold : ∀ x j, j < N → sig n (old ++ [g]) x j = sig n old x j :=
    fun x j hj => sig_append old [g] x j hj
  have holdN : ∀ x, sig n (old ++ [g]) x N = Op.eval g.op (sig n old x g.a) (sig n old x g.b) :=
    fun x => sig_snoc old g x ha hb
  -- число проводов из сигнала
  have hcn : ∀ p, cnt (st.gs ++ [c1] ++ [c2] ++ [c3]) p =
      cnt st.gs p + (if A = p then 2 else 0) + (if B = p then 2 else 0) +
        (if L = p then 1 else 0) + (if L + 1 = p then 1 else 0) := by
    intro p
    rw [cnt_snoc, cnt_snoc, cnt_snoc, hs1, hs2, hs3]
    simp only [countP_pair, decide_eq_true_eq]
    split_ifs <;> omega
  have hcL : cnt st.gs L = 0 := cnt_eq_zero hv le_rfl
  have hcL1 : cnt st.gs (L + 1) = 0 := cnt_eq_zero hv (by omega)
  have hcL2 : cnt st.gs (L + 2) = 0 := cnt_eq_zero hv (by omega)
  have hA1 : cnt st.gs A ≤ 1 := hcl g.a ha
  have hlen : (old ++ [g]).length = old.length + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · simp
  · exact hv3
  · intro j hj
    rw [hlen] at hj
    rw [hl3, Function.update_apply]
    split_ifs with h1
    · omega
    · have := hpos j (by omega); omega
  · intro j hj
    rw [hlen] at hj
    rw [hl3, Function.update_apply, Function.update_apply, Function.update_apply]
    split_ifs with h1 h2 h3
    · omega
    · omega
    · omega
    · have := hlast j (by omega); omega
  · intro x j hj
    rw [hlen] at hj
    rw [Function.update_apply]
    split_ifs with h1
    · rw [hS3L2, h1, holdN]
    · have hj' : j < N := by omega
      rw [hS3lt x _ (hpos j hj'), hsp x j hj', hold x j hj']
  · intro x j hj
    rw [hlen] at hj
    rw [Function.update_apply, Function.update_apply, Function.update_apply]
    split_ifs with h1 h2 h3
    · rw [hS3L2, h1, holdN]
    · rw [hS3L1, h2, hold x g.b hb]
    · rw [hS3L, h3, hold x g.a ha]
    · have hj' : j < N := by omega
      rw [hS3lt x _ (hlast j hj'), hsl x j hj', hold x j hj']
  · intro j j' hj hj' heq
    rw [hlen] at hj hj'
    simp only [Function.update_apply] at heq
    split_ifs at heq <;>
      first
      | omega
      | exact hinj j j' (by omega) (by omega) heq
      | (have h9 := hlast j' (by omega); omega)
      | (have h9 := hlast j (by omega); omega)
  · intro p
    rw [hcn]
    by_cases hba : g.b = g.a
    · have hBL' : B = L := by rw [hBv, ite_eq_left hba]
      rw [hBL']
      by_cases hpA : A = p
      · subst hpA
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; omega
      · by_cases hpL : L = p
        · subst hpL
          rw [ite_eq_right hpA, ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (by omega), hcL]
        · by_cases hpL1 : L + 1 = p
          · subst hpL1
            rw [ite_eq_right hpA, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, hcL1]
            all_goals omega
          · rw [ite_eq_right hpA, ite_eq_right hpL, ite_eq_right hpL, ite_eq_right hpL1]; have := hcnt p; omega
    · have hBl : B = st.last g.b := by rw [hBv, ite_eq_right hba]
      have hAB : A ≠ B := by
        rw [hBl]; intro e; exact hba (hinj _ _ ha hb e).symm
      have hB1 : cnt st.gs B ≤ 1 := by rw [hBl]; exact hcl g.b hb
      have hBL2 : B < L := by rw [hBl]; exact hlast _ hb
      by_cases hpA : A = p
      · subst hpA
        rw [ite_eq_left rfl, ite_eq_right (Ne.symm hAB), ite_eq_right (by omega), ite_eq_right (by omega)]; omega
      · by_cases hpB : B = p
        · subst hpB
          rw [ite_eq_right hAB, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]; omega
        · by_cases hpL : L = p
          · subst hpL
            rw [ite_eq_right hpA, ite_eq_right hpB, ite_eq_left rfl, ite_eq_right (by omega), hcL]
            all_goals omega
          · by_cases hpL1 : L + 1 = p
            · subst hpL1
              rw [ite_eq_right hpA, ite_eq_right hpB, ite_eq_right (by omega), ite_eq_left rfl, hcL1]
              all_goals omega
            · rw [ite_eq_right hpA, ite_eq_right hpB, ite_eq_right hpL, ite_eq_right hpL1]; have := hcnt p; omega
  · intro j hj
    rw [hlen] at hj
    by_cases h1 : j = N
    · have hl : Function.update (Function.update (Function.update st.last g.a L) g.b (L + 1)) N
          (L + 2) j = L + 2 := by
        rw [h1, Function.update_self]
      rw [hl, hcn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        hcL2]
      all_goals omega
    · by_cases h2 : j = g.b
      · have hl : Function.update (Function.update (Function.update st.last g.a L) g.b (L + 1)) N
            (L + 2) j = L + 1 := by
          rw [Function.update_of_ne h1, h2, Function.update_self]
        rw [hl, hcn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, hcL1]
      · by_cases h3 : j = g.a
        · have hl : Function.update (Function.update (Function.update st.last g.a L) g.b (L + 1))
              N (L + 2) j = L := by
            rw [Function.update_of_ne h1, Function.update_of_ne h2, h3, Function.update_self]
          have hba : ¬ g.b = g.a := fun e => h2 (h3.trans e.symm)
          have hBl : B = st.last g.b := by rw [hBv, ite_eq_right hba]
          have hBL2 : B < L := by rw [hBl]; exact hlast _ hb
          rw [hl, hcn, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega), hcL]
        · have hj' : j < N := by omega
          have hl : Function.update (Function.update (Function.update st.last g.a L) g.b (L + 1))
              N (L + 2) j = st.last j := by
            rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
          have hjL := hlast j hj'
          have e1 : ¬ A = st.last j := fun e => h3 (hinj g.a j ha hj' e).symm
          have e2 : ¬ B = st.last j := by
            rw [hBv]; split_ifs with hba
            · omega
            · exact fun e => h2 (hinj g.b j hb hj' e).symm
          rw [hl, hcn, ite_eq_right e1, ite_eq_right e2, ite_eq_right (by omega), ite_eq_right (by omega)]
          have := hcl j hj'; omega
  · intro x
    rw [Ul_snoc hv2 c3 (by rw [hl2]; show L < _; omega) (by rw [hl2]; show L + 1 < _; omega),
      Ul_snoc hv1 c2 (by rw [hl1]; show B < _; omega) (by rw [hl1]; show B < _; omega),
      Ul_snoc hv c1 hAL hAL, Ul_snoc hvo g ha hb, srcs_bin hop, hs1, hs2, hs3, hul]
    simp only [countP_pair]
    rw [hsl x _ ha, hS1B, hS2 x L (by omega), hS1L, hS2L1]
    split_ifs <;> omega

lemma run_snoc (gs : List Gate) (g : Gate) : run n (gs ++ [g]) = step n (run n gs) g := by
  simp [run, List.foldl_append]

/-- Инвариант после обработки всего (правильного) списка. -/
theorem inv_run : ∀ gs : List Gate, ValidL n gs → Inv n gs (run n gs) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _; exact inv_init
  | append_singleton gs g ih =>
    intro hv
    obtain ⟨hv', ha, hb⟩ := validL_snoc.1 hv
    rw [run_snoc]
    unfold step
    split_ifs with hop
    · exact inv_stepNot hv' (ih hv') hop ha hb
    · exact inv_stepBin hv' (ih hv') hop ha hb

end Fan

open Fan

variable {n : ℕ} {κ : Type}

/-- Схема `Σ*` из `fanout`. -/
def fanout (C : Circ n κ) : Circ n κ where
  gates := (run n C.gates).gs
  valid := (inv_run C.gates C.valid).valid
  out := fun k => (run n C.gates).pos (C.out k)
  out_lt := fun k => (inv_run C.gates C.valid).pos_lt _ (C.out_lt k)

theorem fanout_eval (C : Circ n κ) (x : Fin n → Bool) : (fanout C).eval x = C.eval x := by
  funext k
  exact (inv_run C.gates C.valid).sig_pos x _ (C.out_lt k)

lemma U_eq_Ul (C : Circ n κ) (x : Fin n → Bool) : C.U x = Ul n C.gates x :=
  sum_range_getD C.gates (fun g => g.srcs.countP (sig n C.gates x))

theorem fanout_U (C : Circ n κ) (x : Fin n → Bool) : (fanout C).U x = 3 * C.U x := by
  rw [U_eq_Ul, U_eq_Ul]
  exact (inv_run C.gates C.valid).ul x

theorem fanout_outdeg (C : Circ n κ) (j : ℕ) : (fanout C).outdeg j ≤ 3 := by
  rw [outdeg_eq]
  have e : ∑ i ∈ range (fanout C).s, ((fanout C).gate i).srcs.countP (fun k => decide (k = j)) =
      cnt (run n C.gates).gs j :=
    sum_range_getD (run n C.gates).gs (fun g => g.srcs.countP (fun k => decide (k = j)))
  rw [e]
  exact (inv_run C.gates C.valid).cnt_le j

/-- **`fanout`.** Для любой схемы `Σ` есть схема `Σ*` того же оператора с исходящими степенями
всех сигналов (включая входы) `≤ 3` и `U(Σ*,x) ≤ 3U(Σ,x)` (у нашей конструкции — равенство). -/
theorem fanout_bound (C : Circ n κ) :
    ∃ C' : Circ n κ, (∀ x, C'.eval x = C.eval x) ∧ (∀ j, C'.outdeg j ≤ 3) ∧
      ∀ x, C'.U x ≤ 3 * C.U x :=
  ⟨fanout C, fanout_eval C, fanout_outdeg C, fun x => (fanout_U C x).le⟩

theorem fanout_Uav (C : Circ n κ) : (fanout C).Uav = 3 * C.Uav := by
  unfold Circ.Uav avgM
  simp_rw [fanout_U]
  push_cast
  rw [← Finset.mul_sum]; ring

end Act

end PowerActivity
