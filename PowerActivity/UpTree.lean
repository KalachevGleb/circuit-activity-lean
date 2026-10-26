import PowerActivity.UpBase

/-!
# Верхние оценки: сбалансированное дерево ИЛИ и рекурсивный декодер (`decoder`)

* `Up.orT k` — дерево ИЛИ над `k ≥ 1` входами: значение — дизъюнкция входов; схема монотонна;
  если на входах не более одной единицы, то `E ≤ ⌈log k⌉` и `P ≤ ⌈log k⌉` (`orT_spec`).
* `Up.dec r` — рекурсивный декодер блока: схема с `2^r` входами, вход `v` — индикатор `D_v`;
  на унитарном наборе (единица ровно во входе `t`) выход `p` равен `p`-му биту `t`,
  а мощность не больше `r ⌈log r⌉` (`dec_spec`).
-/

namespace PowerActivity

open Finset

namespace Up

variable {n : ℕ} {ι κ : Type}

/-! ## Дерево ИЛИ -/

/-- Свойства дерева ИЛИ с глубиной `d`. -/
structure OrSpec {k : ℕ} (T : Circ k Unit) (d : ℕ) : Prop where
  eval : ∀ y, T.eval y () = decide (∃ i, y i = true)
  mono : Mono T
  one : ∀ y, AtMostOne y → T.E y ≤ d ∧ T.P y ≤ d

lemma OrSpec.mono_d {k : ℕ} {T : Circ k Unit} {d d' : ℕ} (h : OrSpec T d) (hd : d ≤ d') :
    OrSpec T d' :=
  ⟨h.eval, h.mono, fun y hy => ⟨(h.one y hy).1.trans hd, (h.one y hy).2.trans hd⟩⟩

/-- Лист: схема без элементов, выход — вход `0`. -/
def leaf (k : ℕ) (hk : 0 < k) : Circ k Unit := ⟨[], by simp, fun _ => 0, by simpa using hk⟩

lemma leaf_spec : OrSpec (leaf 1 one_pos) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    simp only [Circ.eval, leaf]
    rw [sig_of_lt _ _ (by norm_num : 0 < 1)]
    have e : (⟨0, by norm_num⟩ : Fin 1) = 0 := rfl
    rw [e]
    by_cases h : y 0 = true
    · simp only [h, true_eq_decide_iff]; exact ⟨0, h⟩
    · simp only [Bool.not_eq_true] at h
      simp only [h, false_eq_decide_iff, not_exists, Bool.not_eq_true]
      intro i; rwa [Subsingleton.elim i 0]
  · intro g hg; simp [leaf] at hg
  · intro y _
    constructor
    · exact (E_le_s _ _).trans (by simp [leaf, Circ.s])
    · exact (P_le_s _ _).trans (by simp [leaf, Circ.s])

/-- Элемент ИЛИ с двумя входами. -/
def orGate : Circ 2 Unit := reout (layer 2 1 (fun _ => .or) (fun _ => 0) (fun _ => 1)) (fun _ => 0)

lemma orGate_eval (y : Fin 2 → Bool) : orGate.eval y () = (y 0 || y 1) := by
  simp [orGate, layer_eval, Op.eval]

lemma orGate_mono : Mono orGate := Mono.reout _ (Mono.layer _ _ (by intro; simp))

lemma orGate_s : orGate.s = 1 := by simp [orGate, layer_s]

/-- Шаг дерева: два поддерева (на первых `k1` и последних `k2` входах) и корень. -/
def orStep {k1 k2 k : ℕ} (h : k1 + k2 = k) (T1 : Circ k1 Unit) (T2 : Circ k2 Unit) :
    Circ k Unit :=
  comp (par2 (sel T1 fun i => ⟨i, by omega⟩) (sel T2 fun i => ⟨k1 + i, by omega⟩))
    ![Sum.inl (), Sum.inr ()] orGate

lemma orStep_spec {k1 k2 k : ℕ} (h : k1 + k2 = k) {T1 : Circ k1 Unit} {T2 : Circ k2 Unit}
    {d1 d2 : ℕ} (h1 : OrSpec T1 d1) (h2 : OrSpec T2 d2) :
    OrSpec (orStep h T1 T2) (max d1 d2 + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    unfold orStep
    rw [comp_eval, orGate_eval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, par2_eval_inl, par2_eval_inr, sel_eval,
      h1.eval, h2.eval]
    rw [← Bool.decide_or, decide_eq_decide]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩) <;> exact ⟨_, hi⟩
    · rintro ⟨i, hi⟩
      by_cases hik : (i : ℕ) < k1
      · left; exact ⟨⟨i, hik⟩, by simpa using hi⟩
      · right
        refine ⟨⟨i - k1, by omega⟩, ?_⟩
        convert hi using 2
        ext; simp; omega
  · exact Mono.comp _ (Mono.par2 (Mono.sel _ h1.mono) (Mono.sel _ h2.mono)) orGate_mono
  · intro y hy
    have inj1 : Function.Injective (fun i : Fin k1 => (⟨i, by omega⟩ : Fin k)) := by
      intro a b hab; ext; simpa using hab
    have inj2 : Function.Injective (fun i : Fin k2 => (⟨k1 + i, by omega⟩ : Fin k)) := by
      intro a b hab; ext; simpa using hab
    have hE := comp_E_le (par2 (sel T1 fun i => ⟨i, by omega⟩) (sel T2 fun i => ⟨k1 + i, by omega⟩))
      ![Sum.inl (), Sum.inr ()] orGate y
    have hP := comp_P_le (par2 (sel T1 fun i => ⟨i, by omega⟩) (sel T2 fun i => ⟨k1 + i, by omega⟩))
      ![Sum.inl (), Sum.inr ()] orGate y
    rw [par2_E, sel_E, sel_E, orGate_s] at hE
    rw [par2_P, sel_P, sel_P, orGate_s] at hP
    unfold orStep
    by_cases hz : ∀ i : Fin k1, y ⟨i, by omega⟩ = false
    · have a1 := h1.mono.E_zero hz
      have a2 := h1.mono.P_zero hz
      have b := h2.one _ (hy.comp inj2)
      constructor <;> omega
    · push Not at hz
      obtain ⟨i0, hi0⟩ := hz
      simp only [ne_eq, Bool.not_eq_false] at hi0
      have hz2 : ∀ i : Fin k2, y ⟨k1 + i, by omega⟩ = false := by
        intro i
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        have := hy _ _ hi0 hc
        simp [Fin.ext_iff] at this
        omega
      have a1 := h2.mono.E_zero hz2
      have a2 := h2.mono.P_zero hz2
      have b := h1.one _ (hy.comp inj1)
      constructor <;> omega

/-- Сбалансированное дерево ИЛИ над `k ≥ 1` входами. -/
def orT (k : ℕ) (hk : 0 < k) : Circ k Unit :=
  if h : k = 1 then leaf k hk
  else orStep (k1 := k / 2) (k2 := k - k / 2) (by omega) (orT (k / 2) (by omega))
    (orT (k - k / 2) (by omega))
termination_by k
decreasing_by all_goals omega

lemma orT_spec : ∀ (k : ℕ) (hk : 0 < k), OrSpec (orT k hk) (Nat.clog 2 k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [orT]
    split_ifs with h
    · subst h
      simpa using leaf_spec
    · have s1 := ih (k / 2) (by omega) (by omega)
      have s2 := ih (k - k / 2) (by omega) (by omega)
      apply (orStep_spec _ s1 s2).mono_d
      have hc : Nat.clog 2 k = Nat.clog 2 ((k + 2 - 1) / 2) + 1 :=
        Nat.clog_of_one_lt (by norm_num) (by omega)
      have e : k - k / 2 = (k + 2 - 1) / 2 := by omega
      have m1 : Nat.clog 2 (k / 2) ≤ Nat.clog 2 (k - k / 2) := Nat.clog_mono_right _ (by omega)
      rw [hc, ← e]
      omega

/-! ## Декодер (`decoder`) -/

/-- Унитарный набор: единица ровно во входе с номером `t`. -/
def uvec (N t : ℕ) : Fin N → Bool := fun v => decide ((v : ℕ) = t)

lemma uvec_atMostOne (N t : ℕ) : AtMostOne (uvec N t) := by
  intro i j hi hj
  simp only [uvec, decide_eq_true_eq] at hi hj
  ext; omega

/-- Спецификация декодера (`decoder`). -/
def DecSpec {r : ℕ} (D : Circ (2 ^ r) (Fin r)) : Prop :=
  ∀ t < 2 ^ r, (∀ p : Fin r, D.eval (uvec (2 ^ r) t) p = t.testBit p) ∧
    D.E (uvec (2 ^ r) t) ≤ r * Nat.clog 2 r

lemma mul_add_lt {a b u w : ℕ} (hu : u < a) (hw : w < b) : u * b + w < a * b := by
  calc u * b + w < u * b + b := by omega
    _ = (u + 1) * b := by ring
    _ ≤ a * b := Nat.mul_le_mul_right _ hu

/-- Провод к дереву старшей половины: лист `w` дерева `u` — слово `u·2^{r2} + w`. -/
def wHi (r1 r2 r : ℕ) (h : r1 + r2 = r) (u : Fin (2 ^ r1)) (w : Fin (2 ^ r2)) : Fin (2 ^ r) :=
  ⟨u * 2 ^ r2 + w, by rw [← h, pow_add]; exact mul_add_lt u.2 w.2⟩

/-- Провод к дереву младшей половины: лист `w` дерева `u` — слово `w·2^{r2} + u`. -/
def wLo (r1 r2 r : ℕ) (h : r1 + r2 = r) (u : Fin (2 ^ r2)) (w : Fin (2 ^ r1)) : Fin (2 ^ r) :=
  ⟨w * 2 ^ r2 + u, by rw [← h, pow_add]; exact mul_add_lt w.2 u.2⟩

/-- Первый ярус декодера: деревья ИЛИ для двух половин блока. -/
def decStage1 (r1 r2 r : ℕ) (h : r1 + r2 = r) :
    Circ (2 ^ r) ((Fin (2 ^ r1) × Unit) ⊕ (Fin (2 ^ r2) × Unit)) :=
  par2 (parF (2 ^ r1) fun u => sel (orT (2 ^ r2) (Nat.two_pow_pos _)) (wHi r1 r2 r h u))
    (parF (2 ^ r2) fun u => sel (orT (2 ^ r1) (Nat.two_pow_pos _)) (wLo r1 r2 r h u))

/-- Второй ярус: декодеры половин. -/
def decStage2 {r1 r2 : ℕ} (D1 : Circ (2 ^ r1) (Fin r1)) (D2 : Circ (2 ^ r2) (Fin r2)) :
    Circ (2 ^ r1 + 2 ^ r2) (Fin r1 ⊕ Fin r2) :=
  par2 (sel D1 (Fin.castAdd _)) (sel D2 (Fin.natAdd _))

/-- Соединение ярусов. -/
def decFeed (r1 r2 : ℕ) : Fin (2 ^ r1 + 2 ^ r2) → (Fin (2 ^ r1) × Unit) ⊕ (Fin (2 ^ r2) × Unit) :=
  Fin.addCases (motive := fun _ => (Fin (2 ^ r1) × Unit) ⊕ (Fin (2 ^ r2) × Unit))
    (fun u => Sum.inl (u, ())) (fun u => Sum.inr (u, ()))

/-- Шаг рекурсии декодера: старшие `r1` и младшие `r2` бит слова. -/
def decStep {r1 r2 r : ℕ} (h : r1 + r2 = r) (D1 : Circ (2 ^ r1) (Fin r1))
    (D2 : Circ (2 ^ r2) (Fin r2)) : Circ (2 ^ r) (Fin r) :=
  reout (comp (decStage1 r1 r2 r h) (decFeed r1 r2) (decStage2 D1 D2))
    (fun p => if hp : (p : ℕ) < r2 then Sum.inr ⟨p, hp⟩ else Sum.inl ⟨p - r2, by omega⟩)

lemma hi_iff {r2 u t : ℕ} : (∃ w : Fin (2 ^ r2), u * 2 ^ r2 + w = t) ↔ u = t / 2 ^ r2 := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt w.2]
    simp
  · rintro rfl
    exact ⟨⟨t % 2 ^ r2, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, Nat.div_add_mod' t _⟩

lemma lo_iff {r1 r2 u t : ℕ} (hu : u < 2 ^ r2) (ht : t < 2 ^ r1 * 2 ^ r2) :
    (∃ w : Fin (2 ^ r1), w * 2 ^ r2 + u = t) ↔ u = t % 2 ^ r2 := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  · rintro rfl
    exact ⟨⟨t / 2 ^ r2, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 ht⟩, Nat.div_add_mod' t _⟩

lemma decStage1_eval_inl {r1 r2 r : ℕ} (h : r1 + r2 = r) (t : ℕ) (u : Fin (2 ^ r1)) :
    (decStage1 r1 r2 r h).eval (uvec (2 ^ r) t) (Sum.inl (u, ())) =
      decide ((u : ℕ) = t / 2 ^ r2) := by
  rw [decStage1, par2_eval_inl, parF_eval, sel_eval, (orT_spec _ _).eval, decide_eq_decide]
  simp only [uvec, decide_eq_true_eq]
  simp only [wHi]
  exact hi_iff

lemma decStage1_eval_inr {r1 r2 r : ℕ} (h : r1 + r2 = r) {t : ℕ} (ht : t < 2 ^ r)
    (u : Fin (2 ^ r2)) :
    (decStage1 r1 r2 r h).eval (uvec (2 ^ r) t) (Sum.inr (u, ())) =
      decide ((u : ℕ) = t % 2 ^ r2) := by
  rw [decStage1, par2_eval_inr, parF_eval, sel_eval, (orT_spec _ _).eval, decide_eq_decide]
  simp only [uvec, decide_eq_true_eq]
  simp only [wLo]
  exact lo_iff u.2 (by rw [← pow_add, h]; exact ht)

/-- Сумма, в которой ненулевым может быть лишь одно слагаемое. -/
lemma sum_le_of_single {α : Type} [Fintype α] [DecidableEq α] (f : α → ℕ) (a : α) {B : ℕ}
    (h0 : ∀ b, b ≠ a → f b = 0) (h1 : f a ≤ B) : ∑ b, f b ≤ B := by
  rw [Finset.sum_eq_single a (fun b _ hb => h0 b hb) (by simp)]
  exact h1

lemma decStage1_E {r1 r2 r : ℕ} (h : r1 + r2 = r) {t : ℕ} (ht : t < 2 ^ r) :
    (decStage1 r1 r2 r h).E (uvec (2 ^ r) t) ≤ r := by
  have ht' : t < 2 ^ r1 * 2 ^ r2 := by rw [← pow_add, h]; exact ht
  have hhi : t / 2 ^ r2 < 2 ^ r1 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 ht'
  have hlo : t % 2 ^ r2 < 2 ^ r2 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [decStage1, par2_E, parF_E, parF_E]
  have A : ∑ u : Fin (2 ^ r1), (sel (orT (2 ^ r2) (Nat.two_pow_pos _)) (wHi r1 r2 r h u)).E
        (uvec (2 ^ r) t) ≤ r2 := by
    apply sum_le_of_single _ ⟨t / 2 ^ r2, hhi⟩
    · intro u hu
      rw [sel_E]
      apply (orT_spec _ _).mono.E_zero
      intro w
      simp only [uvec, decide_eq_false_iff_not]
      simp only [wHi]
      intro hw
      apply hu
      ext
      exact hi_iff.1 ⟨w, hw⟩
    · rw [sel_E]
      have inj : Function.Injective (wHi r1 r2 r h ⟨t / 2 ^ r2, hhi⟩) := by
        intro a b hab; simp only [wHi, Fin.mk.injEq] at hab; ext; omega
      have := ((orT_spec _ (Nat.two_pow_pos r2)).one _ ((uvec_atMostOne _ t).comp inj)).1
      rwa [Nat.clog_pow _ _ (by norm_num)] at this
  have B : ∑ u : Fin (2 ^ r2), (sel (orT (2 ^ r1) (Nat.two_pow_pos _)) (wLo r1 r2 r h u)).E
        (uvec (2 ^ r) t) ≤ r1 := by
    apply sum_le_of_single _ ⟨t % 2 ^ r2, hlo⟩
    · intro u hu
      rw [sel_E]
      apply (orT_spec _ _).mono.E_zero
      intro w
      simp only [uvec, decide_eq_false_iff_not]
      simp only [wLo]
      intro hw
      apply hu
      ext
      exact (lo_iff u.2 ht').1 ⟨w, hw⟩
    · rw [sel_E]
      have inj : Function.Injective (wLo r1 r2 r h ⟨t % 2 ^ r2, hlo⟩) := by
        intro a b hab
        simp only [wLo, Fin.mk.injEq, Nat.add_right_cancel_iff] at hab
        ext
        exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hab
      have := ((orT_spec _ (Nat.two_pow_pos r1)).one _ ((uvec_atMostOne _ t).comp inj)).1
      rwa [Nat.clog_pow _ _ (by norm_num)] at this
  omega

lemma decStep_spec {r1 r2 r : ℕ} (h : r1 + r2 = r) {D1 : Circ (2 ^ r1) (Fin r1)}
    {D2 : Circ (2 ^ r2) (Fin r2)} (h1 : DecSpec D1) (h2 : DecSpec D2) (h21 : r2 ≤ r1)
    (hc : Nat.clog 2 r1 + 1 ≤ Nat.clog 2 r) : DecSpec (decStep h D1 D2) := by
  intro t ht
  have ht' : t < 2 ^ r1 * 2 ^ r2 := by rw [← pow_add, h]; exact ht
  have hhi : t / 2 ^ r2 < 2 ^ r1 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 ht'
  have hlo : t % 2 ^ r2 < 2 ^ r2 := Nat.mod_lt _ (Nat.two_pow_pos _)
  -- входы второго яруса
  have y1 : (fun u : Fin (2 ^ r1) => (decStage1 r1 r2 r h).eval (uvec (2 ^ r) t)
      (decFeed r1 r2 (Fin.castAdd (2 ^ r2) u))) = uvec (2 ^ r1) (t / 2 ^ r2) := by
    funext u
    simp only [decFeed, Fin.addCases_left, decStage1_eval_inl, uvec]
  have y2 : (fun u : Fin (2 ^ r2) => (decStage1 r1 r2 r h).eval (uvec (2 ^ r) t)
      (decFeed r1 r2 (Fin.natAdd (2 ^ r1) u))) = uvec (2 ^ r2) (t % 2 ^ r2) := by
    funext u
    simp only [decFeed, Fin.addCases_right, decStage1_eval_inr h ht, uvec]
  constructor
  · intro p
    unfold decStep
    rw [reout_eval, comp_eval]
    split_ifs with hp
    · rw [decStage2, par2_eval_inr, sel_eval, y2, (h2 _ hlo).1]
      simp [Nat.testBit_mod_two_pow, hp]
    · rw [decStage2, par2_eval_inl, sel_eval, y1, (h1 _ hhi).1]
      simp only [Nat.testBit_div_two_pow]
      congr 1
      omega
  · unfold decStep
    rw [reout_E, comp_E, decStage2, par2_E, sel_E, sel_E, y1, y2]
    have e1 := (h1 _ hhi).2
    have e2 := (h2 _ hlo).2
    have e0 := decStage1_E h ht
    have m2 : Nat.clog 2 r2 ≤ Nat.clog 2 r1 := Nat.clog_mono_right _ h21
    have hc1 : 1 ≤ Nat.clog 2 r := by omega
    obtain ⟨c, hcr⟩ : ∃ c, Nat.clog 2 r = c + 1 := ⟨Nat.clog 2 r - 1, by omega⟩
    rw [hcr] at hc ⊢
    have k1 : r1 * Nat.clog 2 r1 ≤ r1 * c := Nat.mul_le_mul_left _ (by omega)
    have k2 : r2 * Nat.clog 2 r2 ≤ r2 * c := Nat.mul_le_mul_left _ (by omega)
    have : r * (c + 1) = r1 * c + r2 * c + r1 + r2 := by rw [← h]; ring
    omega

/-- Рекурсивный декодер (`decoder`). -/
def dec : (r : ℕ) → Circ (2 ^ r) (Fin r)
  | 0 => ⟨[], by simp, fun p => p.elim0, fun p => p.elim0⟩
  | 1 => ⟨[], by simp, fun _ => 1, by intro; simp⟩
  | r + 2 => decStep (r1 := r + 2 - (r + 2) / 2) (r2 := (r + 2) / 2) (by omega)
      (dec (r + 2 - (r + 2) / 2)) (dec ((r + 2) / 2))
termination_by r => r
decreasing_by all_goals omega

/-- `decoder`: декодер на унитарном наборе выдаёт биты номера, мощность `≤ r ⌈log r⌉`. -/
theorem dec_spec : ∀ r, DecSpec (dec r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ =>
      intro t _
      refine ⟨fun p => p.elim0, ?_⟩
      rw [E_eq_sum]; simp [dec, Circ.s]
    | 1, _ =>
      intro t ht
      refine ⟨?_, ?_⟩
      · intro p
        have hp : p = 0 := Subsingleton.elim _ _
        subst hp
        simp only [Circ.eval, dec]
        rw [sig_of_lt _ _ (by norm_num : 1 < 2 ^ 1)]
        simp only [uvec]
        interval_cases t <;> decide
      · rw [E_eq_sum]; simp [dec, Circ.s]
    | r + 2, ih =>
      rw [dec]
      apply decStep_spec _ (ih _ (by omega)) (ih _ (by omega)) (by omega)
      have hc : Nat.clog 2 (r + 2) = Nat.clog 2 ((r + 2 + 2 - 1) / 2) + 1 :=
        Nat.clog_of_one_lt (by norm_num) (by omega)
      rw [hc, show r + 2 - (r + 2) / 2 = (r + 2 + 2 - 1) / 2 by omega]

end Up

end PowerActivity
