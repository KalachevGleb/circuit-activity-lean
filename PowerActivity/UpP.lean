import PowerActivity.Spec
import PowerActivity.UpMint

/-!
# Верхние оценки: квадратичная оценка `P`- и `U`-активности (`UpperPGoal`)

Квадратичная оценка `P`-активности известна (О. М. Касим-Заде, 1992); здесь она доказывается
собственной конструкцией — вариантом схемы А. П. Горяшко (1969). Для префикса `w`
длины `i` индикатор `g_w = [x₁…x_i = w]` и «пропущенные литералы» `p_{w,j} = g_w ∧ x_j`,
`q_{w,j} = g_w ∧ ¬x_j` (`j > i`). Корень: `p_{∅,j} = x_j`, `q_{∅,j} = ¬x_j`; сын `wb`:
`g_{w1} = p_{w,i+1}`, `g_{w0} = q_{w,i+1}`, `p_{wb,j} = g_{wb} ∧ p_{w,j}`, `q_{wb,j} = g_{wb} ∧ q_{w,j}`.
Рекурсивно: `tC k` — схема с входами `g, p₁…p_k, q₁…q_k` и выходами-листьями `g_a`, `a ∈ {0,1}^k`.
На «правильном» входе (`pin k g z`) единицы на входах элементов бывают лишь у детей активного
пути: `P(tC k) ≤ 2k²`. Выход — дерево ИЛИ над листьями `g_a` с `f(a) = 1` (прочие листья
заменены константой `0`). Итог: `P ≤ 6n²`, `U ≤ 2P ≤ 12n²`.
-/

namespace PowerActivity

open Finset

namespace Up

variable {n : ℕ}

/-! ## Номер листа: первая переменная — старший бит -/

/-- `idxH z (k+1) = [z₀]·2^k + idxH (z ∘ succ) k`. -/
def idxH (z : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (if z 0 then 2 ^ k else 0) + idxH (fun i => z (i + 1)) k

lemma idxH_lt : ∀ (k : ℕ) (z : ℕ → Bool), idxH z k < 2 ^ k
  | 0, _ => by simp [idxH]
  | k + 1, z => by
    have := idxH_lt k (fun i => z (i + 1))
    simp only [idxH, pow_succ]
    split_ifs <;> omega

lemma idxH_eq : ∀ (k : ℕ) (z z' : ℕ → Bool), idxH z k = idxH z' k → ∀ i < k, z i = z' i
  | 0, _, _, _ => by intro i hi; omega
  | k + 1, z, z', h => by
    have h1 := idxH_lt k (fun i => z (i + 1))
    have h2 := idxH_lt k (fun i => z' (i + 1))
    simp only [idxH] at h
    have e0 : z 0 = z' 0 ∧ idxH (fun i => z (i + 1)) k = idxH (fun i => z' (i + 1)) k := by
      cases hz : z 0 <;> cases hz' : z' 0 <;> simp only [hz, hz'] at h <;>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, true_and] at h ⊢ <;> omega
    intro i hi
    rcases i with _ | i
    · exact e0.1
    · exact idxH_eq k _ _ e0.2 i (by omega)

/-! ## Схема `T(k)` -/

/-- Правильный вход `T(k)`: `g`, затем `p_i = g ∧ z_i`, затем `q_i = g ∧ ¬z_i`. -/
def pin (k : ℕ) (gv : Bool) (z : ℕ → Bool) : Fin (2 * k + 1) → Bool :=
  fun c => if (c : ℕ) = 0 then gv else if (c : ℕ) ≤ k then (gv && z (c - 1))
    else (gv && !z (c - 1 - k))

/-- Вход-индикатор сына `b`: `p₁` (сын `1`) или `q₁` (сын `0`). -/
def cIdx (b : Bool) (k : ℕ) : Fin (2 * (k + 1) + 1) :=
  if b then ⟨1, by omega⟩ else ⟨k + 2, by omega⟩

/-- Слой сына `b`: `p'_i = c_b ∧ p_{i+1}` (`i < k`), `q'_i = c_b ∧ q_{i+1}`. -/
def chLayer (b : Bool) (k : ℕ) : Circ (2 * (k + 1) + 1) (Fin (2 * k)) :=
  layer _ (2 * k) (fun _ => .and) (fun _ => cIdx b k)
    (fun i => if (i : ℕ) < k then ⟨i + 2, by omega⟩ else ⟨i + 3, by omega⟩)

/-- Вход `T(k)` для сына `b`: `g' = c_b`, затем выходы слоя. -/
def chL (b : Bool) (k : ℕ) : Circ (2 * (k + 1) + 1) (Fin (2 * k + 1)) :=
  withOut (chLayer b k)
    (fun c => if (c : ℕ) = 0 then (cIdx b k : ℕ) else 2 * (k + 1) + 1 + (c - 1))
    (by
      intro c
      have hs : (chLayer b k).s = 2 * k := layer_s _ _ _ _ _
      rw [hs]
      have := c.2
      have := (cIdx b k).2
      split_ifs <;> omega)

lemma chL_mono (b : Bool) (k : ℕ) : Mono (chL b k) :=
  Mono.withOut _ (Mono.layer _ _ (by intro; simp))

lemma chL_s (b : Bool) (k : ℕ) : (chL b k).s = 2 * k := layer_s _ _ _ _ _

/-- Индикатор сына на правильном входе. -/
def gb (b : Bool) (gv : Bool) (z : ℕ → Bool) : Bool := if b then (gv && z 0) else (gv && !z 0)

lemma chL_eval (b : Bool) (k : ℕ) (gv : Bool) (z : ℕ → Bool) :
    (fun c => (chL b k).eval (pin (k + 1) gv z) (id c)) = pin k (gb b gv z) (fun i => z (i + 1)) := by
  have hc : pin (k + 1) gv z (cIdx b k) = gb b gv z := by
    cases b
    · simp only [pin, cIdx, gb, Bool.false_eq_true, ↓reduceIte, Fin.val_mk,
        show k + 2 ≠ 0 by omega, show ¬ (k + 2 ≤ k + 1) by omega,
        show k + 2 - 1 - (k + 1) = 0 by omega]
    · simp only [pin, cIdx, gb, ↓reduceIte, Fin.val_mk, show (1 : ℕ) ≠ 0 by omega,
        show 1 ≤ k + 1 by omega, Nat.sub_self]
  funext c
  simp only [id, chL, withOut_eval]
  by_cases h0 : (c : ℕ) = 0
  · simp only [h0, ↓reduceIte]
    rw [sig_of_lt _ _ (cIdx b k).2]
    simp only [pin, h0, ↓reduceIte]
    exact hc
  · simp only [h0, ↓reduceIte]
    have hi : (c : ℕ) - 1 < 2 * k := by have := c.2; omega
    have e := layer_eval _ (2 * k) (fun _ => .and) (fun _ => cIdx b k)
      (fun i => if (i : ℕ) < k then ⟨i + 2, by omega⟩ else ⟨i + 3, by omega⟩)
      (pin (k + 1) gv z) ⟨(c : ℕ) - 1, hi⟩
    simp only [Circ.eval, layer] at e
    simp only [chLayer, layer]
    rw [e, hc]
    simp only [Op.eval, pin]
    have hgb : ∀ w : Bool, (gb b gv z && (gv && w)) = (gb b gv z && w) := by
      intro w; cases b <;> cases gv <;> simp [gb]
    by_cases hk : (c : ℕ) - 1 < k
    · simp only [hk, ↓reduceIte, show (c : ℕ) - 1 + 2 ≠ 0 by omega,
        show (c : ℕ) - 1 + 2 ≤ k + 1 by omega, show (c : ℕ) ≤ k by omega]
      rw [hgb]
      simp only [h0, ↓reduceIte, show (c : ℕ) - 1 + 2 - 1 = (c : ℕ) - 1 + 1 by omega]
    · simp only [hk, ↓reduceIte, show (c : ℕ) - 1 + 3 ≠ 0 by omega,
        show ¬ ((c : ℕ) - 1 + 3 ≤ k + 1) by omega, show ¬ ((c : ℕ) ≤ k) by omega]
      rw [hgb]
      simp only [h0, ↓reduceIte, show (c : ℕ) - 1 + 3 - 1 - (k + 1) = (c : ℕ) - 1 - k + 1 by omega]

/-- Схема листьев `T(k)`: входы `g, p₁…p_k, q₁…q_k`, выход `a` — индикатор листа `a`. -/
def tC : (k : ℕ) → Circ (2 * k + 1) (Fin (2 ^ k))
  | 0 => ⟨[], by simp, fun _ => 0, by simp⟩
  | k + 1 => reout (par2 (comp (chL true k) id (tC k)) (comp (chL false k) id (tC k)))
      (fun a => if h : (a : ℕ) < 2 ^ k then Sum.inr ⟨a, h⟩
        else Sum.inl ⟨a - 2 ^ k, by
          have := a.2; have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
          omega⟩)

lemma tC_mono : ∀ k, Mono (tC k)
  | 0 => by intro g hg; simp [tC] at hg
  | k + 1 => Mono.reout _ (Mono.par2 (Mono.comp _ (chL_mono _ _) (tC_mono k))
      (Mono.comp _ (chL_mono _ _) (tC_mono k)))

lemma pin_false (k : ℕ) (z : ℕ → Bool) : ∀ c, pin k false z c = false := by
  intro c; simp [pin]

/-- Значения и `P`-активность `T(k)` на правильном входе. -/
theorem tC_spec : ∀ (k : ℕ) (gv : Bool) (z : ℕ → Bool),
    (∀ a : Fin (2 ^ k), (tC k).eval (pin k gv z) a = (gv && decide (idxH z k = a))) ∧
    (tC k).P (pin k gv z) ≤ 2 * k * k
  | 0, gv, z => by
    refine ⟨?_, ?_⟩
    · intro a
      have ha : (a : ℕ) = 0 := by have := a.2; simp at this; omega
      simp only [Circ.eval, tC]
      rw [sig_of_lt _ _ (by norm_num : 0 < 2 * 0 + 1)]
      simp [pin, idxH]
    · rw [P_eq_sum]; simp [tC, Circ.s]
  | k + 1, gv, z => by
    obtain ⟨e1, p1⟩ := tC_spec k (gb true gv z) (fun i => z (i + 1))
    obtain ⟨e0, p0⟩ := tC_spec k (gb false gv z) (fun i => z (i + 1))
    have hlt := idxH_lt k (fun i => z (i + 1))
    refine ⟨?_, ?_⟩
    · intro a
      simp only [tC, reout_eval]
      have ha := a.2
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have hI : idxH z (k + 1) = (if z 0 then 2 ^ k else 0) + idxH (fun i => z (i + 1)) k := rfl
      split_ifs with h
      · rw [par2_eval_inr, comp_eval, chL_eval, e0]
        rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq, hI]
        simp only [gb, Bool.false_eq_true, ↓reduceIte]
        by_cases hz : z 0 = true
        · rw [hz]; cases gv <;> simp
          all_goals omega
        · rw [Bool.not_eq_true] at hz; rw [hz]; cases gv <;> simp
      · rw [par2_eval_inl, comp_eval, chL_eval, e1]
        rw [Bool.eq_iff_iff, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq, hI]
        simp only [gb, ↓reduceIte]
        by_cases hz : z 0 = true
        · rw [hz]; cases gv <;> simp
          all_goals omega
        · rw [Bool.not_eq_true] at hz; rw [hz]; cases gv <;> simp
          all_goals omega
    · simp only [tC, reout_P]
      rw [par2_P, comp_P, comp_P, chL_eval, chL_eval]
      have c1 := P_le_s (chL true k) (pin (k + 1) gv z)
      have c0 := P_le_s (chL false k) (pin (k + 1) gv z)
      rw [chL_s] at c1 c0
      have hk : 2 * (k + 1) * (k + 1) = 2 * k * k + 4 * k + 2 := by ring
      cases hz : z 0
      · have : gb true gv z = false := by simp [gb, hz]
        rw [this] at p1 ⊢
        have z1 := (tC_mono k).P_zero (pin_false k (fun i => z (i + 1)))
        omega
      · have : gb false gv z = false := by simp [gb, hz]
        rw [this] at p0 ⊢
        have z0 := (tC_mono k).P_zero (pin_false k (fun i => z (i + 1)))
        omega

/-! ## Итоговая схема -/

lemma baseC_s (n : ℕ) (hn : 0 < n) : (baseC n hn).s = n + 2 := by
  simp only [baseC, reout_s]
  rw [app_s, invC_s]
  simp [constC, layer_s]

/-- Входы `T(n)`: `g = 1`, `p_i = x_i`, `q_i = ¬x_i`. -/
def pBase (n : ℕ) (hn : 0 < n) : Circ n (Fin (2 * n + 1)) :=
  withOut (baseC n hn)
    (fun c => if (c : ℕ) = 0 then (baseC n hn).out (Sum.inl 0)
      else if h : (c : ℕ) ≤ n then (c : ℕ) - 1
      else (baseC n hn).out (Sum.inr (Sum.inl ⟨c - 1 - n, by have := c.2; omega⟩)))
    (by
      intro c
      split_ifs
      · exact (baseC n hn).out_lt _
      · omega
      · exact (baseC n hn).out_lt _)

lemma pBase_eval (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (fun c => (pBase n hn).eval x (id c)) = pin n true (xb x) := by
  obtain ⟨b1, b2, -, -⟩ := baseC_spec n hn x
  funext c
  simp only [id, pBase, withOut_eval, pin]
  by_cases h0 : (c : ℕ) = 0
  · simp only [h0, ↓reduceIte]; exact b1
  · by_cases h1 : (c : ℕ) ≤ n
    · simp only [h0, h1, ↓reduceIte, ↓reduceDIte, Bool.true_and]
      rw [sig_of_lt _ _ (by omega)]
      simp [xb, show (c : ℕ) - 1 < n by omega]
    · simp only [h0, h1, ↓reduceIte, ↓reduceDIte, Bool.true_and]
      have := b2 ⟨c - 1 - n, by have := c.2; omega⟩
      simp only [Circ.eval] at this
      rw [this]
      have hc : (c : ℕ) - 1 - n < n := by have := c.2; omega
      simp [xb, hc]

/-- Схема листьев всех `x`: выход `a` — `[idxH x = a]`. -/
def leaves (n : ℕ) (hn : 0 < n) : Circ n (Fin (2 ^ n)) := comp (pBase n hn) id (tC n)

lemma leaves_eval (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) (a : Fin (2 ^ n)) :
    (leaves n hn).eval x a = decide (idxH (xb x) n = a) := by
  rw [leaves, comp_eval, pBase_eval, (tC_spec n true (xb x)).1 a, Bool.true_and]

lemma pBase_s (n : ℕ) (hn : 0 < n) : (pBase n hn).s = n + 2 := baseC_s n hn

lemma leaves_s (n : ℕ) (hn : 0 < n) : (pBase n hn).s ≤ (leaves n hn).s := by
  rw [leaves, comp_s]
  omega

/-- Номер константы `0` в схеме листьев. -/
def zIdx (n : ℕ) (hn : 0 < n) : ℕ := (baseC n hn).out (Sum.inr (Sum.inr ()))

lemma zIdx_lt (n : ℕ) (hn : 0 < n) : zIdx n hn < n + (pBase n hn).s := (baseC n hn).out_lt _

lemma leaves_zero (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (leaves n hn).sig x (zIdx n hn) = false := by
  rw [leaves, comp_sig_old _ _ _ x (zIdx_lt n hn)]
  exact (baseC_spec n hn x).2.2.1

/-- Лист `a` используется, если `a` — номер набора `y` с `f(y) = 1`. -/
def useLeaf (n : ℕ) (F : (Fin n → Bool) → Fin 1 → Bool) (a : Fin (2 ^ n)) : Prop :=
  ∃ y : Fin n → Bool, idxH (xb y) n = a ∧ F y 0 = true

open Classical in
/-- Подача листьев в дерево ИЛИ: используемые листья или константа `0`. -/
noncomputable def feedP (n : ℕ) (hn : 0 < n) (F : (Fin n → Bool) → Fin 1 → Bool) :
    Fin (2 ^ n) → ℕ :=
  fun a => if useLeaf n F a then (leaves n hn).out a else zIdx n hn

lemma feedP_lt (n : ℕ) (hn : 0 < n) (F : (Fin n → Bool) → Fin 1 → Bool) (a : Fin (2 ^ n)) :
    feedP n hn F a < n + (leaves n hn).s := by
  unfold feedP
  split_ifs
  · exact (leaves n hn).out_lt _
  · have := zIdx_lt n hn
    have h2 := leaves_s n hn
    omega

/-- Схема с квадратичной `P`-активностью. -/
noncomputable def pCirc (n : ℕ) (hn : 0 < n) (F : (Fin n → Bool) → Fin 1 → Bool) :
    Circ n (Fin 1) :=
  reout (compR (leaves n hn) (2 ^ n) (feedP n hn F) (feedP_lt n hn F)
    (orT (2 ^ n) (Nat.two_pow_pos n))) (fun _ => ())

lemma xb_inj {x y : Fin n → Bool} (h : ∀ i < n, xb x i = xb y i) : x = y := by
  funext i
  have := h i i.2
  simpa [xb] using this

lemma leafVal (n : ℕ) (hn : 0 < n) (F : (Fin n → Bool) → Fin 1 → Bool) (x : Fin n → Bool)
    (a : Fin (2 ^ n)) :
    (leaves n hn).sig x (feedP n hn F a) = true ↔
      useLeaf n F a ∧ idxH (xb x) n = a := by
  unfold feedP
  split_ifs with h
  · have := leaves_eval n hn x a
    simp only [Circ.eval] at this
    rw [this, decide_eq_true_eq]
    exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · rw [leaves_zero]
    simp only [Bool.false_eq_true, false_iff, not_and]
    exact fun h' => absurd h' h

theorem pCirc_realizes (n : ℕ) (hn : 0 < n) (F : (Fin n → Bool) → Fin 1 → Bool) :
    (pCirc n hn F).Realizes F := by
  intro x
  funext c
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  rw [pCirc, reout_eval, compR_eval, (orT_spec _ _).eval]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨⟨y, hy1, hy2⟩, hx⟩ := (leafVal n hn F x a).1 ha
    have : y = x := xb_inj (idxH_eq n _ _ (hy1.trans hx.symm))
    rw [← this]; exact hy2
  · intro hF
    refine ⟨⟨idxH (xb x) n, idxH_lt n _⟩, (leafVal n hn F x _).2 ⟨⟨x, rfl, hF⟩, rfl⟩⟩

theorem pCirc_P (n : ℕ) (hn : 0 < n) (F : (Fin n → Bool) → Fin 1 → Bool) (x : Fin n → Bool) :
    (pCirc n hn F).P x ≤ 2 * n * n + 2 * n + 2 := by
  rw [pCirc, reout_P, compR_P]
  have hl : (leaves n hn).P x = (pBase n hn).P x + (tC n).P (pin n true (xb x)) := by
    rw [leaves, comp_P, pBase_eval]
  have h1 := P_le_s (pBase n hn) x
  rw [pBase_s] at h1
  have h2 := (tC_spec n true (xb x)).2
  have hone : AtMostOne (fun a => (leaves n hn).sig x (feedP n hn F a)) := by
    intro a b ha hb
    have ha' := (leafVal n hn F x a).1 ha
    have hb' := (leafVal n hn F x b).1 hb
    ext; rw [← ha'.2, ← hb'.2]
  have h3 := ((orT_spec _ (Nat.two_pow_pos n)).one _ hone).2
  rw [Nat.clog_pow _ _ (by norm_num)] at h3
  omega

/-- Квадратичная верхняя оценка `P`- и `U`-активности: `P ≤ 6n²`, `U ≤ 12n²`. -/
theorem upperP_goal_pf : UpperPGoal := by
  refine ⟨12, ?_⟩
  intro n hn F
  refine ⟨pCirc n (by omega) F, pCirc_realizes n (by omega) F, fun x => ?_⟩
  have hP := pCirc_P n (by omega) F x
  have hU := U_le_two_P (pCirc n (by omega) F) x
  have hn2 : 2 * n * n + 2 * n + 2 ≤ 6 * (n * n) := by nlinarith
  have hP' : ((pCirc n (by omega) F).P x : ℝ) ≤ 6 * (n : ℝ) ^ 2 := by
    have : (pCirc n (by omega) F).P x ≤ 6 * (n * n) := hP.trans hn2
    have : ((pCirc n (by omega) F).P x : ℝ) ≤ ((6 * (n * n) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  have hU' : ((pCirc n (by omega) F).U x : ℝ) ≤ 2 * ((pCirc n (by omega) F).P x : ℝ) := by
    exact_mod_cast hU
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  constructor <;> nlinarith

end Up

end PowerActivity
