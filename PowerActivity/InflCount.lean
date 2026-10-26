import PowerActivity.InflCirc
import PowerActivity.ApxCount

/-!
# Тезисы, цель `InflGoal`: почти все функции существенно зависят от каждой переменной

Пары `{x, x^{(t)}}` разбивают куб `{0,1}^{n+1}` на `M = 2ⁿ` пар; через
`Fin.insertNthEquiv` функция `f` от `n+1` переменных — это пара функций
`g₀(y) = f(y, x_t = 0)`, `g₁(y) = f(y, x_t = 1)` от `n` переменных, и
`D_t(f) = 2 #{y : g₀(y) ≠ g₁(y)}` (`dif_eq`). «Плохие» для `t` функции (`4 D_t(f) ≤ N`,
`badT`) — это пары с `g₁` в шаре Хэмминга радиуса `M/4` вокруг `g₀`; по оценке шара
`Apx.card_ball_le` `|bad_t| · 3^{M − ⌊M/4⌋} ≤ 2^M 4^M` (`card_badT_le`).
При `n ≥ 8` отсюда `n² |bad_t| ≤ 2^N` (`n2_card_badT_le`; численно — `nat_key`:
`n² 2^M ≤ 3^{M − M/4}`), и доля функций, хороших для всех `t` (`GoodF`), не меньше `1 − 1/n`
(`frac_goodF`).

* `frac_ge_of_cover`, `frac_mono` — оценки доли;
* `frac_first` — доля операторов, у которых координата `0` обладает свойством, равна доле функций
  (как в `ThesesAssemble`, своя копия).
-/

namespace PowerActivity

open Finset

namespace Infl

/-! ## Доля операторов -/

/-- Если операторы без свойства `Q` лежат в `B` и `|B| ≤ δ · |все|`, то доля `Q` не меньше
`1 − δ`. -/
lemma frac_ge_of_cover {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (Q : ((Fin n → Bool) → κ → Bool) → Prop) (B : Finset ((Fin n → Bool) → κ → Bool))
    (hB : ∀ F, ¬ Q F → F ∈ B) {δ : ℝ}
    (hδ : (B.card : ℝ) ≤ δ * Fintype.card ((Fin n → Bool) → κ → Bool)) :
    1 - δ ≤ frac n κ Q := by
  classical
  unfold frac
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  have hsplit := card_filter_add_card_filter_not
    (s := (univ : Finset ((Fin n → Bool) → κ → Bool))) Q
  rw [card_univ] at hsplit
  have hsub : (univ.filter fun F => ¬ Q F) ⊆ B := fun F hF => hB F (mem_filter.mp hF).2
  have h1 : ((univ.filter fun F => ¬ Q F).card : ℝ) ≤ B.card := by
    exact_mod_cast card_le_card hsub
  have hpos : (0 : ℝ) < Fintype.card ((Fin n → Bool) → κ → Bool) := by
    exact_mod_cast Fintype.card_pos
  have h2 : ((univ.filter Q).card : ℝ) + ((univ.filter fun F => ¬ Q F).card : ℝ) =
      Fintype.card ((Fin n → Bool) → κ → Bool) := by exact_mod_cast hsplit
  rw [le_div_iff₀ hpos]
  linarith

/-- Монотонность доли. -/
lemma frac_mono {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    {Q Q' : ((Fin n → Bool) → κ → Bool) → Prop} (h : ∀ F, Q F → Q' F) :
    frac n κ Q ≤ frac n κ Q' := by
  unfold frac
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (Set.toFinite _) h

/-- Доля операторов, координата `0` которых обладает свойством `Q`, равна доле функций
со свойством `Q`. -/
lemma frac_first {n m : ℕ} (hm : 1 ≤ m) (Q : ((Fin n → Bool) → Fin 1 → Bool) → Prop) :
    frac n (Fin m) (fun F => Q (fun x _ => F x ⟨0, hm⟩)) = frac n (Fin 1) Q := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let e : ((Fin n → Bool) → Fin (k + 1) → Bool) ≃
      ((Fin n → Bool) → Fin 1 → Bool) × ((Fin n → Bool) → Fin k → Bool) :=
    { toFun := fun F => (fun x _ => F x 0, fun x j => F x j.succ)
      invFun := fun p x => Fin.cons (p.1 x 0) (p.2 x)
      left_inv := fun F => by
        funext x i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext x i
          have : i = 0 := Subsingleton.elim _ _
          subst this
          simp
        · funext x j
          simp }
  have hsub : {F : (Fin n → Bool) → Fin (k + 1) → Bool // Q (fun x _ => F x ⟨0, hm⟩)} ≃
      {f // Q f} × ((Fin n → Bool) → Fin k → Bool) :=
    (e.subtypeEquiv (p := fun F => Q (fun x _ => F x ⟨0, hm⟩)) (q := fun p => Q p.1)
      (fun F => Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  unfold frac
  rw [Nat.card_congr hsub, Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  have hpos : (0 : ℝ) < Nat.card ((Fin n → Bool) → Fin k → Bool) := by
    exact_mod_cast Nat.card_pos
  push_cast
  rw [mul_div_mul_right _ _ (ne_of_gt hpos)]

/-! ## `D_t(f)` через половины куба -/

lemma flip_insertNth {n : ℕ} (t : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Low.flip (Fin.insertNth t b y) t = Fin.insertNth t (!b) y := by
  unfold Low.flip
  rw [Fin.insertNth_apply_same, Fin.update_insertNth]

/-- `D_t(f) = 2 #{y : f(y, x_t = 0) ≠ f(y, x_t = 1)}`. -/
lemma dif_eq {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (t : Fin (n + 1)) :
    dif f t = 2 * (univ.filter fun y : Fin n → Bool =>
      f (Fin.insertNth t false y) ≠ f (Fin.insertNth t true y)).card := by
  unfold dif
  rw [card_filter, card_filter]
  have hsum : ∑ x : Fin (n + 1) → Bool, (if f x ≠ f (Low.flip x t) then 1 else 0) =
      ∑ p : Bool × (Fin n → Bool),
        (if f (Fin.insertNth t p.1 p.2) ≠ f (Fin.insertNth t (!p.1) p.2) then 1 else 0) := by
    have hbij : Function.Bijective
        (fun p : Bool × (Fin n → Bool) => Fin.insertNth (α := fun _ => Bool) t p.1 p.2) :=
      (Fin.insertNthEquiv (fun _ => Bool) t).bijective
    refine (Fintype.sum_bijective _ hbij _ _ (fun p => ?_)).symm
    simp only [flip_insertNth]
  rw [hsum, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.not_true, Bool.not_false]
  rw [two_mul]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  by_cases h : f (Fin.insertNth t false y) = f (Fin.insertNth t true y)
  · simp [h]
  · have h' : ¬ f (Fin.insertNth t true y) = f (Fin.insertNth t false y) := fun h'' => h h''.symm
    simp only [ne_eq, h, h', not_false_eq_true, ite_true]

/-! ## Подсчёт плохих функций -/

/-- Функции, плохие для переменной `t`: `4 D_t(f) ≤ N`. -/
def badT (n : ℕ) (t : Fin n) : Finset ((Fin n → Bool) → Fin 1 → Bool) :=
  univ.filter fun F => 4 * dif (fun x => F x 0) t ≤ 2 ^ n

/-- `|bad_t| · 3^{M − ⌊M/4⌋} ≤ 2^M 4^M` при `M = 2ⁿ` (функции от `n+1` переменных). -/
lemma card_badT_le (n : ℕ) (t : Fin (n + 1)) :
    (badT (n + 1) t).card * 3 ^ (2 ^ n - 2 ^ n / 4) ≤ 2 ^ 2 ^ n * 4 ^ 2 ^ n := by
  classical
  let φ : ((Fin (n + 1) → Bool) → Fin 1 → Bool) →
      ((Fin n → Bool) → Bool) × ((Fin n → Bool) → Fin 1 → Bool) :=
    fun F => (fun y => F (Fin.insertNth t false y) 0, fun y _ => F (Fin.insertNth t true y) 0)
  let T : Finset (((Fin n → Bool) → Bool) × ((Fin n → Bool) → Fin 1 → Bool)) :=
    univ.biUnion fun g => (Apx.ball g).image fun h => (g, h)
  have hinj : Set.InjOn φ (badT (n + 1) t) := by
    intro F _ F' _ hFF
    funext x i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h1 := congrArg Prod.fst hFF
    have h2 := congrArg Prod.snd hFF
    rw [← Fin.insertNth_self_removeNth t x]
    cases x t
    · exact congrFun h1 (Fin.removeNth t x)
    · exact congrFun (congrFun h2 (Fin.removeNth t x)) 0
  have hmaps : ∀ F ∈ badT (n + 1) t, φ F ∈ T := by
    intro F hF
    simp only [badT, mem_filter, mem_univ, true_and] at hF
    rw [dif_eq] at hF
    simp only [T, mem_biUnion, mem_univ, true_and, mem_image]
    refine ⟨(φ F).1, (φ F).2, ?_, rfl⟩
    simp only [Apx.ball, mem_filter, mem_univ, true_and, φ]
    have hs := card_filter_add_card_filter_not (s := (univ : Finset (Fin n → Bool)))
      (fun y => F (Fin.insertNth t false y) 0 = F (Fin.insertNth t true y) 0)
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hs
    simp only [ne_eq] at hF
    rw [pow_succ] at hF
    omega
  have h1 : (badT (n + 1) t).card ≤ T.card := card_le_card_of_injOn φ hmaps hinj
  calc (badT (n + 1) t).card * 3 ^ (2 ^ n - 2 ^ n / 4)
      ≤ T.card * 3 ^ (2 ^ n - 2 ^ n / 4) := Nat.mul_le_mul_right _ h1
    _ ≤ (∑ g : (Fin n → Bool) → Bool, ((Apx.ball g).image fun h => (g, h)).card) *
          3 ^ (2 ^ n - 2 ^ n / 4) := Nat.mul_le_mul_right _ card_biUnion_le
    _ ≤ (∑ g : (Fin n → Bool) → Bool, (Apx.ball g).card) * 3 ^ (2 ^ n - 2 ^ n / 4) :=
        Nat.mul_le_mul_right _ (sum_le_sum fun g _ => card_image_le)
    _ = ∑ g : (Fin n → Bool) → Bool, (Apx.ball g).card * 3 ^ (2 ^ n - 2 ^ n / 4) := by
        rw [sum_mul]
    _ ≤ ∑ _g : (Fin n → Bool) → Bool, 4 ^ 2 ^ n := sum_le_sum fun g _ => Apx.card_ball_le g
    _ = 2 ^ 2 ^ n * 4 ^ 2 ^ n := by
        rw [sum_const, card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Численная оценка: `n² 2^M ≤ 3^{M − M/4}` при `n = j + 8`, `M = 2^{n−1}`. -/
lemma nat_key (j : ℕ) :
    (j + 7 + 1) ^ 2 * 2 ^ 2 ^ (j + 7) ≤ 3 ^ (2 ^ (j + 7) - 2 ^ (j + 7) / 4) := by
  obtain ⟨b, hb⟩ : ∃ b, b = 16 * 2 ^ j := ⟨_, rfl⟩
  have hM : 2 ^ (j + 7) = 8 * b := by rw [hb, pow_add]; ring
  have hM4 : 2 ^ (j + 7) - 2 ^ (j + 7) / 4 = 6 * b := by rw [hM]; omega
  rw [hM4, hM]
  have hj : (j + 7 + 1) ^ 2 ≤ 2 ^ b := by
    have h1 : j + 7 + 1 < 2 ^ (j + 7 + 1) := Nat.lt_two_pow_self
    have h2 : (j + 7 + 1) ^ 2 ≤ 2 ^ (2 * (j + 7 + 1)) := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left h1.le 2
    have h3 : 2 * (j + 7 + 1) ≤ b := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      omega
    exact h2.trans (Nat.pow_le_pow_right (by norm_num) h3)
  calc (j + 7 + 1) ^ 2 * 2 ^ (8 * b) ≤ 2 ^ b * 2 ^ (8 * b) := Nat.mul_le_mul_right _ hj
    _ = (2 ^ 9) ^ b := by rw [← pow_add, ← pow_mul]; ring_nf
    _ ≤ (3 ^ 6) ^ b := Nat.pow_le_pow_left (by norm_num) b
    _ = 3 ^ (6 * b) := (pow_mul 3 6 b).symm

/-- При `n ≥ 8`: `n² |bad_t| ≤ 2^N`. -/
lemma n2_card_badT_le (j : ℕ) (t : Fin (j + 7 + 1)) :
    (j + 7 + 1) ^ 2 * (badT (j + 7 + 1) t).card ≤ 2 ^ 2 ^ (j + 7 + 1) := by
  have h1 := card_badT_le (j + 7) t
  have h2 := nat_key j
  have hM : 2 ^ 2 ^ (j + 7 + 1) = 4 ^ 2 ^ (j + 7) := by
    rw [pow_succ 2 (j + 7), pow_mul', show (2 : ℕ) ^ 2 = 4 by norm_num]
  rw [hM]
  set M := 2 ^ (j + 7)
  set B := (badT (j + 7 + 1) t).card
  have hpos : 0 < 2 ^ M := by positivity
  have h3 : (j + 7 + 1) ^ 2 * B * 2 ^ M ≤ 4 ^ M * 2 ^ M :=
    calc (j + 7 + 1) ^ 2 * B * 2 ^ M = B * ((j + 7 + 1) ^ 2 * 2 ^ M) := by ring
      _ ≤ B * 3 ^ (M - M / 4) := Nat.mul_le_mul_left _ h2
      _ ≤ 2 ^ M * 4 ^ M := h1
      _ = 4 ^ M * 2 ^ M := by ring
  exact Nat.le_of_mul_le_mul_right h3 hpos

/-- Функция хорошая: `4 D_t(f) > N` при всех `t`. -/
def GoodF (n : ℕ) (F : (Fin n → Bool) → Fin 1 → Bool) : Prop :=
  ∀ t, 2 ^ n < 4 * dif (fun x => F x 0) t

/-- При `n ≥ 8` доля хороших функций не меньше `1 − 1/n`. -/
theorem frac_goodF (n : ℕ) (hn : 8 ≤ n) : 1 - 1 / (n : ℝ) ≤ frac n (Fin 1) (GoodF n) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 + 1 := ⟨n - 8, by omega⟩
  set n' := j + 7 + 1 with hn'
  let B : Finset ((Fin n' → Bool) → Fin 1 → Bool) := univ.biUnion fun t => badT n' t
  apply frac_ge_of_cover (GoodF n') B
  · intro F hF
    simp only [GoodF, not_forall, not_lt] at hF
    obtain ⟨t, ht⟩ := hF
    exact mem_biUnion.mpr ⟨t, mem_univ _, by simp [badT, ht]⟩
  · have hcard : B.card * n' ≤ 2 ^ 2 ^ n' := by
      have hsum : B.card ≤ ∑ t : Fin n', (badT n' t).card := card_biUnion_le
      have hn0 : 0 < n' := by omega
      have h2 : (∑ t : Fin n', (badT n' t).card) * n' * n' ≤ 2 ^ 2 ^ n' * n' :=
        calc (∑ t : Fin n', (badT n' t).card) * n' * n'
            = ∑ t : Fin n', n' ^ 2 * (badT n' t).card := by
              rw [sum_mul, sum_mul]; exact sum_congr rfl fun t _ => by ring
          _ ≤ ∑ _t : Fin n', 2 ^ 2 ^ n' := sum_le_sum fun t _ => n2_card_badT_le j t
          _ = 2 ^ 2 ^ n' * n' := by
              rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
      have h3 := Nat.le_of_mul_le_mul_right h2 hn0
      exact (Nat.mul_le_mul_right _ hsum).trans h3
    have htot : (Fintype.card ((Fin n' → Bool) → Fin 1 → Bool) : ℝ) = 2 ^ 2 ^ n' := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_one]
      push_cast; ring
    rw [htot]
    have hn0 : (0 : ℝ) < n' := by positivity
    have hc : ((B.card * n' : ℕ) : ℝ) ≤ ((2 ^ 2 ^ n' : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at hc
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hn0]
    linarith

end Infl

end PowerActivity
