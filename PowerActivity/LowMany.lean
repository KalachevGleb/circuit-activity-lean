import PowerActivity.LowParity
import PowerActivity.LowEnt

/-!
# Много выходов: `E(Σ) ≥ m/4` для некоторого оператора при `m ≤ 2^{2^n}` (`many-outputs`)

Доказательство: `heavy n` — непроекции веса `≥ N/2`.
Их не меньше `2^{N−1}` (`card_heavy`): отображение `f ↦ f`, если `f ∈ heavy`, и `f ↦ ¬f` иначе,
переводит все функции в `heavy` и склеивает не более двух (`f` и `¬f`); здесь используется,
что `¬x_i` — непроекция веса `N/2`, а проекции имеют вес `N/2`.
Берём `K = min{m, |heavy|}` функций из `heavy` координатами оператора (остальные координаты —
повторы). Разные непроекции реализуются разными элементами, поэтому
`E(Σ,x) ≥ #{j : f_j(x) = 1}` и `E(Σ) ≥ K/2 ≥ m/4`.

* `many_out` — при любом `n` (достаточно `n ≥ 0`), `1 ≤ m ≤ 2^{2^n}`
  (итог `manyOut_goal : ManyOutGoal` — в `LowMain`).
-/

namespace PowerActivity

open Finset

namespace Low

/-- Булевы функции `n` переменных. -/
abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool

/-- Проекция `x_t`. -/
def proj {n : ℕ} (t : Fin n) : Fn n := fun x => x t

/-- Функция — проекция. -/
def IsProj {n : ℕ} (f : Fn n) : Prop := ∃ t, f = proj t

lemma wt_add_wt_not {n : ℕ} (f : Fn n) : wt f + wt (fun x => !f x) = 2 ^ n := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n → Bool)))
    (fun x => f x = true)
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  unfold wt
  rw [← h]
  congr 2
  ext x
  simp

lemma wt_proj_eq {n : ℕ} (t : Fin n) : wt (proj t) = wt (fun x => !proj t x) := by
  unfold wt proj
  simp only [card_filter]
  rw [← Equiv.sum_comp (flipPerm t)]
  apply sum_congr rfl
  intro x _
  simp [flipPerm, flip]

lemma two_wt_not_proj {n : ℕ} (t : Fin n) : 2 * wt (fun x => !proj t x) = 2 ^ n := by
  have h1 := wt_add_wt_not (proj t)
  rw [wt_proj_eq] at h1
  omega

lemma not_proj_not_isProj {n : ℕ} (t : Fin n) : ¬ IsProj (fun x => !proj t x) := by
  rintro ⟨t', h⟩
  have := congrFun h (fun _ => false)
  simp [proj] at this

open Classical in
/-- Непроекции веса `≥ N/2`. -/
noncomputable def heavy (n : ℕ) : Finset (Fn n) :=
  univ.filter fun f => ¬ IsProj f ∧ 2 ^ n ≤ 2 * wt f

lemma mem_heavy {n : ℕ} {f : Fn n} : f ∈ heavy n ↔ ¬ IsProj f ∧ 2 ^ n ≤ 2 * wt f := by
  classical
  unfold heavy
  rw [mem_filter]
  simp

open Classical in
/-- Канонический представитель пары `{f, ¬f}` в `heavy`. -/
noncomputable def psi {n : ℕ} (f : Fn n) : Fn n := if f ∈ heavy n then f else fun x => !f x

lemma psi_mem {n : ℕ} (f : Fn n) : psi f ∈ heavy n := by
  classical
  unfold psi
  split_ifs with hf
  · exact hf
  · rw [mem_heavy] at hf ⊢
    have hw := wt_add_wt_not f
    by_cases hp : IsProj f
    · obtain ⟨t, rfl⟩ := hp
      exact ⟨not_proj_not_isProj t, (two_wt_not_proj t).ge⟩
    · have hlt : 2 * wt f < 2 ^ n := by
        by_contra hc; exact hf ⟨hp, by omega⟩
      refine ⟨?_, by omega⟩
      rintro ⟨t, ht⟩
      have hf' : f = fun x => !proj t x := by
        funext x; have := congrFun ht x; rw [← this]; simp
      have := two_wt_not_proj t
      rw [← hf'] at this
      omega

lemma psi_fiber {n : ℕ} (f g : Fn n) (h : psi f = g) : f = g ∨ f = fun x => !g x := by
  classical
  unfold psi at h
  split_ifs at h
  · exact Or.inl h
  · right; rw [← h]; funext x; simp

/-- `|heavy| ≥ 2^{N−1}`: `2^N ≤ 2 |heavy|`. -/
theorem card_heavy (n : ℕ) : 2 ^ 2 ^ n ≤ 2 * (heavy n).card := by
  classical
  have h1 := card_le_mul_card_image (univ : Finset (Fn n)) 2 (f := psi) (by
    intro g _
    calc (univ.filter fun f => psi f = g).card ≤ ({g, fun x => !g x} : Finset (Fn n)).card := by
          apply card_le_card
          intro f hf
          rw [mem_filter] at hf
          rcases psi_fiber f g hf.2 with h | h <;> simp [h]
      _ ≤ 2 := card_le_two)
  have h2 : (univ.image (psi (n := n))).card ≤ (heavy n).card := by
    apply card_le_card
    intro g hg
    obtain ⟨f, _, rfl⟩ := mem_image.mp hg
    exact psi_mem f
  have h3 : (univ : Finset (Fn n)).card = 2 ^ 2 ^ n := by simp
  omega

/-- **`many-outputs`.** При `1 ≤ m ≤ 2^{2^n}` есть оператор, у которого любая схема
имеет `E(Σ) ≥ m/4`. -/
theorem many_out (n m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 2 ^ n) :
    ∃ F : (Fin n → Bool) → Fin m → Bool, ∀ C : Circ n (Fin m), C.Realizes F →
      (m : ℝ) / 4 ≤ C.Eav := by
  classical
  have hH := card_heavy n
  obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq (min_le_right m (heavy n).card)
  have hpow : 1 ≤ 2 ^ 2 ^ n := Nat.one_le_two_pow
  have hSpos : 0 < S.card := by
    rw [hScard]; apply lt_min (by omega); omega
  have hSm : S.card ≤ m := hScard ▸ min_le_left _ _
  set e := S.equivFin
  -- оператор: координата `k` — функция с номером `k mod |S|`
  let F : (Fin n → Bool) → Fin m → Bool := fun x k =>
    ((e.symm ⟨(k : ℕ) % S.card, Nat.mod_lt _ hSpos⟩ : S) : Fn n) x
  refine ⟨F, fun C hC => ?_⟩
  -- номер выхода для `g ∈ S`
  let kOf : Fn n → Fin m := fun g =>
    if hg : g ∈ S then ⟨(e ⟨g, hg⟩ : ℕ), lt_of_lt_of_le (e ⟨g, hg⟩).2 hSm⟩ else ⟨0, hm1⟩
  have hF_kOf : ∀ g ∈ S, ∀ x, F x (kOf g) = g x := by
    intro g hg x
    simp only [F, kOf, hg, dite_true]
    have : (⟨((e ⟨g, hg⟩ : Fin S.card) : ℕ) % S.card, Nat.mod_lt _ hSpos⟩ : Fin S.card) =
        e ⟨g, hg⟩ := Fin.ext (Nat.mod_eq_of_lt (e ⟨g, hg⟩).2)
    rw [this, Equiv.symm_apply_apply]
  have hsig : ∀ g ∈ S, ∀ x, C.sig x (C.out (kOf g)) = g x := by
    intro g hg x
    have := congrFun (hC x) (kOf g)
    simp only [Circ.eval] at this
    rw [this, hF_kOf g hg x]
  have hout : ∀ g ∈ S, n ≤ C.out (kOf g) := by
    intro g hg
    by_contra hlt
    push Not at hlt
    apply (mem_heavy.mp (hSsub hg)).1
    refine ⟨⟨C.out (kOf g), hlt⟩, ?_⟩
    funext x
    rw [← hsig g hg x]
    simp [Circ.sig, sig_lt _ _ hlt, proj]
  -- элемент, реализующий `g`
  let idx : Fn n → ℕ := fun g => C.out (kOf g) - n
  have hval : ∀ g ∈ S, ∀ x, C.val x (idx g) = g x := by
    intro g hg x
    simp only [Circ.val, idx]
    rw [show n + (C.out (kOf g) - n) = C.out (kOf g) by have := hout g hg; omega, hsig g hg x]
  have hidx_lt : ∀ g ∈ S, idx g < C.s := by
    intro g hg
    have := C.out_lt (kOf g)
    have := hout g hg
    simp only [idx, Circ.s]
    omega
  have hinj : Set.InjOn idx S := by
    intro g hg g' hg' h
    funext x
    rw [← hval g hg x, ← hval g' hg' x, h]
  -- `E(Σ,x) ≥ #{g ∈ S : g(x) = 1}`
  have hE : ∀ x, (S.filter fun g => g x = true).card ≤ C.E x := by
    intro x
    unfold Circ.E
    apply card_le_card_of_injOn idx
    · intro g hg
      have hg' := mem_filter.mp hg
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range]
      exact ⟨hidx_lt g hg'.1, by rw [hval g hg'.1 x]; exact hg'.2⟩
    · intro g hg g' hg' h
      exact hinj (mem_filter.mp hg).1 (mem_filter.mp hg').1 h
  have hsum : S.card * 2 ^ n ≤ 2 * ∑ x, C.E x := by
    calc S.card * 2 ^ n = ∑ _g ∈ S, 2 ^ n := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ g ∈ S, 2 * wt g := by
          apply sum_le_sum; intro g hg; exact (mem_heavy.mp (hSsub hg)).2
      _ = 2 * ∑ x, (S.filter fun g => g x = true).card := by
          rw [← mul_sum]; congr 1
          unfold wt
          simp only [card_filter]
          rw [sum_comm]
      _ ≤ 2 * ∑ x, C.E x := Nat.mul_le_mul_left _ (sum_le_sum fun x _ => hE x)
  have hSm2 : m ≤ 2 * S.card := by
    rw [hScard]
    rcases le_total m (heavy n).card with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  unfold Circ.Eav avgM
  rw [le_div_iff₀ (by positivity)]
  have h1 : ((S.card * 2 ^ n : ℕ) : ℝ) ≤ ((2 * ∑ x, C.E x : ℕ) : ℝ) := by exact_mod_cast hsum
  have h2 : (m : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hSm2
  push_cast at h1
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

end Low

end PowerActivity
