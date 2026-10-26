import PowerActivity.ApxCount
import PowerActivity.ApxEnt
import PowerActivity.ApxBuild

/-!
# Приближённая сложность: итог (`approx-hard`, `cut-compress`)

* `approxHard_goal : ApproxHardGoal` (доказана в модуле `ApxCount`): `a = 1/64`, доля исключений
  `≤ 2^{-n}` при `n ≥ 10`;
* `cutCompress_goal : CutCompressGoal`: `C₄ = 12` (схема: 3 элемента констант и по
  `|I_d| + 2|R_d| + 2 ≤ 9 b_d` элементов на каждое значение `z` из типичного множества
  `T`, `|T| ≤ 2^{4H_d}`);
* формы с `L14`: `cutCompress_L14` (`cut-compress`) и `approxHard_L14…` (`approx-hard`; `L14 F` —
  инфимум по непустому множеству, поэтому нужна хотя бы одна приближающая схема, например
  реализация).
-/

namespace PowerActivity

open Finset Filter Topology Apx

/-- Продолжение назначения проводам разреза до всех пар `(i, t)`. -/
noncomputable def Apx.extZ {n : ℕ} (C : Circ n (Fin 1)) (d : ℕ) (z : C.cut d → Bool) :
    ℕ × ℕ → Bool :=
  fun e => if h : e ∈ C.cut d then z ⟨e, h⟩ else false

/-- **`cut-compress`** с `C₄ = 12`. -/
theorem cutCompress_goal : CutCompressGoal := by
  refine ⟨12, ?_⟩
  intro n hn C hdeg F hF d
  obtain ⟨T, hTcard, hTprob⟩ := exists_typical (C.cutVal d)
  obtain ⟨C', hs, heval⟩ := build C d hn (T.toList.map (extZ C d))
  refine ⟨C', ?_, ?_⟩
  · -- совпадение с `f` на наборах с `Z_d(x) ∈ T`
    unfold Approx14
    refine le_trans hTprob (Nat.mul_le_mul_left 4 (card_le_card ?_))
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have hFx : F x 0 = C.sig x (C.out 0) := by rw [← hF x]; rfl
    have hiff : C'.eval x 0 = true ↔ C.sig x (C.out 0) = true := by
      rw [heval x]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨⟨extZ C d (C.cutVal d x), List.mem_map.2 ⟨_, mem_toList.2 hx, rfl⟩, ?_⟩, h⟩
        intro e he
        simp [extZ, he, Circ.cutVal]
    rw [hFx]
    exact Bool.eq_iff_iff.2 hiff
  · -- размер
    rw [hs]
    have hI := card_inner_le C d
    have hR := card_cut_le C d hdeg
    have hB := one_le_card_fwdBall C d hn
    have hlen : (T.toList.map (extZ C d)).length = T.card := by simp
    rw [hlen]
    have hnat : 3 + T.card * ((inner C d).card + 2 * (C.cut d).card + 2) ≤
        3 + T.card * (9 * (C.fwdBall d).card) := by
      have : (inner C d).card + 2 * (C.cut d).card + 2 ≤ 9 * (C.fwdBall d).card := by omega
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) 3
    have hH : 0 ≤ ent (C.cutVal d) := ent_nonneg _
    have hP : (1 : ℝ) ≤ 2 ^ (4 * ent (C.cutVal d)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hBr : (1 : ℝ) ≤ (C.fwdBall d).card := by exact_mod_cast hB
    have hcast : ((3 + T.card * ((inner C d).card + 2 * (C.cut d).card + 2) : ℕ) : ℝ) ≤
        3 + (T.card : ℝ) * (9 * (C.fwdBall d).card) := by
      have := (Nat.cast_le (α := ℝ)).2 hnat
      push_cast at this ⊢
      linarith
    have e1 : (3 : ℝ) ≤ 3 * (C.fwdBall d).card * 2 ^ (4 * ent (C.cutVal d)) := by nlinarith
    have e2 : (T.card : ℝ) * (9 * (C.fwdBall d).card) ≤
        2 ^ (4 * ent (C.cutVal d)) * (9 * (C.fwdBall d).card) :=
      mul_le_mul_of_nonneg_right hTcard (by positivity)
    nlinarith

/-- Реализация приближает функцию (совпадает на всех `N` наборах). -/
lemma Apx.approx14_of_realizes {n : ℕ} {C : Circ n (Fin 1)}
    {F : (Fin n → Bool) → Fin 1 → Bool} (h : C.Realizes F) : Approx14 C F := by
  unfold Approx14
  have : (univ.filter fun x => C.eval x 0 = F x 0) = univ := by
    ext x; simp [h x]
  rw [this, card_univ]
  simp

/-- `cut-compress` в терминах `L_{1/4}`: `L_{1/4}(f) ≤ C₄ b_d 2^{4H_d}` (`C₄ = 12`). -/
theorem cutCompress_L14 : ∃ C₄ : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ C : Circ n (Fin 1),
    (∀ j, C.outdeg j ≤ 3) → ∀ F, C.Realizes F → ∀ d : ℕ,
      (L14 F : ℝ) ≤ C₄ * (C.fwdBall d).card * (2 : ℝ) ^ (4 * ent (C.cutVal d)) := by
  obtain ⟨C₄, h⟩ := cutCompress_goal
  refine ⟨C₄, fun n hn C hdeg F hF d => ?_⟩
  obtain ⟨C', hA, hs⟩ := h n hn C hdeg F hF d
  have : L14 F ≤ C'.s := Nat.sInf_le ⟨C', rfl, hA⟩
  calc (L14 F : ℝ) ≤ C'.s := by exact_mod_cast this
    _ ≤ _ := hs

/-- Монотонность доли. -/
lemma Apx.frac_mono {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    {P Q : ((Fin n → Bool) → κ → Bool) → Prop} (h : ∀ F, P F → Q F) :
    frac n κ P ≤ frac n κ Q := by
  unfold frac
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun F : {F // P F} => (⟨F.1, h _ F.2⟩ : {F // Q F}))
    (by
      intro F G hFG
      apply Subtype.ext
      have := congrArg Subtype.val hFG
      exact this)

/-- `approx-hard` в терминах `L_{1/4}`: для почти всех `f`, у которых есть хоть одна
приближающая схема (например, реализация), `L_{1/4}(f) ≥ a 2ⁿ/n` (`a = 1/64`). -/
theorem approxHard_L14 : ∃ a : ℝ, 0 < a ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ,
    1 - ε n ≤ frac n (Fin 1) fun F =>
      (∃ C : Circ n (Fin 1), Approx14 C F) → a * 2 ^ n / n ≤ (L14 F : ℝ) := by
  obtain ⟨a, ha, ε, hε, h⟩ := approxHard_goal
  refine ⟨a, ha, ε, hε, fun n => le_trans (h n) (frac_mono ?_)⟩
  intro F hF hex
  have hne : {s | ∃ C : Circ n (Fin 1), C.s = s ∧ Approx14 C F}.Nonempty := by
    obtain ⟨C, hC⟩ := hex
    exact ⟨C.s, C, rfl, hC⟩
  obtain ⟨C, hCs, hCA⟩ := Nat.sInf_mem hne
  unfold L14
  rw [← hCs]
  exact hF C hCA

/-- `approx-hard` для функций с реализацией. -/
theorem approxHard_L14_of_realizes : ∃ a : ℝ, 0 < a ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ n : ℕ, 1 - ε n ≤ frac n (Fin 1) fun F =>
      ∀ C : Circ n (Fin 1), C.Realizes F → a * 2 ^ n / n ≤ (L14 F : ℝ) := by
  obtain ⟨a, ha, ε, hε, h⟩ := approxHard_L14
  exact ⟨a, ha, ε, hε, fun n => le_trans (h n) (frac_mono fun F hF C hC =>
    hF ⟨C, approx14_of_realizes hC⟩)⟩

/-- `approx-hard` без оговорок, если каждый оператор реализуем (цель `ExistsGoal`):
для почти всех `f` выполнено `L_{1/4}(f) ≥ a 2ⁿ/n` (при `n = 0` правая часть равна `0`). -/
theorem approxHard_L14_of_exists (hex : ExistsGoal) : ∃ a : ℝ, 0 < a ∧ ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 1 - ε n ≤ frac n (Fin 1) fun F =>
      a * 2 ^ n / n ≤ (L14 F : ℝ) := by
  obtain ⟨a, ha, ε, hε, h⟩ := approxHard_L14
  refine ⟨a, ha, ε, hε, fun n => le_trans (h n) (frac_mono fun F hF => ?_)⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨C, hC⟩ := hex n 1 hn F
    exact hF ⟨C, approx14_of_realizes hC⟩

end PowerActivity

#print axioms PowerActivity.approxHard_goal
#print axioms PowerActivity.cutCompress_goal
#print axioms PowerActivity.cutCompress_L14
#print axioms PowerActivity.approxHard_L14
#print axioms PowerActivity.approxHard_L14_of_realizes
#print axioms PowerActivity.approxHard_L14_of_exists
