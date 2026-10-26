import PowerActivity.Spec

/-!
# Сборка промежуточных теорем из целей

* общие факты о функциях Шеннона: `opMeas_le`, `le_opMeas`, `shMeas_mono`, `le_shMeas_of`,
  `shMeas_le_of`; о доле `frac`: `exists_of_frac_pos`, `frac_le_one`, `frac_mono`;
* `Circ.withOut` — та же схема с другими выходами (меры не меняются);
* насыщение (`saturation`): `upper_sat` (удаление повторов), `lower_pad` (дополнение повторами);
* `powerBound_of`, `activityBound_of`, `powerBoundGeneral_of` — промежуточные теоремы
  `PowerBound`, `ActivityBound` и `WireBound`, `PowerBoundGeneral` из целей `Spec`.
-/

namespace PowerActivity

open Finset Filter Topology

/-! ## Средняя и максимальная меры -/

lemma avgM_le_maxM {n : ℕ} (μ : (Fin n → Bool) → ℕ) : avgM μ ≤ maxM μ := by
  unfold avgM maxM
  rw [div_le_iff₀ (by positivity)]
  calc ∑ x, (μ x : ℝ) ≤ ∑ _x : Fin n → Bool, ((univ.sup μ : ℕ) : ℝ) := by
        gcongr with x; exact_mod_cast Finset.le_sup (f := μ) (Finset.mem_univ x)
    _ = (univ.sup μ : ℕ) * 2 ^ n := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, mul_comm]

lemma avgM_nonneg {n : ℕ} (μ : (Fin n → Bool) → ℕ) : 0 ≤ avgM μ := by
  unfold avgM; positivity

lemma maxM_le {n : ℕ} {μ : (Fin n → Bool) → ℕ} {b : ℝ} (h : ∀ x, (μ x : ℝ) ≤ b) :
    (maxM μ : ℝ) ≤ b := by
  unfold maxM
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin n → Bool)) univ_nonempty μ
  rw [hx]; exact h x

/-! ## Функции Шеннона -/

section Shannon

variable {n : ℕ} {κ : Type}

lemma opMeas_le {μ : Circ n κ → ℝ} (hμ : ∀ C, 0 ≤ μ C) {F : (Fin n → Bool) → κ → Bool}
    {C : Circ n κ} (hC : C.Realizes F) : opMeas μ F ≤ μ C := by
  unfold opMeas
  exact ciInf_le ⟨0, by rintro _ ⟨C', rfl⟩; exact hμ C'.1⟩
    (⟨C, hC⟩ : {C : Circ n κ // C.Realizes F})

lemma le_opMeas {μ : Circ n κ → ℝ} {F : (Fin n → Bool) → κ → Bool} {b : ℝ}
    (hne : ∃ C : Circ n κ, C.Realizes F) (hb : ∀ C : Circ n κ, C.Realizes F → b ≤ μ C) :
    b ≤ opMeas μ F := by
  unfold opMeas
  obtain ⟨C, hC⟩ := hne
  haveI : Nonempty {C : Circ n κ // C.Realizes F} := ⟨⟨C, hC⟩⟩
  exact le_ciInf fun C => hb C.1 C.2

lemma opMeas_mono {μ ν : Circ n κ → ℝ} (hμ : ∀ C, 0 ≤ μ C) (h : ∀ C, μ C ≤ ν C)
    (F : (Fin n → Bool) → κ → Bool) : opMeas μ F ≤ opMeas ν F := by
  unfold opMeas
  rcases isEmpty_or_nonempty {C : Circ n κ // C.Realizes F} with he | he
  · simp [Real.iInf_of_isEmpty]
  · exact ciInf_mono ⟨0, by rintro _ ⟨C', rfl⟩; exact hμ C'.1⟩ fun C => h C.1

lemma opMeas_le_shMeas {m : ℕ} (μ : Circ n (Fin m) → ℝ) (F : (Fin n → Bool) → Fin m → Bool) :
    opMeas μ F ≤ shMeas n m μ := by
  unfold shMeas
  exact le_ciSup (Set.finite_range _).bddAbove F

lemma shMeas_le {m : ℕ} {μ : Circ n (Fin m) → ℝ} {b : ℝ} (h : ∀ F, opMeas μ F ≤ b) :
    shMeas n m μ ≤ b := by
  unfold shMeas; exact ciSup_le h

lemma shMeas_mono {m : ℕ} {μ ν : Circ n (Fin m) → ℝ} (hμ : ∀ C, 0 ≤ μ C)
    (h : ∀ C, μ C ≤ ν C) : shMeas n m μ ≤ shMeas n m ν := by
  unfold shMeas
  exact ciSup_mono (Set.finite_range _).bddAbove fun F => opMeas_mono hμ h F

lemma le_shMeas_of {m : ℕ} {μ : Circ n (Fin m) → ℝ} {b : ℝ} (hE : ExistsGoal) (hn : 1 ≤ n)
    (F : (Fin n → Bool) → Fin m → Bool) (hb : ∀ C : Circ n (Fin m), C.Realizes F → b ≤ μ C) :
    b ≤ shMeas n m μ :=
  (le_opMeas (hE n m hn F) hb).trans (opMeas_le_shMeas μ F)

lemma shMeas_le_of {m : ℕ} {μ : Circ n (Fin m) → ℝ} {b : ℝ} (hμ : ∀ C, 0 ≤ μ C)
    (h : ∀ F, ∃ C : Circ n (Fin m), C.Realizes F ∧ μ C ≤ b) : shMeas n m μ ≤ b :=
  shMeas_le fun F => by
    obtain ⟨C, hC, hb⟩ := h F
    exact (opMeas_le hμ hC).trans hb

lemma EavSh_le_EmaxSh (n m : ℕ) : EavSh n m ≤ EmaxSh n m :=
  shMeas_mono (fun C => avgM_nonneg C.E) fun C => avgM_le_maxM C.E

lemma PavSh_le_PmaxSh (n m : ℕ) : PavSh n m ≤ PmaxSh n m :=
  shMeas_mono (fun C => avgM_nonneg C.P) fun C => avgM_le_maxM C.P

lemma UavSh_le_UmaxSh (n m : ℕ) : UavSh n m ≤ UmaxSh n m :=
  shMeas_mono (fun C => avgM_nonneg C.U) fun C => avgM_le_maxM C.U

end Shannon

/-! ## Доля операторов -/

section Frac

variable {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

lemma exists_of_frac_pos {Q : ((Fin n → Bool) → κ → Bool) → Prop} (h : 0 < frac n κ Q) :
    ∃ F, Q F := by
  unfold frac at h
  by_contra hne
  push_neg at hne
  have h0 : Nat.card {F // Q F} = 0 := by
    rw [Nat.card_eq_zero]; left; exact ⟨fun ⟨F, hF⟩ => hne F hF⟩
  simp [h0] at h

lemma frac_le_one (Q : ((Fin n → Bool) → κ → Bool) → Prop) : frac n κ Q ≤ 1 := by
  unfold frac
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast Finite.card_subtype_le Q

lemma frac_mono {Q Q' : ((Fin n → Bool) → κ → Bool) → Prop} (h : ∀ F, Q F → Q' F) :
    frac n κ Q ≤ frac n κ Q' := by
  unfold frac
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.card_le_card_of_injective
    (fun F : {F // Q F} => (⟨F.1, h F.1 F.2⟩ : {F // Q' F}))
    (fun a b hab => Subtype.ext (by
      have := congrArg (fun F : {F // Q' F} => F.1) hab
      simpa using this))

end Frac

/-- Если доля не меньше `1 - ε n`, `ε → 0`, то доля стремится к единице. -/
lemma tendsto_frac {κ : Type} [Fintype κ] [DecidableEq κ]
    {Q : (n : ℕ) → ((Fin n → Bool) → κ → Bool) → Prop} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ n, 1 - ε n ≤ frac n κ (Q n)) :
    Tendsto (fun n => frac n κ (Q n)) atTop (𝓝 1) := by
  have hl : Tendsto (fun n => 1 - ε n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds h
    fun n => frac_le_one (Q n)

/-- Из `ε → 0` — порог, начиная с которого `ε n < 1`. -/
lemma eventually_lt_one {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ε n < 1 :=
  Filter.eventually_atTop.mp (hε.eventually (gt_mem_nhds zero_lt_one))

/-! ## Та же схема с другими выходами -/

namespace Circ

variable {n : ℕ} {κ κ' : Type}

/-- Схема `C` с выходами `o` (элементы те же). -/
def withOut (C : Circ n κ) (o : κ' → ℕ) (ho : ∀ k, o k < n + C.gates.length) : Circ n κ' where
  gates := C.gates
  valid := C.valid
  out := o
  out_lt := ho

@[simp] lemma withOut_E (C : Circ n κ) (o : κ' → ℕ) (ho) : (C.withOut o ho).E = C.E := rfl
@[simp] lemma withOut_Eav (C : Circ n κ) (o : κ' → ℕ) (ho) : (C.withOut o ho).Eav = C.Eav := rfl
@[simp] lemma withOut_Emax (C : Circ n κ) (o : κ' → ℕ) (ho) : (C.withOut o ho).Emax = C.Emax := rfl
@[simp] lemma withOut_sig (C : Circ n κ) (o : κ' → ℕ) (ho) : (C.withOut o ho).sig = C.sig := rfl

end Circ

/-! ## Насыщение (`saturation`) -/

lemma card_boolfun (n : ℕ) : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Удаление повторов: оператор с `m` выходами получается из оператора `F'` со всеми
`2^{2^n}` функциями переименованием выходов; мощность схемы та же. -/
lemma upper_sat {n m : ℕ} (F : (Fin n → Bool) → Fin m → Bool) :
    ∃ (F' : (Fin n → Bool) → Fin (2 ^ 2 ^ n) → Bool),
      ∀ C' : Circ n (Fin (2 ^ 2 ^ n)), C'.Realizes F' →
        ∃ C : Circ n (Fin m), C.Realizes F ∧ C.E = C'.E := by
  let e : ((Fin n → Bool) → Bool) ≃ Fin (2 ^ 2 ^ n) := Fintype.equivFinOfCardEq (card_boolfun n)
  refine ⟨fun x i => (e.symm i) x, fun C' hC' => ?_⟩
  refine ⟨C'.withOut (fun j => C'.out (e fun x => F x j)) (fun j => C'.out_lt _), ?_, rfl⟩
  intro x
  funext j
  have h := congrFun (hC' x) (e fun x => F x j)
  simp only [Circ.eval] at h
  show C'.sig x (C'.out (e fun x => F x j)) = F x j
  rw [h, Equiv.symm_apply_apply]

/-- Дополнение повторами: схема оператора `F` с `m ≥ M` выходами, повторяющего `F'`, даёт схему
`F'` с той же мощностью. -/
lemma lower_pad {n m M : ℕ} (hM : 1 ≤ M) (hMm : M ≤ m) (F' : (Fin n → Bool) → Fin M → Bool) :
    ∃ F : (Fin n → Bool) → Fin m → Bool,
      ∀ C : Circ n (Fin m), C.Realizes F → ∃ C' : Circ n (Fin M), C'.Realizes F' ∧ C'.E = C.E := by
  refine ⟨fun x j => F' x (if h : j.1 < M then ⟨j.1, h⟩ else ⟨0, hM⟩), fun C hC => ?_⟩
  refine ⟨C.withOut (fun i : Fin M => C.out ⟨i.1, lt_of_lt_of_le i.2 hMm⟩) (fun i => C.out_lt _),
    ?_, rfl⟩
  intro x
  funext i
  have h := congrFun (hC x) ⟨i.1, lt_of_lt_of_le i.2 hMm⟩
  simp only [Circ.eval] at h
  show C.sig x (C.out ⟨i.1, lt_of_lt_of_le i.2 hMm⟩) = F' x i
  rw [h]
  simp [i.2]

/-! ## Арифметика -/

lemma one_le_logb_succ {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Real.logb 2 ((n : ℝ) + 1) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num; linarith

lemma logb_succ_nonneg (n : ℕ) : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
  Real.logb_nonneg (by norm_num) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

/-- `⌈log₂ r⌉ ≤ 2 log₂(n+1)` при `1 ≤ r ≤ n`. -/
lemma clog_le_two_logb {r n : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    (Nat.clog 2 r : ℝ) ≤ 2 * Real.logb 2 ((n : ℝ) + 1) := by
  have hL := one_le_logb_succ (le_trans hr hrn)
  rcases Nat.lt_or_ge r 2 with h | h
  · have : r = 1 := by omega
    subst this; simp; linarith
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < r)
    have hcpos : 1 ≤ Nat.clog 2 r := Nat.clog_pos (by norm_num) (by omega)
    have hk : ((Nat.clog 2 r - 1 : ℕ) : ℝ) < Real.logb 2 ((n : ℝ) + 1) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
      rw [Real.rpow_natCast]
      have h1 : ((2 : ℕ) ^ (Nat.clog 2 r).pred : ℕ) < r := hlt
      have h2 : ((2 ^ (Nat.clog 2 r - 1) : ℕ) : ℝ) < (r : ℝ) := by
        exact_mod_cast (show 2 ^ (Nat.clog 2 r - 1) < r from by
          simpa [Nat.pred_eq_sub_one] using h1)
      have h3 : (r : ℝ) ≤ n := by exact_mod_cast hrn
      push_cast at h2
      linarith
    have : (Nat.clog 2 r : ℝ) = ((Nat.clog 2 r - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hcpos]; ring
    linarith

/-- Оценка `block-upper` даёт порядок `n + m log(n+1)`. -/
lemma upperBlock_arith (c₀ n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    ((2 * n + c₀ + n * ((m + min m n - 1) / min m n) + m * Nat.clog 2 (min m n) : ℕ) : ℝ) ≤
      (4 + c₀) * (n + m * Real.logb 2 ((n : ℝ) + 1)) := by
  set L := Real.logb 2 ((n : ℝ) + 1) with hLdef
  have hL : 1 ≤ L := one_le_logb_succ (by omega)
  have hr1 : 1 ≤ min m n := le_min hm (by omega)
  have hrn : min m n ≤ n := min_le_right _ _
  have hdiv : n * ((m + min m n - 1) / min m n) ≤ m + n := by
    rcases le_total m n with h | h
    · rw [min_eq_left h]
      have : (m + m - 1) / m ≤ 1 := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega)]; omega
      calc n * ((m + m - 1) / m) ≤ n * 1 := Nat.mul_le_mul_left _ this
        _ ≤ m + n := by omega
    · rw [min_eq_right h]
      calc n * ((m + n - 1) / n) ≤ m + n - 1 := Nat.mul_div_le _ _
        _ ≤ m + n := by omega
  have hclog := clog_le_two_logb hr1 hrn
  have hdivR : ((n * ((m + min m n - 1) / min m n) : ℕ) : ℝ) ≤ m + n := by exact_mod_cast hdiv
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hc0 : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
  have e1 : (m : ℝ) * Nat.clog 2 (min m n) ≤ m * (2 * L) := by gcongr
  have e2 : (m : ℝ) ≤ m * L := by nlinarith
  have e3 : (c₀ : ℝ) ≤ c₀ * n := by nlinarith
  have e4 : 0 ≤ (c₀ : ℝ) * (m * L) := by positivity
  have e5 : 0 ≤ (m : ℝ) * L := by positivity
  have hcast : ((2 * n + c₀ + n * ((m + min m n - 1) / min m n) + m * Nat.clog 2 (min m n) : ℕ) : ℝ)
      = 2 * n + c₀ + ((n * ((m + min m n - 1) / min m n) : ℕ) : ℝ)
        + m * (Nat.clog 2 (min m n) : ℝ) := by push_cast; ring
  have hexp : (4 + (c₀ : ℝ)) * (n + m * L) = 4 * n + 4 * (m * L) + c₀ * n + c₀ * (m * L) := by
    ring
  rw [hcast, hexp]
  linarith

/-! ## `PowerBound` -/

theorem powerBound_of (hE : ExistsGoal) (hBlk : UpperBlockGoal) (hP : ParityGoal) (hL : LowerPowerGoal)
    (hM : ManyOutGoal) : PowerBound := by
  obtain ⟨c₀, hBlk⟩ := hBlk
  obtain ⟨c, hc, ε, hε, hfr⟩ := hL
  obtain ⟨n₀, hn₀⟩ := eventually_lt_one hε
  set Λ : ℝ := Real.logb 2 ((n₀ : ℝ) + 1) + 1 with hΛ
  have hΛpos : 0 < Λ := by have := logb_succ_nonneg n₀; linarith
  set c₁ : ℝ := min c (1 / (4 * Λ)) with hc₁
  have hc₁pos : 0 < c₁ := lt_min hc (by positivity)
  refine ⟨min (1 / 8) (c₁ / 2), 4 + c₀, lt_min (by norm_num) (by positivity), by positivity,
    fun n m hn hm hm2 => ⟨?_, EavSh_le_EmaxSh n m, ?_⟩⟩
  · -- нижняя оценка: чётность и `c₁ m log(n+1)`
    have hn1 : 1 ≤ n := by omega
    set L := Real.logb 2 ((n : ℝ) + 1) with hLdef
    have hL0 : 0 ≤ L := logb_succ_nonneg n
    have hpar : (n : ℝ) / 4 ≤ EavSh n m := by
      refine le_shMeas_of hE hn1 (fun x _ => parity x) fun C hC => ?_
      exact hP n hn (Fin m) C ⟨0, by omega⟩ fun x => by rw [hC x]
    have hlog : c₁ * m * L ≤ EavSh n m := by
      rcases le_or_gt n₀ n with h | h
      · have hpos : 0 < frac n (Fin m) fun F =>
            ∀ C : Circ n (Fin m), C.Realizes F → c * m * L ≤ C.Eav := by
          have h1 := hfr n m hm hm2
          rw [← hLdef] at h1
          have := hn₀ n h; linarith
        obtain ⟨F, hF⟩ := exists_of_frac_pos hpos
        refine le_shMeas_of hE hn1 F fun C hC => le_trans ?_ (hF C hC)
        have : c₁ ≤ c := min_le_left _ _
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hm0) hL0
      · obtain ⟨F, hF⟩ := hM n m hn hm (le_trans hm2 (Nat.pow_le_pow_right (by norm_num)
          (Nat.lt_two_pow_self).le))
        refine le_shMeas_of hE hn1 F fun C hC => le_trans ?_ (hF C hC)
        have hLΛ : L ≤ Λ := by
          have : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 ((n₀ : ℝ) + 1) := by
            apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
            have : (n : ℝ) ≤ n₀ := by exact_mod_cast h.le
            linarith
          linarith
        have hc1 : c₁ ≤ 1 / (4 * Λ) := min_le_right _ _
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        calc c₁ * m * L ≤ (1 / (4 * Λ)) * m * Λ := by gcongr
          _ = (m : ℝ) / 4 := by field_simp
    have h1 : min (1 / 8) (c₁ / 2) ≤ 1 / 8 := min_le_left _ _
    have h2 : min (1 / 8) (c₁ / 2) ≤ c₁ / 2 := min_le_right _ _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmL : 0 ≤ (m : ℝ) * L := by positivity
    calc min (1 / 8) (c₁ / 2) * (n + m * L)
        = min (1 / 8) (c₁ / 2) * n + min (1 / 8) (c₁ / 2) * (m * L) := by ring
      _ ≤ 1 / 8 * n + c₁ / 2 * (m * L) := by gcongr
      _ ≤ EavSh n m := by nlinarith
  · -- верхняя оценка `block-upper`
    refine shMeas_le_of (fun C => Nat.cast_nonneg _) fun F => ?_
    obtain ⟨C, hC, hEx⟩ := hBlk n m hn hm F
    refine ⟨C, hC, maxM_le fun x => le_trans (by exact_mod_cast hEx x) (upperBlock_arith c₀ n m hn hm)⟩

/-! ## `PowerBoundGeneral` -/

lemma Mcap_of_le {n m : ℕ} (h : m ≤ 2 ^ 2 ^ n) : Mcap n m = m := min_eq_left h

lemma Mcap_Mcap (n m : ℕ) : Mcap n (Mcap n m) = Mcap n m := by
  unfold Mcap; exact min_eq_left (min_le_right _ _)

lemma Delta_Mcap (n m : ℕ) : Delta n (Mcap n m) = Delta n m := by
  unfold Delta; rw [Mcap_Mcap]

lemma one_le_Mcap {n m : ℕ} (hm : 1 ≤ m) : 1 ≤ Mcap n m :=
  le_min hm (Nat.one_le_two_pow)

lemma logb_one_add_Delta_nonneg (n m : ℕ) : 0 ≤ Real.logb 2 (1 + Delta n m) := by
  apply Real.logb_nonneg (by norm_num)
  have : 1 ≤ Delta n m := le_max_left _ _
  linarith

theorem powerBoundGeneral_of (hE : ExistsGoal) (hGrp : UpperGroupGoal) (hP : ParityGoal)
    (hG : LowerGeneralGoal) : PowerBoundGeneral := by
  obtain ⟨K, hGrp⟩ := hGrp
  obtain ⟨c, hc, hG⟩ := hG
  refine ⟨min (1 / 8) (c / 2), max K 1, lt_min (by norm_num) (by positivity),
    lt_max_of_lt_right one_pos, fun n m hn hm => ⟨?_, EavSh_le_EmaxSh n m, ?_⟩⟩
  · have hn1 : 1 ≤ n := by omega
    set M := Mcap n m with hMdef
    set L := Real.logb 2 (1 + Delta n m) with hLdef
    have hL0 : 0 ≤ L := logb_one_add_Delta_nonneg n m
    have hM1 : 1 ≤ M := one_le_Mcap hm
    have hMm : M ≤ m := min_le_left _ _
    have hpar : (n : ℝ) / 4 ≤ EavSh n m := by
      refine le_shMeas_of hE hn1 (fun x _ => parity x) fun C hC => ?_
      exact hP n hn (Fin m) C ⟨0, by omega⟩ fun x => by rw [hC x]
    have hlog : c * M * L ≤ EavSh n m := by
      obtain ⟨F', hF'⟩ := hG n M hn hM1 (min_le_right _ _)
      obtain ⟨F, hF⟩ := lower_pad hM1 hMm F'
      refine le_shMeas_of hE hn1 F fun C hC => ?_
      obtain ⟨C', hC', hEq⟩ := hF C hC
      have h := hF' C' hC'
      have hD : Delta n M = Delta n m := Delta_Mcap n m
      have hEav : C'.Eav = C.Eav := by unfold Circ.Eav; rw [hEq]
      rw [hD, hEav] at h
      exact h
    have h1 : min (1 / 8) (c / 2) ≤ 1 / 8 := min_le_left _ _
    have h2 : min (1 / 8) (c / 2) ≤ c / 2 := min_le_right _ _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hML : 0 ≤ (M : ℝ) * L := by positivity
    calc min (1 / 8) (c / 2) * (n + M * L)
        = min (1 / 8) (c / 2) * n + min (1 / 8) (c / 2) * (M * L) := by ring
      _ ≤ 1 / 8 * n + c / 2 * (M * L) := by gcongr
      _ ≤ EavSh n m := by nlinarith
  · set M := Mcap n m with hMdef
    have hX : 0 ≤ (n : ℝ) + M * Real.logb 2 (1 + Delta n m) := by
      have := logb_one_add_Delta_nonneg n m; positivity
    refine shMeas_le_of (fun C => Nat.cast_nonneg _) fun F => ?_
    rcases le_or_gt m (2 ^ 2 ^ n) with h | h
    · obtain ⟨C, hC, hEx⟩ := hGrp n m hn hm h F
      refine ⟨C, hC, maxM_le fun x => le_trans (hEx x) ?_⟩
      rw [hMdef, Mcap_of_le h]
      rw [hMdef, Mcap_of_le h] at hX
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    · obtain ⟨F', hF'⟩ := upper_sat F
      have hMeq : M = 2 ^ 2 ^ n := min_eq_right h.le
      obtain ⟨C', hC', hEx⟩ := hGrp n (2 ^ 2 ^ n) hn Nat.one_le_two_pow le_rfl F'
      obtain ⟨C, hC, hEq⟩ := hF' C' hC'
      refine ⟨C, hC, maxM_le fun x => ?_⟩
      have hD : Delta n (2 ^ 2 ^ n) = Delta n m := by
        rw [← hMeq, hMdef, Delta_Mcap]
      have := hEx x
      rw [hD] at this
      rw [show C.E x = C'.E x by rw [hEq]]
      refine le_trans this ?_
      rw [← hMeq] at *
      push_cast
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX

/-! ## `ActivityBound` и `WireBound` -/

theorem activityBound_of (hE : ExistsGoal) (hUP : UpperPGoal) (hA : ActLowerGoal) : ActivityBound ∧ WireBound := by
  obtain ⟨K, hUP⟩ := hUP
  obtain ⟨c, hc, ε, hε, hfr⟩ := hA
  obtain ⟨n₀, hn₀⟩ := eventually_lt_one hε
  -- трудная функция при больших `n`
  have hard : ∀ n ≥ n₀, ∃ F : (Fin n → Bool) → Fin 1 → Bool, ∀ C : Circ n (Fin 1), C.Realizes F →
      c * n * Real.logb 2 n ≤ C.Uav ∧ c * n * Real.logb 2 n ≤ C.Pav := fun n hn =>
    exists_of_frac_pos (by have := hfr n; have := hn₀ n hn; linarith)
  have hK : ∀ n : ℕ, 1 ≤ n → ∀ F : (Fin n → Bool) → Fin 1 → Bool, ∃ C : Circ n (Fin 1),
      C.Realizes F ∧ ∀ x, (C.P x : ℝ) ≤ max K 1 * n ^ 2 ∧ (C.U x : ℝ) ≤ max K 1 * n ^ 2 := by
    intro n hn F
    obtain ⟨C, hC, hb⟩ := hUP n hn F
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    refine ⟨C, hC, fun x => ⟨le_trans (hb x).1 ?_, le_trans (hb x).2 ?_⟩⟩ <;>
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hn2
  refine ⟨⟨⟨c, hc, tendsto_frac hε fun n => le_trans (hfr n) (frac_mono fun F hF C hC =>
      (hF C hC).2)⟩, ⟨c, max K 1, hc, lt_max_of_lt_right one_pos, ?_⟩⟩,
    ⟨⟨c, hc, tendsto_frac hε fun n => le_trans (hfr n) (frac_mono fun F hF C hC =>
      (hF C hC).1)⟩, ⟨c, max K 1, hc, lt_max_of_lt_right one_pos, ?_⟩⟩⟩
  · filter_upwards [Filter.eventually_ge_atTop (max n₀ 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨F, hF⟩ := hard n (le_trans (le_max_left _ _) hn)
    refine ⟨le_shMeas_of hE hn1 F fun C hC => (hF C hC).2, PavSh_le_PmaxSh n 1, ?_⟩
    refine shMeas_le_of (fun C => Nat.cast_nonneg _) fun F => ?_
    obtain ⟨C, hC, hb⟩ := hK n hn1 F
    exact ⟨C, hC, maxM_le fun x => (hb x).1⟩
  · filter_upwards [Filter.eventually_ge_atTop (max n₀ 1)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨F, hF⟩ := hard n (le_trans (le_max_left _ _) hn)
    refine ⟨le_shMeas_of hE hn1 F fun C hC => (hF C hC).1, UavSh_le_UmaxSh n 1, ?_⟩
    refine shMeas_le_of (fun C => Nat.cast_nonneg _) fun F => ?_
    obtain ⟨C, hC, hb⟩ := hK n hn1 F
    exact ⟨C, hC, maxM_le fun x => (hb x).2⟩

end PowerActivity
