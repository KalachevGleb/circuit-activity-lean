import PowerActivity.LowGen
import PowerActivity.ActWires

/-!
# Тезисы, цель `LayerGoal`: обратные слои «для почти всех» операторов, меры `E` и `U`

Для `E` — `incompressible` в общей форме (`Low.incompressible_general`) с `D = ⌊Δ/4⌋` и оценкой
служебной части описания `Low.overhead_delta`, как в `Low.lower_large_delta`, но с долей вместо
существования (утверждение `large-delta`).

Для `U`: элемент слоя `L_{d+1}` (`d ≥ 0`) — источник входа некоторого элемента из `B_d`
(`exists_wire`), то есть у него есть исходящий провод; провода с разными источниками различны,
поэтому `U(Σ,x) ≥ #{i ∈ ⋃_{d ≤ D} L_{d+1} : φ_i(x) = 1}` (`card_layers_le_U`) и
`U(Σ) ≥ Σ_{d ≤ D} A_d` (`Uav_ge_sum_Ad`, аналог `layer-sum` `Low.Eav_ge_sum_Ad`).

* `Layer.good_Uav` — для хорошего оператора `U(Σ) ≥ (m/4) Σ_{d ≤ D} 1/(d+4)`;
* `Layer.layer_frac` — при `Δ > 255` доля операторов, у которых любая схема имеет
  `E, U ≥ (m/16) log(1+Δ)`, не меньше `1 − 1/n`.
-/

namespace PowerActivity

open Finset

namespace Layer

variable {n m : ℕ} (C : Circ n (Fin m))

/-- Элемент слоя `L_{d+1}` — источник некоторого провода. -/
lemma exists_wire {d i : ℕ} (hi : i ∈ C.rvLayer d) : ∃ e ∈ C.wires, C.wsrc e = n + i := by
  simp only [Circ.rvLayer, mem_sdiff] at hi
  obtain ⟨hi1, hi2⟩ := hi
  have hp : i ∈ C.rvPreds (C.rvBall d) := by
    simp only [Circ.rvBall, mem_union] at hi1
    rcases hi1 with h | h
    · exact absurd h hi2
    · exact h
  simp only [Circ.rvPreds, mem_filter] at hp
  obtain ⟨_, i', hi', hsrc⟩ := hp
  have his : i' < C.s := C.rvBall_lt hi'
  obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.mp hsrc
  refine ⟨(i', t), (Act.mem_wires C).mpr ⟨his, ht⟩, ?_⟩
  rw [Act.wsrc_eq C ht, hte]

/-- `U(Σ,x) ≥ #{i ∈ ⋃_{d ≤ D} L_{d+1} : φ_i(x) = 1}`. -/
lemma card_layers_le_U (D : ℕ) (x : Fin n → Bool) :
    (((range (D + 1)).biUnion C.rvLayer).filter fun i => C.val x i = true).card ≤ C.U x := by
  rw [Act.U_eq_card]
  calc _ ≤ ((C.wires.filter fun e => C.sig x (C.wsrc e) = true).image
          fun e => C.wsrc e - n).card := by
        apply card_le_card
        intro i hi
        rw [mem_filter, mem_biUnion] at hi
        obtain ⟨⟨d, _, hid⟩, hv⟩ := hi
        obtain ⟨e, he, hes⟩ := exists_wire C hid
        rw [mem_image]
        refine ⟨e, mem_filter.mpr ⟨he, ?_⟩, by omega⟩
        rw [hes]; exact hv
    _ ≤ _ := card_image_le

/-- Аналог `layer-sum` для `U`: `U(Σ) ≥ Σ_{d ≤ D} A_d`. -/
theorem Uav_ge_sum_Ad (D : ℕ) : ∑ d ∈ range (D + 1), C.rvA d ≤ C.Uav := by
  have hdisj : ((range (D + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint C.rvLayer :=
    fun d _ d' _ hne => C.rvLayer_disjoint hne
  unfold Circ.rvA
  rw [← sum_biUnion hdisj]
  set L := (range (D + 1)).biUnion C.rvLayer
  have h1 : ∑ i ∈ L, C.lowW i = ∑ x, (L.filter fun i => C.val x i = true).card := by
    simp only [Circ.lowW, card_filter]
    exact sum_comm
  have h2 : ∑ i ∈ L, C.lowP i =
      (∑ x, ((L.filter fun i => C.val x i = true).card : ℝ)) / 2 ^ n := by
    unfold Circ.lowP
    rw [← sum_div]
    congr 1
    exact_mod_cast h1
  rw [h2]
  unfold Circ.Uav avgM
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro x _
  exact_mod_cast card_layers_le_U C D x

/-- Для хорошего оператора `U(Σ) ≥ (m/4) Σ_{d ≤ D} 1/(d+4)`. -/
theorem good_Uav {D : ℕ} {F : (Fin n → Bool) → Fin m → Bool} (hG : Low.Good n m D F)
    (C : Circ n (Fin m)) (hC : C.Realizes F) :
    (m : ℝ) / 4 * ∑ d ∈ range (D + 1), 1 / ((d : ℝ) + 4) ≤ C.Uav := by
  refine le_trans ?_ (Uav_ge_sum_Ad C D)
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  exact Low.Ad_ge C d (hG C hC d (Nat.le_of_lt_succ (mem_range.mp hd)))

/-- **Обратные слои для почти всех операторов.** При `1 ≤ m ≤ 2^{2^n}` и `Δ > 255` доля
операторов, у которых любая схема имеет `E(Σ) ≥ (m/16) log(1+Δ)` и `U(Σ) ≥ (m/16) log(1+Δ)`,
не меньше `1 − 1/n`. -/
theorem layer_frac (n m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ 2 ^ n) (hΔ : 255 < Delta n m) :
    1 - 1 / (n : ℝ) ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      1 / 16 * (m : ℝ) * Real.logb 2 (1 + Delta n m) ≤ C.Eav ∧
        1 / 16 * (m : ℝ) * Real.logb 2 (1 + Delta n m) ≤ C.Uav := by
  obtain ⟨_, hΔn⟩ := Low.delta_facts n m hm1 hm (by linarith)
  set Δ := Delta n m with hΔdef
  have hΔ0 : 0 ≤ Δ / 4 := by linarith
  set D := ⌊Δ / 4⌋₊ with hDdef
  have hn256 : 256 ≤ n := by
    have : (255 : ℝ) < n := lt_of_lt_of_le hΔ hΔn
    have : 255 < n := by exact_mod_cast this
    omega
  have hDle : ∀ d ≤ D, (d : ℝ) ≤ Δ / 4 := by
    intro d hd
    calc (d : ℝ) ≤ D := by exact_mod_cast hd
      _ ≤ Δ / 4 := Nat.floor_le hΔ0
  have hDn : D ≤ n := by
    have : (D : ℝ) ≤ n := by linarith [hDle D le_rfl]
    exact_mod_cast this
  have h8 := Low.incompressible_general n m D hm1 fun d hd =>
    Low.overhead_delta n m hm1 hm hΔ d (hDle d hd)
  have hexc := Low.exc_le n m D (by omega) hm1 hDn
  -- оценка гармонической суммы
  have hsum : 1 / 16 * (m : ℝ) * Real.logb 2 (1 + Δ) ≤
      (m : ℝ) / 4 * ∑ d ∈ range (D + 1), 1 / ((d : ℝ) + 4) := by
    have hD' : Δ + 1 ≤ 4 * ((D : ℝ) + 5) := by
      have := Nat.lt_floor_add_one (Δ / 4)
      rw [← hDdef] at this
      linarith
    have h := Low.harm_bound Δ D hΔ.le hD'
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  refine le_trans (by linarith) (le_trans h8 ?_)
  unfold frac
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (Set.toFinite _) fun F hF C hC =>
    And.intro (hsum.trans (Low.good_Eav hF C hC)) (hsum.trans (good_Uav hF C hC))

end Layer

end PowerActivity
