import PowerActivity.InflCount
import PowerActivity.LayerU
import PowerActivity.ThesesSpec

/-!
# Тезисы: цели `InflGoal` и `LayerGoal`

* `infl_goal : InflGoal` — для почти всех операторов (равномерно по `m ≥ 1`) любая схема имеет
  `E(Σ) ≥ n/16`: `c = 1/16`, `ε(n) = 1` при `n < 8`, `ε(n) = 1/n` иначе. Координата `0`
  оператора хорошая (`4 D_t > N` при всех `t`, `Infl.GoodF`) с долей `≥ 1 − 1/n`
  (`Infl.frac_goodF`, `Infl.frac_first`), и для неё работает `Infl.infl_lower`;
* `layer_goal : LayerGoal` — при `Δ > 255` (`Δ₀ = 255`) для доли операторов `≥ 1 − 1/n`
  любая схема имеет `E(Σ), U(Σ) ≥ (m/16) log(1+Δ)`: `c = 1/16`, `ε(n) = 1/n`
  (`Layer.layer_frac`).
-/

namespace PowerActivity

open Filter Topology

/-- **Влияние переменных**: `E(Σ) ≥ n/16` для почти всех операторов. -/
theorem infl_goal : InflGoal := by
  refine ⟨1 / 16, by norm_num, fun n => if n < 8 then 1 else 1 / (n : ℝ), ?_, ?_⟩
  · have h : (fun n : ℕ => if n < 8 then (1 : ℝ) else 1 / (n : ℝ)) =ᶠ[atTop]
        fun n : ℕ => 1 / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 8] with n hn
      simp [show ¬ n < 8 by omega]
    exact (tendsto_one_div_atTop_nhds_zero_nat).congr' h.symm
  · intro n m hm
    by_cases hn : n < 8
    · simp only [hn, ite_true, sub_self]
      unfold frac
      positivity
    · simp only [hn, ite_false]
      have hn8 : 8 ≤ n := by omega
      have h1 := Infl.frac_goodF n hn8
      rw [← Infl.frac_first hm] at h1
      refine h1.trans (Infl.frac_mono fun F hG C hC => ?_)
      have hf : (fun x => C.eval x ⟨0, hm⟩) = fun x => F x ⟨0, hm⟩ :=
        funext fun x => congrFun (hC x) _
      have h2 := Infl.infl_lower C (by omega) ⟨0, hm⟩ (fun t => by rw [hf]; exact hG t)
      linarith

/-- **Обратные слои для почти всех операторов**: при `Δ > 255`
`E(Σ), U(Σ) ≥ (m/16) log(1+Δ)`. -/
theorem layer_goal : LayerGoal := by
  refine ⟨1 / 16, 255, by norm_num, fun n => 1 / (n : ℝ), tendsto_one_div_atTop_nhds_zero_nat,
    ?_⟩
  intro n m hm1 hm hΔ
  exact Layer.layer_frac n m hm1 hm hΔ

end PowerActivity
