import PowerActivity.OpPGen

/-!
# Верхняя оценка `P`-активности операторов (`UpperPOpGoal`)

* `upperPOp_goal` — `UpperPOpGoal` с `K = 9`: для любого оператора `F : {0,1}ⁿ → {0,1}ᵐ`,
  `n ≥ 1`, `1 ≤ m ≤ 2^{2^n}`, есть схема с `P(Σ,x) ≤ 9 (n² + m log(1+Δ))` на каждом наборе.

Конструкция (идея автора тезисов): общая схема `group-upper` (`Up.genC`), в которой ярус
минтермов (`Up.mtC` из `minterms`, его `P`-активность экспоненциальна) заменён листьями схемы Горяшко
(`OpP.mtP`, `P ≤ 2n² + n + 2`); остальные ярусы состоят из элементов `∨`, и для них `P = E`
(`OpP.P_eq_E`), так что их вклад оценивается мощностью из `Up.gen_spec`.
Целочисленная форма: `P ≤ 2n² + 4n + 3 + 3m + m⌈log ℓ⌉` (`OpP.upperPOp_nat`).

Вспомогательные определения и леммы — в пространстве имён `PowerActivity.OpP`
(модули `OpPBase`, `OpPGen`).
-/

namespace PowerActivity

/-- Верхняя оценка `P`-активности операторов: `P(Σ,x) ≤ 9 (n² + m log(1+Δ))`. -/
theorem upperPOp_goal : UpperPOpGoal := OpP.upperPOp_goal_pf

end PowerActivity

#print axioms PowerActivity.upperPOp_goal
