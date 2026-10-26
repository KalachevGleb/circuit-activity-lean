import PowerActivity.LowGen

/-!
# Нижние оценки мощности: сводный модуль

Модули:
* `LowBasic`  — общие леммы о модели (`Circ.lowW`, `Circ.lowP`, `E(Σ) = Σ_i p_i`);
* `LowParity` — `parity` (чётность, `E ≥ n/4`);
* `LowEnt`    — `h₂(p) − tp ≤ log(1+2^{−t})`, подсчёт таблиц `≤ (N+1)^q 2^{NS}`, гармоническая сумма;
* `LowLayer`  — обратные слои `B_d`, `L_{d+1}`, их размеры (`rev-layers`);
* `LowRepr`   — схема `G_d`, представление `F(x) = G_d(x, Z_d(x))`, описание и декодирование;
* `LowCount`  — `encoding` (подсчёт описаний; `C₀ = 22`);
* `LowL8`     — `layer-sum`, `incompressible`, `LowerPowerGoal`;
* `LowMany`   — `many-outputs`, `ManyOutGoal`;
* `LowGen`    — `large-delta` (в форме существования), `LowerGeneralGoal`.
-/

namespace PowerActivity

/-- `parity`: схема, у которой один из выходов — чётность `n ≥ 2` переменных, имеет `E ≥ n/4`. -/
theorem parity_goal : ParityGoal := by
  intro n hn κ C k hk
  exact Low.parity_lower C hn k hk

/-- `encoding`, `incompressible` и `layer-sum`: для почти всех операторов
`E ≥ (1/16) m log(n+1)`. -/
theorem lowerPower_goal : LowerPowerGoal := Low.lowerPower

/-- `many-outputs`: есть оператор, у любой схемы которого `E ≥ m/4`. -/
theorem manyOut_goal : ManyOutGoal := by
  intro n m _ hm1 hm
  exact Low.many_out n m hm1 hm

/-- `large-delta` и `many-outputs`: `E ≥ (1/32) m log(1+Δ)` для некоторого оператора. -/
theorem lowerGeneral_goal : LowerGeneralGoal := Low.lowerGeneral

#print axioms parity_goal
#print axioms lowerPower_goal
#print axioms manyOut_goal
#print axioms lowerGeneral_goal
#print axioms Low.encoding_bound
#print axioms Low.encoding_count
#print axioms Low.incompressible
#print axioms Low.incompressible_explicit
#print axioms Circ.rv_decode_encode
#print axioms Low.Sd_le

end PowerActivity
