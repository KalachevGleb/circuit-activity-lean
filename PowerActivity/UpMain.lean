import PowerActivity.UpUpper
import PowerActivity.UpP

/-!
# Верхние оценки: итоговые теоремы

* `exists_goal` — `ExistsGoal`: реализация любого оператора при `n ≥ 1`;
* `upperBlock_goal` — `UpperBlockGoal`, оценка `block-upper` с `c₀ = 2`
  (`minterms`, `decoder`; `Up.mtC_spec`, `Up.dec_spec`, `Up.gen_spec`);
* `upperGroup_goal` — `UpperGroupGoal`, оценка `group-upper` с `K = 5` (`group-param`);
* `upperP_goal` — `UpperPGoal` с `K = 12` (`P ≤ 6n²`, `U ≤ 12n²`; собственная конструкция
  в духе схемы Горяшко).

Вспомогательные определения и леммы — в пространстве имён `PowerActivity.Up`
(модули `UpBase`, `UpTree`, `UpMint`, `UpGen`, `UpUpper`, `UpP`).
-/

namespace PowerActivity

/-- Существование реализации любого оператора при `n ≥ 1`. -/
theorem exists_goal : ExistsGoal := Up.exists_goal_pf

/-- `block-upper`: `E(Σ,x) ≤ 2n + 2 + n⌈m/r⌉ + m⌈log r⌉`, `r = min{m,n}`. -/
theorem upperBlock_goal : UpperBlockGoal := Up.upperBlock_goal_pf

/-- `group-upper`: `E(Σ,x) ≤ 5 (n + m log(1+Δ))` при `n ≥ 2`, `1 ≤ m ≤ 2^{2^n}`. -/
theorem upperGroup_goal : UpperGroupGoal := Up.upperGroup_goal_pf

/-- Квадратичная оценка активности: `P(Σ,x) ≤ 12 n²` и `U(Σ,x) ≤ 12 n²`. -/
theorem upperP_goal : UpperPGoal := Up.upperP_goal_pf

/-- `minterms`: все минтермы одной схемой, мощность `≤ 2n + 1` на каждом наборе. -/
theorem minterms_circuit (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (∀ t, (Up.mtC n hn).eval x t = Up.mtVal x t) ∧ (Up.mtC n hn).E x ≤ 2 * n + 1 :=
  Up.mtC_spec n hn x

/-- `decoder`: рекурсивный декодер; на унитарном наборе — биты номера,
мощность `≤ r⌈log r⌉`. -/
theorem decoder_circuit (r : ℕ) : Up.DecSpec (Up.dec r) := Up.dec_spec r

end PowerActivity

#print axioms PowerActivity.exists_goal
#print axioms PowerActivity.upperBlock_goal
#print axioms PowerActivity.upperGroup_goal
#print axioms PowerActivity.upperP_goal
#print axioms PowerActivity.minterms_circuit
#print axioms PowerActivity.decoder_circuit
