import PowerActivity.Assemble
import PowerActivity.UpMain
import PowerActivity.LowMain
import PowerActivity.ActMain
import PowerActivity.ApxMain

/-!
# Промежуточные теоремы без гипотез

Сборка (`Assemble.lean`) с доказательствами целей:
* `powerBound : PowerBound` (`UpperBlockGoal`, `ParityGoal`, `LowerPowerGoal`, `ManyOutGoal`);
* `activityBound : ActivityBound`, `wireBound : WireBound` — для `P` и для `U` (`UpperPGoal`,
  `ApproxHardGoal`, `CutCompressGoal`, `act_lower_of`);
* `powerBoundGeneral : PowerBoundGeneral` (`UpperGroupGoal`, `ParityGoal`, `LowerGeneralGoal`,
  `saturation`).
-/

namespace PowerActivity

theorem actLower_goal : ActLowerGoal := act_lower_of approxHard_goal cutCompress_goal

/-- Порядок мощности при `1 ≤ m ≤ 2ⁿ`. -/
theorem powerBound : PowerBound :=
  powerBound_of exists_goal upperBlock_goal parity_goal lowerPower_goal manyOut_goal

/-- `P`-активность функций. -/
theorem activityBound : ActivityBound := (activityBound_of exists_goal upperP_goal actLower_goal).1

/-- То же для меры `U` (в тезисах `Q`). -/
theorem wireBound : WireBound := (activityBound_of exists_goal upperP_goal actLower_goal).2

/-- Порядок мощности при любом `m ≥ 1`. -/
theorem powerBoundGeneral : PowerBoundGeneral :=
  powerBoundGeneral_of exists_goal upperGroup_goal parity_goal lowerGeneral_goal

end PowerActivity

#print axioms PowerActivity.powerBound
#print axioms PowerActivity.activityBound
#print axioms PowerActivity.wireBound
#print axioms PowerActivity.powerBoundGeneral
