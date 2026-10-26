import PowerActivity

/-!
# Axiom check

Run `lake env lean Verify.lean` after `lake build`. Each `#guard_msgs` fails unless the theorem
depends only on the three standard axioms of Lean and Mathlib (`propext`, `Classical.choice`,
`Quot.sound`); in particular, no `sorry` (`sorryAx`) and no new axioms are used.
-/

/-- info: 'PowerActivity.thesesThm1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.thesesThm1

/-- info: 'PowerActivity.thesesThm2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.thesesThm2

/-- info: 'PowerActivity.thesesThm2U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.thesesThm2U

/-- info: 'PowerActivity.thesesCorP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.thesesCorP

/-- info: 'PowerActivity.powerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.powerBound

/-- info: 'PowerActivity.activityBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.activityBound

/-- info: 'PowerActivity.wireBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.wireBound

/-- info: 'PowerActivity.powerBoundGeneral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PowerActivity.powerBoundGeneral
