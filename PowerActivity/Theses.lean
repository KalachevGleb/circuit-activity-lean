import PowerActivity.ThesesAssemble
import PowerActivity.InflMain
import PowerActivity.BalMain
import PowerActivity.OpPMain

/-!
# Утверждения тезисов без гипотез

* `thesesThm1` — теорема 1: `E(n,m) = Θ(n + m log n')`, `Ê(n,m) = Θ(n + m log n')` равномерно по
  `1 ≤ m ≤ 2^{2^n}`, нижняя оценка — для почти всех операторов;
* `thesesThm2` — теорема 2: `Ω(n log n + m log n') ≤ P(n,m) ≤ P̂(n,m) ≤ O(n² + m log n')`,
  нижняя оценка — для почти всех операторов;
* `thesesThm2U` — те же оценки для числа активных проводов `U`;
* `thesesCorP` — `P(n,m) = Θ(m log n')` при `n²/log n ≤ m ≤ 2ⁿ`.
-/

namespace PowerActivity

/-- Теорема 1 тезисов. -/
theorem thesesThm1 : ThesesThm1 :=
  thesesThm1_of infl_goal layer_goal bal_goal powerBoundGeneral

/-- Теорема 2 тезисов. -/
theorem thesesThm2 : ThesesThm2 :=
  thesesThm2_of exists_goal actLower_goal upperPOp_goal thesesThm1

/-- Теорема 2 тезисов для числа активных проводов. -/
theorem thesesThm2U : ThesesThm2U :=
  thesesThm2U_of exists_goal actLower_goal layer_goal bal_goal upperPOp_goal

/-- Следствие теоремы 2 тезисов. -/
theorem thesesCorP : ThesesCorP := thesesCorP_of thesesThm2

end PowerActivity
