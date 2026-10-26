import PowerActivity.Main
import PowerActivity.Theses

/-!
# Оценки активности схем из функциональных элементов

Г. В. Калачев, «Оценки активности схем из функциональных элементов, реализующих булевы
операторы» (тезисы).

* `PowerActivity/Defs.lean` — модель: СФЭ над `B₀ = {∧₂, ∨₂, ¬}` как список элементов в
  топологическом порядке; меры `E` (мощность), `U` (провода с единицей), `P` (`P`-активность);
  функции Шеннона; доля операторов `frac`;
* `PowerActivity/ThesesSpec.lean` — формулировки тезисов `ThesesThm1`, `ThesesThm2`,
  `ThesesThm2U`, `ThesesCorP`; `PowerActivity/Theses.lean` — их доказательства `thesesThm1`,
  `thesesThm2`, `thesesThm2U`, `thesesCorP`;
* `PowerActivity/Spec.lean` — промежуточные утверждения `PowerBound`, `ActivityBound`,
  `WireBound`, `PowerBoundGeneral` и цели частей; `PowerActivity/Main.lean` — их доказательства.

Проверка аксиом — `Verify.lean` в корне репозитория.
-/
