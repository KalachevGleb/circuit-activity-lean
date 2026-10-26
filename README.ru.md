# Оценки активности схем из функциональных элементов, реализующих булевы операторы: формализация в Lean 4

[![Lean Action CI](https://github.com/KalachevGleb/circuit-activity-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/KalachevGleb/circuit-activity-lean/actions/workflows/lean_action_ci.yml)

[English](README.md) | **Русский**

В репозитории находится полное формальное доказательство двух теорем работы

> Г. В. Калачев. *Оценки активности схем из функциональных элементов, реализующих булевы операторы*.
> Интеллектуальные системы. Теория и приложения, в печати.

на языке [Lean 4](https://lean-lang.org) с библиотекой
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Постановка

Схема из функциональных элементов (СФЭ) над базисом $`B_0=\{\wedge_2,\vee_2,\neg\}`$ с $`n`$ входами —
ациклическая сеть элементов; исходящая степень произвольна, оба входа элемента могут идти от
одного источника (два провода), выходы — любые сигналы. На входном наборе $`x\in\{0,1\}^n`$:

* $`E(\Sigma,x)`$ — **мощность**, число элементов с единицей на выходе;
* $`P(\Sigma,x)`$ — **P-активность**, число элементов с единицей на выходе или хотя бы на одном входе;
* $`U(\Sigma,x)`$ — число проводов с единицей (включая провода от входов).

$`\widehat M(\Sigma)=\max_xM(\Sigma,x)`$, $`M(\Sigma)`$ — среднее по равномерному $`x`$;
$`M(F)=\min_{\Sigma=F}M(\Sigma)`$ и $`M(n,m)=\max_{F\colon\{0,1\}^n\to\{0,1\}^m}M(F)`$ — функции Шеннона.
«Почти все» означает, что доля операторов стремится к 1 при $`n\to\infty`$. Логарифмы двоичные,
$`n':=\max(2,\ n-\log\,\log(m+1))`$.

## Теоремы

**Теорема 1.** Равномерно по $`1\le m\le2^{2^n}`$
$`E(n,m)=\Theta(n+m\,\log\,n')`$ и $`\widehat E(n,m)=\Theta(n+m\,\log\,n')`$; нижняя оценка выполнена для почти
всех операторов.

**Теорема 2.** Равномерно по $`1\le m\le2^{2^n}`$
$`\Omega(n\,\log\,n+m\,\log\,n')\le P(n,m)\le\widehat P(n,m)\le O(n^2+m\,\log\,n')`$; нижняя оценка выполнена для
почти всех операторов.

В Lean ([`PowerActivity/ThesesSpec.lean`](PowerActivity/ThesesSpec.lean),
[`PowerActivity/Theses.lean`](PowerActivity/Theses.lean)):

```lean
def ThesesThm1 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * (n + m * Real.logb 2 (nPrime n m)) ≤ C.Eav) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    c * (n + m * Real.logb 2 (nPrime n m)) ≤ EavSh n m ∧ EavSh n m ≤ EmaxSh n m ∧
      EmaxSh n m ≤ K * (n + m * Real.logb 2 (nPrime n m)))

def ThesesThm2 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    1 - ε n ≤ frac n (Fin m) fun F => ∀ C : Circ n (Fin m), C.Realizes F →
      c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ C.Pav) ∧
  (∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    ∀ F : (Fin n → Bool) → Fin m → Bool, ∃ C : Circ n (Fin m), C.Realizes F ∧
      ∀ x, (C.P x : ℝ) ≤ K * (n ^ 2 + m * Real.logb 2 (nPrime n m))) ∧
  (∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ 2 ^ 2 ^ n →
    c * (n * Real.logb 2 n + m * Real.logb 2 (nPrime n m)) ≤ PavSh n m ∧
      PavSh n m ≤ PmaxSh n m ∧ PmaxSh n m ≤ K * (n ^ 2 + m * Real.logb 2 (nPrime n m)))

theorem thesesThm1 : ThesesThm1
theorem thesesThm2 : ThesesThm2
```

Формальные утверждения немного сильнее текста: оценки функций Шеннона доказаны при всех
$`n\ge2`$ (а не только асимптотически), а верхние оценки — для каждого оператора на каждом наборе.
Квадратичная верхняя оценка $`\widehat P(n,1)`$, которая в тезисах взята из работы О. М. Касим-Заде
(1992), здесь доказана явной схемой в духе Горяшко. Проверены и два замечания тезисов: те же оценки
для числа активных проводов (`thesesThm2U`) и $`P(n,m),\widehat P(n,m)=\Theta(m\,\log\,n')`$ при
$`n^2/\log\,n\le m\le2^{2^n}`$ (`thesesCorP`).

Промежуточные результаты ([`PowerActivity/Spec.lean`](PowerActivity/Spec.lean),
[`PowerActivity/Main.lean`](PowerActivity/Main.lean)): `powerBound` (порядок $`n+m\,\log(n+1)`$ мощности
при $`1\le m\le2^n`$), `activityBound` и `wireBound` (для почти всех булевых функций любая схема имеет
$`P,U\ge cn\,\log\,n`$; $`\widehat P(n,1),\widehat U(n,1)=O(n^2)`$), `powerBoundGeneral` (порядок
$`n+M\,\log(1+\Delta)`$ мощности при любом $`m`$, $`M=\min\{m,2^{2^n}\}`$, $`\Delta=\max\{1,n-\log\,\log(M+1)\}`$).

## Что нужно проверить читателю

Доказательства проверяет Lean. Чтобы доверять результату, достаточно убедиться, что определения
в формулировках означают то же, что в тексте: [`Defs.lean`](PowerActivity/Defs.lean) (модель,
около 250 строк) и `nPrime`, `ThesesThm1`, `ThesesThm2` в
[`ThesesSpec.lean`](PowerActivity/ThesesSpec.lean).

| Текст | Lean |
| --- | --- |
| СФЭ над $`B_0`$ с $`n`$ входами и выходами, занумерованными $`\kappa`$ | `Circ n κ` (список элементов в топологическом порядке; сигнал `j < n` — вход $`x_j`$, сигнал `n + i` — элемент `i`) |
| значение сигнала на наборе $`x`$ | `Circ.sig`, `Circ.val` |
| $`\Sigma`$ реализует $`F`$ | `Circ.Realizes F` |
| $`E(\Sigma,x)`$, $`P(\Sigma,x)`$, $`U(\Sigma,x)`$ | `Circ.E`, `Circ.P`, `Circ.U` |
| $`\widehat E(\Sigma)`$, $`E(\Sigma)`$ (и так же для $`P`$, $`U`$) | `Circ.Emax`, `Circ.Eav`, … |
| $`E(n,m)`$, $`\widehat E(n,m)`$, $`P(n,m)`$, … | `EavSh n m`, `EmaxSh n m`, `PavSh n m`, … |
| доля операторов со свойством | `frac n (Fin m) Q` |
| $`n'`$ | `nPrime n m` |

Файл [`Verify.lean`](Verify.lean) проверяет, что теоремы используют только стандартные аксиомы
`propext`, `Classical.choice` и `Quot.sound`; в частности, `sorry` нет.

## Сборка

Установите Lean через [elan](https://github.com/leanprover/elan) (версия задана в `lean-toolchain`:
Lean 4.34.1, Mathlib v4.34.1), затем

```sh
git clone https://github.com/KalachevGleb/circuit-activity-lean.git
cd circuit-activity-lean
lake exe cache get        # готовые файлы Mathlib
lake build                # проверка всех доказательств
lake env lean Verify.lean # проверка аксиом; при успехе ничего не печатает
```

Те же шаги выполняются в GitHub Actions при каждой отправке
([`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)).

## Устройство доказательства

| Модули | Содержание |
| --- | --- |
| `Defs`, `ThesesSpec`, `Spec` | Модель; формулировки тезисов; промежуточные утверждения и цели. |
| `Up*` | Верхние оценки мощности: `minterms`, `decoder`, `block-upper`, `group-param`, `group-upper`; схема в духе Горяшко с $`P,U=O(n^2)`$. |
| `Low*` | Нижние оценки мощности: `parity`, `rev-layers`, `encoding`, `incompressible`, `layer-sum`, `large-delta`, `many-outputs`. |
| `Act*` | Нижняя оценка активности: `entropy`, `wires`, `fanout`, `fwd-balls`, `cut-sum`, `harmonic`. |
| `Apx*` | Приближённая сложность: `approx-hard`, `cut-compress`. |
| `Assemble`, `Main` | Функции Шеннона, `saturation`, промежуточные результаты. |
| `Infl*`, `LayerU` | Почти все операторы: $`E\ge cn`$ (влияние переменных, обобщение `parity`); обратные слои для $`E`$ и $`U`$. |
| `Bal*` | Почти все операторы: $`E,U\ge cm`$ (много различных сбалансированных выходов), равномерно по $`m\le2^{2^n}`$. |
| `OpP*` | $`P(\Sigma,x)=O(n^2+m\,\log(1+\Delta))`$ для любого оператора: дешифратор Горяшко и монотонная часть схемы для мощности. |
| `ThesesAssemble`, `Theses` | Теоремы тезисов. |

Комментарии в коде — на русском языке; утверждения доказательства обозначены в них короткими метками:

| Метка | Утверждение |
| --- | --- |
| `entropy` | $`H(Z)\le\sum_ih_2(p_i)\le tA+q\,\log(1+2^{-t})`$ и $`H(Z)\le A\,\log(2q)+1`$ для вектора $`Z`$ из $`q`$ битов, $`A=\sum_i\Pr\{Z_i=1\}`$. |
| `parity` | Любая схема чётности $`n\ge2`$ переменных имеет $`E\ge n/4`$. |
| `wires` | $`U\le2P`$; если каждый элемент лежит на пути к выходу, то $`U/2\le P\le2U+1`$. |
| `fanout` | Любую схему можно заменить схемой того же оператора с исходящими степенями не больше $`3`$ (включая входы) и $`U(\Sigma^\ast,x)\le3U(\Sigma,x)`$. |
| `minterms` | Все минтермы вычисляются одной схемой с мощностью $`2n+O(1)`$ на каждом наборе. |
| `decoder` | По индикаторам значений блока из $`r`$ выходов блок восстанавливается с добавочной мощностью не больше $`r\lceil\log\,r\rceil`$. |
| `block-upper` | $`E(\Sigma,x)\le2n+O(1)+n\lceil m/r\rceil+m\lceil\log\,r\rceil`$, $`r=\min\{m,n\}`$. |
| `rev-layers` | Шары и слои по расстоянию до выходов: $`\lvert B_d\rvert,\lvert L_{d+1}\rvert\le m2^{d+1}`$ и $`F(x)=G_d(x,Z_d(x))`$ для сигналов $`Z_d`$ слоя $`L_{d+1}`$. |
| `encoding` | Операторов, у которых есть схема с $`S_d=\sum_{v\in L_{d+1}}h_2(p_v)\le S`$, не больше $`2^{NS+C_0m2^d(n+\log(m+1)+d+1)}`$, $`N=2^n`$. |
| `incompressible` | Для почти всех операторов любая схема имеет $`S_d\ge m/2`$ при всех малых $`d`$. |
| `layer-sum` | $`S_d\le(d+4)A_d+m/4`$, откуда $`E\ge\sum_dA_d=\Omega(m\,\log(n+1))`$. |
| `approx-hard` | Для почти всех $`f`$ любая схема, совпадающая с $`f`$ на $`3/4`$ наборов, имеет не меньше $`a2^n/n`$ элементов. |
| `fwd-balls` | Шары от входов при исходящих степенях $`\le3`$: $`\lvert B_d\rvert\le\tfrac32n3^d`$, $`\lvert R_d\rvert\le3\lvert B_d\rvert`$; разрезы $`R_d`$ попарно не пересекаются. |
| `cut-sum` | $`U\ge\sum_dA_d`$ — сумма средних чисел активных проводов в разрезах. |
| `cut-compress` | $`L_{1/4}(f)\le C_4\lvert B_d\rvert2^{4H_d}`$, $`H_d`$ — энтропия сигналов разреза $`R_d`$. |
| `harmonic` | $`H_d\ge cn`$ при $`d\le c_0n`$, откуда $`U=\Omega(n\,\log\,n)`$. |
| `saturation` | $`E(n,m)=E(n,M)`$, $`M=\min\{m,2^{2^n}\}`$. |
| `group-param` | Глубина $`\ell`$ деревьев над группами удовлетворяет $`\ell=\Theta(\Delta)`$. |
| `group-upper` | Индикаторы всех подмножеств малых групп наборов дают $`\widehat E(n,m)=O(n+m\,\log(1+\Delta))`$. |
| `large-delta` | При большом $`\Delta`$ для почти всех операторов любая схема имеет $`E=\Omega(m\,\log(1+\Delta))`$. |
| `many-outputs` | Существует оператор, любая схема которого имеет $`E\ge m/4`$. |

## Использование инструментов ИИ

Формализация доказательств в Lean 4 выполнена с помощью модели Claude Opus 5.5 (Anthropic) в
Claude Code.

## Цитирование и лицензия

При использовании кода ссылайтесь на работу, указанную выше (см. также [`CITATION.cff`](CITATION.cff)).
Код распространяется по лицензии Apache 2.0 ([`LICENSE`](LICENSE)), как и Mathlib.
