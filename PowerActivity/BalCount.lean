import Mathlib

/-!
# Тезисы, цель `BalGoal`: подсчёт кортежей с малым числом различных «хороших» значений

Пусть `α` — конечное множество (`|α| = K`), `L ⊆ α` — «плохие» элементы, `|L| ≤ B`,
и `F : Fin m → α` — кортеж. `goodVals L F` — множество различных значений `F`, не лежащих в `L`.

* `exists_cover` — если `|goodVals L F| = s`, то есть множество позиций `J`, `|J| ≤ s`,
  такое что все координаты вне `J` лежат в `L ∪ F(J)` (по одной позиции на каждое значение);
* `card_cover_le` — кортежей с данным `J` не больше `K^{|J|} (|L|+|J|)^{m−|J|}`:
  значения на `J` произвольны, остальные — из `L ∪ F(J)`;
* `card_few_le` — суммирование по `2^m` множествам `J`:
  `#{F : |goodVals L F| ≤ t} ≤ 2^m K^t (B+t)^{m−t}` при `t ≤ m`, `B + t ≤ K`.

Это вариант подсчёта «через последовательности»: множитель `K^t` сокращается со знаменателем
`K^m`, и доля таких кортежей не больше `2^m ((B+t)/K)^{m−t}` — без оценок биномиальных
коэффициентов `C(K,t)`.
-/

namespace PowerActivity.Bal

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Различные значения кортежа `F`, не лежащие в `L`. -/
def goodVals {m : ℕ} (L : Finset α) (F : Fin m → α) : Finset α :=
  (univ.image F).filter fun g => g ∉ L

/-- Кортежи, у которых все координаты вне `J` лежат в `L ∪ F(J)`. -/
def cover {m : ℕ} (L : Finset α) (J : Finset (Fin m)) : Finset (Fin m → α) :=
  univ.filter fun F => ∀ j ∉ J, F j ∈ L ∪ J.image F

/-- По одной позиции на каждое хорошее значение: `|J| ≤ |goodVals L F|`, `F ∈ cover L J`. -/
lemma exists_cover {m : ℕ} (L : Finset α) (F : Fin m → α) :
    ∃ J : Finset (Fin m), J.card ≤ (goodVals L F).card ∧ F ∈ cover L J := by
  have hex : ∀ g : goodVals L F, ∃ j, F j = g.1 := by
    intro g
    obtain ⟨j, _, hj⟩ := mem_image.mp (mem_filter.mp g.2).1
    exact ⟨j, hj⟩
  choose pos hpos using hex
  refine ⟨(goodVals L F).attach.image pos, ?_, ?_⟩
  · calc _ ≤ (goodVals L F).attach.card := card_image_le
      _ = _ := card_attach
  · simp only [cover, mem_filter, mem_univ, true_and]
    intro j _
    by_cases hL : F j ∈ L
    · exact mem_union_left _ hL
    · apply mem_union_right
      have hg : F j ∈ goodVals L F := by
        simp only [goodVals, mem_filter, mem_image, mem_univ, true_and]
        exact ⟨⟨j, rfl⟩, hL⟩
      rw [mem_image]
      exact ⟨pos ⟨F j, hg⟩, mem_image_of_mem _ (mem_attach _ _), hpos _⟩

/-- Число кортежей с данным множеством позиций `J`. -/
lemma card_cover_le {m : ℕ} (L : Finset α) (J : Finset (Fin m)) :
    (cover L J).card ≤ Fintype.card α ^ J.card * (L.card + J.card) ^ (m - J.card) := by
  -- ограничение кортежа на `J`
  let r : (Fin m → α) → (J → α) := fun F i => F i
  rw [card_eq_sum_card_fiberwise (f := r) (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ v : J → α, ((cover L J).filter fun F => r F = v).card
      ≤ ∑ _v : J → α, (L.card + J.card) ^ (m - J.card) := by
        apply sum_le_sum
        intro v _
        calc ((cover L J).filter fun F => r F = v).card
            ≤ (Fintype.piFinset fun j : Fin m =>
                if h : j ∈ J then ({v ⟨j, h⟩} : Finset α) else L ∪ univ.image v).card := by
              apply card_le_card
              intro F hF
              simp only [mem_filter, cover, mem_univ, true_and] at hF
              obtain ⟨hcov, hrv⟩ := hF
              rw [Fintype.mem_piFinset]
              intro j
              by_cases hj : j ∈ J
              · simp only [hj, ↓reduceDIte, mem_singleton, ← hrv, r]
              · simp only [hj, ↓reduceDIte]
                have hj' := hcov j hj
                have him : J.image F = univ.image v := by
                  ext a
                  simp only [mem_image, mem_univ, true_and, ← hrv, r]
                  constructor
                  · rintro ⟨i, hi, rfl⟩
                    exact ⟨⟨i, hi⟩, rfl⟩
                  · rintro ⟨i, rfl⟩
                    exact ⟨i, i.2, rfl⟩
                rw [him] at hj'
                exact hj'
          _ = ∏ j : Fin m,
                (if h : j ∈ J then ({v ⟨j, h⟩} : Finset α) else L ∪ univ.image v).card :=
              Fintype.card_piFinset _
          _ ≤ ∏ j : Fin m, (if j ∈ J then 1 else L.card + J.card) := by
              apply prod_le_prod
              intro j _
              by_cases hj : j ∈ J
              · simp only [hj, ↓reduceDIte, ↓reduceIte, card_singleton, le_refl]
              · simp only [hj, ↓reduceDIte, ↓reduceIte]
                calc (L ∪ univ.image v).card ≤ L.card + (univ.image v).card := card_union_le _ _
                  _ ≤ L.card + (univ : Finset J).card := by gcongr; exact card_image_le
                  _ = L.card + J.card := by rw [card_univ, Fintype.card_coe]
          _ = (L.card + J.card) ^ (m - J.card) := by
              rw [prod_ite, prod_const_one, one_mul, prod_const]
              congr 1
              have hc : (univ.filter fun j : Fin m => j ∉ J) = Jᶜ := by
                ext j
                simp
              rw [hc, card_compl, Fintype.card_fin]
    _ = Fintype.card α ^ J.card * (L.card + J.card) ^ (m - J.card) := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_coe, smul_eq_mul]

/-- Монотонность `K^j (b+j)^{m−j}` по `j ≤ t` при `b + t ≤ K`. -/
lemma pow_mono_aux {K b j t m : ℕ} (hjt : j ≤ t) (htm : t ≤ m) (hK : b + t ≤ K) :
    K ^ j * (b + j) ^ (m - j) ≤ K ^ t * (b + t) ^ (m - t) := by
  have e1 : m - j = (t - j) + (m - t) := by omega
  calc K ^ j * (b + j) ^ (m - j) ≤ K ^ j * (b + t) ^ (m - j) := by gcongr
    _ = K ^ j * ((b + t) ^ (t - j) * (b + t) ^ (m - t)) := by rw [e1, pow_add]
    _ ≤ K ^ j * (K ^ (t - j) * (b + t) ^ (m - t)) := by gcongr
    _ = K ^ t * (b + t) ^ (m - t) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hjt]

/-- Главная оценка подсчёта: `#{F : |goodVals L F| ≤ t} ≤ 2^m K^t (B+t)^{m−t}`. -/
theorem card_few_le {m t B : ℕ} (L : Finset α) (hL : L.card ≤ B) (htm : t ≤ m)
    (hK : B + t ≤ Fintype.card α) :
    (univ.filter fun F : Fin m → α => (goodVals L F).card ≤ t).card ≤
      2 ^ m * Fintype.card α ^ t * (B + t) ^ (m - t) := by
  set D := (univ : Finset (Finset (Fin m))).filter fun J => J.card ≤ t with hD
  have hsub : (univ.filter fun F : Fin m → α => (goodVals L F).card ≤ t) ⊆
      D.biUnion (cover L) := by
    intro F hF
    rw [mem_filter] at hF
    obtain ⟨J, hJ, hFJ⟩ := exists_cover L F
    rw [mem_biUnion]
    refine ⟨J, ?_, hFJ⟩
    rw [hD, mem_filter]
    exact ⟨mem_univ _, le_trans hJ hF.2⟩
  calc _ ≤ (D.biUnion (cover L)).card := card_le_card hsub
    _ ≤ ∑ J ∈ D, (cover L J).card := card_biUnion_le
    _ ≤ ∑ _J ∈ D, Fintype.card α ^ t * (B + t) ^ (m - t) := by
        apply sum_le_sum
        intro J hJ
        have hJt : J.card ≤ t := (mem_filter.mp hJ).2
        calc (cover L J).card
            ≤ Fintype.card α ^ J.card * (L.card + J.card) ^ (m - J.card) := card_cover_le L J
          _ ≤ Fintype.card α ^ J.card * (B + J.card) ^ (m - J.card) := by gcongr
          _ ≤ _ := pow_mono_aux hJt htm hK
    _ ≤ ∑ _J : Finset (Fin m), Fintype.card α ^ t * (B + t) ^ (m - t) :=
        sum_le_sum_of_subset (filter_subset _ _)
    _ = 2 ^ m * Fintype.card α ^ t * (B + t) ^ (m - t) := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul, mul_assoc]

end PowerActivity.Bal
