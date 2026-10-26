import PowerActivity.Spec

/-!
# Приближённая сложность: общие леммы о сигналах

* `sig_congr_prefix` — списки элементов, совпадающие на первых `k` позициях, дают одинаковые
  сигналы с номерами `< n + k`;
* `sig_ofFn` — значение сигнала элемента списка `List.ofFn G`;
* `ofFnCirc` — схема с одним выходом, заданная функцией `G : ℕ → Gate` на `0, …, tot-1`.
-/

namespace PowerActivity.Apx

open Finset

/-- Списки, совпадающие на первых `k` позициях, дают одинаковые сигналы с номерами `< n + k`. -/
lemma sig_congr_prefix {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (k : ℕ)
    (h : ∀ i, i < k → gs[i]? = hs[i]?) : ∀ j, j < n + k → sig n gs x j = sig n hs x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjn : j < n
    · rw [sig_lt _ _ hjn, sig_lt _ _ hjn]
    · rw [sig, sig]
      simp only [hjn, dite_false]
      rw [h (j - n) (by omega)]
      cases hg : hs[j - n]? with
      | none => rfl
      | some g =>
        simp only
        by_cases hab : g.a < j ∧ g.b < j
        · rw [dif_pos hab, dif_pos hab, ih _ hab.1 (by omega), ih _ hab.2 (by omega)]
        · rw [dif_neg hab, dif_neg hab]

/-- Значение сигнала элемента списка `List.ofFn G`. -/
lemma sig_ofFn {n tot : ℕ} (G : ℕ → Gate)
    (hv : ∀ i, i < tot → (G i).a < n + i ∧ (G i).b < n + i)
    (x : Fin n → Bool) {i : ℕ} (hi : i < tot) :
    sig n (List.ofFn fun k : Fin tot => G k) x (n + i) =
      Op.eval (G i).op (sig n (List.ofFn fun k : Fin tot => G k) x (G i).a)
        (sig n (List.ofFn fun k : Fin tot => G k) x (G i).b) := by
  have hl : i < (List.ofFn fun k : Fin tot => G k).length := by simp [hi]
  have hg : (List.ofFn fun k : Fin tot => G k)[i] = G i := by simp
  have := sig_gate (List.ofFn fun k : Fin tot => G k) x hl (by rw [hg]; exact (hv i hi).1)
    (by rw [hg]; exact (hv i hi).2)
  rw [this, hg]

/-- Схема с одним выходом `o`, элементы которой заданы функцией `G` на `0, …, tot-1`. -/
def ofFnCirc (n tot : ℕ) (G : ℕ → Gate)
    (hv : ∀ i, i < tot → (G i).a < n + i ∧ (G i).b < n + i) (o : ℕ) (ho : o < n + tot) :
    Circ n (Fin 1) where
  gates := List.ofFn fun k : Fin tot => G k
  valid := by
    intro i hi
    have hi' : i < tot := by simpa using hi
    simpa using hv i hi'
  out := fun _ => o
  out_lt := by intro; simpa using ho

lemma ofFnCirc_s (n tot : ℕ) (G : ℕ → Gate) hv (o : ℕ) ho :
    (ofFnCirc n tot G hv o ho).s = tot := by
  simp [ofFnCirc, Circ.s]

lemma ofFnCirc_eval (n tot : ℕ) (G : ℕ → Gate) hv (o : ℕ) ho (x : Fin n → Bool) (k : Fin 1) :
    (ofFnCirc n tot G hv o ho).eval x k = sig n (List.ofFn fun k : Fin tot => G k) x o := rfl

end PowerActivity.Apx
