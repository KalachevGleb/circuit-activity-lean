import PowerActivity.UpMint

/-!
# Верхние оценки: общая конструкция для мощности

Параметры: `n ≥ 1`, `j ≤ n` (группы точек `{0,1}ⁿ` размера `g = 2^j`, их `q = 2^{n-j}`),
длина блока выходов `r ≥ 1` (блоков `⌈m/r⌉`). Построение (`block-upper`, `group-upper`):
1. все минтермы `Q_t` и константа `0` (`minterms`, `mtC`);
2. для каждой группы `A` индикаторы всех её подмножеств `S_{A,U}` (`subC`);
3. для каждого блока `β` и слова `v` — дерево ИЛИ `D_{β,v} = ⋁_A S_{A,U(A,β,v)}`
   над `q` листьями (при `j = 0` это дизъюнкция минтермов, как в `block-upper`);
4. для каждого блока — рекурсивный декодер (`decoder`).

Итог (`gen_spec`): схема реализует `F` и на каждом наборе
`E ≤ 2n + 1 + (2^{2^j} - 1) + ⌈m/r⌉ (n - j) + m ⌈log r⌉`
(при `j = 0` — оценка `block-upper`, при выборе `j`, `r` как в `group-upper` — оценка
`group-upper`).
-/

namespace PowerActivity

open Finset Up

namespace Up

/-- Значение выхода с номером `c` (вне диапазона — `0`). -/
def yb {m : ℕ} (y : Fin m → Bool) (c : ℕ) : Bool := if h : c < m then y ⟨c, h⟩ else false

/-- Длина блока `β` (блоки по `r` выходов, последний может быть короче). -/
def rb (m r β : ℕ) : ℕ := min r (m - β * r)

/-- Слово блока `β` значения оператора `y`. -/
def bw {m : ℕ} (r : ℕ) (y : Fin m → Bool) (β : ℕ) : ℕ := mask (fun p => yb y (β * r + p)) (rb m r β)

lemma bw_lt {m : ℕ} (r : ℕ) (y : Fin m → Bool) (β : ℕ) : bw r y β < 2 ^ rb m r β := mask_lt _ _

lemma rb_le (m r β : ℕ) : rb m r β ≤ r := min_le_left _ _

lemma bw_lt' {m : ℕ} (r : ℕ) (y : Fin m → Bool) (β : ℕ) : bw r y β < 2 ^ r :=
  lt_of_lt_of_le (bw_lt r y β) (Nat.pow_le_pow_right (by norm_num) (rb_le m r β))

lemma lt_of_lt_nb {m r β : ℕ} (hr : 0 < r) (h : β < (m + r - 1) / r) : β * r < m := by
  have := (Nat.le_div_iff_mul_le hr).1 (show β + 1 ≤ (m + r - 1) / r by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

lemma rb_pos {m r β : ℕ} (hr : 0 < r) (h : β < (m + r - 1) / r) : 0 < rb m r β := by
  have := lt_of_lt_nb hr h
  unfold rb; omega

lemma sum_range_rb (m r : ℕ) : ∀ N, ∑ β ∈ range N, rb m r β = min (N * r) m
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_range_rb m r N, Nat.succ_mul]
    unfold rb
    omega

lemma nb_mul_ge (m r : ℕ) (hr : 0 < r) : m ≤ (m + r - 1) / r * r := by
  have h1 := Nat.div_add_mod (m + r - 1) r
  have h2 := Nat.mod_lt (m + r - 1) hr
  rw [Nat.mul_comm] at h1
  omega

lemma sum_rb (m r : ℕ) (hr : 0 < r) : ∑ β : Fin ((m + r - 1) / r), rb m r β = m := by
  rw [Fin.sum_univ_eq_sum_range (fun β => rb m r β), sum_range_rb]
  have := nb_mul_ge m r hr
  omega

lemma div_lt_nb {m r c : ℕ} (hr : 0 < r) (hc : c < m) : c / r < (m + r - 1) / r := by
  have h1 := Nat.div_mul_le_self c r
  have : c / r + 1 ≤ (m + r - 1) / r := by
    rw [Nat.le_div_iff_mul_le hr, Nat.add_mul, Nat.one_mul]
    omega
  omega

lemma mod_lt_rb {m r c : ℕ} (hr : 0 < r) (hc : c < m) : c % r < rb m r (c / r) := by
  have h1 := Nat.div_add_mod' c r
  have h2 := Nat.mod_lt c hr
  unfold rb
  omega

lemma testBit_bw {m r c : ℕ} (hr : 0 < r) (y : Fin m → Bool) (hc : c < m) :
    (bw r y (c / r)).testBit (c % r) = y ⟨c, hc⟩ := by
  unfold bw
  rw [testBit_mask]
  have := mod_lt_rb hr hc
  simp only [this, decide_true, Bool.true_and, yb]
  rw [Nat.div_add_mod' c r]
  simp [hc]

lemma ag_iff {g A s t : ℕ} (hg : 0 < g) (hs : s < g) : A * g + s = t ↔ A = t / g ∧ s = t % g := by
  constructor
  · rintro rfl
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hs, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  · rintro ⟨rfl, rfl⟩
    exact Nat.div_add_mod' t g

lemma pow_sub_mul {n j : ℕ} (hj : j ≤ n) : 2 ^ (n - j) * 2 ^ j = 2 ^ n := by
  rw [← pow_add, Nat.sub_add_cancel hj]

/-- Маска множества `U(A,β,v)`: точки группы `A`, на которых слово блока `β` равно `v`. -/
def Umask {n m : ℕ} (F : (Fin n → Bool) → Fin m → Bool) (r j A β v : ℕ) : ℕ :=
  mask (fun s => decide (∃ a : Fin n → Bool, idx a = A * 2 ^ j + s ∧ bw r (F a) β = v)) (2 ^ j)

variable {n : ℕ}

/-! ## Ярус индикаторов подмножеств -/

/-- Подача входов схемы подмножеств группы `A`: точки группы и константа `0`. -/
def feedB (n j : ℕ) (hj : j ≤ n) (A : Fin (2 ^ (n - j))) : Fin (2 ^ j + 1) → Fin (2 ^ n + 1) :=
  fun s => if h : (s : ℕ) < 2 ^ j then
    ⟨A * 2 ^ j + s, by have := mul_add_lt A.2 h; rw [pow_sub_mul hj] at this; omega⟩
    else ⟨2 ^ n, by omega⟩

/-- Ярус индикаторов подмножеств всех групп. -/
def stB (n j : ℕ) (hj : j ≤ n) : Circ (2 ^ n + 1) (Fin (2 ^ (n - j)) × Fin (2 ^ 2 ^ j)) :=
  parF (2 ^ (n - j)) fun A => sel (subC (2 ^ j)) (feedB n j hj A)

lemma stB_eval (j : ℕ) (hj : j ≤ n) (x : Fin n → Bool) (A : Fin (2 ^ (n - j)))
    (u : Fin (2 ^ 2 ^ j)) :
    (stB n j hj).eval (mtVal x) (A, u) =
      decide (∃ s : Fin (2 ^ j), (u : ℕ).testBit s = true ∧ idx x = A * 2 ^ j + s) := by
  rw [stB, parF_eval, sel_eval, subC_eval]
  · rw [decide_eq_decide]
    apply exists_congr
    intro s
    apply and_congr Iff.rfl
    simp only [feedB, Fin.val_castSucc, s.2, ↓reduceDIte, mtVal]
    have : (A : ℕ) * 2 ^ j + s < 2 ^ n := by
      have := mul_add_lt A.2 s.2; rwa [pow_sub_mul hj] at this
    simp only [this, ↓reduceIte, decide_eq_true_eq]
  · simp [feedB, mtVal]

lemma stB_E (j : ℕ) (hj : j ≤ n) (x : Fin n → Bool) :
    (stB n j hj).E (mtVal x) ≤ 2 ^ 2 ^ j - 1 := by
  rw [stB, parF_E]
  have hx : idx x / 2 ^ j < 2 ^ (n - j) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), pow_sub_mul hj]; exact idx_lt x
  apply sum_le_of_single _ ⟨idx x / 2 ^ j, hx⟩
  · intro A hA
    rw [sel_E]
    apply (subC_mono _).E_zero
    intro s
    simp only [feedB]
    split_ifs with h
    · simp only [mtVal]
      have : (A : ℕ) * 2 ^ j + s < 2 ^ n := by
        have := mul_add_lt A.2 h; rwa [pow_sub_mul hj] at this
      simp only [this, ↓reduceIte, decide_eq_false_iff_not]
      intro he
      apply hA
      ext
      exact ((ag_iff (Nat.two_pow_pos j) h).1 he.symm).1
    · simp [mtVal]
  · rw [sel_E]
    exact (E_le_s _ _).trans (by rw [subC_s])

/-! ## Ярус деревьев `D_{β,v}` -/

/-- Число блоков. -/
abbrev nb (m r : ℕ) : ℕ := (m + r - 1) / r

/-- Ярус деревьев ИЛИ: для блока `β` и слова `v` — `⋁_A S_{A,U(A,β,v)}`. -/
def stC (n m j r : ℕ) (F : (Fin n → Bool) → Fin m → Bool) :
    Circ (2 ^ (n - j) * 2 ^ 2 ^ j) (Fin (nb m r) × (Fin (2 ^ r) × Unit)) :=
  parF (nb m r) fun β => parF (2 ^ r) fun v => sel (orT (2 ^ (n - j)) (Nat.two_pow_pos _))
    fun A => finProdFinEquiv (A, ⟨Umask F r j A β v, mask_lt _ _⟩)

/-- Входы яруса деревьев. -/
def inC (j : ℕ) (hj : j ≤ n) (x : Fin n → Bool) : Fin (2 ^ (n - j) * 2 ^ 2 ^ j) → Bool :=
  fun i => (stB n j hj).eval (mtVal x) (finProdFinEquiv.symm i)

lemma leafC_iff {m : ℕ} (F : (Fin n → Bool) → Fin m → Bool) (r j : ℕ) (hj : j ≤ n)
    (x : Fin n → Bool) (β v : ℕ) (A : Fin (2 ^ (n - j))) :
    inC j hj x (finProdFinEquiv (A, ⟨Umask F r j A β v, mask_lt _ _⟩)) = true ↔
      (A : ℕ) = idx x / 2 ^ j ∧ bw r (F x) β = v := by
  simp only [inC, Equiv.symm_apply_apply]
  rw [stB_eval, decide_eq_true_eq]
  simp only [Umask, testBit_mask]
  constructor
  · rintro ⟨s, hs1, hs2⟩
    simp only [s.2, decide_true, Bool.true_and, decide_eq_true_eq] at hs1
    obtain ⟨a, ha1, ha2⟩ := hs1
    have hax : a = x := idx_inj (by rw [ha1, hs2])
    subst hax
    exact ⟨((ag_iff (Nat.two_pow_pos j) s.2).1 hs2.symm).1, ha2⟩
  · rintro ⟨hA, hv⟩
    refine ⟨⟨idx x % 2 ^ j, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, ?_, ?_⟩
    · simp only [Nat.mod_lt _ (Nat.two_pow_pos j), decide_true, Bool.true_and,
        decide_eq_true_eq]
      exact ⟨x, by rw [hA]; exact (Nat.div_add_mod' _ _).symm, hv⟩
    · rw [hA]; exact (Nat.div_add_mod' _ _).symm

lemma stC_eval {m : ℕ} (F : (Fin n → Bool) → Fin m → Bool) (r j : ℕ) (hj : j ≤ n)
    (x : Fin n → Bool) (β : Fin (nb m r)) (v : Fin (2 ^ r)) :
    (stC n m j r F).eval (inC j hj x) (β, (v, ())) = decide (bw r (F x) β = v) := by
  rw [stC, parF_eval, parF_eval, sel_eval, (orT_spec _ _).eval, decide_eq_decide]
  constructor
  · rintro ⟨A, hA⟩
    exact ((leafC_iff F r j hj x β v A).1 hA).2
  · intro hv
    have hx : idx x / 2 ^ j < 2 ^ (n - j) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), pow_sub_mul hj]; exact idx_lt x
    exact ⟨⟨idx x / 2 ^ j, hx⟩, (leafC_iff F r j hj x β v _).2 ⟨rfl, hv⟩⟩

lemma stC_E {m : ℕ} (F : (Fin n → Bool) → Fin m → Bool) (r j : ℕ) (hj : j ≤ n)
    (x : Fin n → Bool) : (stC n m j r F).E (inC j hj x) ≤ nb m r * (n - j) := by
  rw [stC, parF_E]
  calc ∑ β : Fin (nb m r), (parF (2 ^ r) fun v => sel (orT (2 ^ (n - j)) (Nat.two_pow_pos _))
          fun A => finProdFinEquiv (A, (⟨Umask F r j A β v, mask_lt _ _⟩ : Fin (2 ^ 2 ^ j)))).E
          (inC j hj x)
        ≤ ∑ _β : Fin (nb m r), (n - j) := by
          apply Finset.sum_le_sum
          intro β _
          rw [parF_E]
          apply sum_le_of_single _ ⟨bw r (F x) β, bw_lt' r (F x) β⟩
          · intro v hv
            rw [sel_E]
            apply (orT_spec _ _).mono.E_zero
            intro A
            rw [← Bool.not_eq_true, leafC_iff]
            rintro ⟨-, h⟩
            exact hv (Fin.ext h.symm)
          · rw [sel_E]
            have hone : AtMostOne (fun A : Fin (2 ^ (n - j)) => inC j hj x
                (finProdFinEquiv (A, ⟨Umask F r j A β (bw r (F x) β), mask_lt _ _⟩))) := by
              intro A1 A2 h1 h2
              rw [leafC_iff] at h1 h2
              ext; rw [h1.1, h2.1]
            have h1 := ((orT_spec _ (Nat.two_pow_pos (n - j))).one _ hone).1
            rwa [Nat.clog_pow _ _ (by norm_num)] at h1
      _ = nb m r * (n - j) := by simp

/-! ## Ярус декодеров -/

/-- Ярус декодеров: для блока `β` — рекурсивный декодер (`decoder`) длины `rb β`. -/
def stD (m r : ℕ) (hr : 0 < r) : Circ (nb m r * 2 ^ r) (Fin (nb m r) × Fin r) :=
  parF (nb m r) fun β => reout (sel (dec (rb m r β)) fun v => finProdFinEquiv (β, ⟨v,
    lt_of_lt_of_le v.2 (Nat.pow_le_pow_right (by norm_num) (rb_le m r β))⟩))
    fun p => ⟨min p (rb m r β - 1), by have := rb_pos hr β.2; omega⟩

/-- Подача входов яруса декодеров. -/
def fD (m r : ℕ) : Fin (nb m r * 2 ^ r) → Fin (nb m r) × (Fin (2 ^ r) × Unit) :=
  fun i => ((finProdFinEquiv.symm i).1, ((finProdFinEquiv.symm i).2, ()))

/-! ## Сборка -/

/-- Схема общей конструкции. -/
def genC (n m j r : ℕ) (hn : 0 < n) (hj : j ≤ n) (hr : 0 < r)
    (F : (Fin n → Bool) → Fin m → Bool) : Circ n (Fin m) :=
  reout (comp (comp (comp (mtC n hn) id (stB n j hj)) finProdFinEquiv.symm (stC n m j r F))
    (fD m r) (stD m r hr))
    fun c => (⟨c / r, div_lt_nb hr c.2⟩, ⟨c % r, Nat.mod_lt _ hr⟩)

lemma inB_eq (hn : 0 < n) (x : Fin n → Bool) :
    (fun t => (mtC n hn).eval x (id t)) = mtVal x := by
  funext t; exact (mtC_spec n hn x).1 t

lemma inC_eq (hn : 0 < n) (j : ℕ) (hj : j ≤ n) (x : Fin n → Bool) :
    (fun i => (comp (mtC n hn) id (stB n j hj)).eval x (finProdFinEquiv.symm i)) =
      inC j hj x := by
  funext i
  rw [comp_eval, inB_eq]
  rfl

lemma inD_eq {m : ℕ} (hn : 0 < n) (j r : ℕ) (hj : j ≤ n) (F : (Fin n → Bool) → Fin m → Bool)
    (x : Fin n → Bool) (β : Fin (nb m r)) (v : Fin (2 ^ r)) :
    (comp (comp (mtC n hn) id (stB n j hj)) finProdFinEquiv.symm (stC n m j r F)).eval x
      (fD m r (finProdFinEquiv (β, v))) = decide (bw r (F x) β = v) := by
  rw [comp_eval, inC_eq]
  simp only [fD, Equiv.symm_apply_apply]
  exact stC_eval F r j hj x β v

/-- Общая конструкция: реализация `F` и поточечная оценка мощности. -/
theorem gen_spec {m : ℕ} (j r : ℕ) (hn : 0 < n) (hj : j ≤ n) (hr : 0 < r)
    (F : (Fin n → Bool) → Fin m → Bool) :
    (genC n m j r hn hj hr F).Realizes F ∧ ∀ x,
      (genC n m j r hn hj hr F).E x ≤
        2 * n + 1 + (2 ^ 2 ^ j - 1) + (m + r - 1) / r * (n - j) + m * Nat.clog 2 r := by
  -- значения входов декодера блока `β`
  have hD : ∀ x (β : Fin (nb m r)), (fun v : Fin (2 ^ rb m r β) =>
      (comp (comp (mtC n hn) id (stB n j hj)) finProdFinEquiv.symm (stC n m j r F)).eval x
        (fD m r (finProdFinEquiv (β, ⟨v, lt_of_lt_of_le v.2
          (Nat.pow_le_pow_right (by norm_num) (rb_le m r β))⟩)))) =
      uvec (2 ^ rb m r β) (bw r (F x) β) := by
    intro x β
    funext v
    rw [inD_eq]
    simp only [uvec]
    rw [decide_eq_decide]
    exact eq_comm
  constructor
  · intro x
    funext c
    simp only [genC, reout_eval]
    rw [comp_eval, stD, parF_eval, reout_eval, sel_eval, hD x,
      ((dec_spec _) _ (bw_lt r (F x) _)).1]
    have h1 := mod_lt_rb hr c.2
    simp only [show min (c % r) (rb m r (c / r) - 1) = c % r by omega]
    exact testBit_bw hr (F x) c.2
  · intro x
    simp only [genC, reout_E]
    rw [comp_E, comp_E, comp_E, inB_eq, inC_eq]
    have e1 := (mtC_spec n hn x).2
    have e2 := stB_E j hj x
    have e3 : (stC n m j r F).E (inC j hj x) ≤ (m + r - 1) / r * (n - j) := stC_E F r j hj x
    have e4 : (stD m r hr).E (fun i => (comp (comp (mtC n hn) id (stB n j hj))
        finProdFinEquiv.symm (stC n m j r F)).eval x (fD m r i)) ≤ m * Nat.clog 2 r := by
      rw [stD, parF_E]
      calc ∑ β : Fin (nb m r), (sel (dec (rb m r β)) fun v => finProdFinEquiv (β, ⟨v,
            lt_of_lt_of_le v.2 (Nat.pow_le_pow_right (by norm_num) (rb_le m r β))⟩)).E
              (fun i => (comp (comp (mtC n hn) id (stB n j hj))
                finProdFinEquiv.symm (stC n m j r F)).eval x (fD m r i))
          ≤ ∑ β : Fin (nb m r), rb m r β * Nat.clog 2 r := by
            apply Finset.sum_le_sum
            intro β _
            rw [sel_E, hD x β]
            exact ((dec_spec _) _ (bw_lt r (F x) _)).2.trans
              (Nat.mul_le_mul_left _ (Nat.clog_mono_right _ (rb_le m r β)))
        _ = m * Nat.clog 2 r := by rw [← Finset.sum_mul, sum_rb m r hr]
    omega

end Up

end PowerActivity
