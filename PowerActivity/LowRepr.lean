import PowerActivity.LowLayer
import PowerActivity.LowEnt

/-!
# Представление `F(x) = G_d(x, Z_d(x))` (`rev-layers`) и описание схемы (для `encoding`)

Схема `G_d` — список элементов над `n + q` входами (`q = |L_{d+1}|`): входы `x`,
дополнительные входы — элементы слоя `L_{d+1}` (перенумерованные по возрастанию), затем
элементы шара `B_d` (перенумерованные по возрастанию, поэтому топологический порядок
сохраняется). Перенумерация сигналов — `Circ.rvTr`.

* `Circ.rv_sig_tr` — сигналы `G_d` на наборе `(x, Z_d(x))` совпадают с сигналами исходной схемы
  (для входов и элементов `B_{d+1} = B_d ∪ L_{d+1}`);
* `Low.Desc n m q s` — «сырое» описание (элементы, выходы, таблицы `L_{d+1}`), `Low.decode` —
  вычисление оператора по описанию (определено для любого описания);
* `Circ.rvEncode` — описание схемы, `Circ.rv_decode_encode` — `decode (rvEncode C d) = F`;
* `Circ.rvS`, `Circ.rvA` — `S_d = Σ_{v ∈ L_{d+1}} h₂(p_v)`, `A_d = Σ_{v ∈ L_{d+1}} p_v`;
  `Circ.rvEncode_tab_sum` — сумма энтропий таблиц описания равна `S_d`.
-/

namespace PowerActivity

open Finset

/-- Второй источник элемента; у `¬` берём первый (второй вход `¬` не используется). -/
def Gate.lowBsrc (g : Gate) : ℕ := if g.op = .not then g.a else g.b

lemma Gate.lowBsrc_mem (g : Gate) : g.lowBsrc ∈ g.srcs := by
  unfold Gate.lowBsrc; split_ifs with h
  · exact g.lowA_mem
  · exact g.lowB_mem h

namespace Circ

variable {n m : ℕ} (C : Circ n (Fin m)) (d : ℕ)

/-- Номер элемента слоя `L_{d+1}` (по возрастанию). -/
noncomputable def rvLidx (i : ℕ) (h : i ∈ C.rvLayer d) : Fin (C.rvLayer d).card :=
  ((C.rvLayer d).orderIsoOfFin rfl).symm ⟨i, h⟩

/-- Номер элемента шара `B_d` (по возрастанию). -/
noncomputable def rvBidx (i : ℕ) (h : i ∈ C.rvBall d) : Fin (C.rvBall d).card :=
  ((C.rvBall d).orderIsoOfFin rfl).symm ⟨i, h⟩

/-- Элемент слоя `L_{d+1}` по номеру. -/
noncomputable def rvLel (v : Fin (C.rvLayer d).card) : ℕ := (C.rvLayer d).orderEmbOfFin rfl v

/-- Элемент шара `B_d` по номеру. -/
noncomputable def rvBel (v : Fin (C.rvBall d).card) : ℕ := (C.rvBall d).orderEmbOfFin rfl v

lemma rvLel_lidx (i : ℕ) (h : i ∈ C.rvLayer d) : C.rvLel d (C.rvLidx d i h) = i := by
  unfold rvLel rvLidx
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

lemma rvBel_bidx (i : ℕ) (h : i ∈ C.rvBall d) : C.rvBel d (C.rvBidx d i h) = i := by
  unfold rvBel rvBidx
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

lemma rvBel_mem (v : Fin (C.rvBall d).card) : C.rvBel d v ∈ C.rvBall d :=
  orderEmbOfFin_mem _ _ _

lemma rvBidx_lt {i i' : ℕ} (h : i ∈ C.rvBall d) (h' : i' ∈ C.rvBall d) (hlt : i < i') :
    C.rvBidx d i h < C.rvBidx d i' h' := by
  unfold rvBidx
  rw [OrderIso.lt_iff_lt]
  exact hlt

/-- Перенумерация сигналов исходной схемы в сигналы `G_d`. -/
noncomputable def rvTr (j : ℕ) : ℕ :=
  if j < n then j
  else if h : j - n ∈ C.rvLayer d then n + (C.rvLidx d (j - n) h : ℕ)
  else if h' : j - n ∈ C.rvBall d then n + (C.rvLayer d).card + (C.rvBidx d (j - n) h' : ℕ)
  else 0

lemma rvTr_of_lt {j : ℕ} (hj : j < n) : C.rvTr d j = j := by simp [rvTr, hj]

lemma rvTr_layer {i : ℕ} (h : i ∈ C.rvLayer d) :
    C.rvTr d (n + i) = n + (C.rvLidx d i h : ℕ) := by
  have hn : ¬ (n + i < n) := by omega
  unfold rvTr
  simp only [hn, Nat.add_sub_cancel_left]
  simp [h]

lemma rvTr_ball {i : ℕ} (h : i ∈ C.rvBall d) :
    C.rvTr d (n + i) = n + (C.rvLayer d).card + (C.rvBidx d i h : ℕ) := by
  have hn : ¬ (n + i < n) := by omega
  unfold rvTr
  simp only [hn, Nat.add_sub_cancel_left]
  simp [C.rv_not_mem_layer h, h]

/-- Область перенумерации: входы и элементы `B_{d+1}`. -/
def RvDom (j : ℕ) : Prop := j < n ∨ (n ≤ j ∧ j - n ∈ C.rvBall (d + 1))

lemma rvDom_src {i : ℕ} (hi : i ∈ C.rvBall d) {a : ℕ} (ha : a ∈ (C.gate i).srcs) :
    C.RvDom d a := by
  by_cases han : a < n
  · exact Or.inl han
  · exact Or.inr ⟨by omega, C.rv_pred_mem hi ha (by omega)⟩

lemma rvDom_out (k : Fin m) : C.RvDom d (C.out k) := by
  rcases C.rv_out_mem k with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, C.rvBall_mono (by omega) h2⟩

lemma rvTr_lt_K {j : ℕ} (hj : C.RvDom d j) :
    C.rvTr d j < n + (C.rvLayer d).card + (C.rvBall d).card := by
  rcases hj with hj | ⟨hjn, hjB⟩
  · rw [C.rvTr_of_lt d hj]; omega
  · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
    simp only [Nat.add_sub_cancel_left] at hjB
    by_cases hL : i ∈ C.rvLayer d
    · rw [C.rvTr_layer d hL]
      have := (C.rvLidx d i hL).2
      omega
    · have hB := C.rv_mem_ball_of_not_layer hjB hL
      rw [C.rvTr_ball d hB]
      have := (C.rvBidx d i hB).2
      omega

/-- Номер источника входа элемента `i ∈ B_d` в `G_d` меньше номера самого элемента. -/
lemma rvTr_src_lt {i : ℕ} (hi : i ∈ C.rvBall d) {a : ℕ} (ha : a ∈ (C.gate i).srcs) :
    C.rvTr d a < n + (C.rvLayer d).card + (C.rvBidx d i hi : ℕ) := by
  have hlt := C.rv_src_lt (C.rvBall_lt hi) ha
  by_cases han : a < n
  · rw [C.rvTr_of_lt d han]; omega
  · obtain ⟨a', rfl⟩ : ∃ a', a = n + a' := ⟨a - n, by omega⟩
    have hB1 : a' ∈ C.rvBall (d + 1) := by
      have := C.rv_pred_mem hi ha (by omega)
      simpa using this
    by_cases hL : a' ∈ C.rvLayer d
    · rw [C.rvTr_layer d hL]
      have := (C.rvLidx d a' hL).2
      omega
    · have hB := C.rv_mem_ball_of_not_layer hB1 hL
      rw [C.rvTr_ball d hB]
      have := C.rvBidx_lt d hB hi (by omega)
      rw [Fin.lt_def] at this
      omega

/-- Элемент `G_d` с номером `v`: тот же тип, источники перенумерованы. -/
noncomputable def rvGate (v : Fin (C.rvBall d).card) : Gate :=
  ⟨(C.gate (C.rvBel d v)).op, C.rvTr d (C.gate (C.rvBel d v)).a,
    C.rvTr d (C.gate (C.rvBel d v)).lowBsrc⟩

/-- Элементы схемы `G_d`. -/
noncomputable def rvGates : List Gate := List.ofFn (C.rvGate d)

/-- Входной набор `G_d`: `(x, Z_d(x))`, `Z_d = (φ_v)_{v ∈ L_{d+1}}`. -/
noncomputable def rvInput (x : Fin n → Bool) : Fin (n + (C.rvLayer d).card) → Bool :=
  Fin.append x fun v => C.val x (C.rvLel d v)

/-- **Представление `F(x) = G_d(x, Z_d(x))`.** Сигналы `G_d` на наборе `(x, Z_d(x))` совпадают
с сигналами исходной схемы на входах и на элементах `B_{d+1}`. -/
theorem rv_sig_tr (x : Fin n → Bool) : ∀ j, C.RvDom d j →
    PowerActivity.sig (n + (C.rvLayer d).card) (C.rvGates d) (C.rvInput d x) (C.rvTr d j) =
      C.sig x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rcases hj with hj | ⟨hjn, hjB⟩
  · rw [C.rvTr_of_lt d hj, sig_lt _ _ (by omega)]
    simp only [rvInput, Circ.sig, sig_lt _ _ hj]
    exact Fin.append_left x _ ⟨j, hj⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
    simp only [Nat.add_sub_cancel_left] at hjB
    by_cases hL : i ∈ C.rvLayer d
    · rw [C.rvTr_layer d hL, sig_lt _ _ (by have := (C.rvLidx d i hL).2; omega)]
      simp only [rvInput]
      have e : (⟨n + (C.rvLidx d i hL : ℕ), by have := (C.rvLidx d i hL).2; omega⟩ :
          Fin (n + (C.rvLayer d).card)) = Fin.natAdd n (C.rvLidx d i hL) := Fin.ext rfl
      rw [e, Fin.append_right, C.rvLel_lidx]
      rfl
    · have hB := C.rv_mem_ball_of_not_layer hjB hL
      have hi : i < C.s := C.rvBall_lt hB
      rw [C.rvTr_ball d hB]
      set v := C.rvBidx d i hB with hv
      have hbel : C.rvBel d v = i := C.rvBel_bidx d i hB
      have hlen : (v : ℕ) < (C.rvGates d).length := by simp [rvGates]
      have hget : (C.rvGates d)[(v : ℕ)] = C.rvGate d v := by simp [rvGates]
      have ha : (C.rvGates d)[(v : ℕ)].a < n + (C.rvLayer d).card + v := by
        rw [hget]; simp only [rvGate, hbel]; exact C.rvTr_src_lt d hB (Gate.lowA_mem _)
      have hb : (C.rvGates d)[(v : ℕ)].b < n + (C.rvLayer d).card + v := by
        rw [hget]; simp only [rvGate, hbel]; exact C.rvTr_src_lt d hB (Gate.lowBsrc_mem _)
      rw [sig_gate _ _ hlen ha hb, hget]
      simp only [rvGate, hbel]
      have e1 := C.val_eq x hi
      simp only [Circ.val] at e1
      rw [e1]
      apply Gate.low_eval_congr
      · exact ih _ (C.rv_src_lt hi (Gate.lowA_mem _)) (C.rvDom_src d hB (Gate.lowA_mem _))
      · intro hop
        have hbs : (C.gate i).lowBsrc = (C.gate i).b := by simp [Gate.lowBsrc, hop]
        rw [ih _ (C.rv_src_lt hi (Gate.lowBsrc_mem _)) (C.rvDom_src d hB (Gate.lowBsrc_mem _)),
          hbs]

end Circ

/-! ## Описания и декодирование -/

namespace Low

/-- Описание оператора: элементы `G_d` (тип и номера источников), номера выходов,
таблицы элементов `L_{d+1}`. -/
abbrev Desc (n m q s : ℕ) :=
  (Fin s → Op × Fin (n + q + s) × Fin (n + q + s)) × (Fin m → Fin (n + q + s)) ×
    (Fin q → (Fin n → Bool) → Bool)

/-- Элементы, записанные в описании. -/
def descGates {n q s : ℕ} (g : Fin s → Op × Fin (n + q + s) × Fin (n + q + s)) : List Gate :=
  List.ofFn fun i => ⟨(g i).1, (g i).2.1, (g i).2.2⟩

/-- Оператор, восстановленный по описанию: `F(x) = G(x, Z(x))` (без условий правильности). -/
def decode {n m q s : ℕ} (D : Desc n m q s) : (Fin n → Bool) → Fin m → Bool :=
  fun x k => sig (n + q) (descGates D.1) (Fin.append x fun v => D.2.2 v x) (D.2.1 k)

end Low

namespace Circ

variable {n m : ℕ} (C : Circ n (Fin m)) (d : ℕ)

lemma rvGate_a_lt (v : Fin (C.rvBall d).card) :
    (C.rvGate d v).a < n + (C.rvLayer d).card + (C.rvBall d).card :=
  C.rvTr_lt_K d (C.rvDom_src d (C.rvBel_mem d v) (Gate.lowA_mem _))

lemma rvGate_b_lt (v : Fin (C.rvBall d).card) :
    (C.rvGate d v).b < n + (C.rvLayer d).card + (C.rvBall d).card :=
  C.rvTr_lt_K d (C.rvDom_src d (C.rvBel_mem d v) (Gate.lowBsrc_mem _))

/-- Описание схемы для данного `d`. -/
noncomputable def rvEncode : Low.Desc n m (C.rvLayer d).card (C.rvBall d).card :=
  (fun v => ((C.rvGate d v).op, ⟨(C.rvGate d v).a, C.rvGate_a_lt d v⟩,
      ⟨(C.rvGate d v).b, C.rvGate_b_lt d v⟩),
    fun k => ⟨C.rvTr d (C.out k), C.rvTr_lt_K d (C.rvDom_out d k)⟩,
    fun v x => C.val x (C.rvLel d v))

/-- **Восстановление оператора по описанию.** -/
theorem rv_decode_encode {F : (Fin n → Bool) → Fin m → Bool} (hC : C.Realizes F) :
    Low.decode (C.rvEncode d) = F := by
  funext x k
  have hG : Low.descGates (C.rvEncode d).1 = C.rvGates d := rfl
  have hy : (Fin.append x fun v => (C.rvEncode d).2.2 v x) = C.rvInput d x := rfl
  simp only [Low.decode, hG, hy]
  rw [show ((C.rvEncode d).2.1 k : ℕ) = C.rvTr d (C.out k) from rfl,
    C.rv_sig_tr d x _ (C.rvDom_out d k)]
  exact congrFun (hC x) k

/-- `S_d = Σ_{v ∈ L_{d+1}} h₂(p_v)`. -/
noncomputable def rvS : ℝ := ∑ i ∈ C.rvLayer d, h2 (C.lowP i)

/-- `A_d = Σ_{v ∈ L_{d+1}} p_v`. -/
noncomputable def rvA : ℝ := ∑ i ∈ C.rvLayer d, C.lowP i

lemma rv_sum_layer (f : ℕ → ℝ) : ∑ v, f (C.rvLel d v) = ∑ i ∈ C.rvLayer d, f i := by
  have h := map_orderEmbOfFin_univ (C.rvLayer d) rfl
  calc ∑ v, f (C.rvLel d v)
      = ∑ i ∈ univ.map ((C.rvLayer d).orderEmbOfFin rfl).toEmbedding, f i := by
        rw [sum_map]; rfl
    _ = ∑ i ∈ C.rvLayer d, f i := by rw [h]

/-- Сумма энтропий таблиц описания равна `S_d`. -/
lemma rvEncode_tab_sum :
    ∑ v, h2 ((Low.wt ((C.rvEncode d).2.2 v) : ℝ) / (2 ^ n : ℕ)) = C.rvS d := by
  unfold rvS
  rw [← C.rv_sum_layer d]
  apply sum_congr rfl
  intro v _
  unfold lowP
  push_cast
  rfl

end Circ

end PowerActivity
