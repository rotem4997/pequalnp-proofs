import PEqualNP.MetaComplexity.Helpers.Parity3

/-!
# Parity needs `4 (n - 1)` gates

Helper for `L-meta-031`. Take a clean circuit of least size for parity or its complement on at
least two inputs. Least size gives two facts: no gate computes a constant, and no gate computes
the same function as an earlier wire, because such a gate can be dropped.

Fix one input to a constant and run the pass of `Elim.lean`. A gate is touched when it reads a
wire of constant status; touched gates are not emitted. It is shown that for some input and
some constant either four gates are touched, or three are touched and the restricted circuit
has a gate equal to an earlier wire, which is then dropped. So four gates are saved.

The argument, by contradiction. If two gates are constant for the same fixing, four gates are
touched. So no input has a NOT gate on it, and the first gate `G` is an AND or OR of two
inputs `x`, `y`. Each of `x`, `y` has exactly one other reader. If these readers differ, the
other reader of `x` copies `x` once `y` is fixed to the absorbing constant of `G`. If they are
the same gate `r`, then `G` has one reader `h1` and `r` has one reader `h2`, and each of the
second inputs of `h1`, `h2` must depend on the fixed input through the other gate, which the
order of the gates forbids.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-! ## Values of wires -/

/-- The value of wire `j` of the gate list `gs` on the input `u`. -/
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

/-- An AND or OR gate with an input at its absorbing value has that value. -/
theorem vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩

/-- Two inputs that agree outside the wire set `B` give wires that agree outside `B`, below the
bound `L`, as soon as every gate outside `B` that reads `B` agrees whenever the earlier wires
outside `B` do. -/
theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

/-- A wire that is not a constant function takes both values. -/
theorem takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

/-! ## Dropping a gate -/

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

/-- A gate that computes the same function as an earlier wire can be dropped. -/
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

/-- A gate that computes a constant can be dropped. -/
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

/-! ## Statuses -/

/-- The input `y` with the value `b` inserted at position `i`. -/
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

/-- The gates the pass emits when input `i` is fixed to `b`. -/
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

/-- The final status of wire `a` is a constant when input `i` is fixed to `b`. -/
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k

/-- The final status of a gate is what `simplify` makes of the final statuses of its inputs. -/
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

/-- A gate that reads no wire of constant status gets a fresh wire. -/
theorem st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩

theorem rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

/-- A gate of non-constant status that reads a wire of constant status `c`: it is an AND or OR
gate, `c` is not its absorbing value, and another input has non-constant status. -/
theorem st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'

theorem four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount

/-! ## A least circuit that cannot be reduced by four -/

/-- Fixing some input of `gs` to some constant gives a clean circuit with four gates fewer. -/
def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o

/-- The hypotheses of the contradiction: a clean circuit whose output flips with every input,
whose restrictions are not constant, with no constant gate and no gate equal to an earlier
wire, and which cannot be reduced by four gates. -/
structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

theorem Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)

theorem Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)

theorem Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩

/-- Three gates are touched and, after the pass, the old wire `p` is a new gate that agrees
with the old wire `j`, an earlier new wire: impossible. -/
theorem Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩

theorem Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])

/-- A set `B` of wires of constant status containing the fixed input: two gates outside `B`
are touched. -/
theorem Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]

/-- No two gates have constant status for the same fixing. -/
theorem Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2

theorem Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)

/-- No NOT gate reads an input. -/
theorem Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0

/-- The only readers of input `X` are the gates `p` and `q`. If `q` agrees on `u` and on `u`
with `X` flipped, or nothing reads `q`, then `p` has the value of `X` on `u`. -/
theorem Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo

/-- Flip input `Z`. Outside the wire set `B` only the gates `ha`, `hb` read `B`; `ha` has an
input outside `B` at its absorbing value and the inputs of `hb` in `B` agree: impossible. -/
theorem Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa

/-- A wire outside `B` that changes when input `Z` is flipped comes after some gate outside `B`
that reads `B`. -/
theorem Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim

/-- The gate `G` is an AND or OR of the inputs `X` and `Y`: another gate reads `X`. -/
theorem Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)

/-- The gate `G` is an AND or OR of the inputs `X` and `Y`: exactly one other gate `r` reads
`X`. It is an AND or OR gate with the other absorbing value, and it does not read `G`. -/
theorem Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)

/-- No gate is an AND or OR of two distinct inputs. -/
theorem Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega

/-- The hypotheses are contradictory. -/
theorem Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)

end

/-! ## Parity -/

/-- A clean circuit for parity or its complement on `n + 1` inputs has at least `4 n` gates. -/
theorem par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra

/-- Parity of `n` inputs needs at least `4 (n - 1)` gates. -/
theorem parity_lower4 : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega

end PEqualNP.MetaComplexity.Helpers
