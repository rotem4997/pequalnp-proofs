import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (as bs : List Gate) (w : List Bool) : W (as ++ bs) w = W bs (W as w) := by
  unfold W
  rw [List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_len (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_snoc_lt (a : List Bool) (v : Bool) (i : ℕ) (h : i < a.length) :
    (a ++ [v]).getD i false = a.getD i false := List.getD_append _ _ _ _ h

theorem getD_snoc_eq (a : List Bool) (v : Bool) (i : ℕ) (h : i = a.length) :
    (a ++ [v]).getD i false = v := by
  subst h
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem getD_snoc_gt (a : List Bool) (v : Bool) (i : ℕ) (h : a.length < i) :
    (a ++ [v]).getD i false = false := by
  apply List.getD_eq_default
  rw [List.length_append, List.length_singleton]
  omega

theorem getD_ge (a : List Bool) (i : ℕ) (h : a.length ≤ i) : a.getD i false = false := by
  apply List.getD_eq_default
  exact h

theorem W_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_snoc_lt w _ i hi

theorem hop_eq (r : ℕ → ℕ) (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool)
    (_ : op = GateOp.and ∨ op = GateOp.or) (h : ∀ i, f i = f' (r i)) :
    op.eval (l.map f) = op.eval ((l.map r).map f') := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h i

theorem hop_le (r : ℕ → ℕ) (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) (h : ∀ i, f i = true → f' (r i) = true) :
    op.eval (l.map f) = true → op.eval ((l.map r).map f') = true := by
  rcases hop with rfl | rfl
  · intro hall
    have h1 : (l.map f).all id = true := hall
    show ((l.map r).map f').all id = true
    rw [List.all_eq_true] at h1 ⊢
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    exact h i (h1 (f i) (List.mem_map.2 ⟨i, hi, rfl⟩))
  · intro hany
    have h1 : (l.map f).any id = true := hany
    show ((l.map r).map f').any id = true
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨b, hb, hbt⟩ := h1
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact ⟨f' (r i), List.mem_map.2 ⟨r i, List.mem_map.2 ⟨i, hi, rfl⟩, rfl⟩, h i hbt⟩

theorem and_base (gm : Gate) (hop : gm.op = GateOp.and) (p : ℕ) (hp : p ∈ gm.inputs)
    (f : ℕ → Bool) : gm.op.eval (gm.inputs.map f) = true → f p = true := by
  rw [hop]
  intro h
  have h1 : (gm.inputs.map f).all id = true := h
  rw [List.all_eq_true] at h1
  exact h1 (f p) (List.mem_map.2 ⟨p, hp, rfl⟩)

theorem step_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ)
    (hp : p < n + m) (a b : List Bool) (va vb : Bool) (hl : a.length = b.length + 1)
    (hn : n + m < a.length)
    (h : ∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) (hv : rel va vb) :
    ∀ i, rel ((a ++ [va]).getD i false) ((b ++ [vb]).getD (eraseRedirect n m p i) false) := by
  intro i
  by_cases hi : i < a.length
  · have hri : eraseRedirect n m p i < b.length := by
      unfold eraseRedirect
      split_ifs <;> omega
    rw [getD_snoc_lt a va i hi, getD_snoc_lt b vb _ hri]
    exact h i
  · have hri : eraseRedirect n m p i = i - 1 := by
      unfold eraseRedirect
      rw [if_neg (by omega), if_pos (by omega)]
    rw [hri]
    by_cases hi2 : i = a.length
    · rw [getD_snoc_eq a va i hi2, getD_snoc_eq b vb (i - 1) (by omega)]
      exact hv
    · rw [getD_snoc_gt a va i (by omega), getD_snoc_gt b vb (i - 1) (by omega)]
      exact h00

theorem W_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool),
      (op = GateOp.and ∨ op = GateOp.or) →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (gs : List Gate) : ∀ (a b : List Bool),
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      a.length = b.length + 1 → n + m < a.length →
      (∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) →
      ∀ i, rel ((W gs a).getD i false)
        ((W (gs.map (rg (eraseRedirect n m p))) b).getD (eraseRedirect n m p i) false) := by
  induction gs with
  | nil => intro a b _ _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hg hl hn h i
    rw [List.map_cons, W_cons, W_cons]
    refine ih (step a g) (step b (rg (eraseRedirect n m p) g)) ?_ ?_ ?_ ?_ i
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · rw [step_len, step_len, hl]
    · rw [step_len]
      omega
    · exact step_rel rel h00 n m p hp a b
        (g.op.eval (g.inputs.map fun i => a.getD i false))
        (g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => b.getD i false))
        hl hn h
        (hop g.op g.inputs (fun i => a.getD i false) (fun i => b.getD i false)
          (hg g (by simp)) h)

theorem sem (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b) (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool),
      (op = GateOp.and ∨ op = GateOp.or) →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (pre post : List Gate) (gm : Gate) (x : List Bool) (hx : x.length = n)
    (hpre : pre.length = m)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hbase : rel (gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false))
      ((W pre x).getD p false)) :
    ∀ i, rel ((W (pre ++ gm :: post) x).getD i false)
      ((W (pre ++ post.map (rg (eraseRedirect n m p))) x).getD (eraseRedirect n m p i) false) := by
  have hA : (W pre x).length = n + m := by rw [W_len, hx, hpre]
  rw [W_append, W_append, W_cons]
  refine W_rel rel (hrefl false) n m p hp hop post (step (W pre x) gm) (W pre x) hpost ?_ ?_ ?_
  · exact step_len _ _
  · rw [step_len, hA]
    omega
  · intro i
    show rel ((W pre x ++ [gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false)]).getD i
      false) ((W pre x).getD (eraseRedirect n m p i) false)
    by_cases hi : i < n + m
    · have hri : eraseRedirect n m p i = i := by
        unfold eraseRedirect
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hri, getD_snoc_lt (W pre x) _ i (by omega)]
      exact hrefl _
    · by_cases hi2 : i = n + m
      · have hri : eraseRedirect n m p i = p := by
          unfold eraseRedirect
          rw [if_pos hi2]
        rw [hri, getD_snoc_eq (W pre x) _ i (by omega)]
        exact hbase
      · have hri : eraseRedirect n m p i = i - 1 := by
          unfold eraseRedirect
          rw [if_neg hi2, if_pos (by omega)]
        rw [hri, getD_snoc_gt (W pre x) _ i (by omega), getD_ge (W pre x) (i - 1) (by omega)]
        exact hrefl false

theorem base_eq (A : List Bool) (gm : Gate) (post : List Gate) (k p : ℕ) (hA : A.length = k)
    (hp : p < k)
    (hyp : (W post (step A gm)).getD k false = (W post (step A gm)).getD p false) :
    gm.op.eval (gm.inputs.map fun i => A.getD i false) = A.getD p false := by
  rw [W_prefix post (step A gm) k (by rw [step_len]; omega),
    W_prefix post (step A gm) p (by rw [step_len]; omega)] at hyp
  have e1 : (step A gm).getD k false = gm.op.eval (gm.inputs.map fun i => A.getD i false) :=
    getD_snoc_eq A (gm.op.eval (gm.inputs.map fun i => A.getD i false)) k hA.symm
  have e2 : (step A gm).getD p false = A.getD p false :=
    getD_snoc_lt A (gm.op.eval (gm.inputs.map fun i => A.getD i false)) p (by omega)
  rw [e1, e2] at hyp
  exact hyp

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p = Circuit.mk
      (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg (eraseRedirect n m p)))
      (eraseRedirect n m p C.output) := if_pos hm

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates
      = C.gates.take m ++ (C.gates.drop (m + 1)).map (rg (eraseRedirect n m p)) :=
  congrArg Circuit.gates (erase_eq n C m p hm)

theorem erase_output (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output :=
  congrArg Circuit.output (erase_eq n C m p hm)

theorem getD_erase (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
    (hj : j + 1 < l.length) :
    (l.take m ++ (l.drop (m + 1)).map f).getD j d
      = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
  have hlt : (l.take m).length = m := by
    rw [List.length_take]
    omega
  by_cases h : j < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
      List.getElem_take]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hlt]
    have e : m + 1 + (j - m) = j + 1 := by omega
    rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
        (by rw [List.length_map, List.length_drop]; omega),
      List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
    simp only [e]

theorem main_clean (n : ℕ) (C : Circuit) (m p : ℕ) (hM : Monotone2 C) (hR : ReadsBack n C)
    (hm : m < C.gates.length) (hpl : p < n + m) :
    Monotone2 (eraseGate n C m p) ∧ ReadsBack n (eraseGate n C m p) ∧
    (eraseGate n C m p).size + 1 = C.size ∧ ∀ x : List Bool, x.length = n →
      ((C.wires x).getD p false = (C.wires x).getD (n + m) false →
        (eraseGate n C m p).eval x = C.eval x) := by
  have hgm : gateAt C m = C.gates[m] := List.getD_eq_getElem _ _ hm
  have hsplit : C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1) = C.gates := by
    rw [hgm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hEg := erase_gates n C m p hm
  have hEo := erase_output n C m p hm
  have hElen : (eraseGate n C m p).gates.length + 1 = C.gates.length := by
    rw [hEg, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [hEg] at hg
    rcases List.mem_append.1 hg with h | h
    · exact hM g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have h0 := hM g0 (List.mem_of_mem_drop hg0)
      refine ⟨h0.1, ?_⟩
      show (g0.inputs.map (eraseRedirect n m p)).length ≤ 2
      rw [List.length_map]
      exact h0.2
  · intro j hj i hi
    have hga : gateAt (eraseGate n C m p) j
        = if j < m then gateAt C j else rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
      have h0 : gateAt (eraseGate n C m p) j
          = (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg (eraseRedirect n m p))).getD j
            (Gate.mk GateOp.or []) :=
        congrArg (fun gs : List Gate => gs.getD j (Gate.mk GateOp.or [])) hEg
      rw [h0]
      exact getD_erase C.gates (rg (eraseRedirect n m p)) (Gate.mk GateOp.or []) m j hm
        (by omega)
    rw [hga] at hi
    by_cases hjm : j < m
    · rw [if_pos hjm] at hi
      exact hR j (by omega) i hi
    · rw [if_neg hjm] at hi
      have hi' : i ∈ (gateAt C (j + 1)).inputs.map (eraseRedirect n m p) := hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
      have h2 := hR (j + 1) (by omega) i0 hi0
      unfold eraseRedirect
      split_ifs <;> omega
  · show (eraseGate n C m p).gates.length + 1 = C.gates.length
    exact hElen
  · intro x hx
    have hpost : ∀ g ∈ C.gates.drop (m + 1), g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have h := (hM g (List.mem_of_mem_drop hg)).1
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h
    have hpre : (C.gates.take m).length = m := by
      rw [List.length_take]
      omega
    have hW : C.wires x = W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x :=
      congrArg (fun gs : List Gate => W gs x) hsplit.symm
    have hWD : (eraseGate n C m p).wires x
        = W (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg (eraseRedirect n m p))) x :=
      congrArg (fun gs : List Gate => W gs x) hEg
    have hfact : W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x
        = W (C.gates.drop (m + 1)) (step (W (C.gates.take m) x) (gateAt C m)) := by
      rw [W_append, W_cons]
    have hA : (W (C.gates.take m) x).length = n + m := by rw [W_len, hx, hpre]
    intro hyp
    have hyp' : (W (C.gates.drop (m + 1)) (step (W (C.gates.take m) x) (gateAt C m))).getD
        (n + m) false
        = (W (C.gates.drop (m + 1)) (step (W (C.gates.take m) x) (gateAt C m))).getD p
          false := by
      rw [← hfact, ← hW]
      exact hyp.symm
    have hv := base_eq (W (C.gates.take m) x) (gateAt C m) (C.gates.drop (m + 1)) (n + m) p
      hA hpl hyp'
    have key := sem (@Eq Bool) (fun _ => rfl) n m p hpl
      (hop_eq (eraseRedirect n m p)) (C.gates.take m) (C.gates.drop (m + 1)) (gateAt C m)
      x hx hpre hpost hv C.output
    show ((eraseGate n C m p).wires x).getD (eraseGate n C m p).output false
      = (C.wires x).getD C.output false
    rw [hWD, hEo, hW]
    exact key.symm

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m p hM hR hm hp
  obtain ⟨h1, h2, h3, h4⟩ := main_clean n C m p hM hR hm hp
  refine ⟨h1, h2, h3, ?_⟩
  intro x hx
  exact h4 (List.ofFn x) (List.length_ofFn) hx

end PEqualNP.Outside.L_meta_2859

theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  PEqualNP.Outside.L_meta_2859.main_aux
