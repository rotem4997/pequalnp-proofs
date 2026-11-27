import Mathlib
import PEqualNP.Defs

-- One lift step keeps the two-input AND/OR form, the output inside the wires, the size
-- and the function. The gate list is split at the lifted gate; the wires of the erased
-- circuit are the old wires under the renaming whenever the lifted operand is false, and
-- when it is true both outputs are true.
namespace PEqualNP.Outside.L_meta_4293

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem wiresFrom_input (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have s : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s, ih _ i (by simp; omega), getD_snoc_ne _ _ _ _ (by omega)]

theorem wiresFrom_or (U : List Bool) (a b : ℕ) :
    wiresFrom [(⟨GateOp.or, [a, b]⟩ : Gate)] U = U ++ [(U.getD a false || U.getD b false)] := by
  simp [wiresFrom, GateOp.eval]

theorem lift_last (n : ℕ) (A : List Gate) (a b : ℕ) (w : List Bool) (hw : w.length = n) :
    (wiresFrom (A ++ [⟨GateOp.or, [a, b]⟩]) w).getD (n + A.length) false
      = ((wiresFrom A w).getD a false || (wiresFrom A w).getD b false) := by
  rw [wiresFrom_append, wiresFrom_or, ← hw, ← length_wiresFrom A w, getD_snoc_eq]

theorem eval_eq (C : Circuit) (w : List Bool) :
    C.eval w = (wiresFrom C.gates w).getD C.output false := rfl

-- Every gate of the list reads only wires below its own index, the first gate being
-- wire k.
def RBfrom : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs => (∀ i ∈ g.inputs, i < k) ∧ RBfrom (k + 1) gs

theorem rbfrom_append : ∀ (l1 l2 : List Gate) (k : ℕ),
    RBfrom k (l1 ++ l2) ↔ RBfrom k l1 ∧ RBfrom (k + l1.length) l2
  | [], l2, k => by simp [RBfrom]
  | g :: l1, l2, k => by
    have ih := rbfrom_append l1 l2 (k + 1)
    have e : k + 1 + l1.length = k + (l1.length + 1) := by omega
    simp only [List.cons_append, RBfrom, List.length_cons, ih, e]
    tauto

theorem rbfrom_iff (d : Gate) : ∀ (gs : List Gate) (k : ℕ),
    RBfrom k gs ↔ ∀ j < gs.length, ∀ i ∈ (gs.getD j d).inputs, i < k + j
  | [], k => by simp [RBfrom]
  | g :: gs, k => by
    have ih := rbfrom_iff d gs (k + 1)
    simp only [RBfrom, ih]
    constructor
    · rintro ⟨h0, h1⟩ j hj i hi
      cases j with
      | zero => exact h0 i (by simpa using hi)
      | succ j =>
        have := h1 j (by simpa using hj) i (by simpa using hi)
        omega
    · intro h
      refine ⟨fun i hi => by simpa using h 0 (by simp) i (by simpa using hi), fun j hj i hi => ?_⟩
      have := h (j + 1) (by simpa using hj) i (by simpa using hi)
      omega

theorem rbfrom_erase (n m p : ℕ) (hp : p < n + m) : ∀ (post : List Gate) (k : ℕ),
    n + m ≤ k → RBfrom (k + 1) post →
      RBfrom k (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
  | [], _, _, _ => trivial
  | g :: post, k, hk, h => by
    refine ⟨?_, rbfrom_erase n m p hp post (k + 1) (by omega) h.2⟩
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
    have := h.1 i0 hi0
    unfold eraseRedirect
    split_ifs <;> omega

-- The wires of the erased list are the old wires under the renaming.
theorem sim (n m p : ℕ) (hp : p < n + m) (post : List Gate) :
    ∀ U V : List Bool, V.length = U.length + 1 → n + m ≤ U.length →
      (∀ i, U.getD (eraseRedirect n m p i) false = V.getD i false) →
      ∀ i, (wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) U).getD
          (eraseRedirect n m p i) false = (wiresFrom post V).getD i false := by
  induction post with
  | nil => intro U V _ _ h; exact h
  | cons g post ih =>
    intro U V hl hU h
    have s1 : wiresFrom ((g :: post).map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) U
        = wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
          (U ++ [g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => U.getD i false)]) :=
      rfl
    have s2 : wiresFrom (g :: post) V
        = wiresFrom post (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) := rfl
    have hval : g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => U.getD i false)
        = g.op.eval (g.inputs.map fun i => V.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    rw [s1, s2, hval]
    apply ih _ _ (by simp [hl]) (by simp; omega)
    intro i
    by_cases hi : i = V.length
    · have hr : eraseRedirect n m p i = U.length := by
        unfold eraseRedirect
        split_ifs <;> omega
      rw [hr, hi, getD_snoc_eq, getD_snoc_eq]
    · have hr : eraseRedirect n m p i ≠ U.length := by
        unfold eraseRedirect
        split_ifs <;> omega
      rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ hr]
      exact h i

theorem sim_base (n m p : ℕ) (W1 : List Bool) (hW1 : W1.length = n + m) (vg : Bool)
    (hvg : vg = W1.getD p false) :
    ∀ i, W1.getD (eraseRedirect n m p i) false = (W1 ++ [vg]).getD i false := by
  intro i
  by_cases hi : i = n + m
  · have hr : eraseRedirect n m p i = p := by
      unfold eraseRedirect
      split_ifs
      rfl
    rw [hr, hi, ← hW1, getD_snoc_eq, hvg]
  · rw [getD_snoc_ne _ _ _ _ (by omega)]
    unfold eraseRedirect
    split_ifs with h2
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    · rfl

theorem lift_eval (n m p h out : ℕ) (hp : p < n + m) (hh : h < n + m) (post : List Gate)
    (W1 : List Bool) (hW1 : W1.length = n + m) (vg : Bool)
    (hvg : vg = (W1.getD p false || W1.getD h false))
    (hbelow : (wiresFrom post (W1 ++ [vg])).getD h false = true →
      (wiresFrom post (W1 ++ [vg])).getD out false = true) :
    ((wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) W1).getD
        (eraseRedirect n m p out) false ||
      (wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) W1).getD h false)
      = (wiresFrom post (W1 ++ [vg])).getD out false := by
  have hUh : (wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) W1).getD
      h false = W1.getD h false := wiresFrom_input _ _ _ (by omega)
  have hVh : (wiresFrom post (W1 ++ [vg])).getD h false = W1.getD h false := by
    rw [wiresFrom_input _ _ _ (by simp; omega), getD_snoc_ne _ _ _ _ (by omega)]
  rw [hUh]
  rw [hVh] at hbelow
  cases hhv : W1.getD h false with
  | true =>
    rw [Bool.or_true]
    exact (hbelow hhv).symm
  | false =>
    rw [Bool.or_false]
    have hvg' : vg = W1.getD p false := by rw [hvg, hhv, Bool.or_false]
    exact sim n m p hp post W1 (W1 ++ [vg]) (by simp) (by omega)
      (sim_base n m p W1 hW1 vg hvg') out

theorem lift_shape (n : ℕ) (C : Circuit) (pre post : List Gate) (gm : Gate) (p h : ℕ)
    (hs : C.gates = pre ++ gm :: post) :
    liftAt n C pre.length p h =
      ⟨(pre ++ post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩) ++
          [⟨GateOp.or, [eraseRedirect n pre.length p C.output, h]⟩],
        n + (pre ++ post.map fun g =>
          (⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩ : Gate)).length⟩ := by
  have hlt : pre.length < C.gates.length := by rw [hs]; simp
  have htake : C.gates.take pre.length = pre := by rw [hs]; exact List.take_left' rfl
  have hdrop : C.gates.drop (pre.length + 1) = post := by
    rw [hs]
    have e : pre ++ gm :: post = (pre ++ [gm]) ++ post := by simp
    rw [e]
    exact List.drop_left' (by simp)
  have hE : eraseGate n C pre.length p =
      ⟨pre ++ post.map fun g => ⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩,
        eraseRedirect n pre.length p C.output⟩ := by
    unfold eraseGate
    rw [ite_eq_left hlt, htake, hdrop]
  unfold liftAt
  rw [hE]

end PEqualNP.Outside.L_meta_4293

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.Outside.L_meta_4293

theorem PEqualNP.Outside.L_meta_4293 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C C' hC hout hL
  obtain ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, rfl⟩ := hL
  obtain ⟨hAO, hRB, hTwo⟩ := hC
  obtain ⟨gm, hgm, hgmval⟩ : ∃ gm : Gate, C.gates[m]? = some gm ∧
      (gm = ⟨GateOp.or, [p, h]⟩ ∨ gm = ⟨GateOp.or, [h, p]⟩) := by
    rcases hgate with e | e
    · exact ⟨_, e, Or.inl rfl⟩
    · exact ⟨_, e, Or.inr rfl⟩
  obtain ⟨pre, post, hs, rfl⟩ : ∃ pre post : List Gate,
      C.gates = pre ++ gm :: post ∧ pre.length = m := by
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.1 hgm
    refine ⟨C.gates.take m, C.gates.drop (m + 1), ?_, by simp [List.length_take]; omega⟩
    rw [← hval, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  rw [lift_shape n C pre post gm p h hs]
  have hRB' : RBfrom n (pre ++ gm :: post) := by
    rw [← hs]
    exact (rbfrom_iff ⟨GateOp.or, []⟩ C.gates n).2 hRB
  rw [rbfrom_append] at hRB'
  obtain ⟨hRBpre, hRBrest⟩ := hRB'
  have hRBpost : RBfrom (n + pre.length + 1) post := hRBrest.2
  have hlen : C.gates.length = pre.length + post.length + 1 := by
    rw [hs]
    simp
    omega
  have hmemC : ∀ g : Gate, g ∈ pre ∨ g ∈ post → g ∈ C.gates := by
    intro g hg
    rw [hs]
    rcases hg with hg | hg
    · exact List.mem_append_left _ hg
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact hAO g (hmemC g (Or.inl hg))
    · exact hAO g0 (hmemC g0 (Or.inr hg0))
    · exact Or.inr rfl
  · refine (rbfrom_iff ⟨GateOp.or, []⟩ _ n).1 ?_
    rw [rbfrom_append, rbfrom_append]
    refine ⟨⟨hRBpre, rbfrom_erase n pre.length p hp post _ (le_refl _) hRBpost⟩, ?_, trivial⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_append, List.length_map]
    rcases hi with rfl | rfl
    · unfold eraseRedirect
      split_ifs <;> omega
    · omega
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact hTwo g (hmemC g (Or.inl hg))
    · simpa using hTwo g0 (hmemC g0 (Or.inr hg0))
    · rfl
  · simp
  · simp [Circuit.size, hlen]
    omega
  · funext x
    have hW1 : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]
      simp
    have hW : wiresFrom C.gates (List.ofFn x) = wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [gm.op.eval (gm.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [hs, wiresFrom_append]
      rfl
    have hvg : gm.op.eval (gm.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)
        = ((wiresFrom pre (List.ofFn x)).getD p false
          || (wiresFrom pre (List.ofFn x)).getD h false) := by
      rcases hgmval with rfl | rfl
      · simp [GateOp.eval]
      · simp [GateOp.eval, Bool.or_comm]
    have key := lift_eval n pre.length p h C.output hp hh post (wiresFrom pre (List.ofFn x)) hW1
      _ hvg (by
        have hb := hbelow x
        rw [← hW]
        exact hb)
    unfold PEqualNP.MetaComplexity.circuitFun
    rw [eval_eq C, hW, ← key, eval_eq, lift_last n _ _ _ _ (by simp), wiresFrom_append]
