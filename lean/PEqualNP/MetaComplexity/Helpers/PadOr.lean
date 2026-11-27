import PEqualNP.MetaComplexity.Helpers.ForestElim

/-!
# Padding by a fresh OR variable costs exactly one gate

Helper for `L-meta-128` (proofs only, no statement may use it). For a non-constant `f` on `n`
inputs, `g x = x last || f (first n of x)` has a circuit with at most `s + 1` gates exactly
when `f` has one with at most `s`.

* Upward: rename the inputs of a circuit for `f` along `Fin.castSucc` (`relabel_size`), then
  add one OR gate reading the new input and the old output.
* Downward: one-gate elimination at the last input with value `false` (`one_gate_at`), then
  drop the unread last input by renaming along a map `Fin (n + 1) → Fin n` (`relabel_size`).
-/

namespace PEqualNP.MetaComplexity.Helpers.PadOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs

/-- Evaluating gates only appends wires, one per gate. -/
theorem fold_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
      t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · simp only [List.foldl_cons]; rw [ht]; simp
    · simp [hl]

/-- Add one OR gate reading wire `a` and the old output. -/
def addOr (C : Circuit) (n a : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, C.output]⟩], n + C.gates.length⟩

theorem addOr_eval (C : Circuit) (x : List Bool) (a : ℕ) (ha : a < x.length) :
    (addOr C x.length a).eval x = (x.getD a false || C.eval x) := by
  obtain ⟨t, ht, hl⟩ := fold_prefix C.gates x
  have hw : C.wires x = x ++ t := ht
  have hw2 : (addOr C x.length a).wires x =
      C.wires x ++ [GateOp.or.eval ([a, C.output].map fun i => (C.wires x).getD i false)] := by
    simp [addOr, Circuit.wires, List.foldl_append]
  have hlen : (C.wires x).length = x.length + C.gates.length := by
    rw [hw, List.length_append, hl]
  unfold Circuit.eval
  rw [hw2]
  have hout : (addOr C x.length a).output = (C.wires x).length := by
    simp [addOr, hlen]
  rw [hout, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  have hxa : (C.wires x).getD a false = x.getD a false := by
    rw [hw, List.getD_append _ _ _ _ ha]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, hxa,
    Bool.or_false]
  rfl

/-- Upward: one more gate pays for the fresh OR variable. -/
theorem pad_up (n s : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1) := by
  obtain ⟨C, ok, hsz, hev⟩ := relabel_size (Fin.castSucc : Fin n → Fin (n + 1)) f s h
  refine ⟨addOr C (n + 1) n, ?_, ?_, ?_⟩
  · intro g hg
    simp only [addOr, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact ok g hg
    · subst hg; simp
  · have : C.gates.length ≤ s := hsz
    simp [addOr, Circuit.size]; omega
  · intro x
    have hl : (List.ofFn x).length = n + 1 := List.length_ofFn
    have e := addOr_eval C (List.ofFn x) n (by rw [hl]; omega)
    rw [hl] at e
    rw [e, hev x]
    have : (List.ofFn x).getD n false = x (Fin.last n) := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getElem_ofFn]; rfl
    rw [this]; rfl

/-- Downward: the fresh OR variable costs at least one gate. -/
theorem pad_down (n s : ℕ) (f : (Fin n → Bool) → Bool) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1)) : HasCircuitSize n f s := by
  obtain ⟨y, y', hyy⟩ := hnc
  set g : (Fin (n + 1) → Bool) → Bool :=
    fun x => x (Fin.last n) || f (fun i : Fin n => x i.castSucc) with hg
  have hupd : ∀ (x : Fin (n + 1) → Bool) (b : Bool),
      (fun i : Fin n => Function.update x (Fin.last n) b i.castSucc) = fun i => x i.castSucc := by
    intro x b; funext i
    exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
  have hres : ∀ x : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) false) = f (fun i : Fin n => x i.castSucc) := by
    intro x; simp only [hg]; rw [hupd]; simp
  have hsn : ∀ z : Fin n → Bool, ∀ b : Bool, (fun i : Fin n => (Fin.snoc z b : Fin (n + 1) → Bool) i.castSucc) = z := by
    intro z b; funext i; exact Fin.snoc_castSucc (α := fun _ => Bool) ..
  -- some point where f is false
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, f z = false := by
    cases h1 : f y
    · exact ⟨y, h1⟩
    · cases h2 : f y'
      · exact ⟨y', h2⟩
      · exact absurd (h1.trans h2.symm) hyy
  have hdep : ∃ x : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ g x := by
    refine ⟨Fin.snoc z false, ?_⟩
    simp only [hg, Function.update_self, Fin.snoc_last]
    rw [hupd, hsn, hz]; simp
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) false) ≠ g (Function.update x' (Fin.last n) false) := by
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    rw [hres, hres, hsn, hsn]; exact hyy
  have h1 := PEqualNP.MetaComplexity.Helpers.Forest.one_gate_at n g (Fin.last n) false s hdep hnc' h
  have h1' : HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc)) s := by
    have e : (fun x => g (Function.update x (Fin.last n) false))
        = (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc)) := by
      funext x; exact hres x
    rw [← e]; exact h1
  -- n is positive: f is non-constant
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd (congrArg f (Subsingleton.elim y y')) hyy
    | succ m => exact ⟨m, rfl⟩
  let π : Fin (m + 1 + 1) → Fin (m + 1) := Fin.lastCases 0 id
  have h2 := relabel_size π _ s h1'
  have e : (fun x : Fin (m + 1) → Bool => f (fun i : Fin (m + 1) => (x ∘ π) i.castSucc)) = f := by
    funext x; congr 1; funext i; simp [π, Fin.lastCases_castSucc]
  rw [e] at h2; exact h2

theorem pad_or (n s : ℕ) (f : (Fin n → Bool) → Bool) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1) ↔ HasCircuitSize n f s :=
  ⟨pad_down n s f hnc, pad_up n s f⟩

end PEqualNP.MetaComplexity.Helpers.PadOr
