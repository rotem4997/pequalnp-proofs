import PEqualNP.Defs

-- Pay for the first binary gate and search its suffix on the boundary rows.
-- Relative to point 0 the other input represents a point, an incident line, or a nonincident line.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6961_416
    (search : let f := fun (x : Fin 26 → Bool) => decide (∃ p l : Fin 13,
       (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
     ∃ b ∈ ([1,13,14] : List (Fin 26)), ∃ (u : Bool) (D : Circuit),
       Monotone2 D ∧ D.size ≤ 62 ∧ ∀ x : Fin 26 → Bool,
       (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) →
       circuitFun 27 D (Fin.snoc x (if u then x 0 || x b else x 0 && x b)) = f x)
    (boundary : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Circuit), Monotone f → Monotone2 T →
     (∀ x, (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) → circuitFun n T x = f x) →
       ∀ x, circuitFun n T x = f x) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (63 : ℕ) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x2 = Decidable.decide (∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (∃ x5 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x3 = x4 + x5) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) := by
  classical
  let f := fun (x : Fin 26 → Bool) => decide (∃ p l : Fin 13,
       (∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  obtain ⟨b,_,u,D,md,sz,correct⟩ := search
  let gate : Gate := ⟨if u then GateOp.or else GateOp.and,[0,b.val]⟩
  let C : Circuit := ⟨gate::D.gates,D.output⟩
  have mc : Monotone2 C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · cases u <;> simp [gate]
    · exact md g hg
  refine ⟨C,mc,?_,?_⟩
  · change D.gates.length + 1 ≤ 63
    change D.gates.length ≤ 62 at sz
    omega
  refine boundary 26 f C ?_ mc ?_
  · intro x y xy
    apply Bool.le_iff_imp.mpr
    intro yes
    obtain ⟨p,l,edge,hp,hl⟩ := of_decide_eq_true yes
    exact decide_eq_true ⟨p,l,edge,Bool.le_iff_imp.mp (xy _) hp,Bool.le_iff_imp.mp (xy _) hl⟩
  · intro x extremal
    let z := if u then x 0 || x b else x 0 && x b
    have init : List.ofFn (Fin.snoc x z) = List.ofFn x ++ [z] := by
      rw [List.ofFn_succ']
      simp
      exact Fin.snoc_last ..
    have v : gate.op.eval (gate.inputs.map fun i => (List.ofFn x).getD i false) = z := by
      have get (i : Fin 26) : (List.ofFn x).getD i.val false = x i := by
        rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
        exact List.getElem_ofFn ..
      change (if u then GateOp.or else GateOp.and).eval
        [(List.ofFn x).getD (0 : Fin 26).val false,(List.ofFn x).getD b.val false] = z
      rw [get 0,get b]
      dsimp only [z]
      cases u <;> cases x 0 <;> cases x b <;> rfl
    have eqn : circuitFun 26 C x = circuitFun 27 D (Fin.snoc x z) := by
      unfold circuitFun Circuit.eval Circuit.wires
      simp only [C,List.foldl_cons]
      rw [v,init]
    exact eqn.trans (correct x extremal)
