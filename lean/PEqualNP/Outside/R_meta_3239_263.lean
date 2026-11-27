import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3239_263
    (phaseTransfer : ∀ (C : BinaryCircuit) (k : ℕ) (p : Bool),
    (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) →
    ∃ D : BinaryCircuit, D.size = C.size ∧ D.output = C.output ∧
      (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) ∧
      ∀ x y : List Bool, x.length = y.length → k < x.length →
        (∀ j, y.getD j false = (x.getD j false != decide (j = k))) →
        (D.eval y != (p != decide (C.output = k))) = (C.eval x != p))
    (mixed : ∀ (C : BinaryCircuit) (b : Bool), (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) →
      (∀ g : BinaryGate, C.gates[0]? = some g → g.op = fun u v => (u == true) && (v == false)) →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (orSeed : ∀ (p q : Fin 11) (C : BinaryCircuit) (b : Bool), (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) →
      (∀ x : Fin 9 → Bool, let row := List.ofFn x ++ [x 0 || x 1, false];
        (C.eval (row ++ [row.getD p.val false || row.getD q.val false]) != b) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C inv signed first eval
  let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 1, false]
  let step (w : List Bool) (g : BinaryGate) := w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
  cases tail : C.gates with
  | nil =>
    apply mixed C inv signed _ eval
    intro g hg
    rw [tail] at hg
    simp at hg
  | cons g gs =>
    have firstG : C.gates[0]? = some g := by rw [tail]; rfl
    obtain ⟨d,phaseG⟩ := (first g firstG).1
    let D : BinaryCircuit := ⟨gs,C.output⟩
    have signedD : ∀ h ∈ D.gates, ∃ a b : Bool, h.op = fun u v => (u == a) && (v == b) := by
      intro h hh
      apply signed h
      rw [tail]
      exact List.mem_cons_of_mem _ hh
    have splitEval (xs : List Bool) : C.eval xs = D.eval (step xs g) := by
      change (C.gates.foldl step xs).getD C.output false =
        (gs.foldl step (step xs g)).getD C.output false
      rw [tail, List.foldl_cons]
    have sizeD : C.size = D.size+1 := by
      change C.gates.length = gs.length+1
      rw [tail,List.length_cons]
    cases d
    · let pick (w : ℕ) : Fin 11 := if h : w < 11 then ⟨w,h⟩ else 10
      have len (x : Fin 9 → Bool) : (row x).length = 11 := by simp [row]
      have reads (x : Fin 9 → Bool) (w : ℕ) : (row x).getD (pick w).val false = (row x).getD w false := by
        by_cases h : w < 11
        · simp [pick,h]
        · have bound : (row x).length ≤ w := by rw [len]; omega
          rw [List.getD_eq_default _ _ bound]
          change (row x).getD (pick w).val false = false
          have eq : (pick w).val = 10 := by simp [pick,h]
          rw [eq]
          change (List.ofFn x ++ [x 0 || x 1, false]).getD 10 false = false
          rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
          rfl
      let p := pick g.left
      let q := pick g.right
      let t (x : Fin 9 → Bool) := (row x).getD p.val false || (row x).getD q.val false
      have bit (x : Fin 9 → Bool) : g.op ((row x).getD g.left false) ((row x).getD g.right false) = !(t x) := by
        have norLaw : ∀ a b : Bool, ((a == false) && (b == false)) = !(a || b) := by decide
        unfold t p q
        rw [reads,reads,phaseG]
        exact norLaw _ _
      obtain ⟨E,sizeE,_,basisE,transfer⟩ := phaseTransfer D 11 inv signedD
      have fits := orSeed p q E (inv != decide (D.output = 11)) basisE (by
        intro x
        change (E.eval (row x ++ [t x]) != (inv != decide (D.output = 11))) = _
        have sim := transfer (row x ++ [!(t x)]) (row x ++ [t x]) (by simp)
          (by simp [len]) (by
            intro j
            by_cases lo : j < 11
            · have hl : j < (row x).length := by simpa only [len] using lo
              have neq : j ≠ 11 := by omega
              rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hl]
              simp [neq]
            by_cases eq : j = 11
            · subst j
              have low : (row x).length ≤ 11 := by simp [len]
              rw [List.getD_append_right _ _ _ _ low, List.getD_append_right _ _ _ _ low, len]
              simp only [Nat.sub_self,List.getD_cons_zero,decide_true]
              cases t x <;> decide
            · have leA : (row x ++ [!(t x)]).length ≤ j := by simp [len]; omega
              have leB : (row x ++ [t x]).length ≤ j := by simp [len]; omega
              rw [List.getD_eq_default _ _ leA,List.getD_eq_default _ _ leB]
              simp [eq])
        rw [sim]
        have e := eval x
        change (C.eval (row x) != inv) = _ at e
        rw [splitEval] at e
        dsimp only [step] at e
        rw [bit] at e
        exact e)
      omega
    · let h : BinaryGate := ⟨fun a b => g.op b a, g.right, g.left⟩
      let B : BinaryCircuit := ⟨h :: gs,C.output⟩
      have swapped : h.op = fun u v => (u == true) && (v == false) := by
        funext u v
        change g.op v u = _
        rw [phaseG,Bool.and_comm]
      have basisB : ∀ f ∈ B.gates, ∃ a b : Bool, f.op = fun u v => (u == a) && (v == b) := by
        intro f hf
        change f ∈ h :: gs at hf
        rcases List.mem_cons.mp hf with e | e
        · subst f
          exact ⟨true,false,swapped⟩
        · exact signedD f e
      have uses (f : BinaryGate) (hf : B.gates[0]? = some f) :
          f.op = fun u v => (u == true) && (v == false) := by
        have e : some h = some f := hf
        exact (Option.some.inj e) ▸ swapped
      have same (xs : List Bool) : B.eval xs = C.eval xs := by
        rw [splitEval]
        rfl
      have n : B.size = C.size := by
        change (h :: gs).length = C.gates.length
        rw [tail]
        rfl
      have lower := mixed B inv basisB uses (by
        intro x
        rw [same]
        exact eval x)
      omega
