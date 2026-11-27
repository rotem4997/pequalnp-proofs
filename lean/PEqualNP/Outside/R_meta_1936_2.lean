import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- At least thirteen gates other than inversions are needed by this edge function.
-- The fixed first inversion leaves at most one inversion available in the suffix.
theorem PEqualNP.Outside.R_meta_1936_2
    (binary : ∀ (D : Circuit), FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9))) →
      13 ≤ D.gates.countP (fun g => g.op.eval [true]))
    (h0 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → 12 ≤ C.size → C.size ≤ 13 →
      C.gates.countP (fun g => !(g.op.eval [true])) = 0 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!x 0]
        C.eval (w ++ [GateOp.and.eval (pins.map fun i => w.getD i false)]) ≠ (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)))
    (h1 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ (C : Circuit), FanInTwo C → C.size = 13 →
      C.gates.countP (fun g => !(g.op.eval [true])) = 1 →
      (∃ a b : Fin 10, a ≠ b ∧ pins = [a.val,b.val] ∧
        ¬ (a.val = 0 ∧ b.val = 9) ∧ ¬ (a.val = 9 ∧ b.val = 0)) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!x 0]
        C.eval (w ++ [GateOp.and.eval (pins.map fun i => w.getD i false)]) ≠ (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins pinSize C fan size
  by_contra agree
  push Not at agree
  let D : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.and,pins⟩ :: C.gates, C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    simp only [D,List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · refine ⟨by simp,pinSize⟩
    · exact fan g hg
  have computes (x : Fin 9 → Bool) : D.eval (List.ofFn x) = (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)) := by
    have first : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    let w := List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]]
    have he : D.eval (List.ofFn x) =
      C.eval (w ++ [GateOp.and.eval (pins.map fun i => w.getD i false)]) := rfl
    rw [he]
    dsimp only [w]
    rw [first]
    exact not_not.mp (agree x)
  have needed := binary D fanD computes
  let binaryGate (g : Gate) := g.op.eval [true]
  have noCount (inputs : List ℕ) (gs : List Gate) :
      List.countP binaryGate (⟨.not,inputs⟩ :: gs) = List.countP binaryGate gs :=
    List.countP_cons_of_neg (p := binaryGate) (a := ⟨.not,inputs⟩) (by change ¬ false = true; decide)
  have yesCount (inputs : List ℕ) (gs : List Gate) :
      List.countP binaryGate (⟨.and,inputs⟩ :: gs) = List.countP binaryGate gs + 1 :=
    List.countP_cons_of_pos (p := binaryGate) (a := ⟨.and,inputs⟩) rfl
  have fixedCount : D.gates.countP (fun g => g.op.eval [true]) =
      1 + C.gates.countP (fun g => g.op.eval [true]) := by
    change List.countP binaryGate (⟨.not,[0]⟩ :: ⟨.and,pins⟩ :: C.gates) = _
    rw [noCount, yesCount]
    exact Nat.add_comm _ _
  rw [fixedCount] at needed
  have partition : C.gates.countP (fun g => g.op.eval [true]) +
      C.gates.countP (fun g => !(g.op.eval [true])) = C.gates.length := by
    simpa only [decide_not, Bool.decide_coe] using
      (List.length_eq_countP_add_countP (fun g : Gate => g.op.eval [true]) (l := C.gates)).symm
  have lengthEq : C.gates.length = C.size := rfl
  by_cases zero : C.gates.countP (fun g => !(g.op.eval [true])) = 0
  · obtain ⟨x, hx⟩ := h0 pins pinSize C fan (by omega) size zero
    exact agree x hx
  · have one : C.gates.countP (fun g => !(g.op.eval [true])) = 1 := by omega
    let w (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
    let pin (x : Fin 9 → Bool) := GateOp.and.eval (pins.map fun i => (w x).getD i false)
    let goodPins := ∃ a b : Fin 10, a ≠ b ∧ pins = [a.val,b.val] ∧
      ¬ (a.val = 0 ∧ b.val = 9) ∧ ¬ (a.val = 9 ∧ b.val = 0)
    have tooFew : C.gates.countP (fun g => g.op.eval [true]) < 13 := by omega
    have first (x : Fin 9 → Bool) : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
    have always (x : Fin 9 → Bool) : C.eval (w x ++ [pin x]) = (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)) := not_not.mp (agree x)
    have shape : goodPins ∨ (∀ x, pin x = true) ∨ ∃ a : ℕ, ∀ x, pin x = (w x).getD a false := by
      have missing (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) :
          (w x).getD i false = false := List.getD_eq_default _ _ (by simpa [w] using hi)
      have cancel (x : Fin 9 → Bool) :
          ((w x).getD 0 false && (w x).getD 9 false) = false := by
        rw [List.getD_append _ _ _ _ (by simp)]
        rw [List.getD_append_right _ _ _ _ (by simp), first]
        simp
      cases pins with
      | nil => exact Or.inr (Or.inl (fun x => rfl))
      | cons a rest =>
        cases rest with
        | nil =>
          exact Or.inr (Or.inr ⟨a, by
            intro x
            change ((w x).getD a false && true) = _
            simp⟩)
        | cons b rest =>
          have restNil : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at pinSize; omega)
          subst rest
          have val (x : Fin 9 → Bool) :
              pin x = ((w x).getD a false && (w x).getD b false) := by
            change ((w x).getD a false && ((w x).getD b false && true)) = _
            simp
          by_cases ha : a < 10
          · by_cases hb : b < 10
            · by_cases e : a = b
              · exact Or.inr (Or.inr ⟨a,by intro x; rw [val,e,Bool.and_self]⟩)
              · by_cases h0 : a = 0 ∧ b = 9
                · refine Or.inr (Or.inr ⟨10,fun x => ?_⟩)
                  rw [val, h0.1, h0.2, cancel, missing x 10 (by decide)]
                · by_cases h9 : a = 9 ∧ b = 0
                  · refine Or.inr (Or.inr ⟨10,fun x => ?_⟩)
                    rw [val,h9.1,h9.2,Bool.and_comm,cancel,missing x 10 (by decide)]
                  · exact Or.inl ⟨⟨a,ha⟩,⟨b,hb⟩,fun h => e (congrArg Fin.val h),rfl,h0,h9⟩
            · exact Or.inr (Or.inr ⟨b,by intro x; rw [val,missing x b (by omega),Bool.and_false]⟩)
          · exact Or.inr (Or.inr ⟨a,by intro x; rw [val,missing x a (by omega),Bool.false_and]⟩)
    rcases shape with good | htrue | ⟨a,hcopy⟩
    · obtain ⟨x,hx⟩ := h1 pins pinSize C fan (by omega) one good
      exact agree x hx
    · let E : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.not,[]⟩ :: C.gates,C.output⟩
      have eFan : FanInTwo E := by
        intro g hg
        simp only [E,List.mem_cons] at hg
        rcases hg with rfl | rfl | hg
        · simp
        · simp
        · exact fan g hg
      have eCorrect (x : Fin 9 → Bool) : E.eval (List.ofFn x) = (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)) := by
        have he : E.eval (List.ofFn x) =
            C.eval ((List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]]) ++ [true]) := rfl
        rw [he,first]
        change C.eval (w x ++ [true]) = _
        rw [← htrue x]
        exact always x
      have eq : E.gates.countP (fun g => g.op.eval [true]) =
          C.gates.countP (fun g => g.op.eval [true]) := by
        change List.countP binaryGate (⟨.not,[0]⟩ :: ⟨.not,[]⟩ :: C.gates) = _
        rw [noCount, noCount]
      have m := binary E eFan eCorrect
      omega
    · let shift (i : ℕ) : ℕ := if i < 10 then i else i+1
      let move (g : Gate) : Gate := ⟨g.op,g.inputs.map shift⟩
      let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
      let rel (u v : List Bool) : Prop :=
        v.length = u.length + 1 ∧ 10 ≤ u.length ∧
        ∀ i, u.getD i false = v.getD (shift i) false
      have preserve (u v : List Bool) (b : Bool) (h : rel u v) : rel (u ++ [b]) (v ++ [b]) := by
        obtain ⟨lh,lu,read⟩ := h
        refine ⟨by simp [lh], by simp; omega, fun i => ?_⟩
        by_cases small : i < 10
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by simp [shift,small]; omega)]
          exact read i
        · have shiftEq : shift i = i+1 := by simp [shift,small]
          by_cases within : i < u.length
          · rw [List.getD_append _ _ _ _ within, List.getD_append _ _ _ _ (by omega)]
            exact read i
          · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega)]
            rw [shiftEq, lh, Nat.add_sub_add_right]
      have run (gs : List Gate) (u v : List Bool) (h : rel u v) :
          rel (gs.foldl step u) ((gs.map move).foldl step v) := by
        induction gs generalizing u v with
        | nil => exact h
        | cons g gs ih =>
          simp only [List.map_cons,List.foldl_cons]
          apply ih
          have same :
              g.inputs.map (fun i => u.getD i false) =
              (move g).inputs.map (fun i => v.getD i false) := by
            simp only [move,List.map_map]
            exact List.map_congr_left (fun i _ => h.2.2 i)
          simp only [step,move] at same ⊢
          rw [same]
          exact preserve u v _ h
      let E : Circuit := ⟨⟨.not,[0]⟩ :: ⟨.not,[a]⟩ :: ⟨.not,[10]⟩ ::
        (C.gates.map move),shift C.output⟩
      have eFan : FanInTwo E := by
        intro g hg
        simp only [E,List.mem_cons] at hg
        rcases hg with rfl | rfl | rfl | hg
        · simp
        · simp
        · simp
        · obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
          exact ⟨(fan g0 hg0).1, by simpa [move] using (fan g0 hg0).2⟩
      have related (x : Fin 9 → Bool) (b : Bool) :
          rel (w x ++ [b]) (w x ++ [!b,b]) := by
        have len : (w x).length = 10 := by simp [w]
        refine ⟨by simp [len],by simp [len],fun i => ?_⟩
        by_cases small : i < 10
        · rw [show shift i = i by simp [shift,small],
            List.getD_append (w x) [b] false i (by omega),
            List.getD_append (w x) [!b,b] false i (by omega)]
        · rw [show shift i = i+1 by simp [shift,small],
            List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega),len]
          have idx : i+1-10 = (i-10)+1 := by omega
          rw [idx]
          rfl
      have eCorrect (x : Fin 9 → Bool) : E.eval (List.ofFn x) = (x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) || x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) || x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) || x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) || x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) || x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)) := by
        let q := List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]]
        have qlen : q.length = 10 := by simp [q]
        have last : (q ++ [!(q.getD a false)]).getD 10 false = !(q.getD a false) := by
          rw [List.getD_append_right _ _ _ _ (by omega), qlen]; rfl
        have he : E.eval (List.ofFn x) =
              ((C.gates.map move).foldl step
                ((q ++ [!(q.getD a false)]) ++ [!((q ++ [!(q.getD a false)]).getD 10 false)])).getD
                  (shift C.output) false := rfl
        rw [he,last,Bool.not_not]
        have qw : q = w x := by dsimp only [q,w]; rw [first]; rfl
        rw [qw, List.append_assoc]
        change ((C.gates.map move).foldl step (w x ++ [!((w x).getD a false),(w x).getD a false])).getD
          (shift C.output) false = _
        rw [← hcopy x]
        have same := (run C.gates _ _ (related x (pin x))).2.2 C.output
        exact same.symm.trans (always x)
      have eq : E.gates.countP (fun g => g.op.eval [true]) =
          C.gates.countP (fun g => g.op.eval [true]) := by
        change List.countP binaryGate
          (⟨.not,[0]⟩ :: ⟨.not,[a]⟩ :: ⟨.not,[10]⟩ :: C.gates.map move) = _
        rw [noCount, noCount, noCount, List.countP_map]
        rfl
      have m := binary E eFan eCorrect
      omega
