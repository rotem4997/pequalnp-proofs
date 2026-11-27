import Mathlib
import PEqualNP.Defs

-- Bit positions correspond to the sample inputs in the order of the posted statement.
-- Each triple consists of the result of a gate followed by its two operands.
-- The first two hypotheses are exactly the checked bounds L-meta-2331 and L-meta-2307.
-- In the remaining search each polarity of the first input feeds exactly one gate.
-- All wire signatures are fresh and the final result is the required output.
-- At least twenty-two signatures must still be distinct after setting the first input to false.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3600000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_3616_1
    (ordinaryBound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (cofactorBound : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.cons Bool.false x2)) (11 : ℕ))
    (twoPorts :
      let seed : List (BitVec 29) := [330021798, 0, 536870911, 206849113, 268469123, 9466894, 6719660, 277352752, 16849344, 101588480, 403693568, 535822336]
      ∀ t : List (BitVec 29 × BitVec 29 × BitVec 29),
      t.length = 14 →
      t.countP (fun g => g.2.1 == 206849113 || g.2.2 == 206849113) = 1 →
      t.countP (fun g => g.2.1 == 330021798 || g.2.2 == 330021798) = 1 →
      (seed ++ t.map Prod.fst).Nodup →
      22 ≤ ((seed ++ t.map Prod.fst).map (fun v => v &&& 330021798)).toFinset.card →
      (∀ i : Fin t.length,
        let prev := seed ++ (t.take i.val).map Prod.fst
        let g := t.get i
        g.2.1 ∈ prev ∧ g.2.2 ∈ prev ∧ (g.1 = g.2.1 &&& g.2.2 ∨ g.1 = g.2.1 ||| g.2.2)) →
      (t.map Prod.fst).getLast? ≠ some 123822719) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (∀ (x7 : Fin x1), (x3 x7).1 < (10 : ℕ) + ↑x7 ∧ (x4 x7).1 < (10 : ℕ) + ↑x7) →     x5.1 < (10 : ℕ) + x1 →       x5.2 = Bool.false →         x1 ≤ (14 : ℕ) →           (have x11 : ℕ × Bool → Prop := fun (x11 : ℕ × Bool) => x11.2 = Bool.true → x11.1 = (0 : ℕ) ∨ x11.1 = (9 : ℕ);             x11 x5 ∧ ∀ (x12 : Fin x1), x11 (x3 x12) ∧ x11 (x4 x12)) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin (9 : ℕ)), x6 x12 ↑x13 = x12 x13) →               (∀ (x13 : Fin (9 : ℕ) → Bool), x6 x13 (9 : ℕ) = Bool.false) →                 (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin x1),                     have x16 : ℕ × Bool → Bool := fun (x16 : ℕ × Bool) => x6 x14 x16.1 ^^ x16.2;                     x6 x14 ((10 : ℕ) + ↑x15) = if x2 x15 = Bool.true then x16 (x3 x15) && x16 (x4 x15) else x16 (x3 x15) || x16 (x4 x15)) →                   (∀ x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (133 : ℕ), (138 : ℕ), (160 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (265 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (385 : ℕ), (402 : ℕ)],                       have x17 : Fin (9 : ℕ) → Bool := fun (x17 : Fin (9 : ℕ)) => x15.testBit ↑x17;                       (x6 x17 x5.1 ^^ x5.2) = Decidable.decide (x15 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ)])) →                     False := by
  classical
  intro n op left right out val before hout phase budget signs inputs zero trace tests
  let sources : List (BitVec 29) := [0,536870911,206849113,268469123,9466894,6719660,
    277352752,16849344,101588480,403693568,535822336]
  let x : (BitVec 29) := 206849113
  let y : (BitVec 29) := 330021798
  let base := y :: sources
  let restricted : List (BitVec 29) := [0,330021798,268469122,8400902,2263204,277352736,
    16849280,34216448,269197312,329252864]
  let target : (BitVec 29) := 123822719
  let available (s : List (BitVec 29)) (t : List (BitVec 29 × BitVec 29 × BitVec 29)) := s ++ t.map Prod.fst
  let legal (s : List (BitVec 29)) (t : List (BitVec 29 × BitVec 29 × BitVec 29)) := ∀ i : Fin t.length,
    let w := available s (t.take i.val)
    let g := t[i.val]
    g.2.1 ∈ w ∧ g.2.2 ∈ w ∧ (g.1 = g.2.1 &&& g.2.2 ∨ g.1 = g.2.1 ||| g.2.2)
  let reads (v : (BitVec 29)) (g : (BitVec 29 × BitVec 29 × BitVec 29)) := g.2.1 == v || g.2.2 == v
  let touch (g : (BitVec 29 × BitVec 29 × BitVec 29)) := reads x g || reads y g
  have extend {s : List (BitVec 29)} {t : List (BitVec 29 × BitVec 29 × BitVec 29)} (h : legal s t) (g : (BitVec 29 × BitVec 29 × BitVec 29))
      (a : g.2.1 ∈ available s t) (b : g.2.2 ∈ available s t)
      (c : g.1 = g.2.1 &&& g.2.2 ∨ g.1 = g.2.1 ||| g.2.2) :
      legal s (t ++ [g]) := by
    intro i
    by_cases hi : i.val < t.length
    · simpa only [available, List.take_append_of_le_length (Nat.le_of_lt hi),
        List.getElem_append_left hi] using h ⟨i.val, hi⟩
    · have e : i.val = t.length := by have := i.isLt; simp at this; omega
      simpa [available, e] using And.intro a (And.intro b c)
  let rows : List Nat := [3,6,12,13,17,24,33,42,50,66,69,104,116,132,133,138,160,200,
    201,208,261,264,265,276,288,320,321,385,402]
  let row (r : Fin 29) : Nat := rows[r.val]!
  let input (r : Fin 29) (i : Fin 9) := (row r).testBit i.val
  let pack (f : Fin 29 → Bool) : (BitVec 29) :=
    (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)
  have bit (f : Fin 29 → Bool) (i : Fin 29) : (pack f)[i.val] = f i := by
    rw [← BitVec.getLsbD_eq_getElem]
    change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = _
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [i.isLt,dite_eq_left, Option.getD_some]
  let wire (i : Nat) := pack (fun r => val (input r) i)
  let src (i : Fin 9) := pack (fun r => input r i)
  have raw (i : Fin 9) : wire i.val = src i := by
    apply congrArg pack
    funext r
    exact inputs (input r) i
  have rawMem : ∀ i : Fin 9, src i ∈ base := by decide +kernel
  have rawZero : wire 0 = x := (raw 0).trans (by decide +kernel)
  have constZero : wire 9 = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    simpa using (bit _ ⟨j,hj⟩).trans (zero (input ⟨j,hj⟩))
  have outEq : wire out.1 = target := by
    have mem : ∀ r : Fin 29, row r ∈ rows := by decide +kernel
    have targetBits : ∀ r : Fin 29, target[r.val] =
        decide (row r ∈ ([3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321] : List Nat)) := by
      change ∀ r : Fin 29, (123822719 : BitVec 29).getLsbD r.val = _
      dsimp [row,rows]
      decide +kernel
    apply BitVec.eq_of_getElem_eq
    intro j hj
    let r : Fin 29 := ⟨j,hj⟩
    have ht := tests (row r) (mem r)
    simp only [phase, Bool.xor_false] at ht
    exact (bit _ r).trans (ht.trans (targetBits r).symm)
  let pin (p : Nat × Bool) : (BitVec 29) := if p.2 then ~~~(wire p.1) else wire p.1
  have pinBit (p : Nat × Bool) (r : Fin 29) :
      (pin p)[r.val] = (val (input r) p.1 ^^ p.2) := by
    cases e : p.2 <;> simp [pin,e,wire,bit,BitVec.getElem_not]
  have gate (j : Fin n) :
      (wire (10+j.val) = pin (left j) &&& pin (right j)) ∨
      (wire (10+j.val) = pin (left j) ||| pin (right j)) := by
    cases e : op j
    · right
      apply BitVec.eq_of_getElem_eq
      intro i hi
      let r : Fin 29 := ⟨i,hi⟩
      have h := trace (input r) j
      rw [BitVec.getElem_or, show (wire _)[i] = _ from bit _ r, pinBit (left j) r, pinBit (right j) r]
      simpa only [e,Bool.false_eq_true,ite_false] using h
    · left
      apply BitVec.eq_of_getElem_eq
      intro i hi
      let r : Fin 29 := ⟨i,hi⟩
      have h := trace (input r) j
      rw [BitVec.getElem_and, show (wire _)[i] = _ from bit _ r, pinBit (left j) r, pinBit (right j) r]
      simpa only [e,ite_true] using h
  have fullTrace : ∀ k ≤ n, ∃ t : List (BitVec 29 × BitVec 29 × BitVec 29), legal base t ∧ t.length ≤ k ∧
      (available base t).Nodup ∧ (∀ g ∈ t, ¬ (reads x g = true ∧ reads y g = true)) ∧
      ∀ i < 10+k, wire i ∈ available base t := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨[], by intro j; exact Fin.elim0 j, by simp, by decide +kernel, by simp, ?_⟩
      intro i hi
      by_cases h : i < 9
      · simpa [available,raw ⟨i,h⟩] using rawMem ⟨i,h⟩
      · have e : i = 9 := by omega
        rw [e,constZero]
        decide +kernel
    | succ k ih =>
      intro hk
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨t,ht,hlen,fresh,sep,seen⟩ := ih (by omega)
      have pinMem (p : Nat × Bool) (h : p.1 < 10+k)
          (s : p.2 = true → p.1 = 0 ∨ p.1 = 9) : pin p ∈ available base t := by
        cases e : p.2
        · simpa [pin,e] using seen p.1 h
        · simp only [pin,e,ite_true]
          apply List.mem_append_left
          rcases s e with q|q
          · rw [q,rawZero]; decide +kernel
          · rw [q,constZero]; decide +kernel
      let g : (BitVec 29 × BitVec 29 × BitVec 29) := (wire (10+k), pin (left j), pin (right j))
      have lg := gate j
      by_cases old : g.1 ∈ available base t
      · refine ⟨t,ht,by omega,fresh,sep,?_⟩
        intro i hi
        by_cases h : i < 10+k
        · exact seen i h
        · have e : i = 10+k := by omega
          exact e ▸ old
      · have clean : ¬(reads x g = true ∧ reads y g = true) := by
          intro both
          have a := both.1
          have b := both.2
          change g.1 = g.2.1 &&& g.2.2 ∨ g.1 = g.2.1 ||| g.2.2 at lg
          have ne : x ≠ y := by decide +kernel
          simp only [reads,Bool.or_eq_true,beq_iff_eq] at a b
          apply old
          apply List.mem_append_left
          rcases a with ha|ha <;> rcases b with hb|hb <;>
            first | exact (ne (ha.symm.trans hb)).elim
                  | rcases lg with hg|hg <;> rw [hg,ha,hb] <;> decide +kernel
        have h1 := pinMem (left j) (before j).1 (signs.2 j).1
        have h2 := pinMem (right j) (before j).2 (signs.2 j).2
        refine ⟨t ++ [g],extend ht g h1 h2 lg,by simp; omega,?_,?_,?_⟩
        · have nd := (List.nodup_concat (available base t) g.1).2 ⟨old,fresh⟩
          simpa [available,List.concat_eq_append,List.append_assoc] using nd
        · intro w hw
          rcases List.mem_append.mp hw with h|h
          · exact sep w h
          · simpa only [List.mem_singleton.mp h] using clean
        · intro i hi
          by_cases h : i < 10+k
          · have m := seen i h
            simpa [available,List.append_assoc] using List.mem_append_left [g.1] m
          · have e : i = 10+k := by omega
            simp [e,available,g]
  obtain ⟨whole, hwhole, sizeWhole, freshWhole, sepWhole, seen⟩ := fullTrace n le_rfl
  have inWhole : target ∈ available base whole := outEq ▸ seen out.1 hout
  have outside : target ∉ base := by decide +kernel
  obtain ⟨lastGate,hg,gateValue⟩ := List.mem_map.mp ((List.mem_append.mp inWhole).resolve_left outside)
  obtain ⟨pre,post,splitAt⟩ := List.append_of_mem hg
  let t := pre ++ [lastGate]
  have cut : whole = t ++ post := by simpa [t] using splitAt
  have ht : legal base t := by
    rw [cut] at hwhole
    intro i
    have hi : i.val < (t ++ post).length := by simp; omega
    simpa only [List.take_append_of_le_length (Nat.le_of_lt i.isLt),List.getElem_append_left i.isLt]
      using hwhole ⟨i.val,hi⟩
  have hlen : t.length ≤ n := by rw [cut,List.length_append] at sizeWhole; omega
  have sep (g) (mem : g ∈ t) := sepWhole g (cut ▸ List.mem_append_left post mem)
  have fresh : (available base t).Nodup := by
    change (base ++ whole.map Prod.fst).Nodup at freshWhole
    rw [cut,List.map_append,← List.append_assoc] at freshWhole
    exact (List.nodup_append.mp freshWhole).1
  have lastIsTarget : (t.map Prod.fst).getLast? = some target := by simp [t,gateValue]
  have result : target ∈ available base t := by simp [available,t,gateValue]
  have prefixLegal {s : List (BitVec 29)} {l : List (BitVec 29 × BitVec 29 × BitVec 29)} {g : (BitVec 29 × BitVec 29 × BitVec 29)} (h : legal s (l ++ [g])) :
      legal s l := by
    intro i
    have h' := h ⟨i.val, by simp⟩
    simpa only [List.take_append_of_le_length (Nat.le_of_lt i.isLt),List.getElem_append_left i.isLt] using h'
  have lastLegal {s : List (BitVec 29)} {l : List (BitVec 29 × BitVec 29 × BitVec 29)} {g : (BitVec 29 × BitVec 29 × BitVec 29)} (h : legal s (l ++ [g])) :
      g.2.1 ∈ available s l ∧ g.2.2 ∈ available s l ∧
      (g.1 = g.2.1 &&& g.2.2 ∨ g.1 = g.2.1 ||| g.2.2) := by
    have h' := h ⟨l.length,by simp⟩
    simpa using h'
  let mkOp (d : Bool) := if d then GateOp.and else GateOp.or
  let indices (p : Bool ⊕ Nat) := p.elim (fun _ => ([] : List Nat)) (fun i => [i])
  let absorbs (d : Bool) (p : Bool ⊕ Nat) := p.elim (fun v => v != d) (fun _ => false)
  let make (d : Bool) (a b : Bool ⊕ Nat) : Gate :=
    if absorbs d a || absorbs d b then ⟨mkOp (!d), []⟩
    else ⟨mkOp d, indices a ++ indices b⟩
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  let read (p : Bool ⊕ Nat) (w : List Bool) := p.elim id (fun i => w.getD i false)
  let valid (k : Nat) (p : Bool ⊕ Nat) := p.elim (fun _ => True) (fun i => i < k)
  have makeSpec (d : Bool) (a b : Bool ⊕ Nat) (w : List Bool) :
      let g := make d a b
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        if d then read a w && read b w else read a w || read b w := by
    rcases a with (_|_)|ia <;> rcases b with (_|_)|ib <;> cases d <;>
      simp [make,mkOp,read,indices,absorbs,evalAnd,evalOr]
  let signals {m : Nat} (gs : List Gate) (v : Fin m → Bool) :=
    (Circuit.mk gs 0).wires (List.ofFn v)
  have sigLength {m} (gs : List Gate) (v : Fin m → Bool) : (signals gs v).length = m + gs.length := by
    have aux (l : List Gate) (w : List Bool) :
        ((Circuit.mk l 0).wires w).length = w.length + l.length := by
      induction l generalizing w with
      | nil => rfl
      | cons g l ih =>
        change ((Circuit.mk l 0).wires (w ++ [_])).length = _
        rw [ih]; simp; omega
    simpa [signals] using aux gs (List.ofFn v)
  have snoc {m} (gs : List Gate) (g : Gate) (v : Fin m → Bool) :
      signals (gs ++ [g]) v = signals gs v ++ [g.op.eval (g.inputs.map fun i => (signals gs v).getD i false)] := by
    dsimp only [signals]
    delta Circuit.wires
    rw [List.foldl_append]
    rfl
  have keep {m} (gs : List Gate) (g : Gate) (p : Bool ⊕ Nat) (hp : valid (m+gs.length) p)
      (v : Fin m → Bool) : read p (signals (gs ++ [g]) v) = read p (signals gs v) := by
    cases p with
    | inl b => rfl
    | inr i =>
      change i < m + gs.length at hp
      rw [snoc]
      exact List.getD_append _ _ _ _ ((sigLength gs v).symm ▸ hp)
  have compile (m : Nat) (s : List (BitVec 29)) (sample : Fin 29 → Fin m → Bool)
      (active : Fin 29 → Prop) (goal : BitVec 29)
      (init : ∀ z ∈ s, ∃ p : Bool ⊕ Fin m, ∀ j, active j →
        p.elim id (sample j) = z.getLsbD j.val)
      (nonconstant : ∀ b : Bool, ∃ j, active j ∧ goal.getLsbD j.val ≠ b)
      (t : List (BitVec 29 × BitVec 29 × BitVec 29)) (ht : legal s t)
      (member : goal ∈ available s t) :
      ∃ C : Circuit, FanInTwo C ∧ C.size = t.length ∧ Monotone (circuitFun m C) ∧
        ∀ j, active j → circuitFun m C (sample j) = goal.getLsbD j.val := by
    let invariant (gs : List Gate) (z : BitVec 29) := ∃ p : Bool ⊕ Nat,
      valid (m+gs.length) p ∧ Monotone (fun v : Fin m → Bool => read p (signals gs v)) ∧
        ∀ j, active j → read p (signals gs (sample j)) = z.getLsbD j.val
    have build (l : List (BitVec 29 × BitVec 29 × BitVec 29)) (hl : legal s l) :
        ∃ gs : List Gate, gs.length = l.length ∧ FanInTwo ⟨gs,0⟩ ∧
        ∀ z ∈ available s l, invariant gs z := by
      induction l using List.reverseRecOn with
      | nil =>
        refine ⟨[],rfl,by intro g hg; simp at hg,?_⟩
        intro z hz
        obtain ⟨p,hs⟩ := init z (by simpa [available] using hz)
        rcases p with b|i
        · exact ⟨.inl b,trivial,monotone_const,hs⟩
        · have atInput (v : Fin m → Bool) : read (.inr i.val) (signals [] v) = v i := by
            change (List.ofFn v).getD i.val false = v i
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          refine ⟨.inr i.val,by exact i.isLt,?_,?_⟩
          · intro v w h; dsimp only; rw [atInput,atInput]; exact h i
          · intro j hj; rw [atInput]; exact hs j hj
      | append_singleton l g ih =>
        obtain ⟨gs,size,fan,seen⟩ := ih (prefixLegal hl)
        obtain ⟨ha,hb,hvalue⟩ := lastLegal hl
        obtain ⟨a,va,ma,ra⟩ := seen g.2.1 ha
        obtain ⟨b,vb,mb,rb⟩ := seen g.2.2 hb
        obtain ⟨d,hg⟩ : ∃ d : Bool,
            g.1 = if d then g.2.1 &&& g.2.2 else g.2.1 ||| g.2.2 := by
          rcases hvalue with h|h
          · exact ⟨true,h⟩
          · exact ⟨false,h⟩
        let last := make d a b
        let q := m + gs.length
        have now (v : Fin m → Bool) : read (.inr q) (signals (gs ++ [last]) v) =
            if d then read a (signals gs v) && read b (signals gs v)
            else read a (signals gs v) || read b (signals gs v) := by
          change (signals (gs ++ [last]) v).getD q false = _
          rw [snoc, show q = (signals gs v).length from (sigLength gs v).symm]
          simpa using (makeSpec d a b (signals gs v)).2
        refine ⟨gs ++ [last],by simp [size],?_,?_⟩
        · intro u hu
          rcases List.mem_append.mp hu with hp|hp
          · exact fan u hp
          · exact (List.mem_singleton.mp hp) ▸ (makeSpec d a b []).1
        · intro z hz
          change z ∈ s ++ (l ++ [g]).map Prod.fst at hz
          rw [List.map_append,← List.append_assoc] at hz
          rcases List.mem_append.mp hz with old|new
          · obtain ⟨p,hp,mp,rp⟩ := seen z old
            refine ⟨p,?_,?_,?_⟩
            · cases p with
              | inl b => trivial
              | inr i =>
                change i < m + gs.length at hp
                change i < m + (gs ++ [last]).length
                simp; omega
            · intro v w h; dsimp only; rw [keep gs last p hp v,keep gs last p hp w]; exact mp h
            · intro j hj; rw [keep gs last p hp]; exact rp j hj
          · have eq : z = g.1 := by simpa using new
            refine ⟨.inr q,by change q < m+(gs++[last]).length; simp [q],?_,?_⟩
            · intro v w hvw
              dsimp only
              rw [now,now]
              have p := ma hvw
              have r := mb hvw
              cases d
              · exact sup_le_sup p r
              · exact inf_le_inf p r
            · intro j hj
              rw [now,ra j hj,rb j hj,eq,hg]
              cases d <;> simp
    obtain ⟨gs,size,fan,seen⟩ := build t ht
    obtain ⟨p,hp,mono,rep⟩ := seen goal member
    rcases p with b|i
    · obtain ⟨j,act,hne⟩ := nonconstant b
      exact (hne (rep j act).symm).elim
    · exact ⟨⟨gs,i⟩,fan,size,mono,rep⟩
  let edge (v : Fin 9 → Bool) :=
    v 0 && v 1 || v 1 && v 2 || v 2 && v 3 || v 3 && v 4 || v 4 && v 0 || v 0 && v 5 ||
    v 1 && v 6 || v 2 && v 7 || v 3 && v 8 || v 5 && v 7 || v 6 && v 8 || v 8 && v 5
  let bits (a : Fin 512) (i : Fin 9) := a.val.testBit i.val
  -- Each five-bit entry selects a comparable boundary row in the same slice.
  let witness (a : Fin 512) : Fin 29 := Fin.ofNat 29 ((0x462014850048d0249000462024d0004cd024d000462014850048d0249900462026d5005cd0275900462014850048d0409000462040d0004cd040d000462014850048d0709c00462056d5005cd0737c0046201485004980249800462024d5004d8024d80046201485004990249900462026d500759027590046201485004980609800462054d5004d8060d80046201485004970709700462056d5006970729700462014850048d0249000462024d0004cd024d000462014850048d024930046202651005cd0265100462014850048d0409000462040d0004cd040d000462014850048d070930046203e4f005cd03e4f00462014850048c0248c00462024cb004cc024cb00462014850048c0248c004620264b0054c0254b00462014850048c020880046201cc7004cc01cc700462014850048c020880046201e470054c01d47 >>> (5*a.val)) % 32)
  have covers : ∀ a : Fin 512,
      let j := witness a
      let z := bits a
      input j 0 = z 0 ∧ target.getLsbD j.val = edge z ∧
      (∀ i, if edge z then input j i ≤ z i else z i ≤ input j i) := by decide +kernel
  have liftAt (f : (Fin 9 → Bool) → Bool) (mono : Monotone f) (z : Fin 9 → Bool)
      (hr : ∀ j, input j 0 = z 0 → f (input j) = target.getLsbD j.val) :
      f z = edge z := by
    let v := BitVec.ofBoolListLE (List.ofFn z)
    let a : Fin 512 := ⟨v.toNat,by have h := v.isLt; simpa [v] using h⟩
    have eq : bits a = z := by
      funext i
      change v.getLsbD i.val = _
      rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    obtain ⟨atZero,goalBit,order⟩ := covers a
    rw [eq] at atZero goalBit order
    have valEq := (hr _ atZero).trans goalBit
    cases h : edge z
    · have le : z ≤ input (witness a) := fun i => by simpa [h] using order i
      have m := mono le
      rw [valEq,h] at m
      exact le_antisymm m (Bool.false_le _)
    · have le : input (witness a) ≤ z := fun i => by simpa [h] using order i
      have m := mono le
      rw [valEq,h] at m
      exact le_antisymm (Bool.le_true _) m
  have ordinary (t : List (BitVec 29 × BitVec 29 × BitVec 29)) (limit : t.length ≤ 14)
      (hl : legal sources t) : target ∉ available sources t := by
    intro member
    have ini : ∀ z ∈ sources, ∃ p : Bool ⊕ Fin 9, ∀ j : Fin 29, True →
        p.elim id (input j) = z.getLsbD j.val := by
      have h : sources.all (fun z => decide (∃ p : Bool ⊕ Fin 9, ∀ j : Fin 29,
          p.elim id (input j) = z.getLsbD j.val)) = true := by decide +kernel
      simpa only [List.all_eq_true,decide_eq_true_eq,true_implies] using h
    have nc : ∀ b : Bool, ∃ j : Fin 29, True ∧ target.getLsbD j.val ≠ b := by decide +kernel
    obtain ⟨C,fan,size,mono,correct⟩ := compile 9 sources input _ target ini nc t hl member
    have agree : circuitFun 9 C = edge := by
      funext z
      exact liftAt _ mono z (fun j _ => correct j trivial)
    have lower := ordinaryBound C fan agree
    omega
  have cofactor (t : List (BitVec 29 × BitVec 29 × BitVec 29)) (limit : t.length ≤ 11)
      (hl : legal restricted t) : (52503078 : BitVec 29) ∉ available restricted t := by
    intro member
    let tailSample (j : Fin 29) (i : Fin 8) := input j i.succ
    let maskTarget : BitVec 29 := 52503078
    let active (j : Fin 29) := input j 0 = false
    have ini : ∀ z ∈ restricted, ∃ p : Bool ⊕ Fin 8, ∀ j : Fin 29, active j →
        p.elim id (tailSample j) = z.getLsbD j.val := by
      have h : restricted.all (fun z => decide (∃ p : Bool ⊕ Fin 8, ∀ j : Fin 29, active j →
          p.elim id (tailSample j) = z.getLsbD j.val)) = true := by decide +kernel
      simpa only [List.all_eq_true,decide_eq_true_eq] using h
    have nc : ∀ b : Bool, ∃ j : Fin 29, active j ∧ maskTarget.getLsbD j.val ≠ b := by decide +kernel
    obtain ⟨C,fan,size,mono,correct⟩ := compile 8 restricted tailSample active maskTarget ini nc t hl member
    have coincide : ∀ j : Fin 29, active j → maskTarget.getLsbD j.val = target.getLsbD j.val := by
      decide +kernel
    apply cofactorBound
    refine ⟨C,fan,by omega,?_⟩
    intro v
    let f (z : Fin 9 → Bool) := circuitFun 8 C (fun i => z i.succ)
    have fm : Monotone f := fun _ _ h => mono (fun i => h i.succ)
    have eq := liftAt f fm (Fin.cons false v) (fun j hj => (correct j hj).trans (coincide j hj))
    change circuitFun 8 C v = edge (Fin.cons false v)
    simpa only [f,Fin.cons_succ] using eq
  have noNeg : 0 < t.countP (reads y) := by
    by_contra! none
    have avoids : ∀ g ∈ t, reads y g = false := by
      have z : t.countP (reads y) = 0 := by omega
      simpa [List.countP_eq_zero] using z
    have bare : legal sources t := by
      intro i
      obtain ⟨a,b,hg⟩ := ht i
      have h := avoids t[i.val] (List.getElem_mem ..)
      simp only [reads,Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      change _ ∈ y :: available sources _ at a b
      exact ⟨(List.mem_cons.mp a).resolve_left h.1, (List.mem_cons.mp b).resolve_left h.2,hg⟩
    have rn : target ≠ y := by decide +kernel
    exact (ordinary t (by omega) bare) ((List.mem_cons.mp result).resolve_left rn)
  have posRead : 0 < t.countP (reads x) := by
    by_contra! none
    have avoids : ∀ g ∈ t, reads x g = false := by
      have z : t.countP (reads x) = 0 := by omega
      simpa [List.countP_eq_zero] using z
    let ordered (v : (BitVec 29)) : Prop := v.getLsbD 0 = true → v.getLsbD 7 = true
    have initial : ∀ v ∈ base, v ≠ x → ordered v := by
      have h : base.all (fun v => decide (v ≠ x → ordered v)) = true := by decide +kernel
      simpa only [List.all_eq_true,decide_eq_true_eq] using h
    have inv (l : List (BitVec 29 × BitVec 29 × BitVec 29)) (hl : legal base l) (hr : ∀ g ∈ l, reads x g = false) :
        ∀ v ∈ available base l, v ≠ x → ordered v := by
      induction l using List.reverseRecOn with
      | nil => simpa [available] using initial
      | append_singleton l g ih =>
        have baseInv := ih (prefixLegal hl) (fun a ha => hr a (List.mem_append_left _ ha))
        have a := lastLegal hl
        have h := hr g (by simp)
        simp only [reads,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at h
        have pa := baseInv _ a.1 h.1
        have pb := baseInv _ a.2.1 h.2
        intro v hv hx
        change v ∈ base ++ (l ++ [g]).map Prod.fst at hv
        rw [List.map_append,← List.append_assoc] at hv
        rcases List.mem_append.mp hv with old|new
        · exact baseInv v old hx
        · have e : v = g.1 := by simpa using new
          rcases a.2.2 with eq|eq <;> rw [e,eq] <;>
            simp only [ordered,BitVec.getLsbD_and,BitVec.getLsbD_or,Bool.and_eq_true,
              Bool.or_eq_true] at pa pb ⊢ <;> tauto
    have impossible := inv t ht avoids target result (by decide +kernel)
    exact (show ¬ ordered target by decide +kernel) impossible
  let proj (v : (BitVec 29)) := v &&& y
  have starts : ∀ v ∈ base, proj v ∈ restricted := by
    have h : base.all (fun v => decide (proj v ∈ restricted)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  have initialBack : ∀ v ∈ restricted, v ∈ base.map proj := by
    have h : restricted.all (fun v => decide (v ∈ base.map proj)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  have compression (l : List (BitVec 29 × BitVec 29 × BitVec 29)) (hl : legal base l) :
      ∃ u : List (BitVec 29 × BitVec 29 × BitVec 29), legal restricted u ∧ u.length + l.countP touch ≤ l.length ∧
      (available restricted u).Nodup ∧
      (∀ z ∈ available restricted u, z ∈ (available base l).map proj) ∧
      ∀ v ∈ available base l, proj v ∈ available restricted u := by
    induction l using List.reverseRecOn with
    | nil =>
      exact ⟨[], by intro j; exact Fin.elim0 j,by simp,by decide +kernel,
        by simpa [available] using initialBack,by simpa [available] using starts⟩
    | append_singleton l g ih =>
      obtain ⟨u,hu,hlen,freshU,back,seen⟩ := ih (prefixLegal hl)
      obtain ⟨a,b,gateEq⟩ := lastLegal hl
      have ha := seen _ a
      have hb := seen _ b
      have projected : proj g.1 = proj g.2.1 &&& proj g.2.2 ∨
          proj g.1 = proj g.2.1 ||| proj g.2.2 := by
        rcases gateEq with h|h
        · left; rw [h]
          calc
            _ = (g.2.1 &&& g.2.2) &&& (y &&& y) := by simp [proj]
            _ = _ := by dsimp [proj]; ac_rfl
        · right; rw [h]; exact BitVec.and_or_distrib_right
      have oldIfTouch (h : touch g = true) : proj g.1 ∈ available restricted u := by
        have z : (0 : (BitVec 29)) ∈ available restricted u :=
          List.mem_append_left _ (by decide +kernel : (0 : (BitVec 29)) ∈ restricted)
        have m : y ∈ available restricted u :=
          List.mem_append_left _ (by decide +kernel : y ∈ restricted)
        have zx : proj x = 0 := by decide +kernel
        have zy : proj y = y := by decide +kernel
        have reduce (v : BitVec 29) :
            proj v &&& y = proj v ∧ y &&& proj v = proj v ∧
            proj v ||| y = y ∧ y ||| proj v = y := by
          have a : proj v &&& y = proj v := by simp [proj,BitVec.and_assoc]
          have b : proj v ||| y = y := by
            apply BitVec.eq_of_getElem_eq
            intro i hi
            simp only [proj,BitVec.getElem_and,BitVec.getElem_or]
            cases y[i] <;> simp
          exact ⟨a,(BitVec.and_comm ..).trans a,b,(BitVec.or_comm ..).trans b⟩
        have zeroL (v : BitVec 29) : (0 : BitVec 29) &&& v = 0 := BitVec.zero_and
        have zeroR (v : BitVec 29) : v &&& (0 : BitVec 29) = 0 := BitVec.and_zero
        have orL (v : BitVec 29) : (0 : BitVec 29) ||| v = v := BitVec.zero_or
        have orR (v : BitVec 29) : v ||| (0 : BitVec 29) = v := BitVec.or_zero
        have aa := reduce g.2.1
        have bb := reduce g.2.2
        simp only [touch,reads,Bool.or_eq_true,beq_iff_eq] at h
        rcases h with (h|h)|(h|h) <;> rcases projected with eq|eq <;> rw [eq,h] <;>
          simp only [zx,zy,zeroL,zeroR,orL,orR,
            aa.1,aa.2.2.1,bb.2.1,bb.2.2.2] <;> assumption
      have liftSeen (u' : List (BitVec 29 × BitVec 29 × BitVec 29)) (old : ∀ a ∈ available restricted u, a ∈ available restricted u')
          (new : proj g.1 ∈ available restricted u') :
          ∀ v ∈ available base (l ++ [g]), proj v ∈ available restricted u' := by
        intro v hv
        change v ∈ base ++ (l ++ [g]).map Prod.fst at hv
        rw [List.map_append,← List.append_assoc] at hv
        rcases List.mem_append.mp hv with h|h
        · exact old _ (seen _ h)
        · have eq : v = g.1 := by simpa using h
          exact eq ▸ new
      have larger : (available base (l ++ [g])).map proj =
          (available base l).map proj ++ [proj g.1] := by simp [available,List.append_assoc]
      have backOld (v) (hv : v ∈ available restricted u) :
          v ∈ (available base (l ++ [g])).map proj := larger ▸ List.mem_append_left _ (back v hv)
      by_cases old : proj g.1 ∈ available restricted u
      · refine ⟨u,hu,?_,freshU,backOld,liftSeen u (fun _ h => h) old⟩
        cases h : touch g <;> simp [List.countP_append,h] <;> omega
      · have h : touch g ≠ true := fun h => old (oldIfTouch h)
        let g' : BitVec 29 × BitVec 29 × BitVec 29 := (proj g.1, proj g.2.1, proj g.2.2)
        refine ⟨u ++ [g'],extend hu g' ha hb projected,?_,?_,?_,liftSeen _ ?_ ?_⟩
        · simp [List.countP_append,h]; omega
        · have nd := (List.nodup_concat (available restricted u) (proj g.1)).2 ⟨old,freshU⟩
          simpa [available,List.concat_eq_append,List.append_assoc,g'] using nd
        · intro z hz
          change z ∈ restricted ++ (u ++ [g']).map Prod.fst at hz
          rw [List.map_append,← List.append_assoc] at hz
          rcases List.mem_append.mp hz with ho|hg
          · exact backOld z ho
          · rw [larger]; exact List.mem_append_right _ (by simpa [g'] using hg)
        · intro v hv
          simpa [available,List.append_assoc] using List.mem_append_left [g'.1] hv
        · simp [available,g']
  obtain ⟨u, hu, ulen, freshU, back, us⟩ := compression t ht
  have gmem := us target result
  have sufficient : 12 ≤ u.length := by
    by_contra! h
    have projEq : proj target = 52503078 := by decide +kernel
    rw [projEq] at gmem
    exact cofactor u (by omega) hu gmem
  have countAux (l : List (BitVec 29 × BitVec 29 × BitVec 29))
      (hs : ∀ g ∈ l, ¬ (reads x g = true ∧ reads y g = true)) :
      l.countP touch = l.countP (reads x) + l.countP (reads y) := by
    induction l with
    | nil => rfl
    | cons g gs ih =>
      have hh := hs g (by simp)
      have tail := ih (fun a ha => hs a (List.mem_cons_of_mem _ ha))
      simp only [List.countP_cons, show touch g = (reads x g || reads y g) from rfl, tail]
      cases a : reads x g <;> cases b : reads y g <;>
        first | exact (hh ⟨a,b⟩).elim | simp <;> omega
  have count := countAux t sep
  have hx : t.countP (reads x) = 1 := by omega
  have hy : t.countP (reads y) = 1 := by omega
  have sub : (available restricted u).toFinset ⊆ ((available base t).map proj).toFinset :=
    fun v h => List.mem_toFinset.mpr (back v (List.mem_toFinset.mp h))
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup freshU] at card
  simp only [available,List.length_append,List.length_map,show restricted.length = 10 from rfl] at card
  have dimension : 22 ≤ ((available base t).map proj).toFinset.card := by
    exact le_trans (by omega : 22 ≤ 10 + u.length) card
  exact twoPorts t (by omega) hx hy fresh dimension ht lastIsTarget
