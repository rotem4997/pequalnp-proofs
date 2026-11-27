import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Rows zero through twenty are edges. Rows twenty-one through fifty-seven are maximal independent sets.
-- To check the negative rows, choose the seven point bits and add all lines disjoint from those points.
-- Each initial integer is one input column. The low and high base-sixty-four digits select crossing rows.
theorem PEqualNP.Outside.R_meta_2876_58
    (cover :
      let P := fun (x : Fin 14 → Bool) => ∃ u v : Fin 14,
      (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true ∧
      x u = true ∧ x v = true
      let row := fun (r : Fin 58) (v : Fin 14) => (([129,130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208,127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ).getD r.val 0).testBit v.val
      ∀ x, (Minimal P x → ∃ r : Fin 58, r.val < 21 ∧ x = row r) ∧
        (Maximal (fun y => ¬ P y) x → ∃ r : Fin 58, 21 ≤ r.val ∧ x = row r))
    (synthesis :
      ∃ (gs : List (Bool × ℕ × ℕ)) (a b : ℕ) (s : Fin 16),
        gs.length ≤ 25 ∧ 14 ≤ a ∧ a < b ∧ b < 14 + gs.length ∧
        let k := ([64,256,448,1429,1557,2389,3669,1494,1558,1750,1942,2390,2902,1688,1880,2008] : List ℕ).getD s.val 0
        let i := k % 64
        let j := k / 64
        let w := gs.foldl (fun w g => w ++ [(fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
          if g.1 then (w.getD g.2.1 0) ||| (w.getD g.2.2 0)
          else (w.getD g.2.1 0) &&& (w.getD g.2.2 0)) w g]) ([95229015649944073,63038587928642,256463372304,4292497062825988,8521482511360,14003410187716736,55389823206179104,189297016294080519,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088] : List ℕ)
        let A := w.getD a 0
        let B := w.getD b 0
        (if i < 21 then A ||| B else A &&& B) = 2097151 ∧
          A.testBit i ≠ B.testBit i ∧ A.testBit i = B.testBit j ∧ B.testBit i = A.testBit j) :
    have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.GateOp) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ × ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (25 : ℕ) ∧       (14 : ℕ) ≤ x4 ∧         x4 < x5 ∧           x5 < (14 : ℕ) + x2.size ∧             (x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6 ∈ [((129 : ℕ), (130 : ℕ)), ((129 : ℕ), (260 : ℕ)), ((129 : ℕ), (544 : ℕ))] ∨ x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6 ∈ [((127 : ℕ), (244 : ℕ)), ((127 : ℕ), (432 : ℕ)), ((127 : ℕ), (3716 : ℕ)), ((127 : ℕ), (16256 : ℕ)), ((244 : ℕ), (314 : ℕ)), ((244 : ℕ), (432 : ℕ)), ((244 : ℕ), (792 : ℕ)), ((244 : ℕ), (1290 : ℕ)), ((244 : ℕ), (3716 : ℕ)), ((244 : ℕ), (7426 : ℕ)), ((432 : ℕ), (660 : ℕ)), ((432 : ℕ), (1220 : ℕ)), ((432 : ℕ), (1548 : ℕ))]) ∧               have x7 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (14 : ℕ) → Bool) => (x2.wires (List.ofFn x8)).getD x7 Bool.false;               have x8 : Fin (14 : ℕ) → Bool := fun (x8 : Fin (14 : ℕ)) => x6.1.testBit ↑x8;               have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => x6.2.testBit ↑x9;               have x10 : (Fin (14 : ℕ) → Bool) → Bool := fun (x10 : Fin (14 : ℕ) → Bool) => x3.eval [x7 x4 x10, x7 x5 x10];               x7 x4 x8 ≠ x7 x5 x8 ∧ x7 x4 x8 = x7 x5 x9 ∧ x7 x5 x8 = x7 x4 x9 ∧ (∀ (x11 : Fin (14 : ℕ) → Bool), Minimal x1 x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.true) ∧ ∀ (x11 : Fin (14 : ℕ) → Bool), Maximal (fun (x12 : Fin (14 : ℕ) → Bool) => ¬x1 x12) x11 → x3 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x11 = x8 ∨ x11 = x9) ∨ x10 x11 = Bool.false := by
  intro P
  let rows := ([129,130,136,257,260,320,514,544,576,1025,1040,1056,2056,2064,2112,4100,4104,4128,8194,8196,8208,127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ)
  let initial := ([95229015649944073,63038587928642,256463372304,4292497062825988,8521482511360,14003410187716736,55389823206179104,189297016294080519,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088] : List ℕ)
  let codes := ([64,256,448,1429,1557,2389,3669,1494,1558,1750,1942,2390,2902,1688,1880,2008] : List ℕ)
  let op := fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
          if g.1 then (w.getD g.2.1 0) ||| (w.getD g.2.2 0)
          else (w.getD g.2.1 0) &&& (w.getD g.2.2 0)
  let gate := fun (g : Bool × ℕ × ℕ) => Gate.mk (if g.1 then .or else .and) [g.2.1, g.2.2]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  let row := fun (r : ℕ) (v : Fin 14) => (rows.getD r 0).testBit v.val
  obtain ⟨gs,a,b,s,hsize,ha,hab,hb,hw,hne,hxy,hyx⟩ := synthesis
  let k := codes.getD s.val 0
  let i := k % 64
  let j := k / 64
  let W := gs.foldl (fun w g => w ++ [op w g]) initial
  let C := Circuit.mk (gs.map gate) b
  let t : GateOp := if i < 21 then .or else .and
  have lookup (n : ℕ) (w : List ℕ) (r : ℕ) :
      (w.map (fun z => z.testBit r)).getD n false = (w.getD n 0).testBit r := by
    simp only [List.getD, List.getElem?_map]
    cases w[n]? <;> simp
  have run (ls : List (Bool × ℕ × ℕ)) (w : List ℕ) (r : ℕ) :
      (ls.map gate).foldl step (w.map fun z => z.testBit r) =
      (ls.foldl (fun z g => z ++ [op z g]) w).map (fun z => z.testBit r) := by
    induction ls generalizing w with
    | nil => rfl
    | cons g ls ih =>
      simp only [List.map_cons,List.foldl_cons]
      rw [← ih]
      congr 1
      rcases g with ⟨kind,left,right⟩
      cases kind
      · change w.map _ ++ [((w.map _).getD left false && ((w.map _).getD right false && true))] = _
        simp only [lookup, op, Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
          List.map_nil, Nat.testBit_and, Bool.and_true]
      · change w.map _ ++ [((w.map _).getD left false || ((w.map _).getD right false || false))] = _
        simp only [lookup, op, ↓reduceIte, List.map_append, List.map_cons,
          List.map_nil, Nat.testBit_or, Bool.or_false]
  have columns : ∀ r : Fin 58, List.ofFn (row r.val) = initial.map (fun z => z.testBit r.val) := by
    decide +kernel
  have wire (n r : ℕ) (hr : r < 58) :
      (C.wires (List.ofFn (row r))).getD n false = (W.getD n 0).testBit r := by
    change ((gs.map gate).foldl step (List.ofFn (row r))).getD n false = _
    rw [columns ⟨r,hr⟩, run, lookup]
  have bounds : ∀ s : Fin 16, (codes.getD s.val 0) % 64 < 58 ∧ (codes.getD s.val 0) / 64 < 58 := by
    decide +kernel
  obtain ⟨hi,hj⟩ := bounds s
  have types : ∀ s : Fin 16, let k := codes.getD s.val 0
      let m := (rows.getD (k % 64) 0, rows.getD (k / 64) 0)
      ((k % 64 < 21 ∧ m ∈ ([(129,130),(129,260),(129,544)] : List (ℕ × ℕ))) ∨
       (¬ k % 64 < 21 ∧ m ∈ ([(127,244),(127,432),(127,3716),(127,16256),(244,314),(244,432),(244,792),(244,1290),(244,3716),(244,7426),(432,660),(432,1220),(432,1548)] : List (ℕ × ℕ)))) := by decide +kernel
  have val (r : Fin 58) : t.eval [(C.wires (List.ofFn (row r.val))).getD a false,
      (C.wires (List.ofFn (row r.val))).getD b false] = decide (r.val < 21) := by
    rw [wire a _ r.isLt, wire b _ r.isLt]
    have bits : ∀ n : Fin 58, (2097151 : ℕ).testBit n.val = decide (n.val < 21) := by decide +kernel
    have hword : (if i < 21 then (W.getD a 0) ||| (W.getD b 0)
                            else (W.getD a 0) &&& (W.getD b 0)) = 2097151 := hw
    have col := (congrArg (fun v : ℕ => v.testBit r.val) hword).trans (bits r)
    by_cases h : i < 21
    · simp only [t, ite_eq_left h, Nat.testBit_or] at col ⊢
      change ((_ || (_ || false)) = _)
      simpa only [id_eq, Bool.or_false] using col
    · simp only [t, ite_eq_right h, Nat.testBit_and] at col ⊢
      change ((_ && (_ && true)) = _)
      simpa only [id_eq, Bool.and_true] using col
  refine ⟨C,t,a,b,(rows.getD i 0, rows.getD j 0),?_,?_,ha,hab,?_,?_,?_,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨⟨kind,l,r⟩, _, rfl⟩ := List.mem_map.mp hg
    cases kind
    · exact ⟨Or.inl rfl, le_rfl⟩
    · exact ⟨Or.inr rfl, le_rfl⟩
  · change (gs.map gate).length ≤ 25
    simpa only [List.length_map] using hsize
  · change b < 14 + (gs.map gate).length
    simpa only [List.length_map] using hb
  · rcases types s with ⟨hc,hm⟩ | ⟨hc,hm⟩
    · exact Or.inl ⟨ite_eq_left hc, hm⟩
    · exact Or.inr ⟨ite_eq_right hc, hm⟩
  · exact fun h => hne ((wire a i hi).symm.trans (h.trans (wire b i hi)))
  · exact (wire a i hi).trans (hxy.trans (wire b j hj).symm)
  · exact (wire b i hi).trans (hyx.trans (wire a j hj).symm)
  · intro x hx
    obtain ⟨r, hr, he⟩ := (cover x).1 hx
    subst x
    exact Or.inr ((val r).trans (by simp [hr]))
  · intro x hx
    obtain ⟨r, hr, he⟩ := (cover x).2 hx
    subst x
    exact Or.inr ((val r).trans (by simp [show ¬ r.val < 21 by omega]))
