import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2147_583
    (geometry :
      let ds : Finset (Fin 13) := {0, 1, 3, 9}
      let rows : List ℕ := [7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587,
        19988517, 3211303, 19415081, 7372867, 24117317, 7340103, 23085129,
        23068749, 22052945, 5275731, 22020181, 19939425, 19923045, 18890857,
        6389891, 6619269, 6357127, 6570121, 6553741, 6324419, 6308041,
        21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625,
        17891877]
      ∀ k ∈ rows, ∀ t : Fin 13,
        let P := Finset.univ.filter (fun p : Fin 13 => k.testBit (p-t).val)
        let Q := Finset.univ.filter (fun l : Fin 13 => k.testBit (13+(l-t).val))
        (∀ l : Fin 13, l ∈ Q ↔ ∀ p ∈ P, ¬∃ d ∈ ds, p = l+d) ∧
        (∀ p ∉ P, ∃ l ∈ Q, ∃ d ∈ ds, p = l+d) ∧
        (¬∃ l : Fin 13, ∀ p ∈ P, ∃ d ∈ ds, p = l+d) ∧
        (¬∃ p : Fin 13, ∀ l ∈ Q, ∃ d ∈ ds, p = l+d))
    (normalized :
      let rows : List ℕ := [7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587,
        19988517, 3211303, 19415081, 7372867, 24117317, 7340103, 23085129,
        23068749, 22052945, 5275731, 22020181, 19939425, 19923045, 18890857,
        6389891, 6619269, 6357127, 6570121, 6553741, 6324419, 6308041,
        21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625,
        17891877]
      ¬∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧ C.output+1 = 26+C.size ∧
        (∀ b ∈ C.gates.zipIdx, ∀ a ∈ b.1.inputs, a < 26+b.2 ∨ a = 89) ∧
        ¬HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧ ¬HasLineDegree 26 (Finset.range 13) C 1 ∧
        (∀ l d : Fin 13, (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9) →
          circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 (l+d) ∨ i = Fin.natAdd 13 l)) = true) ∧
        ∀ k ∈ rows, ∀ t : Fin 13,
          circuitFun 26 C (fun i => decide
            ((∃ p : Fin 13, k.testBit (p-t).val ∧ i = Fin.castAdd 13 p) ∨
             (∃ l : Fin 13, k.testBit (13+(l-t).val) ∧ i = Fin.natAdd 13 l))) = false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
    ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧
      x2.size ≤ (63 : ℕ) ∧
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) x2 (1 : ℕ) ∧
      ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧
      (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) →
        (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧
      ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧
      ∃ x7 ∈ x1, x4 = x6 + x7) →
        ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧
      ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) →
        ∃ x8 ∈ x1, x5 = x6 + x8) →
        (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧
      ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false := by
  intro ds h
  obtain ⟨C, hmono, hsize, highL, highP, hpos, hneg⟩ := h
  let rows : List ℕ := [7405575, 23330829, 5799955, 22282261, 21757977, 21233693, 3735587,
        19988517, 3211303, 19415081, 7372867, 24117317, 7340103, 23085129,
        23068749, 22052945, 5275731, 22020181, 19939425, 19923045, 18890857,
        6389891, 6619269, 6357127, 6570121, 6553741, 6324419, 6308041,
        21512457, 21528849, 4751635, 21496089, 17318185, 20988233, 21004625,
        17891877]
  have keep {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
      (i : ℕ) (z : α) (hi : i < w.length) :
      (gs.foldl (fun l g => l ++ [f l g]) w).getD i z = w.getD i z := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
        change (gs.foldl (fun l g => l ++ [f l g]) (w ++ [f w g])).getD i z = _
        rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]
  have sizeFold {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
      (gs.foldl (fun l g => l ++ [f l g]) w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
        change (gs.foldl (fun l g => l ++ [f l g]) (w ++ [f w g])).length = _
        rw [ih]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
  let f (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun i => w.getD i false))
  have positive (l : Fin 13) : circuitFun 26 C (fun i =>
      decide (i = Fin.castAdd 13 l ∨ i = Fin.natAdd 13 l)) = true :=
    hpos l l ⟨0, by decide, by simp⟩
  have houtLo : 26 ≤ C.output := by
    by_contra hlt
    have hi : C.output < 26 := by omega
    let i : Fin 26 := ⟨C.output, hi⟩
    let input (l : Fin 13) (i : Fin 26) := decide (i = Fin.castAdd 13 l ∨ i = Fin.natAdd 13 l)
    have read (l : Fin 13) : input l i = true := by
      have h := positive l
      change (C.gates.foldl (fun w g => w ++ [f w g]) (List.ofFn (input l))).getD C.output false = true at h
      rw [keep f _ _ _ _ (by simpa only [List.length_ofFn] using hi),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
        List.getElem_ofFn] at h
      exact h
    have disjoint : ∀ j : Fin 26, (input 0 j && input 1 j) = false := by decide
    have contra := disjoint i
    rw [read 0, read 1] at contra
    exact Bool.noConfusion contra
  have houtHi : C.output < 26 + C.gates.length := by
    by_contra hn
    have h := positive 0
    let w : List Bool := List.ofFn (fun i : Fin 26 =>
      decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13)))
    change (C.gates.foldl (fun w g => w ++ [f w g]) w).getD C.output false = true at h
    rw [List.getD_eq_default _ _ (by
      rw [sizeFold]
      have hw : w.length = 26 := List.length_ofFn
      omega)] at h
    exact Bool.noConfusion h
  let cut := C.output + 1 - 26
  let D : Circuit := ⟨C.gates.take cut, C.output⟩
  have cut_le : cut ≤ C.gates.length := by omega
  have lengthD : D.gates.length = cut := by
    change (C.gates.take cut).length = cut
    rw [List.length_take, min_eq_left cut_le]
  have hshape : D.output+1 = 26+D.size := by
    change C.output+1 = 26+D.gates.length
    omega
  have same {α : Type} (f : List α → Gate → α) (w : List α) (hlen : w.length = 26) (z : α) :
      (C.gates.foldl (fun l g => l ++ [f l g]) w).getD C.output z =
        (D.gates.foldl (fun l g => l ++ [f l g]) w).getD D.output z := by
    conv_lhs => rw [← List.take_append_drop cut C.gates, List.foldl_append]
    change ((C.gates.drop cut).foldl (fun l g => l ++ [f l g])
      (D.gates.foldl (fun l g => l ++ [f l g]) w)).getD C.output z = _
    rw [keep f _ _ _ _ (by rw [sizeFold, hlen, lengthD]; omega)]
  have eval (x : Fin 26 → Bool) : circuitFun 26 C x = circuitFun 26 D x :=
    same f (List.ofFn x) List.length_ofFn false
  have deg (M : Finset ℕ) : C.lineDeg 26 M = D.lineDeg 26 M :=
    same (fun l g => g.lineDegree l)
      ((List.range 26).map fun i => if i ∈ M then 1 else 0) (by simp) 0
  have Dsize : D.size ≤ 63 := by
    change D.gates.length ≤ 63
    change C.gates.length ≤ 63 at hsize
    omega
  have DlengthLe : D.gates.length ≤ 63 := Dsize
  let rewriteGate (b : Gate × ℕ) : Gate :=
    ⟨b.1.op, b.1.inputs.map (fun i => if i < 26+b.2 then i else 89)⟩
  let E : Circuit := ⟨(D.gates.zipIdx).map rewriteGate, D.output⟩
  have Elength : E.gates.length = D.gates.length := by simp [E]
  have Esize : E.size ≤ 63 := by
    change E.gates.length ≤ 63
    rw [Elength]
    exact Dsize
  have Eshape : E.output+1 = 26+E.size := by
    change D.output+1 = 26+E.gates.length
    rw [Elength]
    exact hshape
  have clamp {α : Type} (run : GateOp → List α → α) (z : α)
      (gs : List Gate) (w : List α) (k : ℕ) (hw : w.length = 26+k)
      (hbound : k+gs.length ≤ 63) :
      gs.foldl (fun l g => l ++ [run g.op (g.inputs.map (fun i => l.getD i z))]) w =
      ((gs.zipIdx k).map rewriteGate).foldl
        (fun l g => l ++ [run g.op (g.inputs.map (fun i => l.getD i z))]) w := by
    induction gs generalizing w k with
    | nil => rfl
    | cons g gs ih =>
        have mapped : ((rewriteGate (g,k)).inputs.map (fun i => w.getD i z)) =
            g.inputs.map (fun i => w.getD i z) := by
          change (g.inputs.map (fun i => if i < 26+k then i else 89)).map _ = _
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          change w.getD (if i < 26+k then i else 89) z = w.getD i z
          by_cases hi : i < 26+k
          · rw [ite_eq_left hi]
          · rw [ite_eq_right hi, List.getD_eq_default _ _ (by omega),
              List.getD_eq_default _ _ (by omega)]
        simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons, mapped]
        change gs.foldl _ (w ++ [_]) = ((gs.zipIdx (k+1)).map rewriteGate).foldl _ (w ++ [_])
        apply ih
        · simp [hw]; omega
        · simp only [List.length_cons] at hbound
          omega
  have Eeval (x : Fin 26 → Bool) : circuitFun 26 D x = circuitFun 26 E x := by
    change (D.gates.foldl _ (List.ofFn x)).getD D.output false =
      (((D.gates.zipIdx 0).map rewriteGate).foldl _ (List.ofFn x)).getD D.output false
    exact congrArg (fun w => w.getD D.output false)
      (clamp GateOp.eval false D.gates (List.ofFn x) 0 (by simp)
        (by simpa only [Nat.zero_add] using DlengthLe))
  have Edeg (M : Finset ℕ) : D.lineDeg 26 M = E.lineDeg 26 M := by
    let base := (List.range 26).map fun i => if i ∈ M then 1 else 0
    let run (op : GateOp) (l : List ℕ) :=
      @ite ℕ (op = .and) (lineDegreeGateOpDecEq op .and) l.sum (l.foldr max 0)
    change (D.gates.foldl _ base).getD D.output 0 =
      (((D.gates.zipIdx 0).map rewriteGate).foldl _ base).getD D.output 0
    exact congrArg (fun w => w.getD D.output 0)
      (clamp run 0 D.gates base 0 (by simp [base])
        (by simpa only [Nat.zero_add] using DlengthLe))
  have Emono : Monotone2 E := by
    intro g hg
    change g ∈ (D.gates.zipIdx).map rewriteGate at hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    have hm := (List.mem_zipIdx_iff_le_and_getElem?_sub.mp hb).2
    have hp : b.1 ∈ D.gates := List.mem_of_getElem? hm
    have orig := hmono b.1 (List.take_subset cut C.gates hp)
    simpa [rewriteGate] using orig
  have Esources (i : ℕ) (hi : i < E.gates.length) (a : ℕ) (ha : a ∈ E.gates[i].inputs) :
      a < 26+i ∨ a = 89 := by
    have hj : i < (D.gates.zipIdx 0).length := by simpa [Elength] using hi
    change a ∈ ((D.gates.zipIdx 0).map rewriteGate)[i].inputs at ha
    rw [List.getElem_map, List.getElem_zipIdx hj] at ha
    rw [Nat.zero_add] at ha
    change a ∈ D.gates[i].inputs.map (fun x => if x < 26+i then x else 89) at ha
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    by_cases hx : x < 26+i
    · exact Or.inl (by simp [hx])
    · exact Or.inr (by simp [hx])
  apply normalized
  refine ⟨E, Emono, Esize, Eshape, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb a ha
    obtain ⟨g, i⟩ := b
    have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp hb
    obtain ⟨hi, eq⟩ := List.getElem?_eq_some_iff.mp atIndex
    exact Esources i hi a (eq.symm ▸ ha)
  · intro h
    apply highL
    change E.lineDeg 26 _ ≤ 1 at h
    change C.lineDeg 26 _ ≤ 1
    rw [deg, Edeg]
    exact h
  · intro h
    apply highP
    change E.lineDeg 26 _ ≤ 1 at h
    change C.lineDeg 26 _ ≤ 1
    rw [deg, Edeg]
    exact h
  · intro l d hd
    rw [← Eeval, ← eval]
    have member : d ∈ ds := by
      change d ∈ ({0, 1, 3, 9} : Finset (Fin 13))
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hd
    exact hpos _ _ ⟨d, member, rfl⟩
  · intro k hk t
    let P := Finset.univ.filter (fun p : Fin 13 => k.testBit (p-t).val)
    let Q := Finset.univ.filter (fun l : Fin 13 => k.testBit (13+(l-t).val))
    have props := geometry k hk t
    change (∀ l : Fin 13, l ∈ Q ↔ ∀ p ∈ P, ¬∃ d ∈ ds, p = l+d) ∧
      (∀ p ∉ P, ∃ l ∈ Q, ∃ d ∈ ds, p = l+d) ∧
      (¬∃ l : Fin 13, ∀ p ∈ P, ∃ d ∈ ds, p = l+d) ∧
      (¬∃ p : Fin 13, ∀ l ∈ Q, ∃ d ∈ ds, p = l+d) at props
    obtain ⟨hQ, hclosed, hline, hpencil⟩ := props
    have hreject := hneg P
      (fun p hp => by
        obtain ⟨l, hl, hd⟩ := hclosed p hp
        exact ⟨l, (hQ l).mp hl, hd⟩)
      ⟨hline, fun h => by
        obtain ⟨p, hp⟩ := h
        exact hpencil ⟨p, fun l hl => hp l ((hQ l).mp hl)⟩⟩
    rw [← Eeval, ← eval]
    convert hreject using 2
    funext i
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with ⟨p, hp, he⟩ | ⟨l, hl, he⟩
      · exact Or.inl ⟨p, by simpa [P] using hp, he⟩
      · exact Or.inr ⟨l, he, (hQ l).mp (by simpa [Q] using hl)⟩
    · intro h
      rcases h with ⟨p, hp, he⟩ | ⟨l, he, hl⟩
      · exact Or.inl ⟨p, by simpa [P] using hp, he⟩
      · have hx := (hQ l).mpr hl
        exact Or.inr ⟨l, by simpa [Q] using hx, he⟩
