import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.List.Sublists
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3773_791
    (transfer : ∀ gs : List (Bool × ℕ × ℕ), ∀ h ∈ gs.head?,
      h ∈ [(false,0,13), (true,0,1), (true,0,13), (true,2,13)] →
      ∃ C : Circuit, Monotone2 C ∧ C.size = gs.length ∧
        (∃ g : Gate, C.gates.head? = some g ∧
          ((g.op = .and ∧ g.inputs = [0,13]) ∨
           (g.op = .or ∧ g.inputs ∈ [[0,1],[0,13],[2,13]]))) ∧
        ∀ (w : List ℕ) (i : ℕ), w.length = 26 →
          C.eval (w.map fun r => r.testBit i) = ((gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
        w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
              else w.getD g.2.1 0 &&& w.getD g.2.2 0]) w).getLastD 0).testBit i)
    (search : 
      let D : Finset (Fin 13) := {0,1,3,9}
      let disj := fun s : Finset (Fin 13) =>
        Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p+l ∉ D
      let edges := (List.finRange 13).flatMap fun p => ([0,1,3,9] : List (Fin 13)).map fun d =>
        (true, incidenceInput {p} {d-p})
      let small := (List.range 4).flatMap fun k => ((List.finRange 13).sublistsLen k).map List.toFinset
      let ordinary := small.flatMap fun s =>
        [(false, incidenceInput s (disj s)), (false, incidenceInput (disj s) s)]
      let rows := edges ++ ordinary
      let words := List.ofFn fun i : Fin 26 =>
        (rows.map fun r => r.2.getD i.val false).foldr Nat.bit 0
      ∃ (gs : List (Bool × ℕ × ℕ)) (h : Bool × ℕ × ℕ),
        gs.length ≤ 63 ∧ gs.head? = some h ∧ h ∈ [(false,0,13), (true,0,1), (true,0,13), (true,2,13)] ∧
        (gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
        w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
              else w.getD g.2.1 0 &&& w.getD g.2.2 0]) words).getLastD 0 = (rows.map Prod.fst).foldr Nat.bit 0) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  let D : Finset (Fin 13) := {0,1,3,9}
  let disj := fun s : Finset (Fin 13) =>
    Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p+l ∉ D
  let edges := (List.finRange 13).flatMap fun p => ([0,1,3,9] : List (Fin 13)).map fun d =>
    (true, incidenceInput {p} {d-p})
  let subsets := (List.range 4).flatMap fun k => ((List.finRange 13).sublistsLen k).map List.toFinset
  let ordinary := subsets.flatMap fun s =>
    [(false, incidenceInput s (disj s)), (false, incidenceInput (disj s) s)]
  let rows := edges ++ ordinary
  let words := List.ofFn fun i : Fin 26 =>
    (rows.map fun r => r.2.getD i.val false).foldr Nat.bit 0
  obtain ⟨gs,h,lim,head,lead,computed⟩ := search
  have hasHead : h ∈ gs.head? := by simp [head]
  obtain ⟨C,legal,size,first,correct⟩ := transfer gs h hasHead lead
  have bit (bits : List Bool) (j : ℕ) :
      (bits.foldr Nat.bit 0).testBit j = bits.getD j false := by
    induction bits generalizing j with
    | nil => simp
    | cons b t ih =>
      cases j with
      | zero => simp
      | succ j => simp [Nat.testBit_bit_succ, ih]
  have evalRow (r : Bool × List Bool) (member : r ∈ rows) (length : r.2.length = 26) :
      C.eval r.2 = r.1 := by
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem member
    have rowBits : (words.map fun w => w.testBit i) = r.2 := by
      rw [List.map_ofFn]
      apply List.ext_getElem
      · simp [length]
      · intro j hj hj'
        have jLt : j < 26 := by simpa using hj
        simp only [List.getElem_ofFn, Function.comp_apply]
        rw [bit, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hi]
        simp only [Option.map_some, Option.getD_some, eq, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj']
    have v := correct words i (by simp [words])
    change C.eval (words.map fun w => w.testBit i) = _ at v
    rw [rowBits] at v
    rw [v]
    change ((gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
      w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
            else w.getD g.2.1 0 &&& w.getD g.2.2 0]) words).getLastD 0).testBit i = _
    rw [computed, bit, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
    simp [eq]
  have len (s t : Finset (Fin 13)) : (incidenceInput s t).length = 26 := by
    unfold incidenceInput
    simp
  have positiveRow : ∀ p l : Fin 13,
      List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) =
        incidenceInput {p} {l} := by
    intro p l
    unfold incidenceInput PEqualNP.EdgeOwnership.pairInput
    rw [List.ofFn_add]
    congr 1
    · apply congrArg List.ofFn
      funext i
      have ne : i.val ≠ l.val + 13 := by omega
      simp [Fin.ext_iff, ne]
    · apply congrArg List.ofFn
      funext i
      have ne : i.val + 13 ≠ p.val := by omega
      simp [Fin.ext_iff, ne]
  have negRow (s t : Finset (Fin 13)) :
      incidenceInput s t =
        List.ofFn (Fin.addCases (fun p : Fin 13 => decide (p ∈ s))
          (fun l : Fin 13 => decide (l ∈ t))) := by
    unfold incidenceInput
    rw [List.ofFn_add]
    congr 1 <;> congr 1 <;> funext i <;> symm <;>
      first | exact Fin.addCases_left i | exact Fin.addCases_right i
  refine ⟨C,legal,size.trans_le lim,first,?_,?_⟩
  · intro p l inc
    rw [positiveRow]
    apply evalRow (true,incidenceInput {p} {l}) _ (len _ _)
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨p, by simp, List.mem_map.mpr ?_⟩
    have member : p+l ∈ ([0,1,3,9] : List (Fin 13)) := by
      simpa [D] using inc
    exact ⟨p+l, member, by simp [add_sub_cancel_left]⟩
  · intro s small
    have subset : s ∈ subsets := by
      let ls := (List.finRange 13).filter fun i => decide (i ∈ s)
      have eq : ls.toFinset = s := by
        ext i
        simp [ls]
      have nd : ls.Nodup := (List.nodup_finRange 13).filter _
      have size : ls.length = s.card := by rw [← eq, List.toFinset_card_of_nodup nd]
      exact List.mem_flatMap.mpr ⟨ls.length, List.mem_range.mpr (by omega),
        List.mem_map.mpr ⟨ls, List.mem_sublistsLen_self List.filter_sublist, eq⟩⟩
    have mem (row : List Bool)
        (m : (false,row) ∈ [(false,incidenceInput s (disj s)),(false,incidenceInput (disj s) s)]) :
        (false,row) ∈ rows := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨s, subset, m⟩
    have l := evalRow (false,incidenceInput s (disj s)) (mem _ (by simp)) (len _ _)
    have r := evalRow (false,incidenceInput (disj s) s) (mem _ (by simp)) (len _ _)
    change C.eval (incidenceInput s (disj s)) = false at l
    change C.eval (incidenceInput (disj s) s) = false at r
    rw [negRow] at l r
    have point (i : Fin 13) : decide (i ∈ disj s) = decide (∀ p ∈ s, p+i ∉ D) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, disj, Finset.mem_filter, Finset.mem_univ, true_and]
    have fn : (fun i : Fin 13 => decide (i ∈ disj s)) =
        (fun i : Fin 13 => decide (∀ p ∈ s, p+i ∉ D)) := funext point
    have rev : (fun i : Fin 13 => decide (i ∈ disj s)) =
        (fun i : Fin 13 => decide (∀ p ∈ s, i+p ∉ D)) := by
      rw [fn]
      funext i
      simp only [add_comm i]
    rw [fn] at l
    rw [rev] at r
    exact ⟨l,r⟩
