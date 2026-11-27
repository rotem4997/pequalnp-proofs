import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- A gate-by-gate simulation lets the checked bounds L_meta_2862 and
-- L_meta_5351, with normalization L_meta_4342, cover every order below 350.
-- For the remaining orders the first exceptional gate is a strict intersection
-- with at least three points. Every wire accepting two point singletons is
-- false on at most one maximal single-line negative input.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_4289_350
    (normalize : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x4 : Fin x1) => Bool.false) = Bool.false → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2)
    (smallOrder : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x1 < (200 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size)
    (linear : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x11 x12 : Finset (Fin x2)), x12.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x11 x12 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x11 x12) = Bool.false) →
      (349 : ℕ) * x2 ≤ (100 : ℕ) * x4.size)
    (largeOrder : ∀ (q N : Nat) (S : Fin N → Finset (Fin N)) (C : Circuit),
      350 ≤ q → N = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      Monotone2 C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      let m := N+N
      let P := fun w => {p : Fin N | (C.wires (List.ofFn (fun i : Fin N => decide (i=p)) ++ List.ofFn (fun _ : Fin N => false))).getD w false = true}
      (∀ w < m+C.size, 2 ≤ (P w).ncard →
        {l : Fin N | (C.wires (incidenceInput (S l)ᶜ {l})).getD w false = false}.Subsingleton) →
      (∃ g < C.size, ∃ a < m+g, ∃ b < m+g,
        C.gates[g]? = some ⟨GateOp.and,[a,b]⟩ ∧
        3 ≤ (P (m+g)).ncard ∧ P (m+g) ⊂ P a ∧ P (m+g) ⊂ P b ∧
        (¬ ∃ i < m+g, ∃ j < m+g, P (m+g) = P i ∪ P j) ∧
        ∀ k < g, 2 ≤ (P (m+k)).ncard → ∃ i < m+k, ∃ j < m+k, P (m+k) = P i ∪ P j) →
      N*q ≤ 100*C.size)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Fin x2) (x22 : Fin x2), x21 ≠ x22 ∧ x21 ∈ x19 Bool.true (x12 + x20) ∧ x22 ∈ x19 Bool.true (x12 + x20) ∧ ¬∃ x23 < x12 + x20, ∃ x24 < x12 + x20, x19 Bool.true (x12 + x20) = x19 Bool.true x23 ∪ x19 Bool.true x24) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI qbig order degree unique s o W
  dsimp only
  intro ho raw gates pos neg exceptional
  let m := N+N
  let one := fun p j : Fin N => decide (j=p)
  let S := fun l : Fin N => Finset.univ.filter (fun p => I p l)
  have deg (l) : (S l).card = q+1 := by simpa [S,Fintype.card_subtype] using degree l
  have meet (p r : Fin N) (h : p ≠ r) : ∃! l, p ∈ S l ∧ r ∈ S l := by
    simpa [S] using unique p r h
  have each (j : Fin s) : ∃ a b : Nat, max a b < m+j ∧
      W (m+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b] := gates j j.isLt
  choose a b prior law using each
  let G := fun j : Fin s =>
    if W (m+j) = W (a j) ∪ W (b j) then (⟨.or,[a j,b j]⟩ : Gate)
    else if W (m+j) = W (a j) then ⟨.or,[a j]⟩
    else if W (m+j) = ∅ then ⟨.or,[]⟩ else ⟨.and,[a j,b j]⟩
  have shape (j : Fin s) :
      (G j = ⟨.or,[a j,b j]⟩ ∧ W (m+j) = W (a j) ∪ W (b j)) ∨
      (G j = ⟨.or,[a j]⟩ ∧ W (m+j) = W (a j)) ∨
      (G j = ⟨.or,[]⟩ ∧ W (m+j) = ∅) ∨
      (G j = ⟨.and,[a j,b j]⟩ ∧ W (m+j) = W (a j) ∩ W (b j)) := by
    have h := law j
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    by_cases u : W (m+j) = W (a j) ∪ W (b j)
    · exact Or.inl ⟨by simp [G,u],u⟩
    by_cases c : W (m+j) = W (a j)
    · exact Or.inr (Or.inl ⟨by simp only [G,ite_eq_right u,ite_eq_left c],c⟩)
    by_cases z : W (m+j) = ∅
    · exact Or.inr (Or.inr (Or.inl ⟨by simp only [G,ite_eq_right u,ite_eq_right c,ite_eq_left z],z⟩))
    exact Or.inr (Or.inr (Or.inr ⟨by simp only [G,ite_eq_right u,ite_eq_right c,ite_eq_right z],((h.resolve_left u).resolve_left c).resolve_left z⟩))
  let gate := fun j : Nat => if h : j < s then G ⟨j,h⟩ else ⟨GateOp.or,[]⟩
  let C : Circuit := ⟨(List.range s).map gate,o⟩
  have size : C.size = s := by change ((List.range s).map gate).length = s; simp
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    have lt := List.mem_range.mp hj
    rw [show gate j = G ⟨j,lt⟩ from dite_eq_left lt]
    rcases shape ⟨j,lt⟩ with ⟨e,_⟩ | ⟨e,_⟩ | ⟨e,_⟩ | ⟨e,_⟩ <;> rw [e] <;> simp
  have evalAnd (v : List Bool) : GateOp.and.eval v = v.all id := rfl
  have evalOr (v : List Bool) : GateOp.or.eval v = v.any id := rfl
  have inputEq (X Y : Finset (Fin N)) : incidenceInput X Y =
      List.ofFn (fun p => decide (p ∈ X)) ++ List.ofFn (fun l => decide (l ∈ Y)) := rfl
  -- The first k gates implement exactly the first m+k set-valued wires.
  have runs (x y : Fin N → Bool) (w) (hw : w < m+s) :
      (C.wires (List.ofFn x ++ List.ofFn y)).getD w false = true ↔ (x,y) ∈ W w := by
    let step := fun (v : List Bool) (g : Gate) => v ++ [g.op.eval (g.inputs.map (fun j => v.getD j false))]
    let run := fun k => ((List.range k).map gate).foldl step (List.ofFn x ++ List.ofFn y)
    have inv (k) (bound : k ≤ s) : (run k).length = m+k ∧
        ∀ u < m+k, (run k).getD u false = true ↔ (x,y) ∈ W u := by
      induction k with
      | zero =>
        constructor
        · simp [run,m]
        intro u hu
        by_cases left : u < N
        · let p : Fin N := ⟨u,left⟩
          rw [show W u = _ from (raw p).1]
          change (List.ofFn x ++ List.ofFn y).getD u false = true ↔ x p = true
          rw [List.getD_append _ _ _ _ (by simpa using left),List.getD_eq_getElem _ _ (by simpa using left)]
          simp [p]
        · let l : Fin N := ⟨u-N,by dsimp [m] at hu; omega⟩
          have eu : u = N+l.val := by dsimp [l]; omega
          rw [eu,(raw l).2]
          change (List.ofFn x ++ List.ofFn y).getD (N+l.val) false = true ↔ y l = true
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp only [List.length_ofFn,Nat.add_sub_cancel_left]
          rw [List.getD_eq_getElem _ _ (by simpa using l.isLt)]
          simp
      | succ k ih =>
        obtain ⟨len,earlier⟩ := ih (by omega)
        let j : Fin s := ⟨k,by omega⟩
        have step_run : run (k+1) = step (run k) (G j) := by
          simp [run,List.range_succ,gate,j.isLt,j]
        constructor
        · rw [step_run]; simp [step,len,Nat.add_assoc]
        intro u hu
        by_cases prev : u < m+k
        · rw [step_run]
          change ((run k ++ [_]).getD u false = true) ↔ _
          rw [List.getD_append _ _ _ _ (len ▸ prev)]
          exact earlier u prev
        have eq : u=m+k := by omega
        subst u
        rw [step_run]
        change ((run k ++ [_]).getD (m+k) false = true) ↔ _
        rw [List.getD_append_right _ _ _ _ len.le,len,Nat.sub_self]
        have ha := earlier (a j) (lt_of_le_of_lt (le_max_left _ _) (prior j))
        have hb := earlier (b j) (lt_of_le_of_lt (le_max_right _ _) (prior j))
        change ((G j).op.eval ((G j).inputs.map fun t => (run k).getD t false)) = true ↔ (x,y) ∈ W (m+j)
        rcases shape j with ⟨op,sem⟩ | ⟨op,sem⟩ | ⟨op,sem⟩ | ⟨op,sem⟩ <;>
          rw [op,sem] <;> simp [evalAnd,evalOr,← List.getD_eq_getElem?_getD,ha,hb]
    exact (inv s le_rfl).2 w hw
  let below (x y : (Fin N → Bool) × (Fin N → Bool)) :=
    (∀ p, x.1 p = true → y.1 p = true) ∧ (∀ l, x.2 l = true → y.2 l = true)
  have mon (w) (hw : w < m+s) : ∀ x y, below x y → x ∈ W w → y ∈ W w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x y le hx
      by_cases hp : w < N
      · let p : Fin N := ⟨w,hp⟩
        rw [show W w = _ from (raw p).1] at hx ⊢
        exact le.1 p hx
      by_cases hl : w < m
      · let l : Fin N := ⟨w-N,by dsimp [m] at hl; omega⟩
        have e : w=N+l.val := by dsimp [l]; omega
        rw [e,(raw l).2] at hx ⊢
        exact le.2 l hx
      let j : Fin s := ⟨w-m,by omega⟩
      have e : m+j.val=w := by dsimp [j]; omega
      have h := prior j
      rw [e] at h
      have al := lt_of_le_of_lt (le_max_left _ _) h
      have bl := lt_of_le_of_lt (le_max_right _ _) h
      have A := ih _ al (by omega) x y le
      have B := ih _ bl (by omega) x y le
      rw [← e] at hx ⊢
      rcases shape j with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ <;> rw [h] at hx ⊢
      · exact hx.imp A B
      · exact A hx
      · exact hx
      · exact ⟨A hx.1,B hx.2⟩
  -- Positivity on flags and monotonicity transfer the promise to ordinary circuit inputs.
  have right : RightOnIncidentPairs S C := by
    intro l p hp
    change (C.wires (incidenceInput {p} {l})).getD o false = true
    have hit := (runs (one p) (one l) o ho).2 (pos p l (Finset.mem_filter.mp hp).2)
    simpa only [inputEq,Finset.mem_singleton,one] using hit
  have clean (X Y : Finset (Fin N)) (card : Y.card ≤ q) (off : IsFalseInput S X Y) :
      C.eval (incidenceInput X Y) = false := by
    let x := fun p => decide (p ∈ X)
    let y := fun l => decide (l ∈ Y)
    let z := fun p => decide (¬∃ l, I p l ∧ y l = true)
    have sizeY : Fintype.card {l // y l = true} ≤ q := by simpa [y,Fintype.card_subtype] using card
    have down : below (x,y) (z,y) := by
      refine ⟨?_,fun _ h => h⟩
      intro p hp
      apply decide_eq_true
      rintro ⟨l,inc,hl⟩
      have hy : l ∈ Y := of_decide_eq_true hl
      have hx : p ∈ X := of_decide_eq_true hp
      exact Finset.disjoint_left.mp (off l hy) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩) hx
    have bad := neg y sizeY
    cases e : C.eval (incidenceInput X Y) with
    | false => rfl
    | true => exact False.elim (bad (mon o ho _ _ down ((runs x y o ho).1 e)))
  have anyClean (z : Fin (N+N) → Bool) (card : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q)
      (off : ¬∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
      circuitFun (N+N) C z = false := by
    let X := Finset.univ.filter fun p : Fin N => z (Fin.castAdd N p) = true
    let Y := Finset.univ.filter fun l : Fin N => z (Fin.natAdd N l) = true
    have hxy : IsFalseInput S X Y := by
      intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hx
      exact off ⟨p,l,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hl).2⟩
    have he : incidenceInput X Y = List.ofFn z := by
      rw [List.ofFn_add (n := N) (m := N)]
      change List.ofFn (fun p => decide (p ∈ X)) ++ List.ofFn (fun l => decide (l ∈ Y)) =
        List.ofFn (fun i => z (Fin.castAdd N i)) ++ List.ofFn (fun i => z (Fin.natAdd N i))
      simp [X,Y]
    change C.eval (List.ofFn z) = false
    rw [← he]
    exact clean X Y (by simpa [Y,Fintype.card_subtype] using card) hxy
  by_cases h200 : q < 200
  · rw [← size]
    apply smallOrder q N I C qbig h200 order degree unique mono _ anyClean
    intro p l inc
    have ok := right l p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩)
    change C.eval (List.ofFn _) = true
    rw [List.ofFn_add (n := N) (m := N)]
    have left (i : Fin N) : (Fin.castAdd N i = Fin.castAdd N p ∨ Fin.castAdd N i = Fin.natAdd N l) ↔ i = p := by
      simp only [Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]; omega
    have right' (i : Fin N) : (Fin.natAdd N i = Fin.castAdd N p ∨ Fin.natAdd N i = Fin.natAdd N l) ↔ i = l := by
      simp only [Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]; omega
    change C.eval (List.ofFn (fun i : Fin N => decide (Fin.castAdd N i = Fin.castAdd N p ∨ Fin.castAdd N i = Fin.natAdd N l)) ++
      List.ofFn (fun i : Fin N => decide (Fin.natAdd N i = Fin.castAdd N p ∨ Fin.natAdd N i = Fin.natAdd N l))) = true
    simpa only [left,right',inputEq,Finset.mem_singleton] using ok
  by_cases h350 : q < 350
  · have zero : circuitFun (N+N) C (fun _ => false) = false :=
      anyClean _ (by simp) (by simp)
    obtain ⟨D,valid,cost,equiv⟩ := normalize (N+N) C mono zero
    have transfer (X Y : Finset (Fin N)) : D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y) := by
      let z := Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ Y))
      have he : List.ofFn z = incidenceInput X Y := by
        rw [List.ofFn_add (n := N) (m := N)]
        change List.ofFn (fun i => z (Fin.castAdd N i)) ++ List.ofFn (fun i => z (Fin.natAdd N i)) = _
        simp only [z,Fin.append_left,Fin.append_right,inputEq]
      have eq := congrFun equiv z
      change D.eval (List.ofFn z) = C.eval (List.ofFn z) at eq
      rwa [he] at eq
    have bound := linear q N S D (by omega) order deg meet valid
      (fun l p hp => (transfer {p} {l}).trans (right l p hp))
      (fun X Y hc hf => (transfer X Y).trans (clean X Y hc hf))
    have a := Nat.mul_le_mul_left N (show q ≤ 349 by omega)
    have b := Nat.mul_le_mul_left 100 cost
    rw [Nat.mul_comm N 349] at a
    omega
  let P := fun w => {p : Fin N | (C.wires (List.ofFn (fun i : Fin N => decide (i=p)) ++ List.ofFn (fun _ : Fin N => false))).getD w false = true}
  have axis (w) (hw : w < m+s) (p : Fin N) : p ∈ P w ↔ (one p,fun _ => false) ∈ W w := by
    simpa only [P,Set.mem_ofPred_eq,one] using runs (one p) (fun _ => false) w hw
  -- A wire which accepts two point singletons can be false on at most one
  -- maximal single-line negative, since two distinct points determine a line.
  have uniqueLine (w) (hw : w < m+C.size) (many : 2 ≤ (P w).ncard) :
      {l : Fin N | (C.wires (incidenceInput (S l)ᶜ {l})).getD w false = false}.Subsingleton := by
    rw [size] at hw
    have contains (l : Fin N) (miss : (C.wires (incidenceInput (S l)ᶜ {l})).getD w false = false) :
        ∀ p ∈ P w, p ∈ S l := by
      intro p hp
      by_contra outside
      let x := fun i => decide (i ∈ (S l)ᶜ)
      have le : below (one p,fun _ => false) (x,one l) := by
        refine ⟨?_,by simp⟩
        intro i h
        obtain rfl : i=p := of_decide_eq_true h
        simpa [x] using outside
      have hit := (runs x (one l) w hw).2 (mon w hw _ _ le ((axis w hw p).1 hp))
      rw [inputEq] at miss
      simp only [Finset.mem_singleton] at miss
      change (C.wires (List.ofFn x ++ List.ofFn (one l))).getD w false = false at miss
      exact Bool.noConfusion (miss.symm.trans hit)
    obtain ⟨p,hp,r,hr,ne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp (show 1 < (P w).ncard by omega)
    obtain ⟨l,_,uniqueL⟩ := meet p r ne
    intro a ha b hb
    exact (uniqueL a ⟨contains a ha p hp,contains a ha r hr⟩).trans
      (uniqueL b ⟨contains b hb p hp,contains b hb r hr⟩).symm
  have rawP (p : Fin N) : P p.val = {p} := by
    ext r
    rw [axis _ (by dsimp [m]; omega), (raw p).1]
    change decide (p = r) = true ↔ r = p
    rw [decide_eq_true_eq,eq_comm]
  let B := fun j => 2 ≤ (P (m+j)).ncard ∧ ¬∃ i < m+j, ∃ k < m+j, P (m+j) = P i ∪ P k
  -- Choose the first gate whose point support has no earlier binary union representation.
  have existsBad : ∃ j, j < s ∧ B j := by
    obtain ⟨j,hj,p,r,ne,hp,hr,novel⟩ := exceptional
    have eq (w) (h : w < m+s) : P w = {v | (one v,fun _ => false) ∈ W w} := by ext v; exact axis w h v
    refine ⟨j,hj,?_,?_⟩
    · have pp := (axis (m+j) (by omega) p).2 hp
      have rr := (axis (m+j) (by omega) r).2 hr
      by_contra! small
      exact ne (((Set.ncard_le_one (Set.toFinite _)).mp (by omega : (P (m+j)).ncard ≤ 1)) p pp r rr)
    · rintro ⟨a,ha,b,hb,split⟩
      exact novel ⟨a,ha,b,hb,by
        change {v | (one v,fun _ => false) ∈ W (m+j)} = {v | (one v,fun _ => false) ∈ W a} ∪ {v | (one v,fun _ => false) ∈ W b}
        rwa [eq _ (by omega),eq a (by omega),eq b (by omega)] at split⟩
  let k := Nat.find existsBad
  have kb := Nat.find_spec existsBad
  change k < s ∧ B k at kb
  let j : Fin s := ⟨k,kb.1⟩
  obtain ⟨card,novel⟩ := kb.2
  have al : a j < m+k := lt_of_le_of_lt (le_max_left _ _) (prior j)
  have bl : b j < m+k := lt_of_le_of_lt (le_max_right _ _) (prior j)
  have zlt : m+k < m+s := by omega
  have uncopy (u) (hu : u < m+k) : P (m+k) ≠ P u := fun e => novel ⟨u,hu,u,hu,by simpa using e⟩
  have three : 3 ≤ (P (m+k)).ncard := by
    by_contra! few
    obtain ⟨p,r,_,e⟩ := Set.ncard_eq_two.mp (show (P (m+k)).ncard=2 by omega)
    exact novel ⟨p.val,by dsimp [m];omega,r.val,by dsimp [m];omega,by rw [rawP,rawP,e]; ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_union]⟩
  have oldest (b) (hb : b < k) (card : 2 ≤ (P (m+b)).ncard) :
      ∃ u < m+b, ∃ v < m+b, P (m+b) = P u ∪ P v := by
    by_contra hn
    exact Nat.find_min existsBad hb ⟨by omega,card,hn⟩
  rw [← size]
  apply largeOrder q N S C (by omega) order deg meet mono right clean uniqueLine
  rcases shape j with ⟨_,sem⟩ | ⟨_,sem⟩ | ⟨_,sem⟩ | ⟨op,sem⟩
  · exfalso
    apply novel ⟨a j,al,b j,bl,?_⟩
    ext p
    rw [axis _ zlt,show W (m+k) = _ from sem,Set.mem_union,Set.mem_union,axis _ (by omega),axis _ (by omega)]
  · exfalso
    apply uncopy _ al
    ext p
    rw [axis _ zlt,show W (m+k) = _ from sem,axis _ (by omega)]
  · exfalso
    have e : P (m+k) = ∅ := by ext p; rw [axis _ zlt,show W (m+k) = _ from sem]; rfl
    simp [e] at three
  · have eq : P (m+k) = P (a j) ∩ P (b j) := by
      ext p
      rw [axis _ zlt,show W (m+k) = _ from sem,Set.mem_inter_iff,Set.mem_inter_iff,axis _ (by omega),axis _ (by omega)]
    refine ⟨k,by omega,a j,al,b j,bl,?_,three,?_,?_,novel,oldest⟩
    · simp [C,gate,kb.1,show G ⟨k,kb.1⟩ = _ from op]
    · exact lt_of_le_of_ne (show P (m+k) ⊆ P (a j) by rw [eq]; exact Set.inter_subset_left) (uncopy _ al)
    · exact lt_of_le_of_ne (show P (m+k) ⊆ P (b j) by rw [eq]; exact Set.inter_subset_right) (uncopy _ bl)
