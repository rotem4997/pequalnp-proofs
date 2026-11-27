import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7139_418
  (tree : let S := singerLines3
    let input (X Y : Finset (Fin 13)) := incidenceInput X Y
    let span (q : List (BitVec 4)) := q.foldr (fun a (s : Finset (BitVec 4)) =>
      s ∪ s.image (fun b => a ^^^ b)) {0}
    let missingBit (i : Fin 4) := ([14,13,11,7] : List (BitVec 4)).getD i.val 0
    ∀ C : Circuit, Monotone2 C → (∀ j < C.size, (readers 26 C j).card ≤ 1) →
      RightOnIncidentPairs S C → C.eval (input Finset.univ ∅) = false →
      C.eval (input ∅ Finset.univ) = false →
      (∀ l p, p ∈ S l → C.eval (input ((S l).erase p)
        (Finset.univ.filter (fun m => m ≠ l ∧ p ∈ S m))) = false) →
      ∃ rows : Fin 26 → List (BitVec 4), (∑ v, (rows v).length) ≤ C.size + 1 ∧
        (∀ v, 15 ∈ span (rows v)) ∧ ∀ p : Fin 13, ∀ i : Fin 4,
        let d := ([0,1,3,9] : List (Fin 13)).getD i.val 0
        missingBit i ∈ span (rows (Fin.castAdd 13 p)) ∨
        missingBit i ∈ span (rows (Fin.natAdd 13 (p-d))))
  (sharing : let S := singerLines3
    ∀ C : Circuit, Monotone2 C → 38 ≤ C.size → (∃ j < C.size, 2 ≤ (readers 26 C j).card) →
      RightOnIncidentPairs S C → (∀ X Y, IsFalseInput S X Y →
            ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l) →
            C.eval (incidenceInput X Y) = false) → 64 ≤ C.size)
  : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     (37 : ℕ) ≤ x3.size →       x3.size ≤ (62 : ℕ) →         ∀ (x7 x8 : Fin ((26 : ℕ) + x3.size)),           x7 ≠ x8 →             (∀ (x10 x11 : Finset (Fin (13 : ℕ))),                 ((∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x10, x2 x13 x12) ∨ ∃ (x12 : Fin (13 : ℕ)), ∀ x13 ∈ x11, x2 x12 x13) →                   have x13 : Fin (26 : ℕ) → Bool := fun (x13 : Fin (26 : ℕ)) => Decidable.decide ((∃ x14 ∈ x10, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ x14 ∈ x11, x13 = Fin.natAdd (13 : ℕ) x14);                   have x14 : List Bool := x3.wires (List.ofFn x13);                   (x14.getD (↑x7) Bool.false || x14.getD (↑x8) Bool.false) = Decidable.decide (∃ x15 ∈ x10, ∃ x16 ∈ x11, x2 x15 x16)) →               False) := by
  dsimp only at tree sharing ⊢
  have append (n : ℕ) (C : Circuit) (mono : Monotone2 C) (a b : Fin (n+C.size)) :
      ∃ D : Circuit, Monotone2 D ∧ D.size=C.size+1 ∧
        ∀ w : List Bool, w.length=n → D.eval w = ((C.wires w).getD a.val false || (C.wires w).getD b.val false) := by
    let g : Gate := ⟨.or,[a.val,b.val]⟩
    let D : Circuit := ⟨C.gates++[g],n+C.size⟩
    have md : Monotone2 D := by
      intro gate h
      change gate ∈ C.gates ++ [g] at h
      rcases List.mem_append.mp h with old | new
      · exact mono gate old
      · rw [List.mem_singleton] at new
        subst gate
        simp [g]
    refine ⟨D,md,by change (C.gates++[g]).length=C.gates.length+1; simp,?_⟩
    intro w hw
    let step (x : List Bool) (gate : Gate) := x ++ [gate.op.eval (gate.inputs.map fun i => x.getD i false)]
    have len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length+gs.length := by
      induction gs generalizing x with
      | nil => simp
      | cons h t ih => rw [List.foldl_cons, ih]; simp [step]; omega
    have nch : (C.wires w).length = n+C.size := (len _ _).trans (by change w.length+C.gates.length=n+C.gates.length; rw [hw])
    change ((C.gates++[g]).foldl step w).getD (n+C.size) false = _
    rw [List.foldl_append]
    change ((C.wires w) ++ [GateOp.or.eval ([(a.val),(b.val)].map fun i => (C.wires w).getD i false)]).getD (n+C.size) false = _
    have last (z : Bool) : ((C.wires w)++[z]).getD (n+C.size) false = z := by
      have e := congrArg (fun k => ((C.wires w)++[z]).getD k false) nch.symm
      exact e.trans (by simp [List.getD_eq_getElem?_getD])
    rw [last]
    change (_ || (_ || false)) = _
    simp
  intro C hm enough hsize a b _ query
  obtain ⟨D, md, ds, deval⟩ := append 26 C hm a b
  let Inc (p l : Fin 13) := ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l + d
  have geom : ∀ p l, p ∈ singerLines3 l ↔ Inc p l := by
    intro p
    fin_cases p <;> decide +kernel
  let row (X Y : Finset (Fin 13)) (u : Fin 26) :=
    decide ((∃ p ∈ X, u = Fin.castAdd 13 p) ∨ ∃ l ∈ Y, u = Fin.natAdd 13 l)
  have eq (X Y : Finset (Fin 13)) : incidenceInput X Y = List.ofFn (row X Y) := by
    change List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) = List.ofFn (row X Y)
    rw [← List.ofFn_fin_append]
    congr 1
    funext u
    refine Fin.addCases (fun p => ?_) (fun l => ?_) u
    · rw [Fin.append_left]
      apply decide_eq_decide.mpr
      constructor
      · intro hp
        exact Or.inl ⟨p,hp,rfl⟩
      · rintro (⟨q,hq,e⟩ | ⟨l,_,e⟩)
        · have pq : p = q := Fin.ext (congrArg (fun x : Fin 26 => x.val) e)
          exact pq.symm ▸ hq
        · have clash := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at clash
          omega
    · rw [Fin.append_right]
      apply decide_eq_decide.mpr
      constructor
      · intro hl
        exact Or.inr ⟨l,hl,rfl⟩
      · rintro (⟨p,_,e⟩ | ⟨q,hq,e⟩)
        · have clash := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at clash
          omega
        · have lq : l = q := by
            apply Fin.ext
            have z := congrArg Fin.val e
            simp only [Fin.val_natAdd] at z
            omega
          exact lq.symm ▸ hq
  have fit X Y
      (h : (∃ l, ∀ p ∈ X, Inc p l) ∨ ∃ p, ∀ l ∈ Y, Inc p l) :
      D.eval (incidenceInput X Y) = decide (∃ p ∈ X, ∃ l ∈ Y, Inc p l) := by
    rw [eq]
    exact (deval _ (by simp)).trans (query X Y h)
  let S := singerLines3
  have good : RightOnIncidentPairs S D ∧ ∀ X Y, IsFalseInput S X Y ∧
      ((∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l) → D.eval (incidenceInput X Y) = false := by
    constructor
    · intro l p hp
      have inc := (geom p l).mp hp
      rw [fit _ _ (Or.inl ⟨l, fun q hq => (Finset.mem_singleton.mp hq).symm ▸ inc⟩)]
      exact decide_eq_true ⟨p, by simp, l, by simp, inc⟩
    · rintro X Y ⟨off, support⟩
      have tested : (∃ l, ∀ p ∈ X, Inc p l) ∨ ∃ p, ∀ l ∈ Y, Inc p l := by
        rcases support with ⟨l, hl⟩ | ⟨p, hp⟩
        · exact Or.inl ⟨l, fun p h => (geom p l).mp (hl h)⟩
        · exact Or.inr ⟨p, fun l h => (geom p l).mp (hp l h)⟩
      rw [fit X Y tested]
      apply decide_eq_false
      rintro ⟨p, hp, l, hl, inc⟩
      exact (Finset.disjoint_left.mp (off l hl)) ((geom p l).mpr inc) hp
  by_cases reused : ∃ j < D.size, 2 ≤ (readers 26 D j).card
  · have large := sharing D md (by omega) reused good.1 (fun X Y off tested => good.2 X Y ⟨off,tested⟩)
    omega
  have uniqueReader : ∀ j < D.size, (readers 26 D j).card ≤ 1 := by
    intro j hj
    by_contra! bad
    exact reused ⟨j,hj,bad⟩
  have pshore := good.2 Finset.univ ∅ ⟨by intro l hl; simp at hl,Or.inr ⟨0,by simp⟩⟩
  have lshore := good.2 ∅ Finset.univ ⟨by intro l _; exact Finset.disjoint_empty_right _,Or.inl ⟨0,by simp⟩⟩
  have central : ∀ l p, p ∈ singerLines3 l →
      IsFalseInput singerLines3 ((singerLines3 l).erase p) (Finset.univ.filter (fun m => m ≠ l ∧ p ∈ singerLines3 m)) := by
    decide +kernel
  obtain ⟨rows,budget,fullStars,flags⟩ := tree D md uniqueReader good.1 pshore lshore (by
    intro l p hp
    exact good.2 _ _ ⟨central l p hp, Or.inl ⟨l, Finset.erase_subset _ _⟩⟩)
  let span (q : List (BitVec 4)) := q.foldr (fun a (s : Finset (BitVec 4)) =>
        s ∪ s.image (fun b => a ^^^ b)) {0}
  let missingBit (i : Fin 4) := ([14,13,11,7] : List (BitVec 4)).getD i.val 0
  have cycleBudget (valid : Fin 26 → Fin 4 → Prop) [∀ v, DecidablePred (valid v)]
      (shift : Fin 4 → Fin 13) (ownership : ∀ p : Fin 13, ∀ i : Fin 4,
         valid (Fin.castAdd 13 p) i ∨ valid (Fin.natAdd 13 (p - shift i)) i) :
      52 ≤ ∑ v : Fin 26, (Finset.univ.filter (valid v)).card := by
    let value (v : Fin 26) (i : Fin 4) := if valid v i then 1 else 0
    have fixed (i : Fin 4) : 13 ≤ ∑ v : Fin 26, value v i := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13)))
        (f := fun _ => 1) (g := fun p => value (Fin.castAdd 13 p) i + value (Fin.natAdd 13 (p-shift i)) i)
        (fun p _ => by rcases ownership p i with h | h <;> simp only [value,ite_eq_left h] <;> omega)
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_one,Finset.sum_add_distrib] at h
      have perm : (∑ p : Fin 13, value (Fin.natAdd 13 (p-shift i)) i) =
          ∑ l : Fin 13, value (Fin.natAdd 13 l) i :=
        Fintype.sum_equiv (Equiv.subRight (shift i)) _ _ (fun _ => rfl)
      rw [perm] at h
      rw [Fin.sum_univ_add (a := 13) (b := 13)]
      exact h
    have all := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ => fixed i)
    rw [Finset.sum_comm] at all
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at all
    simpa only [Finset.card_filter,value] using all
  let valid (v : Fin 26) (i : Fin 4) := missingBit i ∈ span (rows v)
  let lost (v : Fin 26) := Finset.univ.filter (valid v)
  have paid : 52 ≤ ∑ v : Fin 26, (lost v).card :=
    cycleBudget valid (fun i => ([0,1,3,9] : List (Fin 13)).getD i.val 0) flags
  let cap (R : List (BitVec 4)) := (Finset.univ.filter (fun i => missingBit i ∈ span R)).card
  have rank (R : List (BitVec 4)) (T : Finset (Fin 4))
      (full : 15 ∈ span R) (loss : ∀ i ∈ T, missingBit i ∈ span R) :
      4+3*T.card ≤ 4*R.length := by
    have bounded : T.card ≤ cap R := Finset.card_le_card (fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,loss i hi⟩)
    have total : T.card ≤ 4 := by simpa using Finset.card_le_univ T
    rcases R with _ | ⟨a,R⟩
    · simp [span] at full
    rcases R with _ | ⟨b,R⟩
    · have one : ∀ a : BitVec 4, 15 ∈ span [a] → cap [a] = 0 := by
        dsimp only [cap,span,missingBit]; decide +kernel
      have := one a full
      simp only [List.length_cons,List.length_nil] at *
      omega
    rcases R with _ | ⟨c,R⟩
    · have two : ∀ a b : BitVec 4, 15 ∈ span [a,b] → cap [a,b] ≤ 1 := by
        dsimp only [cap,span,missingBit]; decide +kernel
      have := two a b full
      simp only [List.length_cons,List.length_nil] at *
      omega
    rcases R with _ | ⟨z,R⟩
    · have three : ∀ a b c : BitVec 4, 15 ∈ span [a,b,c] → cap [a,b,c] ≤ 2 := by
        dsimp only [cap,span,missingBit]; decide +kernel
      have := three a b c full
      simp only [List.length_cons,List.length_nil] at *
      omega
    · simp only [List.length_cons]; omega
  have joined := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 26)))
    (fun v _ => rank (rows v) (lost v) (fullStars v) (fun i h => (Finset.mem_filter.mp h).2))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ←Finset.mul_sum] at joined
  omega
