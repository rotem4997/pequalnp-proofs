import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

set_option maxRecDepth 40000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_3402_415
    (aliases : let decode (m : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => m.testBit i.val)
      let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
      let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let input (T : Finset (Fin 9)) (x : Fin 9 → Bool) :=
        List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ T, x i = true)]
      ∀ k ∈ ([0, 1, 2, 4, 8, 16, 64, 17] : List ℕ), ∀ C : Circuit, Monotone2 C → C.size ≤ 13 →
        ∃ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288, 42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ), C.eval (input (decode k) (bits m)) ≠ edge (bits m))
    (distinct : let decode (m : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => m.testBit i.val)
      let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
      let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let input (T : Finset (Fin 9)) (x : Fin 9 → Bool) :=
        List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ T, x i = true)]
      ∀ k ∈ ([3, 5, 6, 9, 10, 12, 18, 20, 24, 34, 36, 65, 66, 68, 72, 80, 96, 132, 192, 260] : List ℕ), ∀ C : Circuit, Monotone2 C → C.size ≤ 13 →
        ∃ m ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288, 42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402] : List ℕ), C.eval (input (decode k) (bits m)) ≠ edge (bits m)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → (14 : ℕ) ≤ x1.size := by
  let decode (m : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i : Fin 9 => m.testBit i.val)
  let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
  let edge (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
    List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let input (T : Finset (Fin 9)) (x : Fin 9 → Bool) :=
    List.ofFn x ++ [x 0 || x 4, decide (∃ i ∈ T, x i = true)]
  let simple : List ℕ := [0, 1, 2, 4, 8, 16, 64, 17]
  let pairs : List ℕ := [3, 5, 6, 9, 10, 12, 18, 20, 24, 34, 36, 65, 66, 68, 72, 80, 96, 132, 192, 260]
  let representatives := simple ++ pairs
  let tests : List ℕ := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288, 42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
  intro C T fan card none computes
  by_contra! short
  have size : C.size ≤ 13 := by omega
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have noNot : C.gates.filter (fun g => decide (g.op = GateOp.not)) = [] := by
    have len : (C.gates.filter (fun g => decide (g.op = GateOp.not))).length = 0 := none
    exact List.length_eq_zero_iff.mp len
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨hop,arity⟩ := fan g hg
    refine ⟨?_,arity⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with eq | eq | eq
    · exact Or.inl eq
    · exact Or.inr eq
    · have member : g ∈ C.gates.filter (fun g => decide (g.op = GateOp.not)) :=
        List.mem_filter.mpr ⟨hg,decide_eq_true eq⟩
      rw [noNot] at member
      exact (List.not_mem_nil member).elim
  let flip (i : Fin 9) : Fin 9 := ([0,5,8,3,4,1,7,6,2] : List (Fin 9)).getD i.val 0
  let pack (T : Finset (Fin 9)) : ℕ :=
    ((List.finRange 9).filter fun i => decide (i ∈ T)).foldr (fun i k => 2 ^ i.val ||| k) 0
  have decodeBits (xs : List (Fin 9)) (i : Fin 9) :
      (xs.foldr (fun (j : Fin 9) k => 2 ^ j.val ||| k) 0).testBit i.val = decide (i ∈ xs) := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      simp only [List.foldr_cons, Nat.testBit_or, Nat.testBit_two_pow, ih]
      by_cases eq : i = j
      · subst j
        simp
      · have ne : j.val ≠ i.val := fun h => eq (Fin.ext h.symm)
        simp [eq,ne]
  have unpack (T : Finset (Fin 9)) : decode (pack T) = T := by
    ext i
    simp [decode, pack, decodeBits]
  have smallPack (T : Finset (Fin 9)) : pack T < 512 := by
    have go (xs : List (Fin 9)) : xs.foldr (fun (j : Fin 9) k => 2 ^ j.val ||| k) 0 < 512 := by
      induction xs with
      | nil => decide
      | cons i xs ih =>
        exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) i.isLt) ih
    exact go _
  have orbit : ∀ k : Fin 512, (decode k.val).card ≤ 2 →
      k.val ∈ representatives ∨ pack ((decode k.val).image flip) ∈ representatives := by
    decide +kernel
  let k : Fin 512 := ⟨pack T,smallPack T⟩
  have choice := orbit k (by change (decode (pack T)).card ≤ 2; rwa [unpack])
  change pack T ∈ representatives ∨ pack ((decode (pack T)).image flip) ∈ representatives at choice
  rw [unpack] at choice
  have refute (m : ℕ) (hm : m ∈ representatives) (D : Circuit) (hD : Monotone2 D)
      (bound : D.size ≤ 13) :
      ∃ a ∈ tests, D.eval (input (decode m) (bits a)) ≠ edge (bits a) := by
    rcases List.mem_append.mp hm with h | h
    · exact aliases m h D hD bound
    · exact distinct m h D hD bound
  rcases choice with hkeep | hreflect
  · obtain ⟨m,_,bad⟩ := refute (pack T) hkeep C mono size
    rw [unpack] at bad
    exact bad (computes (bits m))
  let move (i : ℕ) : ℕ := if h : i < 9 then (flip ⟨i,h⟩).val else i
  have flip0 : flip 0 = 0 := rfl
  have flip4 : flip 4 = 4 := rfl
  have preserve : ∀ x : Fin 9 → Bool, edge (x ∘ flip) = edge x := by decide +kernel
  have reflectBits (x : Fin 9 → Bool) :
      decide (∃ i ∈ T, (x ∘ flip) i = true) = decide (∃ i ∈ T.image flip, x i = true) := by
    apply Bool.decide_congr
    constructor
    · rintro ⟨i,hi,hx⟩
      exact ⟨flip i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,hx⟩
    · rintro ⟨j,hj,hx⟩
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i,hi,hx⟩
  have small (i : ℕ) (hi : i < 9) : move i < 9 := by
    rw [show move i = (flip ⟨i,hi⟩).val from dite_eq_left hi]
    exact (flip ⟨i,hi⟩).isLt
  have high (i : ℕ) (hi : 9 ≤ i) : move i = i := dite_eq_right (by omega)
  let relabel (g : Gate) : Gate := ⟨g.op,g.inputs.map move⟩
  let D : Circuit := ⟨C.gates.map relabel,move C.output⟩
  have monoD : Monotone2 D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(mono a ha).1,by simpa only [relabel,List.length_map] using (mono a ha).2⟩
  have sizeD : D.size ≤ 13 := by
    change (C.gates.map relabel).length ≤ 13
    rw [List.length_map]
    exact size
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  let sameWires (u v : List Bool) := u.length = v.length ∧ 9 ≤ u.length ∧
    ∀ i, u.getD i false = v.getD (move i) false
  have stable (u v : List Bool) (b : Bool) (h : sameWires u v) : sameWires (u++[b]) (v++[b]) := by
    obtain ⟨len,lower,same⟩ := h
    refine ⟨by simp [len],by simp; omega,fun i => ?_⟩
    by_cases raw : i < 9
    · rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by have := small i raw; omega)]
      exact same i
    · rw [high i (by omega)]
      by_cases inside : i < u.length
      · rw [List.getD_append _ _ _ _ inside, List.getD_append _ _ _ _ (by omega)]
        simpa only [high i (by omega)] using same i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]
  have run (gs : List Gate) (u v : List Bool) (h : sameWires u v) :
      sameWires (gs.foldl step u) ((gs.map relabel).foldl step v) := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      change sameWires (gs.foldl step (step u g)) ((gs.map relabel).foldl step (step v (relabel g)))
      apply ih
      have pins : g.inputs.map (fun i => u.getD i false) =
          (relabel g).inputs.map (fun i => v.getD i false) := by
        simp only [relabel,List.map_map]
        apply List.map_congr_left
        exact fun i _ => h.2.2 i
      change sameWires (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
        (v ++ [g.op.eval ((relabel g).inputs.map fun i => v.getD i false)])
      rw [← pins]
      exact stable _ _ _ h
  have base (x : Fin 9 → Bool) : sameWires (input T (x ∘ flip)) (input (T.image flip) x) := by
    refine ⟨by simp [input],by simp [input],fun i => ?_⟩
    by_cases raw : i < 9
    · have lookup (y : Fin 9 → Bool) (j : Fin 9) :
          (List.ofFn y).getD j.val false = y j := by
        rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
      change (List.ofFn (x ∘ flip) ++ _).getD i false =
        (List.ofFn x ++ _).getD (move i) false
      rw [List.getD_append _ _ _ _ (by simpa using raw),
        List.getD_append _ _ _ _ (by have := small i raw; simpa using this)]
      rw [show move i = (flip ⟨i,raw⟩).val from dite_eq_left raw]
      exact (lookup (x ∘ flip) ⟨i,raw⟩).trans (lookup x (flip ⟨i,raw⟩)).symm
    · rw [high i (by omega)]
      have firstEq : ((x ∘ flip) 0 || (x ∘ flip) 4) = (x 0 || x 4) := by
        simp only [Function.comp_apply,flip0,flip4]
      have e := reflectBits x
      change (List.ofFn (x ∘ flip) ++ [_,_]).getD i false =
        (List.ofFn x ++ [_,_]).getD i false
      rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt raw),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt raw),
        List.length_ofFn,List.length_ofFn,firstEq,e]
  obtain ⟨m,_,bad⟩ := refute (pack (T.image flip)) hreflect D monoD sizeD
  rw [unpack] at bad
  let x := bits m
  have agrees : C.eval (input T (x ∘ flip)) = D.eval (input (T.image flip) x) :=
    (run C.gates _ _ (base x)).2.2 C.output
  exact bad (agrees.symm.trans ((computes (x ∘ flip)).trans (preserve x)))
