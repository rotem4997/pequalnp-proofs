import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2766_606
    (andCase : let s : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661]
      let pool := 0 :: s
      let left := (16777215 :: pool.flatMap (fun a => pool.map (fun b => a &&& b)))
      ∀ t ∈ left, ∀ gs : List Gate, gs.length = 13 →
      (∀ g ∈ gs, g = ⟨.and,[]⟩ ∨ ∃ a b : Fin 25, g = ⟨.and,[a.val,b.val]⟩ ∨ g = ⟨.or,[a.val,b.val]⟩) →
      ¬ ∀ k : Fin 24, (Circuit.mk gs 23).eval
        ((s ++ [t]).map (fun z => z.getLsbD k.val)) =
        (4095 : BitVec 24).getLsbD k.val)
    (orCase : let s : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661]
      let pool := 0 :: s
      let left := (16777215 :: pool.flatMap (fun a => pool.map (fun b => a &&& b)))
      ∀ t ∈ ((pool.flatMap (fun a => pool.map (fun b => a ||| b))).filter (fun t => t ∉ left)), ∀ gs : List Gate, gs.length = 13 →
      (∀ g ∈ gs, g = ⟨.and,[]⟩ ∨ ∃ a b : Fin 25, g = ⟨.and,[a.val,b.val]⟩ ∨ g = ⟨.or,[a.val,b.val]⟩) →
      ¬ ∀ k : Fin 24, (Circuit.mk gs 23).eval
        ((s ++ [t]).map (fun z => z.getLsbD k.val)) =
        (4095 : BitVec 24).getLsbD k.val)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C form count good
  obtain ⟨len, out, head, shape⟩ := form
  let seed : List (BitVec 24) := [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661]
  let pool := 0 :: seed
  let left := (16777215 : BitVec 24) :: pool.flatMap (fun a => pool.map (fun b => a &&& b))
  let right := (pool.flatMap (fun a => pool.map (fun b => a ||| b))).filter (fun t => t ∉ left)
  let bit (k : Fin 24) (z : BitVec 24) := z.getLsbD k.val
  let masks : List ℕ := [3,6,12,24,17,33,66,132,264,160,320,288,42,50,69,104,116,138,201,208,261,276,385,402]
  let input (k : Fin 24) (i : Fin 9) := (masks.getD k.val 0).testBit i.val
  have seed_ok : ∀ k : Fin 24, seed.map (bit k) = List.ofFn (input k) ++ [input k 0 || input k 3] := by decide +kernel
  have target_ok : ∀ k : Fin 24, ((input k 0 && input k 1 || input k 1 && input k 2 ||
      input k 2 && input k 3 || input k 3 && input k 4 || input k 4 && input k 0 ||
      input k 0 && input k 5 || input k 1 && input k 6 || input k 2 && input k 7 ||
      input k 3 && input k 8 || input k 5 && input k 7 || input k 6 && input k 8 ||
      input k 8 && input k 5) = bit k 4095) := by decide +kernel
  have allowed (g : Gate) (hg : g ∈ C.gates) : g = ⟨.and,[]⟩ ∨ ∃ a b : Fin 25, g = ⟨.and,[a.val,b.val]⟩ ∨ g = ⟨.or,[a.val,b.val]⟩ := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have q := shape i hi
    dsimp only at q
    rcases q with h | ⟨a,_,h⟩ | ⟨a,b,ha,hb,_,h⟩
    · exact Or.inl h
    · have bad := List.countP_eq_zero.mp count _ (List.getElem_mem hi)
      rw [h] at bad
      exact (bad rfl).elim
    · exact Or.inr ⟨⟨a,by omega⟩,⟨b,by omega⟩,h⟩
  cases hh : C.gates with
  | nil => simp [hh] at len
  | cons h tail =>
    have hhead : h = ⟨.or,[0,3]⟩ := by simpa [hh] using head
    subst h
    cases tail with
    | nil => simp [hh] at len
    | cons g gs =>
      have slen : gs.length = 13 := by simpa [hh] using len
      have allg (p : Gate) (hp : p ∈ gs) : p = ⟨.and,[]⟩ ∨ ∃ a b : Fin 25, p = ⟨.and,[a.val,b.val]⟩ ∨ p = ⟨.or,[a.val,b.val]⟩ :=
        allowed p (by rw [hh]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
      have read (a : ℕ) (k : Fin 24) :
          (seed.map (bit k)).getD a false = bit k (seed.getD a 0) := by
        rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
        cases v : seed[a]? <;> simp [bit]
      have choose : ∃ t : BitVec 24, (t ∈ left ∨ t ∈ right) ∧
          ∀ k : Fin 24, g.op.eval (g.inputs.map (fun i => (seed.map (bit k)).getD i false)) = bit k t := by
        have base := allowed g (by rw [hh]; simp)
        have ua : ∀ a b : Fin 25, (seed.getD a.val 0 &&& seed.getD b.val 0) ∈ left := by decide +kernel
        have uo : ∀ a b : Fin 25, ((seed.getD a.val 0 ||| seed.getD b.val 0) ∈ left ∨
          (seed.getD a.val 0 ||| seed.getD b.val 0) ∈ right) := by decide +kernel
        rcases base with e | ⟨a,b,e|e⟩
        · subst g
          exact ⟨16777215,Or.inl (by decide +kernel),by decide +kernel⟩
        · subst g
          refine ⟨_,Or.inl (ua a b),?_⟩
          intro k
          change ((seed.map (bit k)).getD a.val false && ((seed.map (bit k)).getD b.val false && true)) = _
          rw [read,read]
          simp [bit]
        · subst g
          refine ⟨_,uo a b,?_⟩
          intro k
          change ((seed.map (bit k)).getD a.val false || ((seed.map (bit k)).getD b.val false || false)) = _
          rw [read,read]
          simp [bit]
      obtain ⟨t, ht, values⟩ := choose
      have tests (k : Fin 24) : (Circuit.mk gs 23).eval ((seed ++ [t]).map (bit k)) = bit k 4095 := by
        have q := (congrFun good (input k)).trans (target_ok k)
        change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn (input k))).getD C.output false = _ at q
        rw [out,hh,List.foldl_cons,List.foldl_cons] at q
        have firstVal : GateOp.or.eval ([0,3].map fun i => (List.ofFn (input k)).getD i false) =
            (input k 0 || input k 3) := by
          change ([0,3].map fun i => (List.ofFn (input k)).getD i false).any id = _
          simp [List.getD_eq_getElem?_getD]
        change (gs.foldl _ ((List.ofFn (input k) ++ [GateOp.or.eval ([0,3].map _)]) ++ [_])).getD 23 false = _ at q
        rw [firstVal,←seed_ok k,values k] at q
        change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          ((seed ++ [t]).map (bit k))).getD 23 false = _
        simpa only [List.map_append,List.map_cons,List.map_nil] using q
      rcases ht with ht | ht
      · exact andCase t ht gs slen allg tests
      · exact orCase t ht gs slen allg tests
