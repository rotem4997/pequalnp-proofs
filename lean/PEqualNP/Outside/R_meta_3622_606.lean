import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3622_606
    (original : let seed : List (BitVec 29) := [503381504,18022921,176694291,70599750,30017540,987296,107774216,359669808,427868608,33489407]
      let raw := seed.take 9
      let normal := raw.flatMap (fun a => (raw.filter (fun b => a != b)).map (fun b => a &&& b))
      ∀ t ∈ normal, ∀ C : Circuit, Monotone2 C → 12 ≤ C.size → C.size ≤ 13 →
      ¬∀ k : Fin 29, C.eval ((seed ++ [t]).map (fun z => z.getLsbD k.val)) = (65535 : BitVec 29).getLsbD k.val)
    (remaining : let seed : List (BitVec 29) := [503381504,18022921,176694291,70599750,30017540,987296,107774216,359669808,427868608,33489407]
      let raw := seed.take 9
      let normal := raw.flatMap (fun a => (raw.filter (fun b => a != b)).map (fun b => a &&& b))
      let pool := 0 :: seed
      let vals := (536870911 : BitVec 29) :: pool.flatMap (fun a => pool.map (fun b => a &&& b))
      ∀ t ∈ (vals.filter (fun t => t ∉ normal)), ∀ C : Circuit, Monotone2 C → 12 ≤ C.size → C.size ≤ 13 →
      ¬∀ k : Fin 29, C.eval ((seed ++ [t]).map (fun z => z.getLsbD k.val)) = (65535 : BitVec 29).getLsbD k.val)
    : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         (12 : ℕ) ≤ x3.size →           x3.size ≤ (13 : ℕ) →             List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.true]) x3.gates = (0 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro ins cap C hf lo hi cnt
  by_contra! h
  let seed : List (BitVec 29) := [503381504,18022921,176694291,70599750,30017540,987296,107774216,359669808,427868608,33489407]
  let pool := 0 :: seed
  let raw := seed.take 9
  let normal := raw.flatMap (fun a => (raw.filter (fun b => a != b)).map (fun b => a &&& b))
  let vals := (536870911 : BitVec 29) :: pool.flatMap (fun a => pool.map (fun b => a &&& b))
  let masks : List Nat := [6,12,24,66,132,160,264,288,320,3,13,17,33,133,265,321,42,50,104,116,138,200,208,276,402,69,201,261,385]
  let bit (k : Fin 29) (z : BitVec 29) := z.getLsbD k.val
  let x (k : Fin 29) (i : Fin 9) := (masks.getD k.val 0).testBit i.val
  have seed_ok : ∀ k : Fin 29, seed.map (bit k) = List.ofFn (x k) ++ [!x k 0] := by decide +kernel
  have target_ok : ∀ k : Fin 29, ((x k 0 && x k 1) || (x k 1 && x k 2) || (x k 2 && x k 3) || (x k 3 && x k 4) || (x k 4 && x k 0) || (x k 0 && x k 5) || (x k 1 && x k 6) || (x k 2 && x k 7) || (x k 3 && x k 8) || (x k 5 && x k 7) || (x k 6 && x k 8) || (x k 8 && x k 5)) = bit k 65535 := by decide +kernel
  have m : Monotone2 C := by
    intro g hg
    have q := hf g hg
    rcases q.1 with e|e|e
    · exact ⟨Or.inl e,q.2⟩
    · exact ⟨Or.inr e,q.2⟩
    · have hn := List.countP_eq_zero.mp cnt g hg
      change g.op = GateOp.not at e
      rw [e] at hn
      exact (hn rfl).elim
  have read (i : Nat) (k : Fin 29) :
      (seed.map (bit k)).getD i false = bit k (seed.getD i 0) := by
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases e : seed[i]? <;> simp [bit]
  have mem (i : Nat) : seed.getD i 0 ∈ pool := by
    rw [List.getD_eq_getElem?_getD]
    cases e : seed[i]? with
    | none => exact List.mem_cons_self
    | some y => exact List.mem_cons_of_mem _ (List.mem_of_getElem? e)
  have both (a b : BitVec 29) (ha : a ∈ pool) (hb : b ∈ pool) : a &&& b ∈ vals := by
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    exact ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
  have witness : ∃ t ∈ vals, ∀ k : Fin 29,
      GateOp.and.eval (ins.map (fun i => (seed.map (bit k)).getD i false)) = bit k t := by
    cases ins with
    | nil => exact ⟨536870911,List.mem_cons_self,by decide +kernel⟩
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨seed.getD i 0,?_,?_⟩
        · simpa only [BitVec.and_self] using both _ _ (mem i) (mem i)
        · intro k
          change ((seed.map (bit k)).getD i false && true) = _
          rw [Bool.and_true,read]
      | cons j more =>
        cases more with
        | nil =>
          refine ⟨_,both _ _ (mem i) (mem j),?_⟩
          intro k
          change ((seed.map (bit k)).getD i false && ((seed.map (bit k)).getD j false && true)) = _
          rw [read,read]
          simp [bit]
        | cons c t => simp at cap
  obtain ⟨t,ht,values⟩ := witness
  have tests (k : Fin 29) : C.eval ((seed ++ [t]).map (bit k)) = bit k 65535 := by
    have q := (Classical.not_not.mp (h (x k))).trans (target_ok k)
    rw [←seed_ok k,values k] at q
    simpa only [List.map_append,List.map_cons,List.map_nil] using q
  by_cases hn : t ∈ normal
  · exact original t hn C m lo hi tests
  · have keep : t ∈ vals.filter (fun v => v ∉ normal) := List.mem_filter.mpr ⟨ht,decide_eq_true hn⟩
    exact remaining t keep C m lo hi tests
