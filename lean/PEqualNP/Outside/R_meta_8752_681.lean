import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 15000000 in
theorem PEqualNP.Outside.R_meta_8752_681
    (single : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      C.output + 1 = 26 + C.gates.length →
      (∃ ws : List Nat, C.gates.getLast? = some (⟨PEqualNP.CircuitLowerBounds.GateOp.or,ws⟩ : PEqualNP.CircuitLowerBounds.Gate)) →
      (∀ P L : Finset (Fin 13), C.eval (List.ofFn fun k : Fin 26 =>
        if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ P) else decide (Fin.ofNat 13 k.val ∈ L)) = true ↔
        ∃ p ∈ P, ∃ l ∈ L, (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)) →
      51 ≤ {i : Nat | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (mono : ∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin n → Bool), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ i, x i = true → y i = true) →
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (50 : ℕ) ≤ {x6 : ℕ | ∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  have geom : ∀ S : Finset (Fin 13), 3 < S.card →
      ({l : Fin 13 | ∀ p ∈ S, (p.val+l.val)%13 ∉ ([0,1,3,9] : List Nat)} : Finset (Fin 13)).card ≤ 3 := by
    let rel (p l : Fin 13) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
    have four : ∀ a b c d : Fin 13, a < b → b < c → c < d →
        (Finset.univ.filter fun l => ¬rel a l ∧ ¬rel b l ∧ ¬rel c l ∧ ¬rel d l).card ≤ 3 := by
      dsimp only [rel]
      decide +kernel
    intro S hs
    obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq (s := S) (n := 4) hs
    let f := T.orderEmbOfFin hcard
    have inside (i : Fin 4) : f i ∈ S := hT (T.orderEmbOfFin_mem hcard i)
    have hh := four (f 0) (f 1) (f 2) (f 3) (f.strictMono (by decide))
      (f.strictMono (by decide)) (f.strictMono (by decide))
    refine (Finset.card_le_card ?_).trans hh
    intro l hl
    have avoid := (Finset.mem_filter.mp hl).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, avoid _ (inside 0), avoid _ (inside 1),
      avoid _ (inside 2), avoid _ (inside 3)⟩
  classical
  intro C W hc hw ht
  let I (p l : Fin 13) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
  let inp (P L : Finset (Fin 13)) (k : Fin 26) :=
    if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ P) else decide (Fin.ofNat 13 k.val ∈ L)
  let miss (P : Finset (Fin 13)) := Finset.univ.filter fun l : Fin 13 => ∀ p ∈ P, ¬I p l
  let K : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or,W⟩
  let B : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ [K], 26+C.gates.length⟩
  have hb : PEqualNP.MetaComplexity.Monotone2 B := by
    intro g hg
    change g ∈ C.gates ++ [K] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hc g hg
    · have : g = K := by simpa using hg
      subst g
      exact ⟨by simp [K],hw⟩
  have wlen (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).length = v.length+gs.length := by
    induction gs generalizing v with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega
  have val (P L : Finset (Fin 13)) : B.eval (List.ofFn (inp P L)) =
      PEqualNP.CircuitLowerBounds.GateOp.or.eval (W.map fun i => (C.wires (List.ofFn (inp P L))).getD i false) := by
    let v := C.wires (List.ofFn (inp P L))
    have len : v.length = 26+C.gates.length := by
      have hlen := wlen C.gates (List.ofFn (inp P L))
      change v.length = (List.ofFn (inp P L)).length+C.gates.length at hlen
      simpa only [List.length_ofFn] using hlen
    change List.getD ((C.gates ++ [K]).foldl
      (fun (w : List Bool) g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (inp P L))) (26+C.gates.length) false = _
    rw [List.foldl_append]
    change (v ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (W.map fun i => v.getD i false)]).getD (26+C.gates.length) false = _
    rw [← len]
    simp [List.getD_eq_getElem?_getD, v]
  have poses : ∀ p l, I p l → B.eval (List.ofFn (inp {p} {l})) = true := by
    intro p l h; rw [val]; exact ht.1 p l h
  have negs : ∀ S : Finset (Fin 13), S.card ≤ 3 → B.eval (List.ofFn (inp S (miss S))) = false ∧
      B.eval (List.ofFn (inp (miss S) S)) = false := by
    intro S hs; rw [val,val]; exact ht.2 S hs
  have grow {P L P' L' : Finset (Fin 13)} (hp : P ⊆ P') (hl : L ⊆ L') :
      B.eval (List.ofFn (inp P L)) = true → B.eval (List.ofFn (inp P' L')) = true := by
    apply mono 26 B _ _ hb
    intro k hk
    by_cases a : k.val < 13
    · have hm : Fin.ofNat 13 k.val ∈ P := by simpa only [inp,ite_eq_left a,decide_eq_true_eq] using hk
      simpa only [inp,ite_eq_left a,decide_eq_true_eq] using hp hm
    · have hm : Fin.ofNat 13 k.val ∈ L := by simpa only [inp,ite_eq_right a,decide_eq_true_eq] using hk
      simpa only [inp,ite_eq_right a,decide_eq_true_eq] using hl hm
  have exactness (P L : Finset (Fin 13)) : B.eval (List.ofFn (inp P L)) = true ↔
      ∃ p ∈ P, ∃ l ∈ L, I p l := by
    constructor
    · intro h
      by_contra no
      have hl : L ⊆ miss P := by
        intro l hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hP hI => no ⟨p,hP,l,hL,hI⟩⟩
      have hp : P ⊆ miss L := by
        intro p hP
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro l hL hi
        exact no ⟨p,hP,l,hL,by simpa [I,Nat.add_comm] using hi⟩
      by_cases hs : P.card ≤ 3
      · have b := grow (Finset.Subset.refl P) hl h
        exact Bool.false_ne_true ((negs P hs).1.symm.trans b)
      · have bound : L.card ≤ 3 := (Finset.card_le_card hl).trans (geom P (Nat.lt_of_not_ge hs))
        have b := grow hp (Finset.Subset.refl L) h
        exact Bool.false_ne_true ((negs L bound).2.symm.trans b)
    · rintro ⟨p,hP,l,hL,hi⟩
      exact grow (Finset.singleton_subset_iff.mpr hP) (Finset.singleton_subset_iff.mpr hL) (poses p l hi)
  let ors (A : PEqualNP.CircuitLowerBounds.Circuit) := {i : Nat | ∃ g : PEqualNP.CircuitLowerBounds.Gate, A.gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}
  have finalWire : B.output+1 = 26+B.gates.length := by simp [B,Nat.add_assoc]
  have finalGate : ∃ ws : List Nat, B.gates.getLast? = some (⟨PEqualNP.CircuitLowerBounds.GateOp.or,ws⟩ : PEqualNP.CircuitLowerBounds.Gate) :=
    ⟨W,by simp [B,K]⟩
  have bound : 51 ≤ (ors B).ncard := single B hb finalWire finalGate exactness
  have sub : ors B ⊆ insert C.gates.length (ors C) := by
    rintro i ⟨g,hg,ho⟩
    have hget := List.getElem?_eq_some_iff.mp hg
    have hi : i < C.gates.length+1 := by simpa [B] using hget.1
    by_cases h : i < C.gates.length
    · apply Set.mem_insert_of_mem
      refine ⟨g,?_,ho⟩
      simpa only [B,List.getElem?_append_left h] using hg
    · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_gt h))
  have fin : (ors C).Finite := by
    apply (Set.finite_Iio C.gates.length).subset
    rintro i ⟨g,hg,_⟩
    exact (List.getElem?_eq_some_iff.mp hg).1
  have step := (Set.ncard_le_ncard sub (fin.insert _)).trans (Set.ncard_insert_le _ _)
  change 50 ≤ (ors C).ncard
  omega
