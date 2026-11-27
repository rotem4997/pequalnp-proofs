import PEqualNP.Defs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_8752_385
  (single : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    let I (p l : Fin 13) := (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)
    let inp (P L : Finset (Fin 13)) (k : Fin 26) := if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ P) else decide (Fin.ofNat 13 k.val ∈ L)
    let miss (P : Finset (Fin 13)) := Finset.univ.filter fun l : Fin 13 => ∀ p ∈ P, ¬ I p l
    let f (w : Nat) (P L : Finset (Fin 13)) := (C.wires (List.ofFn (inp P L))).getD w false
    let safe (w : Nat) := ∀ S : Finset (Fin 13), S.card ≤ 3 → f w S (miss S) = false ∧ f w (miss S) S = false
    let edges := {a : Fin 13 × Fin 13 | I a.1 a.2}
    let hits (w : Nat) := {a : Fin 13 × Fin 13 | f w {a.1} {a.2} = true}
    ∀ i : Fin C.gates.length, safe (26+i.val) → edges ⊆ hits (26+i.val) → 50 ≤ {i : Nat | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
  (pair : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    let I (p l : Fin 13) := (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)
    let inp (P L : Finset (Fin 13)) (k : Fin 26) := if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ P) else decide (Fin.ofNat 13 k.val ∈ L)
    let miss (P : Finset (Fin 13)) := Finset.univ.filter fun l : Fin 13 => ∀ p ∈ P, ¬ I p l
    let f (w : Nat) (P L : Finset (Fin 13)) := (C.wires (List.ofFn (inp P L))).getD w false
    let safe (w : Nat) := ∀ S : Finset (Fin 13), S.card ≤ 3 → f w S (miss S) = false ∧ f w (miss S) S = false
    let edges := {a : Fin 13 × Fin 13 | I a.1 a.2}
    let hits (w : Nat) := {a : Fin 13 × Fin 13 | f w {a.1} {a.2} = true}
    ∀ i j : Fin C.gates.length, safe (26+i.val) → safe (26+j.val) → edges ⊆ hits (26+i.val) ∪ hits (26+j.val) → ¬ edges ⊆ hits (26+i.val) → ¬ edges ⊆ hits (26+j.val) → 50 ≤ {i : Nat | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (50 : ℕ) ≤ {x6 : ℕ | ∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C W hm hw htest
  let I (p l : Fin 13) := (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)
  let inp (P L : Finset (Fin 13)) (k : Fin 26) := if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ P) else decide (Fin.ofNat 13 k.val ∈ L)
  let miss (P : Finset (Fin 13)) := Finset.univ.filter fun l : Fin 13 => ∀ p ∈ P, ¬ I p l
  let f (w : Nat) (P L : Finset (Fin 13)) := (C.wires (List.ofFn (inp P L))).getD w false
  let safe (w : Nat) := ∀ S : Finset (Fin 13), S.card ≤ 3 → f w S (miss S) = false ∧ f w (miss S) S = false
  let edges := {a : Fin 13 × Fin 13 | I a.1 a.2}
  let hits (w : Nat) := {a : Fin 13 × Fin 13 | f w {a.1} {a.2} = true}
  let bound : Prop := 50 ≤ {i : Nat | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard
  have cells : edges.Nonempty := ⟨(0,0), by decide⟩
  have tests : (∀ p l, I p l → (W.map (fun w => f w {p} {l})).any id = true) ∧
      ∀ S : Finset (Fin 13), S.card ≤ 3 →
        (W.map (fun w => f w S (miss S))).any id = false ∧ (W.map (fun w => f w (miss S) S)).any id = false := htest
  have covered (a : Fin 13 × Fin 13) (h : a ∈ edges) : ∃ w ∈ W, a ∈ hits w := by
    obtain ⟨b, hb, htrue⟩ := List.any_eq_true.mp (tests.1 a.1 a.2 h)
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hb
    exact ⟨w, hw', htrue⟩
  have neg (w : Nat) (mem : w ∈ W) : safe w := by
    intro S hs
    obtain ⟨left, right⟩ := tests.2 S hs
    constructor
    · cases h : f w S (miss S) with
      | false => rfl
      | true => exact False.elim ((List.any_eq_false.mp left) _ (List.mem_map.mpr ⟨w,mem,rfl⟩) h)
    · cases h : f w (miss S) S with
      | false => rfl
      | true => exact False.elim ((List.any_eq_false.mp right) _ (List.mem_map.mpr ⟨w,mem,rfl⟩) h)
  have suffix (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : List Bool) :
      ∃ t : List Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires v = v ++ t ∧ t.length = gs.length := by
    induction gs generalizing v with
    | nil => exact ⟨[], (List.append_nil _).symm, rfl⟩
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun i => v.getD i false)
      obtain ⟨t, eqn, len⟩ := ih (v ++ [b])
      refine ⟨b :: t, ?_, by simp only [List.length_cons, len]⟩
      change (PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires (v ++ [b]) = _
      rw [eqn, List.append_assoc]
      rfl
  have shape (P L : Finset (Fin 13)) : ∃ t : List Bool,
      C.wires (List.ofFn (inp P L)) = List.ofFn (inp P L) ++ t ∧ t.length = C.gates.length :=
    suffix C.gates (List.ofFn (inp P L))
  have prim (k : Fin 26) (P L : Finset (Fin 13)) : f k.val P L = inp P L k := by
    obtain ⟨t, e, _⟩ := shape P L
    have h : k.val < (List.ofFn (inp P L)).length := by simpa only [List.length_ofFn] using k.isLt
    dsimp only [f]
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    rw [List.getElem?_eq_getElem h, List.getElem_ofFn]; rfl
  have primaryTest : ∀ k : Fin 26, inp ∅ (miss ∅) k = true ∨ inp (miss ∅) ∅ k = true := by decide
  have internal (w : Nat) (hs : safe w) (hh : (edges ∩ hits w).Nonempty) :
      ∃ i : Fin C.gates.length, 26+i.val = w := by
    have lo : 26 ≤ w := by
      by_contra! short
      have bad := hs ∅ (by decide)
      obtain h | h := primaryTest ⟨w,short⟩
      · have := (prim ⟨w,short⟩ ∅ (miss ∅)).trans h
        exact Bool.false_ne_true (bad.1.symm.trans this)
      · have := (prim ⟨w,short⟩ (miss ∅) ∅).trans h
        exact Bool.false_ne_true (bad.2.symm.trans this)
    obtain ⟨a, _, ha⟩ := hh
    obtain ⟨t, e, len⟩ := shape {a.1} {a.2}
    have len' : (C.wires (List.ofFn (inp {a.1} {a.2}))).length = 26+C.gates.length := by rw [e, List.length_append, List.length_ofFn,len]
    have hi : w < 26+C.gates.length := by
      by_contra! out
      change (C.wires (List.ofFn (inp {a.1} {a.2}))).getD w false = true at ha
      rw [List.getD_eq_default _ _ (by omega)] at ha
      contradiction
    exact ⟨⟨w-26,by omega⟩,by change 26+(w-26) = w; omega⟩
  have finish (w : Nat) (mem : w ∈ W) (all : edges ⊆ hits w) : bound := by
    obtain ⟨a,ha⟩ := cells
    obtain ⟨i, eqn⟩ := internal w (neg w mem) ⟨a,ha,all ha⟩
    exact single C hm i (eqn ▸ neg w mem) (eqn ▸ all)
  by_cases one : ∃ w ∈ W, edges ⊆ hits w
  · obtain ⟨w, mem, all⟩ := one
    exact finish w mem all
  · have many (i j : Nat) (list : W = [i,j]) : bound := by
      have mi : i ∈ W := list ▸ (by simp)
      have mj : j ∈ W := list ▸ (by simp)
      have ni : ¬ edges ⊆ hits i := fun h => one ⟨i,mi,h⟩
      have nj : ¬ edges ⊆ hits j := fun h => one ⟨j,mj,h⟩
      have both : edges ⊆ hits i ∪ hits j := by
        intro a ha
        obtain ⟨w,mem,yes⟩ := covered a ha
        rw [list] at mem
        rcases List.mem_cons.mp mem with rfl | next
        · exact Or.inl yes
        · have eqn : w = j := List.mem_singleton.mp next
          exact Or.inr (eqn ▸ yes)
      have need {u v : Set (Fin 13 × Fin 13)} (no : ¬edges ⊆ u) (cov : edges ⊆ u ∪ v) : (edges ∩ v).Nonempty := by
        by_contra h
        apply no
        intro a ha
        exact (cov ha).resolve_right (fun hv => h ⟨a, ha, hv⟩)
      obtain ⟨u, hu⟩ := internal i (neg i mi) (need nj (Set.union_comm _ _ ▸ both))
      obtain ⟨v, hv⟩ := internal j (neg j mj) (need ni both)
      subst i
      subst j
      exact pair C hm u v (neg _ mi) (neg _ mj) both ni nj
    cases W with
    | nil =>
      obtain ⟨a,ha⟩ := cells
      obtain ⟨w,mem,_⟩ := covered a ha
      exact (List.not_mem_nil mem).elim
    | cons i tail =>
      cases tail with
      | nil =>
        apply finish i (by simp)
        intro a ha
        obtain ⟨w,mem,yes⟩ := covered a ha
        exact (List.mem_singleton.mp mem) ▸ yes
      | cons j tail =>
        cases tail with
        | nil => exact many i j rfl
        | cons k rest => simp only [List.length_cons] at hw; omega
