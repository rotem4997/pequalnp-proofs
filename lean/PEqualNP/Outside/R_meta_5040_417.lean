import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5040_417 (h1 : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x1 (x3 - x4) = Bool.true → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x1 (x6 - x5) = Bool.true}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x1 (x7 - x6) = Bool.false)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → x2 x3 → (¬∃ (x7 : ℕ) (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x7 x8) → (64 : ℕ) ≤ x3.size) (h2 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x2 x10 ∧ x10.size < x4.size) : have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ x2.output + (1 : ℕ) = (26 : ℕ) + x2.size ∧ (∀ x3 ∈ x2.gates.zipIdx, ∀ x5 ∈ x3.1.inputs, x5 < (26 : ℕ) + x3.2 ∨ x5 = (89 : ℕ)) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x4 = (0 : Fin (13 : ℕ)) ∨ x4 = (1 : Fin (13 : ℕ)) ∨ x4 = (3 : Fin (13 : ℕ)) ∨ x4 = (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) (x3 + x4) ∨ x6 = Fin.natAdd (13 : ℕ) x3)) = Bool.true) ∧ ∀ x3 ∈ x1, ∀ (x5 : Fin (13 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ (x7 : Fin (13 : ℕ)), x3.testBit ↑(x7 - x5) = Bool.true ∧ x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x3.testBit ((13 : ℕ) + ↑(x7 - x5)) = Bool.true ∧ x6 = Fin.natAdd (13 : ℕ) x7)) = Bool.false := by
  intro rows
  rintro ⟨C, hmono, hsize, -, hreads, -, -, hinc, hrows⟩
  extract_lets D1 Q1 at h1
  extract_lets D2 Q2 N2 at h2
  have norm : ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧ C'.size = C.size ∧
      ∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x := by
    classical
    obtain ⟨fix, hfix⟩ : ∃ fix : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate,
        ∀ g : PEqualNP.CircuitLowerBounds.Gate, fix g =
        if g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 89 ∈ g.inputs then ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
        else ⟨g.op, g.inputs.filter (fun i => decide (i ≠ 89))⟩ := ⟨_, fun g => rfl⟩
    have eand : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun l => rfl
    have eor : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun l => rfl
    have hstep : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → w.length ≤ 89 →
        (fix g).op.eval ((fix g).inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      intro g w hop hw
      have h89 : w.getD 89 false = false := by
        rw [List.getD_eq_default]
        exact hw
      rw [hfix]
      split_ifs with h
      · obtain ⟨ea, eb⟩ := h
        rw [ea]
        simp only [eand, eor, List.map_nil, List.any_nil]
        symm
        rw [List.all_eq_false]
        exact ⟨false, List.mem_map.mpr ⟨89, eb, h89⟩, by simp⟩
      · rcases hop with eo | eo
        · have e89 : 89 ∉ g.inputs := fun h' => h ⟨eo, h'⟩
          have ef : g.inputs.filter (fun i => decide (i ≠ 89)) = g.inputs := by
            rw [List.filter_eq_self]
            intro a ha
            simp only [ne_eq, decide_eq_true_eq]
            rintro rfl
            exact e89 ha
          simp only [ef]
        · simp only [eo, eor]
          rw [Bool.eq_iff_iff]
          simp only [List.any_eq_true, List.mem_map, List.mem_filter, id, ne_eq, decide_eq_true_eq]
          constructor
          · rintro ⟨b, ⟨i, ⟨hi, -⟩, rfl⟩, hb⟩
            exact ⟨_, ⟨i, hi, rfl⟩, hb⟩
          · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
            refine ⟨_, ⟨i, ⟨hi, ?_⟩, rfl⟩, hb⟩
            rintro rfl
            rw [h89] at hb
            exact Bool.false_ne_true hb
    have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        w.length + gs.length ≤ 89 →
        (gs.map fix).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
      intro gs
      induction gs with
      | nil =>
        intro w _ _
        rfl
      | cons g gs ih =>
        intro w hops hlen
        simp only [List.length_cons] at hlen
        simp only [List.map_cons, List.foldl_cons]
        rw [hstep g w (hops g List.mem_cons_self) (by omega)]
        refine ih _ (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg')) ?_
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      have := (hmono g hg).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    refine ⟨⟨C.gates.map fix, C.output⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have h0 := hmono g0 hg0
      rw [hfix]
      split_ifs with h
      · simp
      · exact ⟨h0.1, (List.length_filter_le _ _).trans h0.2⟩
    · intro j hj i hi
      simp only [List.length_map] at hj
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨C.gates.map fix, C.output⟩ j = fix (C.gates[j]) := by
        show (C.gates.map fix).getD j _ = fix (C.gates[j])
        simp [hj]
      rw [hg, hfix] at hi
      have hmem : (C.gates[j], j) ∈ C.gates.zipIdx := by
        simp [List.mem_zipIdx_iff_getElem?, hj]
      split_ifs at hi with h
      · simp at hi
      · simp only [List.mem_filter, ne_eq, decide_eq_true_eq] at hi
        rcases hreads _ hmem i hi.1 with h' | h'
        · exact h'
        · exact absurd h' hi.2
    · show (C.gates.map fix).length = C.gates.length
      simp only [List.length_map]
    · intro x hx
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      simp only
      have hsz : C.gates.length ≤ 63 := hsize
      rw [hfold C.gates x hops (by omega)]
  have chk : ((List.range 13).all fun a => (List.range 13).all fun b => !(decide (a < b)) || ((List.range 13).all fun c => !(decide (b < c)) || ((List.range 13).all fun d => !(decide (c < d)) ||
     (!((List.range 13).all fun l => decide ((Nat.testBit 523 (((13 - l) + a) % 13)).toNat + (Nat.testBit 523 (((13 - l) + b) % 13)).toNat + (Nat.testBit 523 (((13 - l) + c) % 13)).toNat + (Nat.testBit 523 (((13 - l) + d) % 13)).toNat ≤ 2)) ||
       ([a,b,c,d].any fun t => ([7405575,23330829,5799955,22282261,21757977,21233693,3735587,19988517,3211303,19415081,7372867,24117317,7340103,23085129,23068749,22052945,5275731,22020181,19939425,19923045,18890857,6389891,6619269,6357127,6570121,6553741,6324419,6308041,21512457,21528849,4751635,21496089,17318185,20988233,21004625,17891877] : List ℕ).any fun k => (List.range 13).all fun p =>
          (k.testBit (((13 - t) + p) % 13) == decide (p = a ∨ p = b ∨ p = c ∨ p = d)) && (k.testBit (13 + ((13 - t) + p) % 13) == (!Nat.testBit 523 (((13 - p) + a) % 13) && !Nat.testBit 523 (((13 - p) + b) % 13) && !Nat.testBit 523 (((13 - p) + c) % 13) && !Nat.testBit 523 (((13 - p) + d) % 13)))))))) = true := by
    decide +kernel
  have factA : ∀ a b c d : Fin 13, a < b → b < c → c < d →
     (∀ l : Fin 13, (Nat.testBit 523 (a - l).val).toNat + (Nat.testBit 523 (b - l).val).toNat + (Nat.testBit 523 (c - l).val).toNat + (Nat.testBit 523 (d - l).val).toNat ≤ 2) →
     ∃ k ∈ ([7405575,23330829,5799955,22282261,21757977,21233693,3735587,19988517,3211303,19415081,7372867,24117317,7340103,23085129,23068749,22052945,5275731,22020181,19939425,19923045,18890857,6389891,6619269,6357127,6570121,6553741,6324419,6308041,21512457,21528849,4751635,21496089,17318185,20988233,21004625,17891877] : List ℕ), ∃ t : Fin 13, ∀ p : Fin 13,
         k.testBit (p - t).val = decide (p = a ∨ p = b ∨ p = c ∨ p = d) ∧
         k.testBit (13 + (p - t).val) = (!Nat.testBit 523 (a - p).val && !Nat.testBit 523 (b - p).val && !Nat.testBit 523 (c - p).val && !Nat.testBit 523 (d - p).val) := by
    intro a b c d hab hbc hcd hq
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at chk
    rcases chk a.val a.isLt b.val b.isLt with h | chk
    · exact absurd hab h
    rcases chk c.val c.isLt with h | chk
    · exact absurd hbc h
    rcases chk d.val d.isLt with h | chk
    · exact absurd hcd h
    rcases chk with h | ⟨t, ht, k, hk, hp⟩
    · exfalso
      rw [← Bool.not_eq_true, List.all_eq_true] at h
      apply h
      intro l hl
      rw [List.mem_range] at hl
      have := hq ⟨l, hl⟩
      simpa only [Fin.val_sub, decide_eq_true_eq] using this
    · have ht13 : t < 13 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        omega
      refine ⟨k, hk, ⟨t, ht13⟩, fun p => ?_⟩
      have := hp p.val p.isLt
      simp only [Fin.val_sub, Fin.ext_iff]
      exact this
  have quadFact : ∀ S : Finset (Fin 13), S.card = 4 →
        (∀ x5 : Fin 13, (S.filter (fun x6 => x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
        ∃ k ∈ ([7405575,23330829,5799955,22282261,21757977,21233693,3735587,19988517,3211303,19415081,7372867,24117317,7340103,23085129,23068749,22052945,5275731,22020181,19939425,19923045,18890857,6389891,6619269,6357127,6570121,6553741,6324419,6308041,21512457,21528849,4751635,21496089,17318185,20988233,21004625,17891877] : List ℕ),
          ∃ t : Fin 13, (∀ p : Fin 13, k.testBit (p - t).val = decide (p ∈ S)) ∧
            ∀ l : Fin 13, k.testBit (13 + (l - t).val) = decide (∀ x7 ∈ S, x7 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) := by
    intro S hcard hquad
    have hD : ∀ y : Fin 13, Nat.testBit 523 y.val = decide (y ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by decide
    have hlen := Finset.length_sort (s := S) (· ≤ ·)
    have hsorted := (Finset.sortedLT_sort S).pairwise
    have hmem : ∀ x, x ∈ S.sort (· ≤ ·) ↔ x ∈ S := fun x => Finset.mem_sort (· ≤ ·)
    rw [hcard] at hlen
    generalize S.sort (· ≤ ·) = L at hlen hsorted hmem
    rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp only [List.length_nil, List.length_cons] at hlen <;> try omega
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_imp_iff, implies_true, and_true, List.Pairwise.nil] at hsorted
    obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hsorted
    have hS : S = {a, b, c, d} := by
      ext x
      rw [← hmem]
      simp
    subst hS
    obtain ⟨k, hk, t, hkt⟩ := factA a b c d hab hbc hcd (by
      intro l
      have := hquad l
      rw [Finset.card_filter, Finset.sum_insert (by simp [hab.ne, hac.ne, had.ne]), Finset.sum_insert (by simp [hbc.ne, hbd.ne]), Finset.sum_insert (by simp [hcd.ne]), Finset.sum_singleton] at this
      simp only [hD]
      convert this using 1
      simp only [Bool.toNat, Bool.cond_decide]
      ring)
    refine ⟨k, hk, t, fun p => ?_, fun l => ?_⟩
    · rw [(hkt p).1]
      simp
    · rw [(hkt l).2]
      simp only [hD]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq, and_assoc]
  have hQ : ∀ E : PEqualNP.CircuitLowerBounds.Circuit, Q2 E → Q1 E := by
    intro E hE
    have hD : ∀ y : Fin 13, D1 y = true ↔ y ∈ D2 := by
      intro y
      simp [D1, D2]
    have hD' : ∀ y : Fin 13, D1 y = false ↔ y ∉ D2 := by
      intro y
      rw [← hD, Bool.not_eq_true]
    refine ⟨fun x3 x4 h => hE.1 x3 x4 ((hD _).mp h), fun S hc hquad => ?_⟩
    have e : ∀ x5 : Fin 13, S.filter (fun x6 => x6 - x5 ∈ D2) = S.filter (fun x6 => D1 (x6 - x5) = true) :=
      fun x5 => Finset.filter_congr (fun x _ => (hD _).symm)
    have e2 : ∀ x6 : Fin 13, decide (∀ x7 ∈ S, D1 (x7 - x6) = false) = decide (∀ x7 ∈ S, x7 - x6 ∉ D2) :=
      fun x6 => decide_eq_decide.mpr (forall₂_congr fun x7 _ => hD' _)
    have h3 := hE.2 S hc (fun x5 => by rw [e]; exact hquad x5)
    simp only [e2]
    exact h3
  have main : ∀ n : ℕ, ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 E → Q2 E → E.size = n → n < 64 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro E hm hr hq hn hlt
      by_cases hN : N2 E
      · obtain ⟨E', hm', hr', hq', hlt'⟩ := h2 E hm hr hq (by omega) hN
        exact ih E'.size (by omega) E' hm' hr' hq' rfl (by omega)
      · have h64 := h1 E hm hr (hQ E hq) hN
        omega
  have hsplit : ∀ f : Fin 26 → Bool, List.ofFn f =
      List.ofFn (fun i : Fin 13 => f (Fin.castAdd 13 i)) ++ List.ofFn (fun i : Fin 13 => f (Fin.natAdd 13 i)) :=
    fun f => List.ofFn_add (m := 13) (n := 13) (f := f)
  have hcn : ∀ i j : Fin 13, Fin.castAdd 13 i ≠ Fin.natAdd 13 j := by
    intro i j h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  have hcc : ∀ i j : Fin 13, ((Fin.castAdd 13 i : Fin 26) = Fin.castAdd 13 j) = (i = j) := by
    intro i j
    simp only [Fin.ext_iff, Fin.val_castAdd]
  have hnn : ∀ i j : Fin 13, ((Fin.natAdd 13 i : Fin 26) = Fin.natAdd 13 j) = (i = j) := by
    intro i j
    simp only [Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]
  have hcn' : ∀ i j : Fin 13, ((Fin.castAdd 13 i : Fin 26) = Fin.natAdd 13 j) = False := by
    intro i j
    exact eq_false (hcn i j)
  have hnc' : ∀ i j : Fin 13, ((Fin.natAdd 13 i : Fin 26) = Fin.castAdd 13 j) = False := by
    intro i j
    exact eq_false (fun h => hcn j i h.symm)
  obtain ⟨C', hm', hr', hs', hev⟩ := norm
  refine main C'.size C' hm' hr' ⟨?_, ?_⟩ rfl (by omega)
  · intro p l hpl
    rw [hev _ (by simp)]
    have h3 := hinc l (p - l) (by simpa [D2] using hpl)
    rw [add_sub_cancel] at h3
    unfold PEqualNP.MetaComplexity.circuitFun at h3
    rw [hsplit] at h3
    simp only [hcc, hnn, hcn', hnc', or_false, false_or] at h3
    exact h3
  · intro S hc hq
    rw [hev _ (by simp)]
    obtain ⟨k, hk, t, hp, hl⟩ := quadFact S hc hq
    have h3 := hrows k hk t
    unfold PEqualNP.MetaComplexity.circuitFun at h3
    rw [hsplit] at h3
    simp only [hcc, hnn, hcn', hnc', and_false, exists_false, or_false, false_or, exists_eq_right', Bool.decide_eq_true, hp, hl] at h3
    exact h3
