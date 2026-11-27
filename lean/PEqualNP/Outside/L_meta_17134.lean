import PEqualNP.Defs

-- The count compiler adapts L-meta-9051. The pin and cleanup tools adapt L-meta-5058.
-- The gate-removal construction adapts the merged L-meta-707 development.
-- Singleton cleanup uses L-meta-563 by sanchan (PR 631); the empty raw
-- output observation uses L-meta-561 by SaschaAlex (PR 610).
-- The high-level cofactor split is related to MorZxd's reduction (PR 10452).
-- The slot-packing and checked pin-chain lower bounds are supplied here.

namespace PEqualNP.Outside.L_meta_17134_aux.Generic

namespace Pin

open PEqualNP.AndCount

-- Adapted from open-goat/pequalnp-proofs L-meta-707 (Apache License 2.0), which credits
-- L-meta-564 for fuel stabilization. We also track preservation of surviving bare reads.
private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

private theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private def signal {n k : ℕ} (U A : Finset (Fin n)) (P : Finset (Fin k))
    (val : Fin k → Bool) : Prop :=
  (∃ v ∈ A, v ∈ U) ∨ ∃ j ∈ P, val j = true

private theorem gate_spec {n : ℕ} (C : AndCountCircuit n) (hw : C.WellFormed)
    (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔ signal U (C.leftVars i) (C.leftGates i) (C.gateVal U) ∧
      signal U (C.rightVars i) (C.rightGates i) (C.gateVal U) := by
  rw [gateVal_eq, Bool.and_eq_true]
  simp only [signal, AndCountCircuit.sideTrue, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hl with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases hr with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · rcases hl with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hw i).1 j hj, hv⟩
    · rcases hr with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hw i).2 j hj, hv⟩

private def expandVars {n m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin n))
    (P : Finset (Fin (m + 1))) : Finset (Fin n) :=
  A ∪ if i ∈ P then B else ∅

private def expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1))) :
    Finset (Fin m) :=
  Finset.univ.filter (fun k => i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F)

private theorem mem_expandVars {n m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin n))
    (P : Finset (Fin (m + 1))) (v : Fin n) :
    v ∈ expandVars i B A P ↔ v ∈ A ∨ i ∈ P ∧ v ∈ B := by
  by_cases h : i ∈ P <;> simp [expandVars, h]

private theorem mem_expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1)))
    (k : Fin m) :
    k ∈ expandRefs i F P ↔ i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := by
  simp [expandRefs]

private theorem signal_expand {n m : ℕ} (i : Fin (m + 1)) (U B A : Finset (Fin n))
    (F P : Finset (Fin (m + 1))) (val : Fin (m + 1) → Bool) (val' : Fin m → Bool)
    (before : ∀ j ∈ F, j < i) (expand : val i = true ↔ signal U B F val)
    (agree : ∀ k ∈ expandRefs i F P, val' k = val (i.succAbove k)) :
    signal U (expandVars i B A P) (expandRefs i F P) val' ↔ signal U A P val := by
  constructor
  · rintro (⟨v, hv, hu⟩ | ⟨k, hk, ht⟩)
    · rcases (mem_expandVars i B A P v).mp hv with hvA | ⟨hi, hvB⟩
      · exact Or.inl ⟨v, hvA, hu⟩
      · exact Or.inr ⟨i, hi, expand.mpr (Or.inl ⟨v, hvB, hu⟩)⟩
    · rw [agree k hk] at ht
      rcases (mem_expandRefs i F P k).mp hk with hP | ⟨hi, hF⟩
      · exact Or.inr ⟨_, hP, ht⟩
      · exact Or.inr ⟨i, hi, expand.mpr (Or.inr ⟨_, hF, ht⟩)⟩
  · rintro (⟨v, hv, hu⟩ | ⟨j, hj, ht⟩)
    · exact Or.inl ⟨v, (mem_expandVars i B A P v).mpr (Or.inl hv), hu⟩
    · by_cases hji : j = i
      · subst j
        rcases expand.mp ht with ⟨v, hv, hu⟩ | ⟨l, hl, ht'⟩
        · exact Or.inl ⟨v, (mem_expandVars i B A P v).mpr (Or.inr ⟨hj, hv⟩), hu⟩
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (ne_of_lt (before l hl))
          have hk := (mem_expandRefs i F P k).mpr (Or.inr ⟨hj, hl⟩)
          exact Or.inr ⟨k, hk, (agree k hk).trans ht'⟩
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hk := (mem_expandRefs i F P k).mpr (Or.inl hj)
        exact Or.inr ⟨k, hk, (agree k hk).trans ht⟩

private def Removal {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (i : Fin C.size) : Prop :=
  ∃ C' : AndCountCircuit n, ∃ f : Fin C'.size → Fin C.size,
    C'.WellFormed ∧ C'.size + 1 = C.size ∧ StrictMono f ∧
    (∀ j, j ≠ i ↔ ∃ k, f k = j) ∧
    (∀ k, C.leftVars (f k) ⊆ C'.leftVars k ∧ C.rightVars (f k) ⊆ C'.rightVars k) ∧
    ∀ U ∈ D, C'.eval U = C.eval U ∧ ∀ j, C'.gateVal U j = C.gateVal U (f j)

private theorem eliminate {n m : ℕ}
    (lv rv : Fin (m + 1) → Finset (Fin n)) (lg rg : Fin (m + 1) → Finset (Fin (m + 1)))
    (ov : Finset (Fin n)) (og : Finset (Fin (m + 1))) (i : Fin (m + 1))
    (D : Set (Finset (Fin n))) (B : Finset (Fin n)) (F : Finset (Fin (m + 1)))
    (hw : (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).WellFormed) (before : ∀ j ∈ F, j < i)
    (same : ∀ U ∈ D, (AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U i = true ↔
      signal U B F ((AndCountCircuit.mk (m + 1) lv lg rv rg ov og).gateVal U)) :
    Removal (AndCountCircuit.mk (m + 1) lv lg rv rg ov og) D i := by
  let C : AndCountCircuit n := ⟨m + 1, lv, lg, rv, rg, ov, og⟩
  let C' : AndCountCircuit n :=
    ⟨m, fun j => expandVars i B (lv (i.succAbove j)) (lg (i.succAbove j)),
      fun j => expandRefs i F (lg (i.succAbove j)),
      fun j => expandVars i B (rv (i.succAbove j)) (rg (i.succAbove j)),
      fun j => expandRefs i F (rg (i.succAbove j)),
      expandVars i B ov og, expandRefs i F og⟩
  have lt_ref (j k : Fin m) (P : Finset (Fin (m + 1)))
      (old : ∀ l ∈ P, l < i.succAbove j) (hk : k ∈ expandRefs i F P) : k < j := by
    apply Fin.succAbove_lt_succAbove_iff.mp
    rcases (mem_expandRefs i F P k).mp hk with hp | ⟨hi, hf⟩
    · exact old _ hp
    · exact (before _ hf).trans (old i hi)
  have hw' : C'.WellFormed := by
    intro j
    exact ⟨fun k hk => lt_ref j k _ (hw (i.succAbove j)).1 hk,
      fun k hk => lt_ref j k _ (hw (i.succAbove j)).2 hk⟩
  refine ⟨C', i.succAbove, hw', rfl, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    exact Fin.succAbove_lt_succAbove_iff.mpr hjk
  · intro j
    exact ⟨Fin.exists_succAbove_eq, by rintro ⟨k, rfl⟩; exact Fin.succAbove_ne i k⟩
  · intro k
    exact ⟨fun _ h => (mem_expandVars i B _ _ _).mpr (Or.inl h),
      fun _ h => (mem_expandVars i B _ _ _).mpr (Or.inl h)⟩
  intro U hU
  have values (j : Fin m) : C'.gateVal U j = C.gateVal U (i.succAbove j) := by
    induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin m → Fin m → Prop)).induction with
    | h j ih =>
      rw [Bool.eq_iff_iff, gate_spec C' hw', gate_spec C hw]
      exact and_congr
        (signal_expand i U B _ F _ _ _ before (same U hU)
          (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).1 hk)))
        (signal_expand i U B _ F _ _ _ before (same U hU)
          (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).2 hk)))
  refine ⟨?_, values⟩
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  exact signal_expand i U B ov F og _ _ before (same U hU) (fun k _ => values k)

private def Expandable {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (i : Fin C.size) : Prop :=
  ∃ B : Finset (Fin n), ∃ F : Finset (Fin C.size), (∀ j ∈ F, j < i) ∧
    ∀ U ∈ D, C.gateVal U i = true ↔ signal U B F (C.gateVal U)

private theorem remove_one {n : ℕ} (C : AndCountCircuit n) (D : Set (Finset (Fin n)))
    (i : Fin C.size) (hw : C.WellFormed) (g : Expandable C D i) : Removal C D i := by
  obtain ⟨B, F, before, same⟩ := g
  rcases C with ⟨s, lv, lg, rv, rg, ov, og⟩
  cases s with
  | zero => exact Fin.elim0 i
  | succ m => exact eliminate lv rv lg rg ov og i D B F hw before same

variable {n : ℕ}

def pinReads (C : AndCountCircuit n) (T : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i)

theorem mem_pinReads (C : AndCountCircuit n) (T : Finset (Fin n)) (i : Fin C.size) :
    i ∈ pinReads C T ↔ ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by
  simp [pinReads]

theorem pinReads_card (C : AndCountCircuit n) (T : Finset (Fin n)) :
    (pinReads C T).card =
      {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard := by
  have eq : (↑(pinReads C T) : Set (Fin C.size)) =
      {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i} := by
    ext i
    exact mem_pinReads C T i
  rw [← eq, Set.ncard_coe_finset]

private theorem pin_expandable (C : AndCountCircuit n) (wf : C.WellFormed)
    (T : Finset (Fin n)) (i : Fin C.size) (hi : i ∈ pinReads C T) :
    Expandable C {U : Finset (Fin n) | T ⊆ U} i := by
  rcases (mem_pinReads C T i).mp hi with ⟨v, hv, vL | vR⟩
  · refine ⟨C.rightVars i, C.rightGates i, (wf i).2, ?_⟩
    intro U hU
    exact (gate_spec C wf U i).trans
      ⟨fun h => h.2, fun h => ⟨Or.inl ⟨v, vL, hU hv⟩, h⟩⟩
  · refine ⟨C.leftVars i, C.leftGates i, (wf i).1, ?_⟩
    intro U hU
    exact (gate_spec C wf U i).trans
      ⟨fun h => h.1, fun h => ⟨h, Or.inl ⟨v, vR, hU hv⟩⟩⟩

private theorem pin_remove (T : Finset (Fin n)) (s : ℕ) :
    ∀ (C : AndCountCircuit n), C.size = s → C.WellFormed →
      ∃ D : AndCountCircuit n, D.WellFormed ∧ pinReads D T = ∅ ∧
        D.size + (pinReads C T).card ≤ C.size ∧
        ∀ U : Finset (Fin n), T ⊆ U → D.eval U = C.eval U := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs wf
    by_cases e : pinReads C T = ∅
    · exact ⟨C, wf, e, by simp [e], fun _ _ => rfl⟩
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr e
      obtain ⟨C', f, wf', size, mono, ran, bare, sem⟩ :=
        remove_one C {U : Finset (Fin n) | T ⊆ U} i wf (pin_expandable C wf T i hi)
      have hsub : (pinReads C T).erase i ⊆ (pinReads C' T).image f := by
        intro j hj
        obtain ⟨jne, jmem⟩ := Finset.mem_erase.mp hj
        obtain ⟨k, rfl⟩ := (ran j).mp jne
        obtain ⟨v, hv, hraw⟩ := (mem_pinReads C T (f k)).mp jmem
        exact Finset.mem_image.mpr
          ⟨k, (mem_pinReads C' T k).mpr
            ⟨v, hv, hraw.imp (fun h => (bare k).1 h) (fun h => (bare k).2 h)⟩, rfl⟩
      have hcard : ((pinReads C T).erase i).card ≤ (pinReads C' T).card :=
        (Finset.card_le_card hsub).trans Finset.card_image_le
      have cs := Finset.card_erase_add_one hi
      obtain ⟨D, wd, empty, bound, val⟩ := ih C'.size (by omega) C' rfl wf'
      exact ⟨D, wd, empty, by omega, fun U hU => (val U hU).trans (sem U hU).1⟩

private def relabel (C : AndCountCircuit n)
    (f : Finset (Fin n) → Finset (Fin n)) : AndCountCircuit n :=
  ⟨C.size, fun i => f (C.leftVars i), C.leftGates, fun i => f (C.rightVars i),
    C.rightGates, f C.outVars, C.outGates⟩

private abbrev hit (U B : Finset (Fin n)) : Prop := ∃ v ∈ B, v ∈ U

private theorem eval_relabel (C : AndCountCircuit n) (f : Finset (Fin n) → Finset (Fin n))
    (U V : Finset (Fin n))
    (l : ∀ i, hit U (f (C.leftVars i)) ↔ hit V (C.leftVars i))
    (r : ∀ i, hit U (f (C.rightVars i)) ↔ hit V (C.rightVars i))
    (o : hit U (f C.outVars) ↔ hit V C.outVars) :
    (relabel C f).eval U = C.eval V := by
  have fuel (d : ℕ) (i : Fin C.size) :
      (relabel C f).gateValFuel U d i = C.gateValFuel V d i := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      change
        (AndCountCircuit.sideTrue U (f (C.leftVars i)) (C.leftGates i) i
          ((relabel C f).gateValFuel U d) &&
        AndCountCircuit.sideTrue U (f (C.rightVars i)) (C.rightGates i) i
          ((relabel C f).gateValFuel U d)) = _
      rw [show (relabel C f).gateValFuel U d = C.gateValFuel V d from funext ih]
      have side (B : Finset (Fin n)) (S : Finset (Fin C.size))
          (h : hit U (f B) ↔ hit V B) :
          AndCountCircuit.sideTrue U (f B) S i (C.gateValFuel V d) =
          AndCountCircuit.sideTrue V B S i (C.gateValFuel V d) := by
        unfold AndCountCircuit.sideTrue
        exact decide_eq_decide.mpr (or_congr h Iff.rfl)
      rw [side _ _ (l i), side _ _ (r i)] <;> rfl
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  change (hit U (f C.outVars) ∨
      ∃ j ∈ C.outGates, (relabel C f).gateValFuel U C.size j = true) ↔
    (hit V C.outVars ∨ ∃ j ∈ C.outGates, C.gateValFuel V C.size j = true)
  exact or_congr o (by simp only [fuel])

private theorem hit_mask_union (T F U B : Finset (Fin n))
    (none : ¬ hit T B) : hit U (B \ F) ↔ hit (T ∪ (U \ F)) B := by
  constructor
  · rintro ⟨v, hv, vu⟩
    obtain ⟨vb, vf⟩ := Finset.mem_sdiff.mp hv
    exact ⟨v, vb, Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨vu, vf⟩)⟩
  · rintro ⟨v, vb, h⟩
    rcases Finset.mem_union.mp h with vt | vuf
    · exact (none ⟨v, vb, vt⟩).elim
    · obtain ⟨vu, vf⟩ := Finset.mem_sdiff.mp vuf
      exact ⟨v, Finset.mem_sdiff.mpr ⟨vb, vf⟩, vu⟩

theorem pin_exists (C : AndCountCircuit n) (wf : C.WellFormed)
    (T F : Finset (Fin n)) (hT : C.eval T = false) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.size + {i : Fin C.size | ∃ v ∈ T, v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ C.size ∧
      ∀ U, D.eval U = C.eval (T ∪ (U \ F)) := by
  obtain ⟨E, ew, empty, bound, sem⟩ := pin_remove T C.size C rfl wf
  have l (i : Fin E.size) : ¬ hit T (E.leftVars i) := by
    rintro ⟨v, vl, vt⟩
    have hh := (mem_pinReads E T i).mpr ⟨v, vt, Or.inl vl⟩
    simp only [empty, Finset.notMem_empty] at hh
  have r (i : Fin E.size) : ¬ hit T (E.rightVars i) := by
    rintro ⟨v, vr, vt⟩
    have hh := (mem_pinReads E T i).mpr ⟨v, vt, Or.inr vr⟩
    simp only [empty, Finset.notMem_empty] at hh
  have o : ¬ hit T E.outVars := by
    intro h
    have et := (sem T (fun _ ht => ht)).trans hT
    have tt : E.eval T = true := by
      unfold AndCountCircuit.eval
      exact decide_eq_true (Or.inl h)
    rw [et] at tt
    contradiction
  refine ⟨relabel E (fun B => B \ F), ew, ?_, ?_⟩
  · rw [← pinReads_card]
    exact bound
  · intro U
    exact (eval_relabel E (fun B => B \ F) U (T ∪ (U \ F))
      (fun i => hit_mask_union T F U _ (l i))
      (fun i => hit_mask_union T F U _ (r i))
      (hit_mask_union T F U _ o)).trans
        (sem _ (fun _ ht => Finset.mem_union_left _ ht))

end Pin

namespace Pin

open PEqualNP.AndCount

variable {n m : ℕ}

/-- Keep the same vertex type. Vertices outside A become isolated. -/
def activeGraph (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj a b := a ∈ A ∧ b ∈ A ∧ G.Adj a b
  symm := ⟨fun a b h => ⟨h.2.1, h.1, G.symm.symm a b h.2.2⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.2.2⟩

theorem activeGraph_adj (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a b : Fin n) :
    (activeGraph G A).Adj a b ↔ a ∈ A ∧ b ∈ A ∧ G.Adj a b := Iff.rfl

theorem activeGraph_univ (G : SimpleGraph (Fin n)) : activeGraph G Finset.univ = G := by
  ext a b
  simp [activeGraph_adj]

/-- All true-pinned vertices and their neighbors, computed in the ambient graph. -/
def closedPin (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v ∈ T ∨ ∃ t ∈ T, G.Adj t v)

theorem mem_closedPin (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (v : Fin n) :
    v ∈ closedPin G T ↔ v ∈ T ∨ ∃ t ∈ T, G.Adj t v := by
  simp [closedPin]

theorem mem_closedPin_singleton (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) : w ∈ closedPin G {v} ↔ w = v ∨ G.Adj v w := by
  simp [mem_closedPin]

abbrev HasEdge (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : Prop :=
  ∃ a ∈ U, ∃ b ∈ U, G.Adj a b

abbrev Independent (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b

theorem singleton_independent (G : SimpleGraph (Fin n)) (v : Fin n) :
    Independent G {v} := by
  intro a ha b hb
  have ea := Finset.mem_singleton.mp ha
  have eb := Finset.mem_singleton.mp hb
  subst a
  subst b
  exact G.loopless.irrefl v

theorem edges_on_cofactor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T U : Finset (Fin n)) (ind : Independent G T) :
    HasEdge (activeGraph G A) (T ∪ (U \ closedPin G T)) ↔
      HasEdge (activeGraph G (A \ closedPin G T)) U := by
  constructor
  · rintro ⟨a, ha, b, hb, hadj⟩
    obtain ⟨aa, bb, ab⟩ := (activeGraph_adj G A a b).mp hadj
    have aout : a ∉ T := by
      intro atT
      rcases Finset.mem_union.mp hb with bt | bf
      · exact ind a atT b bt ab
      · exact (Finset.mem_sdiff.mp bf).2
          ((mem_closedPin G T b).mpr (Or.inr ⟨a, atT, ab⟩))
    have bout : b ∉ T := by
      intro bt
      rcases Finset.mem_union.mp ha with atT | af
      · exact ind a atT b bt ab
      · exact (Finset.mem_sdiff.mp af).2
          ((mem_closedPin G T a).mpr (Or.inr ⟨b, bt, G.symm.symm a b ab⟩))
    have af := Finset.mem_sdiff.mp ((Finset.mem_union.mp ha).resolve_left aout)
    have bf := Finset.mem_sdiff.mp ((Finset.mem_union.mp hb).resolve_left bout)
    exact ⟨a, af.1, b, bf.1, (activeGraph_adj G _ a b).mpr
      ⟨Finset.mem_sdiff.mpr ⟨aa, af.2⟩, Finset.mem_sdiff.mpr ⟨bb, bf.2⟩, ab⟩⟩
  · rintro ⟨a, ha, b, hb, hadj⟩
    obtain ⟨aa, bb, ab⟩ := (activeGraph_adj G _ a b).mp hadj
    obtain ⟨aA, af⟩ := Finset.mem_sdiff.mp aa
    obtain ⟨bA, bf⟩ := Finset.mem_sdiff.mp bb
    exact ⟨a, Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨ha, af⟩),
      b, Finset.mem_union_right T (Finset.mem_sdiff.mpr ⟨hb, bf⟩),
      (activeGraph_adj G A a b).mpr ⟨aA, bA, ab⟩⟩

/-- One cofactor step. The size credit counts distinct AND gates, not raw slots. -/
theorem pin_active (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T : Finset (Fin n)) (wf : C.WellFormed) (comp : C.Computes (activeGraph G A))
    (ind : Independent G T) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.Computes (activeGraph G (A \ closedPin G T)) ∧
      D.size + (pinReads C T).card ≤ C.size := by
  have hT : C.eval T = false := by
    apply Bool.eq_false_of_ne_true
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := (comp T).mp h
    exact ind a ha b hb ((activeGraph_adj G A a b).mp hab).2.2
  obtain ⟨D, wd, bound, sem⟩ := pin_exists C wf T (closedPin G T) hT
  refine ⟨D, wd, ?_, ?_⟩
  · intro U
    rw [sem U]
    exact (comp _).trans (edges_on_cofactor G A T U ind)
  · simpa only [pinReads_card C T] using bound

theorem pin_graph (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : Finset (Fin n)) (wf : C.WellFormed) (comp : C.Computes G) (ind : Independent G T) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.Computes (activeGraph G (Finset.univ \ closedPin G T)) ∧
      D.size + (pinReads C T).card ≤ C.size :=
  pin_active C G Finset.univ T wf (by simpa only [activeGraph_univ] using comp) ind

-- The fuel induction is the dimension-changing form of the checked Pin's bare-side congruence.
private def relabelAcross (C : AndCountCircuit n)
    (f : Finset (Fin n) → Finset (Fin m)) : AndCountCircuit m :=
  ⟨C.size, fun i => f (C.leftVars i), C.leftGates, fun i => f (C.rightVars i),
    C.rightGates, f C.outVars, C.outGates⟩

private abbrev bareHit {s : ℕ} (U B : Finset (Fin s)) : Prop := ∃ v ∈ B, v ∈ U

private theorem eval_across (C : AndCountCircuit n) (f : Finset (Fin n) → Finset (Fin m))
    (U : Finset (Fin m)) (V : Finset (Fin n))
    (l : ∀ i, bareHit U (f (C.leftVars i)) ↔ bareHit V (C.leftVars i))
    (r : ∀ i, bareHit U (f (C.rightVars i)) ↔ bareHit V (C.rightVars i))
    (o : bareHit U (f C.outVars) ↔ bareHit V C.outVars) :
    (relabelAcross C f).eval U = C.eval V := by
  have fuel (d : ℕ) (i : Fin C.size) :
      (relabelAcross C f).gateValFuel U d i = C.gateValFuel V d i := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      change
        (AndCountCircuit.sideTrue U (f (C.leftVars i)) (C.leftGates i) i
          ((relabelAcross C f).gateValFuel U d) &&
        AndCountCircuit.sideTrue U (f (C.rightVars i)) (C.rightGates i) i
          ((relabelAcross C f).gateValFuel U d)) = _
      rw [show (relabelAcross C f).gateValFuel U d = C.gateValFuel V d from funext ih]
      have side (B : Finset (Fin n)) (S : Finset (Fin C.size))
          (h : bareHit U (f B) ↔ bareHit V B) :
          AndCountCircuit.sideTrue U (f B) S i (C.gateValFuel V d) =
          AndCountCircuit.sideTrue V B S i (C.gateValFuel V d) := by
        unfold AndCountCircuit.sideTrue
        exact decide_eq_decide.mpr (or_congr h Iff.rfl)
      rw [side _ _ (l i), side _ _ (r i)]
      rfl
  unfold AndCountCircuit.eval
  rw [decide_eq_decide]
  change (bareHit U (f C.outVars) ∨
      ∃ j ∈ C.outGates, (relabelAcross C f).gateValFuel U C.size j = true) ↔
    (bareHit V C.outVars ∨ ∃ j ∈ C.outGates, C.gateValFuel V C.size j = true)
  exact or_congr o (by simp only [fuel])

/-- Relabel bare vertices and preserve all AND indices, refs, and gate count. -/
def transport (C : AndCountCircuit n) (e : Fin n ≃ Fin m) : AndCountCircuit m :=
  relabelAcross C (fun B => B.map e.toEmbedding)

theorem transport_size (C : AndCountCircuit n) (e : Fin n ≃ Fin m) :
    (transport C e).size = C.size := rfl

theorem transport_wf (C : AndCountCircuit n) (e : Fin n ≃ Fin m) (wf : C.WellFormed) :
    (transport C e).WellFormed := wf

private theorem hit_transport (e : Fin n ≃ Fin m) (U : Finset (Fin m)) (B : Finset (Fin n)) :
    bareHit U (B.map e.toEmbedding) ↔ bareHit (U.map e.symm.toEmbedding) B := by
  constructor
  · rintro ⟨v, vb, vu⟩
    exact ⟨e.symm v, Finset.mem_map_equiv.mp vb,
      Finset.mem_map_equiv.mpr (by simpa only [Equiv.symm_symm, Equiv.apply_symm_apply] using vu)⟩
  · rintro ⟨v, vb, vu⟩
    exact ⟨e v, Finset.mem_map_equiv.mpr (by simpa only [Equiv.symm_apply_apply] using vb),
      by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using vu⟩

theorem transport_eval (C : AndCountCircuit n) (e : Fin n ≃ Fin m) (U : Finset (Fin m)) :
    (transport C e).eval U = C.eval (U.map e.symm.toEmbedding) :=
  eval_across C (fun B => B.map e.toEmbedding) U _ (fun _ => hit_transport e U _)
    (fun _ => hit_transport e U _) (hit_transport e U _)

theorem transport_computes (C : AndCountCircuit n)
    (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (e : Fin n ≃ Fin m)
    (adj : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b) (comp : C.Computes G) :
    (transport C e).Computes H := by
  intro U
  rw [transport_eval, comp (U.map e.symm.toEmbedding)]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨e a, by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using ha,
      e b, by simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hb, (adj a b).mpr hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    have ha' : e.symm a ∈ U.map e.symm.toEmbedding := Finset.mem_map.mpr ⟨a, ha, rfl⟩
    have hb' : e.symm b ∈ U.map e.symm.toEmbedding := Finset.mem_map.mpr ⟨b, hb, rfl⟩
    exact ⟨e.symm a, ha', e.symm b, hb', (adj _ _).mp
      (by simpa only [Equiv.apply_symm_apply] using hab)⟩

abbrev Lower (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ (C : AndCountCircuit n), C.WellFormed → C.Computes G → k ≤ C.size

theorem lower_transport (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (e : Fin n ≃ Fin m)
    (adj : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b) {k : ℕ} (low : Lower G k) :
    Lower H k := by
  have inv (a b : Fin m) : G.Adj (e.symm a) (e.symm b) ↔ H.Adj a b := by
    simpa only [Equiv.apply_symm_apply] using (adj (e.symm a) (e.symm b)).symm
  intro C wf comp
  exact low (transport C e.symm) (transport_wf C _ wf) (transport_computes C H G e.symm inv comp)

private theorem outVars_empty (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (comp : C.Computes G) : C.outVars = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  have tr : C.eval {v} = true := by
    unfold AndCountCircuit.eval
    exact decide_eq_true (Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (comp _).mp tr
  have ea := Finset.mem_singleton.mp ha
  have eb := Finset.mem_singleton.mp hb
  exact G.loopless.irrefl v (by simpa only [ea, eb] using hab)

private theorem miss_insert {v : Fin n} {U B : Finset (Fin n)} (nov : v ∉ B) :
    bareHit (insert v U) B ↔ bareHit U B := by
  constructor
  · rintro ⟨w, wb, hu⟩
    rcases Finset.mem_insert.mp hu with eq | wu
    · subst w
      exact (nov wb).elim
    · exact ⟨w, wb, wu⟩
  · rintro ⟨w, wb, wu⟩
    exact ⟨w, wb, Finset.mem_insert_of_mem wu⟩

theorem useful_read_pos (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (comp : C.Computes G) (v : Fin n) (hn : ∃ w, G.Adj v w) :
    0 < (pinReads C {v}).card := by
  apply Finset.card_pos.mpr
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h0
  have notread (i : Fin C.size) : ¬ (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) := by
    intro h
    have hi := (mem_pinReads C {v} i).mpr ⟨v, Finset.mem_singleton_self v, h⟩
    simp only [h0, Finset.notMem_empty] at hi
  obtain ⟨w, adj⟩ := hn
  have o := outVars_empty C G comp
  have same : C.eval (insert v {w}) = C.eval {w} := by
    have h := eval_across C id (insert v {w}) {w}
      (fun i => miss_insert (fun hv => notread i (Or.inl hv)))
      (fun i => miss_insert (fun hv => notread i (Or.inr hv)))
      (by
        simp only [id, o]
        constructor
        · rintro ⟨x, hx, _⟩
          exact (Finset.notMem_empty x hx).elim
        · rintro ⟨x, hx, _⟩
          exact (Finset.notMem_empty x hx).elim)
    exact h
  have yes : C.eval (insert v {w}) = true :=
    (comp _).mpr ⟨v, Finset.mem_insert_self v _, w,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self w), adj⟩
  have no : C.eval {w} ≠ true := by
    intro hw
    obtain ⟨a, ha, b, hb, ab⟩ := (comp _).mp hw
    have ea := Finset.mem_singleton.mp ha
    have eb := Finset.mem_singleton.mp hb
    exact G.loopless.irrefl w (by simpa only [ea, eb] using ab)
  exact no (same.symm.trans yes)

/-- k useful singleton pins in order, on the active graph remaining at each step. -/
inductive Chain (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ → Finset (Fin n) → Prop
  | nil (A) : Chain G 0 A
  | cons {k A} (v : Fin n) (hv : v ∈ A) (hn : ∃ w ∈ A, G.Adj v w)
      (tail : Chain G k (A \ closedPin G {v})) : Chain G (k + 1) A

theorem chain_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k : ℕ} {A : Finset (Fin n)} (h : Chain G k A) : Lower (activeGraph G A) k := by
  induction h with
  | nil A =>
    intro C _ _
    exact Nat.zero_le C.size
  | cons v hv hn tail ih =>
    intro C wf comp
    obtain ⟨D, wd, dc, bound⟩ :=
      pin_active C G _ {v} wf comp (singleton_independent G v)
    have pos := useful_read_pos C _ comp v (by
      obtain ⟨w, hw, adj⟩ := hn
      exact ⟨w, hv, hw, adj⟩)
    have lower := ih D wd dc
    omega

end Pin

namespace Slot

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Fuel stabilization follows merged L-meta-707, which credits L-meta-564.

private theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j : Fin k, j < i → val j = val' j) :
    AndCountCircuit.sideTrue U B F i val = AndCountCircuit.sideTrue U B F i val' := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_decide]
  constructor
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hlt, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩

private theorem fuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d d' : ℕ) (i : Fin C.size), i.val < d → i.val < d' →
      C.gateValFuel U d i = C.gateValFuel U d' i := by
  intro d
  induction d with
  | zero =>
    intro d' i h
    exact absurd h (Nat.not_lt_zero _)
  | succ e ih =>
    intro d' i h h'
    cases d' with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ e' =>
      have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateValFuel U e' j := by
        intro j hj
        have hji : j.val < i.val := hj
        exact ih e' j (by omega) (by omega)
      show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) =
        (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e') &&
          AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e'))
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

private theorem gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hi : i.val < C.size := i.2
  obtain ⟨e, he⟩ : ∃ e, C.size = e + 1 := ⟨C.size - 1, by omega⟩
  have key : ∀ j : Fin C.size, j < i → C.gateValFuel U e j = C.gateVal U j := by
    intro j hj
    have hji : j.val < i.val := hj
    exact fuel_indep C U e C.size j (by omega) j.2
  have h1 : C.gateVal U i = C.gateValFuel U (e + 1) i :=
    fuel_indep C U C.size (e + 1) i i.2 (by omega)
  rw [h1]
  show (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U e) &&
      AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U e)) = _
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ key,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ key]

variable {n : ℕ}

abbrev Side (C : AndCountCircuit n) := Fin C.size × Bool

def raw (C : AndCountCircuit n) (s : Side C) : Finset (Fin n) :=
  if s.2 then C.rightVars s.1 else C.leftVars s.1

def prev (C : AndCountCircuit n) (s : Side C) : Finset (Fin C.size) :=
  if s.2 then C.rightGates s.1 else C.leftGates s.1

def other (C : AndCountCircuit n) (s : Side C) : Side C := (s.1, !s.2)

def hits (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Side C) : Prop :=
  ∃ v ∈ raw C s, v ∈ U

def sval (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Side C) : Bool :=
  sideTrue U (raw C s) (prev C s) s.1 (C.gateVal U)

lemma ne_other (C : AndCountCircuit n) (s : Side C) : other C s ≠ s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [other]

lemma hit_insert (C : AndCountCircuit n) (U : Finset (Fin n)) (v : Fin n) (s : Side C) :
    hits C (insert v U) s ↔ hits C U s ∨ v ∈ raw C s := by
  simp only [hits, Finset.mem_insert]
  constructor
  · rintro ⟨a, ha, eq | hm⟩
    · exact Or.inr (eq ▸ ha)
    · exact Or.inl ⟨a, ha, hm⟩
  · rintro (⟨a, ha, hm⟩ | hv)
    · exact ⟨a, ha, Or.inr hm⟩
    · exact ⟨v, hv, Or.inl rfl⟩

lemma hit_singleton (C : AndCountCircuit n) (v : Fin n) (s : Side C) :
    hits C {v} s ↔ v ∈ raw C s := by
  simp only [hits, Finset.mem_singleton, exists_eq_right]

lemma sval_congr (C : AndCountCircuit n) (U V : Finset (Fin n)) (s : Side C)
    (hh : hits C U s ↔ hits C V s)
    (hp : ∀ j : Fin C.size, j < s.1 → C.gateVal U j = C.gateVal V j) :
    sval C U s = sval C V s := by
  unfold sval
  rw [sideTrue_congr U (raw C s) (prev C s) s.1 _ _ hp]
  simp only [sideTrue, decide_eq_decide]
  exact or_congr hh Iff.rfl

lemma gate_eq_sval (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sval C U (i,false) && sval C U (i,true)) := by
  rw [gateVal_eq C U i]
  rfl

lemma gate_congr (C : AndCountCircuit n) (U V : Finset (Fin n)) (i : Fin C.size)
    (hL : hits C U (i,false) ↔ hits C V (i,false))
    (hR : hits C U (i,true) ↔ hits C V (i,true))
    (hp : ∀ j : Fin C.size, j < i → C.gateVal U j = C.gateVal V j) :
    C.gateVal U i = C.gateVal V i := by
  rw [gate_eq_sval C U i, gate_eq_sval C V i,
    sval_congr C U V (i,false) hL hp, sval_congr C U V (i,true) hR hp]

lemma eval_congr (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hout : C.outVars = ∅) (hv : ∀ i : Fin C.size, C.gateVal U i = C.gateVal V i) :
    C.eval U = C.eval V := by
  simp only [AndCountCircuit.eval, hout, Finset.notMem_empty, false_and, exists_false,
    false_or, hv]

lemma eval_eq_of_hits (C : AndCountCircuit n) (U V : Finset (Fin n))
    (hout : C.outVars = ∅)
    (hh : ∀ s : Side C, hits C U s ↔ hits C V s) : C.eval U = C.eval V := by
  apply eval_congr C U V hout
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    exact gate_congr C U V i (hh (i,false)) (hh (i,true)) ih

lemma same_before_if (C : AndCountCircuit n) (U V : Finset (Fin n))
    (s : Side C) (hH : ∀ t : Side C, t ≠ s → (hits C U t ↔ hits C V t)) :
    ∀ i : Fin C.size, i < s.1 → C.gateVal U i = C.gateVal V i := by
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    intro hi
    have ne (b : Bool) : (i,b) ≠ s := fun e =>
      (ne_of_lt hi) (congrArg Prod.fst e)
    exact gate_congr C U V i (hH (i,false) (ne false)) (hH (i,true) (ne true))
      (fun j hj => ih j hj (hj.trans hi))

lemma pivot_gate (C : AndCountCircuit n) (U V : Finset (Fin n))
    (s : Side C) (hout : C.outVars = ∅)
    (hH : ∀ t : Side C, t ≠ s → (hits C U t ↔ hits C V t))
    (hne : C.eval U ≠ C.eval V) : C.gateVal U s.1 ≠ C.gateVal V s.1 := by
  intro hEq
  apply hne
  apply eval_congr C U V hout
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    by_cases hi : i = s.1
    · simpa only [hi] using hEq
    · have ne (b : Bool) : (i,b) ≠ s := fun e => hi (congrArg Prod.fst e)
      exact gate_congr C U V i (hH (i,false) (ne false)) (hH (i,true) (ne true)) ih

lemma pivot_other (C : AndCountCircuit n) (U V : Finset (Fin n))
    (s : Side C) (hout : C.outVars = ∅)
    (hH : ∀ t : Side C, t ≠ s → (hits C U t ↔ hits C V t))
    (hne : C.eval U ≠ C.eval V) : sval C U (other C s) = true := by
  have gates := pivot_gate C U V s hout hH hne
  have hop := sval_congr C U V (other C s) (hH _ (ne_other C s))
    (same_before_if C U V s hH)
  have f (h : sval C U (other C s) = false) : False := by
    have hv : sval C V (other C s) = false := hop.symm.trans h
    apply gates
    rcases s with ⟨i,b⟩
    cases b <;>
      simp only [other, Bool.not_false, Bool.not_true] at h hv <;>
      simp [gate_eq_sval, h, hv]
  cases h : sval C U (other C s)
  · exact (f h).elim
  · rfl

def positions (C : AndCountCircuit n) (v : Fin n) : Finset (Side C) :=
  Finset.univ.filter (fun s => v ∈ raw C s)

lemma mem_positions (C : AndCountCircuit n) (v : Fin n) (s : Side C) :
    s ∈ positions C v ↔ v ∈ raw C s := by simp [positions]

def readers (C : AndCountCircuit n) (v : Fin n) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)

lemma mem_readers (C : AndCountCircuit n) (v : Fin n) (i : Fin C.size) :
    i ∈ readers C v ↔ v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by simp [readers]

lemma positions_image (C : AndCountCircuit n) (v : Fin n) :
    (positions C v).image Prod.fst = readers C v := by
  ext i
  simp only [Finset.mem_image, mem_positions, mem_readers]
  constructor
  · rintro ⟨⟨j,b⟩, hj, rfl⟩
    cases b
    · exact Or.inl (by simpa [raw] using hj)
    · exact Or.inr (by simpa [raw] using hj)
  · rintro (hl | hr)
    · exact ⟨(i,false), by simpa [raw] using hl, rfl⟩
    · exact ⟨(i,true), by simpa [raw] using hr, rfl⟩

lemma positions_card (C : AndCountCircuit n) (v : Fin n)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    (positions C v).card = (readers C v).card := by
  rw [← positions_image]
  symm
  apply Finset.card_image_of_injOn
  rintro ⟨i,b⟩ hb ⟨j,c⟩ hc (e : i = j)
  subst j
  rw [Finset.mem_coe, mem_positions] at hb hc
  cases b <;> cases c <;> simp only [raw, Bool.false_eq_true, ite_false, ite_true] at hb hc
  · rfl
  · exact (Finset.disjoint_left.mp (hd i) hb hc).elim
  · exact (Finset.disjoint_left.mp (hd i) hc hb).elim
  · rfl

lemma readers_ncard (C : AndCountCircuit n) (v : Fin n) :
    {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard =
      (readers C v).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  exact (mem_readers C v i).symm

lemma hit_unchanged_if_not (C : AndCountCircuit n) (U : Finset (Fin n))
    (v : Fin n) (s : Side C) (hn : v ∉ raw C s) :
    hits C U s ↔ hits C (insert v U) s := by simp [hit_insert, hn]

lemma hit_unchanged_if_already (C : AndCountCircuit n) (U : Finset (Fin n))
    (v : Fin n) (s : Side C) (hh : hits C U s) :
    hits C U s ↔ hits C (insert v U) s := by simp [hit_insert, hh]

lemma separation (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (U : Finset (Fin n)) (v w : Fin n) (hw : w ∈ U)
    (hind : ∀ a ∈ U, ∀ b ∈ U, ¬ G.Adj a b) (ha : G.Adj v w) :
    ∃ s : Side C, v ∈ raw C s ∧ ¬ hits C U s := by
  classical
  by_contra! bad
  have he := eval_eq_of_hits C U (insert v U) ho (fun s => by
    by_cases hs : v ∈ raw C s
    · exact hit_unchanged_if_already C U v s (bad s hs)
    · exact hit_unchanged_if_not C U v s hs)
  have hz : C.eval U = false := Bool.eq_false_iff.mpr (fun hy => by
    obtain ⟨a, ham, b, hbm, hab⟩ := (hc U).mp hy
    exact hind a ham b hbm hab)
  have hy : C.eval (insert v U) = true :=
    (hc _).mpr ⟨v, by simp, w, Finset.mem_insert_of_mem hw, ha⟩
  simpa [hz, hy] using he

lemma some_position (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅) {v w : Fin n} (h : G.Adj v w) :
    (positions C v).Nonempty := by
  obtain ⟨s, hm, _⟩ := separation G C hc ho {w} v w (by simp) (by simp) h
  exact ⟨s, (mem_positions C v s).mpr hm⟩

lemma unique_position_neighbor (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (hs : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false)
    {v w : Fin n} (h : G.Adj v w) (s : Side C) (just : positions C v = {s}) :
    w ∈ raw C (other C s) := by
  have hz : C.eval {w} = false := Bool.eq_false_iff.mpr (fun hy => by
    obtain ⟨a, ham, b, hbm, hab⟩ := (hc {w}).mp hy
    simp only [Finset.mem_singleton] at ham hbm
    subst a
    subst b
    exact G.loopless.irrefl w hab)
  have hy : C.eval (insert v {w}) = true :=
    (hc _).mpr ⟨v, by simp, w, by simp, h⟩
  have hH (t : Side C) (ht : t ≠ s) : hits C {w} t ↔ hits C (insert v {w}) t := by
    apply hit_unchanged_if_not
    intro hmem
    have hh := (mem_positions C v t).mpr hmem
    rw [just, Finset.mem_singleton] at hh
    exact ht hh
  have hp := pivot_other C {w} (insert v {w}) s ho hH (by simp [hz,hy])
  change sideTrue {w} (raw C (other C s)) (prev C (other C s))
    (other C s).1 (C.gateVal {w}) = true at hp
  simp only [sideTrue, decide_eq_true_eq, hs, Bool.false_eq_true, and_false,
    exists_false, or_false, Finset.mem_singleton, exists_eq_right] at hp
  exact hp

lemma uniform_singletons (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (hs : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false)
    (color : Fin n → Bool)
    (cross : ∀ {v w}, G.Adj v w → color v ≠ color w)
    {v w : Fin n} (col : color v = color w)
    (nbv : ∃ u, G.Adj v u) (nbw : ∃ u, G.Adj w u)
    (diff : ∃ u, (G.Adj v u ∧ ¬ G.Adj w u) ∨ (G.Adj w u ∧ ¬ G.Adj v u))
    (s t : Side C) (hv : positions C v = {s}) (hw : positions C w = {t}) :
    s.1 ≠ t.1 := by
  intro hgate
  have ne : s ≠ t := by
    intro hst
    obtain ⟨u, hd | hd⟩ := diff
    · have hz : C.eval {w,u} = false := Bool.eq_false_iff.mpr (fun hy => by
        obtain ⟨a, ha, b, hb, hab⟩ := (hc _).mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact G.loopless.irrefl _ hab
        · exact hd.2 hab
        · exact hd.2 hab.symm
        · exact G.loopless.irrefl _ hab)
      have hy : C.eval {v,u} = true := (hc _).mpr ⟨v, by simp, u, by simp, hd.1⟩
      have hh (r : Side C) : v ∈ raw C r ↔ w ∈ raw C r := by
        rw [← mem_positions, ← mem_positions, hv, hw, hst]
      have eq := eval_eq_of_hits C {v,u} {w,u} ho (fun r => by
        rw [hit_insert, hit_insert, hh])
      simpa [hz,hy] using eq
    · have hz : C.eval {v,u} = false := Bool.eq_false_iff.mpr (fun hy => by
        obtain ⟨a, ha, b, hb, hab⟩ := (hc _).mp hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact G.loopless.irrefl _ hab
        · exact hd.2 hab
        · exact hd.2 hab.symm
        · exact G.loopless.irrefl _ hab)
      have hy : C.eval {w,u} = true := (hc _).mpr ⟨w, by simp, u, by simp, hd.1⟩
      have hh (r : Side C) : v ∈ raw C r ↔ w ∈ raw C r := by
        rw [← mem_positions, ← mem_positions, hv, hw, hst]
      have eq := eval_eq_of_hits C {v,u} {w,u} ho (fun r => by
        rw [hit_insert, hit_insert, hh])
      simpa [hz,hy] using eq
  have et : t = other C s := by
    rcases s with ⟨i,b⟩
    rcases t with ⟨j,d⟩
    change i = j at hgate
    subst j
    cases b <;> cases d <;> first | rfl | exact (ne rfl).elim
  have es : s = other C t := by
    rw [et]
    rcases s with ⟨i,b⟩
    cases b <;> rfl
  obtain ⟨a, ha⟩ := nbv
  obtain ⟨b, hb⟩ := nbw
  have aT : a ∈ raw C t := by rw [et]; exact unique_position_neighbor G C hc ho hs ha s hv
  have bS : b ∈ raw C s := by rw [es]; exact unique_position_neighbor G C hc ho hs hb t hw
  have sameAB : color a = color b := by
    calc
      color a = !(color v) := Bool.eq_not_of_ne (cross ha).symm
      _ = !(color w) := congrArg Bool.not col
      _ = color b := (Bool.eq_not_of_ne (cross hb).symm).symm
  have hind : ∀ x ∈ ({a,b} : Finset (Fin n)), ∀ y ∈ ({a,b} : Finset (Fin n)), ¬ G.Adj x y := by
    intro x hx y hy h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hxC : color x = color a := hx.elim (fun e => congrArg color e)
      (fun e => (congrArg color e).trans sameAB.symm)
    have hyC : color y = color a := hy.elim (fun e => congrArg color e)
      (fun e => (congrArg color e).trans sameAB.symm)
    exact cross h (hxC.trans hyC.symm)
  obtain ⟨r, hr, hnone⟩ := separation G C hc ho {a,b} v a (by simp) hind ha
  have eq : r = s := by
    have h := (mem_positions C v r).mpr hr
    simpa only [hv, Finset.mem_singleton] using h
  rw [eq] at hnone
  exact hnone ⟨b, bS, by simp⟩

lemma uniform_one_count (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅)
    (hs : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (color : Fin n → Bool)
    (cross : ∀ {v w}, G.Adj v w → color v ≠ color w)
    (T : Finset (Fin n)) (b : Bool) (col : ∀ v ∈ T, color v = b)
    (nb : ∀ v ∈ T, ∃ w, G.Adj v w)
    (diff : ∀ v ∈ T, ∀ w ∈ T, v ≠ w →
      ∃ u, (G.Adj v u ∧ ¬G.Adj w u) ∨ (G.Adj w u ∧ ¬G.Adj v u))
    (one : ∀ v ∈ T, (readers C v).card = 1) :
    T.card ≤ C.size := by
  classical
  have pick (v : {v // v ∈ T}) : ∃ s, positions C v.1 = {s} := by
    apply Finset.card_eq_one.mp
    rw [positions_card C v.1 hd]
    exact one v.1 v.2
  let index (v : {v // v ∈ T}) : Fin C.size := (Classical.choose (pick v)).1
  have inj : Function.Injective index := by
    intro v w hix
    apply Subtype.ext
    by_contra h
    exact uniform_singletons G C hc ho hs color cross
      ((col v.1 v.2).trans (col w.1 w.2).symm) (nb v.1 v.2) (nb w.1 w.2)
      (diff v.1 v.2 w.1 w.2 h) _ _ (Classical.choose_spec (pick v))
      (Classical.choose_spec (pick w)) hix
  simpa using (Fintype.card_le_of_injective index inj)

end Slot
/-! Normalization lemma reused from sanchan, merged L-meta-563 (PR #631), open-goat/pequalnp-proofs
    (lean/PEqualNP/Outside/L_meta_563.lean at upstream baseline 1ebe834).
    Apache 2.0 repository code; only the wrapper and private namespace names are changed.
    The checked proof uses only the base definitions. -/
namespace ActiveNorm.Credited563

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

private lemma strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    cases h : (stripCircuit C).gateVal {v} i
    · rfl
    · exfalso
      rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true] at h
      have hL := h.1
      have hR := h.2
      unfold sideTrue at hL hR
      rw [decide_eq_true_eq] at hL hR
      have hvL : v ∈ (stripCircuit C).leftVars i := by
        rcases hL with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      have hvR : v ∈ (stripCircuit C).rightVars i := by
        rcases hR with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      rw [mem_strip_leftVars] at hvL
      rw [mem_strip_rightVars] at hvR
      apply hvL.2
      rw [gateVal_unfold C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvL.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvR.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

private lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

private lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

private lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩

end ActiveNorm.Credited563

theorem ActiveNorm.normalizeSingleton : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
      C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
      (∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) ∧
      (∀ i : Fin C'.size, Disjoint (C'.leftVars i) (C'.rightVars i)) ∧
      (C.WellFormed → C'.WellFormed) := by
  intro n C
  refine ⟨PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm.Credited563.stripCircuit C, le_refl C.size,
    fun U => PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm.Credited563.strip_eval_eq C U,
    fun i v => PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm.Credited563.strip_singleton_false C v C.size i i.isLt,
    fun i => PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm.Credited563.strip_disjoint C i,
    fun hWF => hWF⟩
/- Append after credited Normalize563, GraphBridge, and SlotStructure.
   Supplies the non-reader, non-geometric Slot.Environment pieces and a constructor.
   The output-bare argument is the outVars half of SaschaAlex’s merged L-meta-561 (PR #610). -/
namespace ActiveNorm

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17134_aux.Generic.Pin

variable {n : Nat}

/-- Keep the index type for AND gates and every gate edge. Restrict only bare vertices. -/
def mask (C : AndCountCircuit n) (A : Finset (Fin n)) : AndCountCircuit n :=
  ⟨C.size, fun i => C.leftVars i ∩ A, C.leftGates, fun i => C.rightVars i ∩ A,
    C.rightGates, C.outVars ∩ A, C.outGates⟩

@[simp] theorem mask_size (C : AndCountCircuit n) (A : Finset (Fin n)) :
    (mask C A).size = C.size := rfl

theorem mask_wf (C : AndCountCircuit n) (A : Finset (Fin n)) (wf : C.WellFormed) :
    (mask C A).WellFormed := wf

private abbrev Hits (U B : Finset (Fin n)) : Prop := ∃ v ∈ B, v ∈ U

private theorem hits_mask (U B A : Finset (Fin n)) :
    Hits U (B ∩ A) ↔ Hits (U ∩ A) B := by
  constructor
  · rintro ⟨v, hv, hu⟩
    obtain ⟨hB,hA⟩ := Finset.mem_inter.mp hv
    exact ⟨v,hB,Finset.mem_inter.mpr ⟨hu,hA⟩⟩
  · rintro ⟨v,hB,hv⟩
    obtain ⟨hu,hA⟩ := Finset.mem_inter.mp hv
    exact ⟨v,Finset.mem_inter.mpr ⟨hB,hA⟩,hu⟩

private theorem side_mask (U B A : Finset (Fin n)) {m : Nat}
    (F : Finset (Fin m)) (i : Fin m) (values : Fin m → Bool) :
    sideTrue U (B ∩ A) F i values = sideTrue (U ∩ A) B F i values := by
  unfold sideTrue
  exact decide_eq_decide.mpr (or_congr (hits_mask U B A) Iff.rfl)

theorem fuel_mask (C : AndCountCircuit n) (A U : Finset (Fin n)) :
    ∀ (d : Nat) (i : Fin C.size),
      (mask C A).gateValFuel U d i = C.gateValFuel (U ∩ A) d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
      intro i
      change
        (sideTrue U (C.leftVars i ∩ A) (C.leftGates i) i
          ((mask C A).gateValFuel U d) &&
         sideTrue U (C.rightVars i ∩ A) (C.rightGates i) i
          ((mask C A).gateValFuel U d)) =
        (sideTrue (U ∩ A) (C.leftVars i) (C.leftGates i) i
          (C.gateValFuel (U ∩ A) d) &&
         sideTrue (U ∩ A) (C.rightVars i) (C.rightGates i) i
          (C.gateValFuel (U ∩ A) d))
      rw [show (mask C A).gateValFuel U d = C.gateValFuel (U ∩ A) d from funext ih]
      simp only [side_mask]

theorem gate_mask (C : AndCountCircuit n) (A U : Finset (Fin n)) (i : Fin C.size) :
    (mask C A).gateVal U i = C.gateVal (U ∩ A) i :=
  fuel_mask C A U C.size i

theorem eval_mask (C : AndCountCircuit n) (A U : Finset (Fin n)) :
    (mask C A).eval U = C.eval (U ∩ A) := by
  unfold AndCountCircuit.eval
  apply decide_eq_decide.mpr
  change (Hits U (C.outVars ∩ A) ∨
      ∃ j ∈ C.outGates, (mask C A).gateVal U j = true) ↔
    (Hits (U ∩ A) C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal (U ∩ A) j = true)
  exact or_congr (hits_mask U C.outVars A) (by simp only [gate_mask])

theorem computes_mask (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (comp : C.Computes (activeGraph G A)) :
    (mask C A).Computes (activeGraph G A) := by
  intro U
  rw [eval_mask, comp]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ⟨a,(Finset.mem_inter.mp ha).1,b,(Finset.mem_inter.mp hb).1,hab⟩
  · rintro ⟨a,ha,b,hb,hab⟩
    have hab' := (activeGraph_adj G A a b).mp hab
    exact ⟨a,Finset.mem_inter.mpr ⟨ha,hab'.1⟩,
      b,Finset.mem_inter.mpr ⟨hb,hab'.2.1⟩,hab⟩

private theorem empty_fuel (C : AndCountCircuit n) :
    ∀ (d : Nat) (i : Fin C.size), C.gateValFuel ∅ d i = false := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
      intro i
      simp only [gateValFuel]
      rw [show C.gateValFuel ∅ d = (fun _ => false) from funext ih]
      simp [sideTrue]

theorem single_mask (C : AndCountCircuit n) (A : Finset (Fin n))
    (clean : ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false) :
    ∀ i : Fin (mask C A).size, ∀ v : Fin n, (mask C A).gateVal {v} i = false := by
  intro i v
  let j : Fin C.size := i
  refine (gate_mask C A {v} j).trans ?_
  by_cases hv : v ∈ A
  · have h : ({v} : Finset (Fin n)) ∩ A = {v} := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro e
        subst w
        exact ⟨rfl,hv⟩
    rw [h]
    exact clean j v
  · have h : ({v} : Finset (Fin n)) ∩ A = ∅ := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨e,hw⟩
      exact hv (e ▸ hw)
    rw [h]
    exact empty_fuel C C.size j

theorem disjoint_mask (C : AndCountCircuit n) (A : Finset (Fin n))
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    ∀ i, Disjoint ((mask C A).leftVars i) ((mask C A).rightVars i) := by
  intro i
  apply Finset.disjoint_left.mpr
  intro v hv hrv
  exact (Finset.disjoint_left.mp (hd i)) (Finset.mem_inter.mp hv).1
    (Finset.mem_inter.mp hrv).1

theorem mask_used (C : AndCountCircuit n) (A : Finset (Fin n)) :
    ∀ s : Slot.Side (mask C A), Slot.raw (mask C A) s ⊆ A := by
  intro s v hv
  rcases s with ⟨i,b⟩
  cases b
  · change v ∈ C.leftVars i ∩ A at hv
    exact (Finset.mem_inter.mp hv).2
  · change v ∈ C.rightVars i ∩ A at hv
    exact (Finset.mem_inter.mp hv).2

/-- The output-bare argument from SaschaAlex’s merged L-meta-561 (PR #610). -/
theorem out_of_computes (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (comp : C.Computes G) :
    C.outVars = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  have tr : C.eval {v} = true := by
    unfold AndCountCircuit.eval
    exact decide_eq_true (Or.inl ⟨v,hv,Finset.mem_singleton_self v⟩)
  obtain ⟨a,ha,b,hb,adj⟩ := (comp {v}).mp tr
  have ea := Finset.mem_singleton.mp ha
  have eb := Finset.mem_singleton.mp hb
  exact G.loopless.irrefl v (by simpa only [ea, eb] using adj)

structure Result (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) where
  circuit : AndCountCircuit n
  size_le : circuit.size ≤ C.size
  wf : circuit.WellFormed
  comp : circuit.Computes (activeGraph G A)
  out : circuit.outVars = ∅
  clean : ∀ i : Fin circuit.size, ∀ v : Fin n, circuit.gateVal {v} i = false
  disjoint : ∀ i, Disjoint (circuit.leftVars i) (circuit.rightVars i)
  used : ∀ s : Slot.Side circuit, Slot.raw circuit s ⊆ A

/-- Normalize singleton behavior before restricting the raw supports.
The old reader sets are deliberately not part of this output. -/
theorem normalizeActive (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (wf : C.WellFormed) (comp : C.Computes (activeGraph G A)) :
    Nonempty (Result C G A) := by
  obtain ⟨D,dsize,deval,dclean,ddisj,dwf⟩ := normalizeSingleton n C
  have dcomp : D.Computes (activeGraph G A) := by
    intro U
    rw [deval U]
    exact comp U
  have d'comp := computes_mask D G A dcomp
  exact ⟨⟨mask D A, dsize, mask_wf D A (dwf wf), d'comp,
    out_of_computes _ _ d'comp, single_mask D A dclean,
    disjoint_mask D A ddisj, mask_used D A⟩⟩

/-- Adapter from Pin's distinct AND reader count to Slot's side positions. -/
theorem pinReads_eq_readers (C : AndCountCircuit n) (v : Fin n) :
    pinReads C {v} = Slot.readers C v := by
  ext i
  simp [mem_pinReads, Slot.mem_readers]

theorem positions_eq_pinReads_card (C : AndCountCircuit n) (v : Fin n)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) :
    (Slot.positions C v).card = (pinReads C {v}).card := by
  rw [Slot.positions_card C v hd, pinReads_eq_readers]
end ActiveNorm
end PEqualNP.Outside.L_meta_17134_aux.Generic

namespace PEqualNP.Outside.L_meta_17134_aux.Compile

open PEqualNP.CircuitLowerBounds PEqualNP.AndCount

def isAndOp (op : GateOp) : Bool :=
  GateOp.casesOn op true false false (fun _ => false) false

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih]
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (a d : α) (w : ℕ) (h : w < l.length) :
    (l ++ [a]).getD w d = l.getD w d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

lemma getD_snoc_gt {α : Type*} (l : List α) (a d : α) (w : ℕ) (h : l.length < w) :
    (l ++ [a]).getD w d = d := by
  rw [List.getD_eq_default]
  simp
  omega

lemma gateValFuel_stable {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d1 d2 : ℕ) (i : Fin A.size), i.val < d1 → i.val < d2 →
      A.gateValFuel U d1 i = A.gateValFuel U d2 i := by
  intro d1
  induction d1 with
  | zero => intro d2 i hi; omega
  | succ d1 ih =>
    intro d2 i h1 h2
    cases d2 with
    | zero => omega
    | succ d2 =>
      simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
      congr 1
      · simp only [decide_eq_decide]
        refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
        constructor
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [← ih d2 j (by omega) (by omega)]; exact hv⟩
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [ih d2 j (by omega) (by omega)]; exact hv⟩
      · simp only [decide_eq_decide]
        refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
        constructor
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [← ih d2 j (by omega) (by omega)]; exact hv⟩
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [ih d2 j (by omega) (by omega)]; exact hv⟩

lemma gateVal_eq {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin A.size) :
    A.gateVal U i =
      (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateVal U) &&
       AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateVal U)) := by
  unfold AndCountCircuit.gateVal
  have h1 : A.gateValFuel U A.size i = A.gateValFuel U (i.val + 1) i :=
    gateValFuel_stable A U A.size (i.val + 1) i i.isLt (by omega)
  rw [h1]
  simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
  congr 1
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    constructor
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U A.size i.val j j.isLt hj]; exact hv⟩
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U i.val A.size j hj j.isLt]; exact hv⟩
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    constructor
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U A.size i.val j j.isLt hj]; exact hv⟩
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U i.val A.size j hj j.isLt]; exact hv⟩

lemma gateValFuel_withOut {n : ℕ} (A : AndCountCircuit n)
    (Bout : Finset (Fin n)) (Fout : Finset (Fin A.size)) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin A.size),
      ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel U d i =
        A.gateValFuel U d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
    have hfn : ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel U d =
        A.gateValFuel U d := funext ih
    rw [hfn]

def evalRep {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) :
    Option (Finset (Fin n) × Finset (Fin A.size)) → Bool
  | none => true
  | some (B, F) => decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, A.gateVal U j = true)

def orRep {n k : ℕ} :
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin k))
  | none, _ => none
  | _, none => none
  | some (B1, F1), some (B2, F2) => some (B1 ∪ B2, F1 ∪ F2)

lemma evalRep_orRep {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n))
    (r1 r2 : Option (Finset (Fin n) × Finset (Fin A.size))) :
    evalRep A U (orRep r1 r2) = (evalRep A U r1 || evalRep A U r2) := by
  cases r1 with
  | none => simp [orRep, evalRep]
  | some p1 =>
    rcases p1 with ⟨B1, F1⟩
    cases r2 with
    | none => simp [orRep, evalRep]
    | some p2 =>
      rcases p2 with ⟨B2, F2⟩
      rw [Bool.eq_iff_iff]
      simp only [orRep, evalRep, decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro (⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩)
        · rcases Finset.mem_union.mp hv with h | h
          · exact Or.inl (Or.inl ⟨v, h, hvu⟩)
          · exact Or.inr (Or.inl ⟨v, h, hvu⟩)
        · rcases Finset.mem_union.mp hj with h | h
          · exact Or.inl (Or.inr ⟨j, h, hju⟩)
          · exact Or.inr (Or.inr ⟨j, h, hju⟩)
      · rintro ((⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩) | (⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩))
        · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvu⟩
        · exact Or.inr ⟨j, Finset.mem_union_left _ hj, hju⟩
        · exact Or.inl ⟨v, Finset.mem_union_right _ hv, hvu⟩
        · exact Or.inr ⟨j, Finset.mem_union_right _ hj, hju⟩

def liftRep {n k : ℕ} :
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin (k + 1)))
  | none => none
  | some (B, F) => some (B, F.map Fin.castSuccEmb)

abbrev snocCircuit {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size)) : AndCountCircuit n where
  size := A.size + 1
  leftVars i := if h : i.val < A.size then A.leftVars ⟨i.val, h⟩ else B1
  leftGates i := if h : i.val < A.size then (A.leftGates ⟨i.val, h⟩).map Fin.castSuccEmb else F1.map Fin.castSuccEmb
  rightVars i := if h : i.val < A.size then A.rightVars ⟨i.val, h⟩ else B2
  rightGates i := if h : i.val < A.size then (A.rightGates ⟨i.val, h⟩).map Fin.castSuccEmb else F2.map Fin.castSuccEmb
  outVars := A.outVars
  outGates := A.outGates.map Fin.castSuccEmb

lemma snocCircuit_wellFormed {n : ℕ} (A : AndCountCircuit n) (hWF : A.WellFormed)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size)) :
    (snocCircuit A B1 F1 B2 F2).WellFormed := by
  intro i
  by_cases hi : i.val < A.size
  · constructor
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact (hWF ⟨i.val, hi⟩).1 j0 hj0
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact (hWF ⟨i.val, hi⟩).2 j0 hj0
  · have hieq : i.val = A.size := by have : i.val < A.size + 1 := i.isLt; omega
    constructor
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, _, rfl⟩
      change j0.val < i.val
      omega
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, _, rfl⟩
      change j0.val < i.val
      omega

lemma snocCircuit_gateVal_castSucc {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) :
    ∀ (k : ℕ) (hk : k < A.size),
      (snocCircuit A B1 F1 B2 F2).gateVal U (Fin.castSucc ⟨k, hk⟩) = A.gateVal U ⟨k, hk⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    rw [gateVal_eq (snocCircuit A B1 F1 B2 F2) U (Fin.castSucc ⟨k, hk⟩), gateVal_eq A U ⟨k, hk⟩]
    simp only [snocCircuit, Fin.val_castSucc, hk, ↓reduceDIte, AndCountCircuit.sideTrue]
    congr 1
    · simp only [decide_eq_decide]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨j, hj, hlt, hval⟩
        rw [Finset.mem_map] at hj
        rcases hj with ⟨j0, hj0, rfl⟩
        have hlt' : j0.val < k := hlt
        refine ⟨j0, hj0, hlt', ?_⟩
        rw [← ih j0.val hlt' j0.isLt]
        exact hval
      · rintro ⟨j0, hj0, hlt, hval⟩
        have hlt' : j0.val < k := hlt
        refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, hlt', ?_⟩
        rw [ih j0.val hlt' j0.isLt]
        exact hval
    · simp only [decide_eq_decide]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨j, hj, hlt, hval⟩
        rw [Finset.mem_map] at hj
        rcases hj with ⟨j0, hj0, rfl⟩
        have hlt' : j0.val < k := hlt
        refine ⟨j0, hj0, hlt', ?_⟩
        rw [← ih j0.val hlt' j0.isLt]
        exact hval
      · rintro ⟨j0, hj0, hlt, hval⟩
        have hlt' : j0.val < k := hlt
        refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, hlt', ?_⟩
        rw [ih j0.val hlt' j0.isLt]
        exact hval

lemma snocCircuit_gateVal_last {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) :
    (snocCircuit A B1 F1 B2 F2).gateVal U (Fin.last A.size) =
      (evalRep A U (some (B1, F1)) && evalRep A U (some (B2, F2))) := by
  rw [gateVal_eq]
  simp only [snocCircuit, Fin.val_last, lt_irrefl, ↓reduceDIte, AndCountCircuit.sideTrue, evalRep]
  congr 1
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, _, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, Fin.castSucc_lt_last j0, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, _, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, Fin.castSucc_lt_last j0, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval

lemma evalRep_liftRep {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) (r : Option (Finset (Fin n) × Finset (Fin A.size))) :
    evalRep (snocCircuit A B1 F1 B2 F2) U (liftRep r) = evalRep A U r := by
  cases r with
  | none => rfl
  | some p =>
    rcases p with ⟨B, F⟩
    simp only [liftRep, evalRep, decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval

lemma any_map_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    (l.map f).any id = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, id]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma step_same_circuit {n : ℕ} (gs : List Gate) (g : Gate) (A : AndCountCircuit n)
    (rep : List (Option (Finset (Fin n) × Finset (Fin A.size))))
    (hlen : rep.length = n + gs.length)
    (hval : ∀ (U : Finset (Fin n)) (w : ℕ),
      (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
        evalRep A U (rep.getD w (some (∅, ∅))))
    (rnew : Option (Finset (Fin n) × Finset (Fin A.size)))
    (hnew : ∀ U : Finset (Fin n),
      g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun j : Fin n => decide (j ∈ U))).getD i false) =
        evalRep A U rnew) :
    ∀ (U : Finset (Fin n)) (w : ℕ),
      (run (gs ++ [g]) (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
        evalRep A U ((rep ++ [rnew]).getD w (some (∅, ∅))) := by
  intro U w
  rw [run_snoc]
  have hrl : (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).length = n + gs.length := by
    rw [run_length, List.length_ofFn]
  rcases Nat.lt_trichotomy w (n + gs.length) with hlt | rfl | hgt
  · rw [getD_snoc_lt _ _ _ w (by omega), getD_snoc_lt _ _ _ w (by omega)]
    exact hval U w
  · rw [← hrl, getD_snoc_eq, hrl, ← hlen, getD_snoc_eq]
    exact hnew U
  · rw [getD_snoc_gt _ _ _ w (by omega), getD_snoc_gt _ _ _ w (by omega)]
    simp [evalRep]

lemma build_aux (n : ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (A : AndCountCircuit n) (rep : List (Option (Finset (Fin n) × Finset (Fin A.size)))),
      A.WellFormed ∧
      A.size ≤ gs.countP (fun g => isAndOp g.op) ∧
      rep.length = n + gs.length ∧
      ∀ (U : Finset (Fin n)) (w : ℕ),
        (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
          evalRep A U (rep.getD w (some (∅, ∅))) := by
  induction gs using List.reverseRecOn with
  | nil =>
    let A0 : AndCountCircuit n :=
      { size := 0
        leftVars := Fin.elim0
        leftGates := Fin.elim0
        rightVars := Fin.elim0
        rightGates := Fin.elim0
        outVars := ∅
        outGates := ∅ }
    let rep0 : List (Option (Finset (Fin n) × Finset (Fin 0))) :=
      List.ofFn fun i : Fin n => some ({i}, ∅)
    refine ⟨A0, rep0, fun i => Fin.elim0 i, by simp [A0], by simp [rep0], ?_⟩
    intro U w
    simp only [run, List.foldl_nil]
    by_cases hw : w < n
    · rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp [rep0, hw])]
      simp [rep0, evalRep]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [List.getD_eq_default _ _ (by simp [rep0]; omega)]
      simp [evalRep]
  | append_singleton gs g ih =>
    have hMgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (List.mem_append_left _ hg')
    obtain ⟨A, rep, hWF, hsz, hlen, hval⟩ := ih hMgs
    obtain ⟨hop, hglen⟩ := hM g (List.mem_append_right _ List.mem_cons_self)
    have hcnt : (gs ++ [g]).countP (fun g' => isAndOp g'.op) =
        gs.countP (fun g' => isAndOp g'.op) + (if isAndOp g.op then 1 else 0) := by
      simp [List.countP_append]
    let getR : ℕ → Option (Finset (Fin n) × Finset (Fin A.size)) :=
      fun u => rep.getD u (some (∅, ∅))
    rcases hop with hand | hor
    · have hisA : isAndOp g.op = true := by simp [isAndOp, hand]
      rcases hins : g.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
      · refine ⟨A, rep ++ [none], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
        exact step_same_circuit gs g A rep hlen hval none fun U => by
          simp [hand, hins, GateOp.eval, evalRep]
      · refine ⟨A, rep ++ [getR u], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
        exact step_same_circuit gs g A rep hlen hval (getR u) fun U => by
          simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, Bool.and_true, id]
          exact hval U u
      · cases hru : getR u with
        | none =>
          refine ⟨A, rep ++ [getR v], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
          exact step_same_circuit gs g A rep hlen hval (getR v) fun U => by
            simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
              List.all_cons, List.all_nil, Bool.and_true, id]
            rw [hval U u, hval U v]
            change (evalRep A U (getR u) && evalRep A U (getR v)) = evalRep A U (getR v)
            rw [hru]; simp [evalRep]
        | some p1 =>
          cases hrv : getR v with
          | none =>
            refine ⟨A, rep ++ [some p1], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
            exact step_same_circuit gs g A rep hlen hval (some p1) fun U => by
              simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
                List.all_cons, List.all_nil, Bool.and_true, id]
              rw [hval U u, hval U v]
              change (evalRep A U (getR u) && evalRep A U (getR v)) = evalRep A U (some p1)
              rw [hru, hrv]; simp [evalRep]
          | some p2 =>
            rcases p1 with ⟨B1, F1⟩
            rcases p2 with ⟨B2, F2⟩
            refine ⟨snocCircuit A B1 F1 B2 F2, rep.map liftRep ++ [some (∅, {Fin.last A.size})],
              snocCircuit_wellFormed A hWF B1 F1 B2 F2,
              by show A.size + 1 ≤ _; rw [hcnt, hisA]; simp; omega,
              by simp [hlen]; omega, ?_⟩
            intro U w
            rw [run_snoc]
            have hrl : (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).length = n + gs.length := by
              rw [run_length, List.length_ofFn]
            have hmlen : (rep.map liftRep).length = n + gs.length := by rw [List.length_map, hlen]
            rcases Nat.lt_trichotomy w (n + gs.length) with hlt | rfl | hgt
            · rw [getD_snoc_lt _ _ _ w (by omega)]
              rw [getD_snoc_lt _ _ _ w (by omega)]
              rw [hval U w]
              rw [List.getD_eq_getElem _ _ (by omega : w < (rep.map liftRep).length), List.getElem_map, evalRep_liftRep]
              rw [List.getD_eq_getElem _ _ (by omega : w < rep.length)]
            · rw [← hrl, getD_snoc_eq, hrl, ← hmlen, getD_snoc_eq]
              simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
                List.all_cons, List.all_nil, Bool.and_true, id]
              rw [hval U u, hval U v]
              change (evalRep A U (getR u) && evalRep A U (getR v)) =
                evalRep (snocCircuit A B1 F1 B2 F2) U (some (∅, {Fin.last A.size}))
              rw [hru, hrv]
              simp only [evalRep, Finset.notMem_empty, false_and, exists_false, false_or,
                Finset.mem_singleton, exists_eq_left]
              rw [snocCircuit_gateVal_last]
              simp only [evalRep]
              exact Bool.decide_eq_true.symm
            · rw [getD_snoc_gt _ _ _ w (by omega)]
              rw [getD_snoc_gt _ _ _ w (by omega)]
              simp [evalRep]
      · rw [hins] at hglen; simp at hglen
    · let rnew := g.inputs.foldl (fun acc u => orRep acc (getR u)) (some (∅, ∅))
      have hfold : ∀ (U : Finset (Fin n)) (xs : List ℕ)
          (init : Option (Finset (Fin n) × Finset (Fin A.size))),
          evalRep A U (xs.foldl (fun acc u => orRep acc (getR u)) init) =
            (evalRep A U init || xs.any fun u => evalRep A U (getR u)) := by
        intro U xs
        induction xs with
        | nil => intro init; simp
        | cons a t iht =>
          intro init
          simp only [List.foldl_cons, List.any_cons]
          rw [iht (orRep init (getR a)), evalRep_orRep, Bool.or_assoc]
      refine ⟨A, rep ++ [rnew], hWF, by rw [hcnt]; omega, by simp [hlen]; omega, ?_⟩
      exact step_same_circuit gs g A rep hlen hval rnew fun U => by
        simp only [hor, GateOp.eval]
        dsimp only [rnew]
        rw [hfold U g.inputs (some (∅, ∅))]
        have hemp : evalRep A U (some (∅, ∅)) = false := by simp [evalRep]
        rw [hemp, Bool.false_or]
        exact any_map_congr g.inputs _ _ fun u _ => hval U u

end PEqualNP.Outside.L_meta_17134_aux.Compile
namespace PEqualNP.Outside.L_meta_17134_aux.Compile

open PEqualNP.CircuitLowerBounds PEqualNP.AndCount PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_17134_aux.Generic

theorem mono (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 n C) : Monotone2 C := by
  intro g hg
  refine ⟨?_, (ao.2.2 g hg).le⟩
  simpa using ao.1 g hg

theorem asEdges {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Fin n)) : graphFun G ∅ (fun i => decide (i ∈ U)) = true ↔
      ∃ a ∈ U, ∃ b ∈ U, G.Adj a b := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq, decide_eq_true_iff]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    exact ⟨a,ha,b,hb,hab⟩
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ⟨a,b,hab,ha,hb⟩

theorem mask_edges {n : Nat} (G : SimpleGraph (Fin n)) (A U : Finset (Fin n)) :
    (∃ a ∈ U ∩ A, ∃ b ∈ U ∩ A, G.Adj a b) ↔
      ∃ a ∈ U, ∃ b ∈ U, (Pin.activeGraph G A).Adj a b := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ⟨a,(Finset.mem_inter.mp ha).1,b,(Finset.mem_inter.mp hb).1,
      (Pin.activeGraph_adj G A a b).2 ⟨(Finset.mem_inter.mp ha).2,(Finset.mem_inter.mp hb).2,hab⟩⟩
  · rintro ⟨a,ha,b,hb,hab⟩
    obtain ⟨ha',hb',e⟩ := (Pin.activeGraph_adj G A a b).1 hab
    exact ⟨a,Finset.mem_inter.mpr ⟨ha,ha'⟩,b,Finset.mem_inter.mpr ⟨hb,hb'⟩,e⟩

theorem compilePinned {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 n C)
    (agree : ∀ x : Fin n → Bool, x v = false → circuitFun n C x = graphFun G ∅ x) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧
      D.Computes (Pin.activeGraph G (Finset.univ.erase v)) ∧
      D.size ≤ C.gates.countP (fun g =>
        GateOp.rec true false false (fun (_ : Nat) => false) false g.op) := by
  obtain ⟨A, rep, hWF, hsz, _, hval⟩ := build_aux n C.gates (mono C ao)
  cases hrout : rep.getD C.output (some (∅, ∅)) with
  | none =>
    exfalso
    have h0 := hval ∅ C.output
    rw [hrout] at h0
    have h0' : circuitFun n C (fun i : Fin n => decide (i ∈ (∅ : Finset (Fin n)))) = true := h0
    rw [agree _ (by simp), asEdges G ∅] at h0'
    simpa using h0'
  | some p =>
    rcases p with ⟨Bout,Fout⟩
    let A' : AndCountCircuit n := { A with outVars := Bout, outGates := Fout }
    let act : Finset (Fin n) := Finset.univ.erase v
    refine ⟨ActiveNorm.mask A' act, ActiveNorm.mask_wf A' act hWF, ?_, ?_⟩
    · intro U
      rw [ActiveNorm.eval_mask]
      have h1 := hval (U ∩ act) C.output
      rw [hrout] at h1
      have h2 : A'.eval (U ∩ act) = evalRep A (U ∩ act) (some (Bout,Fout)) := by
        simp only [AndCountCircuit.eval, evalRep, A', AndCountCircuit.gateVal]
        have hgv : ∀ j : Fin A.size, ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel (U ∩ act) A.size j =
            A.gateValFuel (U ∩ act) A.size j :=
          gateValFuel_withOut A Bout Fout (U ∩ act) A.size
        simp only [hgv]
        rfl
      rw [h2, ← h1]
      change circuitFun n C (fun i : Fin n => decide (i ∈ U ∩ act)) = true ↔ _
      rw [agree _ (by simp [act]), asEdges G, mask_edges]
    · change A.size ≤ _
      exact hsz

end PEqualNP.Outside.L_meta_17134_aux.Compile


/- To be concatenated after A14Generic; this source only uses its Slot interface. -/
namespace PEqualNP.Outside.L_meta_17134_aux.OneRead
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17134_aux.Generic.Slot
open scoped Classical

variable {n : Nat}
abbrev Gph := SimpleGraph (Fin n)

def SquareFree (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u z a b, u ≠ z → a ≠ b → G.Adj u a → G.Adj u b → G.Adj z a → G.Adj z b → False

def DegreeTwo (G : SimpleGraph (Fin n)) (u : Fin n) : Prop :=
  ∃ a b, a ≠ b ∧ G.Adj u a ∧ G.Adj u b

def Clean (C : AndCountCircuit n) : Prop :=
  ∀ i : Fin C.size, ∀ v : Fin n, C.gateVal {v} i = false

def Split (C : AndCountCircuit n) : Prop :=
  ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)

def IsOne (C : AndCountCircuit n) (u : Fin n) (s : Side C) :=
  positions C u = {s}

lemma mem_other_iff (C : AndCountCircuit n) (s : Side C) (u : Fin n) :
    u ∈ raw C s ∨ u ∈ raw C (other C s) ↔ s.1 ∈ readers C u := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [raw, other, mem_readers, or_comm]

lemma not_mem_other (C : AndCountCircuit n) (hd : Split C) (s : Side C) {u : Fin n}
    (h : u ∈ raw C s) : u ∉ raw C (other C s) := by
  rcases s with ⟨i,b⟩
  cases b
  · exact fun ho => Finset.disjoint_left.mp (hd i) h ho
  · exact fun ho => Finset.disjoint_left.mp (hd i) ho h

lemma sides_same_or_other (C : AndCountCircuit n) (s t : Side C) (h : s.1 = t.1) :
    t = s ∨ t = other C s := by
  rcases s with ⟨i,b⟩
  rcases t with ⟨j,d⟩
  change i = j at h
  subst j
  cases b <;> cases d <;> simp [other]

lemma one_of_card (C : AndCountCircuit n) (hd : Split C) (u : Fin n)
    (h : (readers C u).card = 1) : ∃ s : Side C, IsOne C u s := by
  exact Finset.card_eq_one.mp ((positions_card C u hd).trans h)

lemma one_mem (C : AndCountCircuit n) {u : Fin n} {s : Side C}
    (h : IsOne C u s) : u ∈ raw C s := by
  apply (mem_positions C u s).mp
  rw [h, Finset.mem_singleton]

lemma one_readers (C : AndCountCircuit n) {u : Fin n} {s : Side C}
    (h : IsOne C u s) : readers C u = {s.1} := by
  rw [← positions_image, h]
  simp

lemma one_neighbor (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅) (hs : Clean C)
    {u w : Fin n} {s : Side C} (hu : IsOne C u s) (edge : G.Adj u w) :
    w ∈ raw C (other C s) :=
  unique_position_neighbor G C hc ho hs edge s hu

lemma one_pure (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅) (hs : Clean C) (hd : Split C)
    (sq : SquareFree G) {u : Fin n} {s : Side C}
    (hu : IsOne C u s) (dg : DegreeTwo G u) : raw C s = {u} := by
  ext z
  rw [Finset.mem_singleton]
  constructor
  · intro hz
    by_contra hzu
    have no_uz : ¬ G.Adj u z := fun e =>
      not_mem_other C hd s hz (one_neighbor G C hc ho hs hu e)
    have incl : ∀ w, G.Adj u w → G.Adj z w := by
      intro w huw
      by_contra hzw
      have hind : ∀ a ∈ ({z,w} : Finset (Fin n)), ∀ b ∈ ({z,w} : Finset (Fin n)),
          ¬ G.Adj a b := by
        intro a ha b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst a <;> subst b
        · exact G.irrefl
        · exact hzw
        · exact fun e => hzw (e.symm)
        · exact G.irrefl
      obtain ⟨t, ht, miss⟩ := separation G C hc ho ({z,w} : Finset (Fin n))
        u w (by simp) hind huw
      have hp := (mem_positions C u t).mpr ht
      rw [hu, Finset.mem_singleton] at hp
      subst t
      exact miss ⟨z,hz,by simp⟩
    obtain ⟨a,b,ab,ua,ub⟩ := dg
    exact sq u z a b (Ne.symm hzu) ab ua ub (incl a ua) (incl b ub)
  · intro e
    subst z
    exact one_mem C hu

lemma owners_distinct (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅) (hs : Clean C) (hd : Split C)
    (sq : SquareFree G) {u w : Fin n} {s t : Side C}
    (huw : u ≠ w) (hu : IsOne C u s) (hw : IsOne C w t)
    (du : DegreeTwo G u) (dw : DegreeTwo G w) : s.1 ≠ t.1 := by
  intro eq
  have pu := one_pure G C hc ho hs hd sq hu du
  have pw := one_pure G C hc ho hs hd sq hw dw
  rcases sides_same_or_other C s t eq with eq' | eq'
  · subst t
    have mem := one_mem C hu
    rw [pw, Finset.mem_singleton] at mem
    exact huw mem
  · subst t
    obtain ⟨a,b,ab,ha,hb⟩ := du
    have aa := one_neighbor G C hc ho hs hu ha
    have bb := one_neighbor G C hc ho hs hu hb
    rw [pw, Finset.mem_singleton] at aa bb
    exact ab (aa.trans bb.symm)

lemma adjacent_owners_impossible (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hc : C.Computes G) (ho : C.outVars = ∅) (hs : Clean C) (hd : Split C)
    (sq : SquareFree G) {u w : Fin n} {s t : Side C}
    (edge : G.Adj u w) (hu : IsOne C u s) (hw : IsOne C w t)
    (du : DegreeTwo G u) (dw : DegreeTwo G w) : False := by
  have neq : u ≠ w := fun eq => G.irrefl (eq ▸ edge)
  have mem := (mem_positions C w (other C s)).mpr (one_neighbor G C hc ho hs hu edge)
  rw [hw, Finset.mem_singleton] at mem
  exact owners_distinct G C hc ho hs hd sq neq hu hw du dw (by simpa [other] using congrArg (fun z : Side C => z.1) mem)

lemma sval_true_iff (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Side C) :
    sval C U s = true ↔ hits C U s ∨
      ∃ j ∈ prev C s, j < s.1 ∧ C.gateVal U j = true := by
  classical
  unfold sval sideTrue hits
  simp

def Born (C : AndCountCircuit n) (u w : Fin n) (s : Side C) : Prop :=
  u ∈ raw C s ∧ w ∈ raw C (other C s)

lemma gate_true_birth (C : AndCountCircuit n) (hd : Split C) (u w : Fin n)
    (i : Fin C.size) (hi : C.gateVal {u,w} i = true) : ∃ s, Born C u w s := by
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction with
  | h i ih =>
    by_cases prevh : ∃ j : Fin C.size, j < i ∧ C.gateVal {u,w} j = true
    · obtain ⟨j,hj,hv⟩ := prevh
      exact ih j hj hv
    · rw [gate_eq_sval, Bool.and_eq_true] at hi
      have rawh (b : Bool) : hits C ({u,w} : Finset (Fin n)) (i,b) := by
        have h := (sval_true_iff C {u,w} (i,b)).mp (by cases b; exact hi.1; exact hi.2)
        rcases h with h | ⟨j,_,hj,hv⟩
        · exact h
        · exact (prevh ⟨j,hj,hv⟩).elim
      obtain ⟨a,ha,au⟩ := rawh false
      obtain ⟨b,hb,bu⟩ := rawh true
      simp only [Finset.mem_insert, Finset.mem_singleton] at au bu
      have ne : a ≠ b := by
        intro eq
        subst b
        exact Finset.disjoint_left.mp (hd i) ha hb
      rcases au with au | au <;> rcases bu with bu | bu
      · exact (ne (au.trans bu.symm)).elim
      · exact ⟨(i,false), au ▸ ha, bu ▸ hb⟩
      · exact ⟨(i,true), bu ▸ hb, au ▸ ha⟩
      · exact (ne (au.trans bu.symm)).elim

lemma edge_birth (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) (hd : Split C)
    (hc : C.Computes G) (ho : C.outVars = ∅) {u w : Fin n} (edge : G.Adj u w) :
    ∃ s, Born C u w s := by
  have ev : C.eval {u,w} = true := (hc _).mpr ⟨u,by simp,w,by simp,edge⟩
  unfold AndCountCircuit.eval at ev
  rw [decide_eq_true_eq] at ev
  rcases ev with ⟨v,hv,_⟩ | ⟨i,_,hi⟩
  · simp [ho] at hv
  · exact gate_true_birth C hd u w i hi

lemma birth_readers (C : AndCountCircuit n) {u w : Fin n} {s : Side C}
    (h : Born C u w s) : s.1 ∈ readers C u ∧ s.1 ∈ readers C w :=
  ⟨(mem_other_iff C s u).mp (.inl h.1), (mem_other_iff C s w).mp (.inr h.2)⟩

lemma birth_not_owner (C : AndCountCircuit n) {u w v : Fin n} {s t : Side C}
    (e : Born C u w s) (p : raw C t = {v}) (uv : u ≠ v) (wv : w ≠ v) : s.1 ≠ t.1 := by
  intro eq
  rcases sides_same_or_other C t s eq.symm with h | h
  · subst s
    exact uv (Finset.mem_singleton.mp (p ▸ e.1))
  · subst s
    have hh : other C (other C t) = t := by
      rcases t with ⟨i,b⟩
      cases b <;> rfl
    have em := e.2
    rw [hh,p,Finset.mem_singleton] at em
    exact wv em

end PEqualNP.Outside.L_meta_17134_aux.OneRead


namespace PEqualNP.Outside.L_meta_17134_aux.Floors
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17134_aux.Generic.Pin
open PEqualNP.Outside.L_meta_17134_aux.Generic.Slot
open PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm
open PEqualNP.Outside.L_meta_17134_aux.OneRead

variable {n : ℕ}

theorem other_other (C : AndCountCircuit n) (s : Side C) : other C (other C s) = s := by
  rcases s with ⟨i,b⟩
  cases b <;> rfl

theorem triangle_birth {C : AndCountCircuit n} (split : Split C)
    {a b c : Fin n} {s t q : Side C} (ab : Born C a b s) (ac : Born C a c t)
    (bc : Born C b c q) (st : s.1 = t.1) (sq : s.1 = q.1) : False := by
  have tab : t = s := by
    rcases sides_same_or_other C s t st with h | h
    · exact h
    · exact (not_mem_other C split s ab.1 (h ▸ ac.1)).elim
  subst t
  rcases sides_same_or_other C s q sq with h | h
  · subst q
    exact not_mem_other C split s bc.1 ab.2
  · subst q
    have f := bc.2
    rw [other_other] at f
    exact not_mem_other C split s f ac.2

theorem triangle {G : SimpleGraph (Fin n)} {a b c : Fin n}
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : Lower G 2 := by
  intro C wf comp
  by_contra! small
  obtain ⟨D,ds,de,dc,dd,dw⟩ := normalizeSingleton n C
  have dcomp : D.Computes G := fun U => by rw [de U]; exact comp U
  have dsmall : D.size < 2 := lt_of_le_of_lt ds small
  have dout := out_of_computes D G dcomp
  obtain ⟨s,hs⟩ := edge_birth G D dd dcomp dout ab
  obtain ⟨t,ht⟩ := edge_birth G D dd dcomp dout ca.symm
  obtain ⟨q,hq⟩ := edge_birth G D dd dcomp dout bc
  have equal (i j : Fin D.size) : i = j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  exact triangle_birth dd hs ht hq (equal _ _) (equal _ _)

theorem pin_floor {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A : Finset (Fin n)} {v : Fin n} {k : ℕ}
    (edge : ∃ w, (activeGraph G A).Adj v w)
    (rest : Lower (activeGraph G (A \ closedPin G {v})) k) :
    Lower (activeGraph G A) (k+1) := by
  intro C wf comp
  obtain ⟨D,dw,dc,ds⟩ := pin_active C G A {v} wf comp (singleton_independent G v)
  have hn := rest D dw dc
  have hp := useful_read_pos C (activeGraph G A) comp v edge
  omega

theorem reader_cap {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A : Finset (Fin n)} {v : Fin n} {k B : ℕ} {C : AndCountCircuit n}
    (wf : C.WellFormed) (comp : C.Computes (activeGraph G A)) (budget : C.size ≤ B)
    (rest : Lower (activeGraph G (A \ closedPin G {v})) k) :
    (readers C v).card ≤ B-k := by
  obtain ⟨D,dw,dc,ds⟩ := pin_active C G A {v} wf comp (singleton_independent G v)
  rw [pinReads_eq_readers] at ds
  have hn := rest D dw dc
  omega

theorem owner_of_floor {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A : Finset (Fin n)} {v : Fin n} {k : ℕ} {C : AndCountCircuit n}
    (wf : C.WellFormed) (comp : C.Computes (activeGraph G A)) (split : Split C)
    (budget : C.size ≤ k+1) (edge : ∃ w, (activeGraph G A).Adj v w)
    (rest : Lower (activeGraph G (A \ closedPin G {v})) k) :
    ∃ s, IsOne C v s := by
  have hcap := reader_cap wf comp budget rest
  have hp := useful_read_pos C (activeGraph G A) comp v edge
  rw [pinReads_eq_readers] at hp
  apply one_of_card C split v
  omega

theorem adjacent_four {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A : Finset (Fin n)} {u v : Fin n}
    (sq : SquareFree (activeGraph G A)) (edge : (activeGraph G A).Adj u v)
    (du : DegreeTwo (activeGraph G A) u) (dv : DegreeTwo (activeGraph G A) v)
    (fU : Lower (activeGraph G (A \ closedPin G {u})) 2)
    (fV : Lower (activeGraph G (A \ closedPin G {v})) 2) :
    Lower (activeGraph G A) 4 := by
  intro C wf comp
  by_contra! small
  obtain ⟨R⟩ := normalizeActive C G A wf comp
  have bud : R.circuit.size ≤ 2+1 := by have h := R.size_le; omega
  obtain ⟨s,hs⟩ := owner_of_floor R.wf R.comp R.disjoint bud ⟨v,edge⟩ fU
  obtain ⟨t,ht⟩ := owner_of_floor R.wf R.comp R.disjoint bud ⟨u,edge.symm⟩ fV
  exact adjacent_owners_impossible _ R.circuit R.comp R.out R.clean R.disjoint sq edge hs ht du dv

theorem unique_other_reader {C : AndCountCircuit n} {u : Fin n} {s i j : Fin C.size}
    (cap : (readers C u).card ≤ 2) (hs : s ∈ readers C u)
    (hi : i ∈ readers C u) (hj : j ∈ readers C u)
    (his : i ≠ s) (hjs : j ≠ s) : i = j := by
  by_contra hij
  have sub : ({i,j,s} : Finset (Fin C.size)) ⊆ readers C u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hs
  have ct : ({i,j,s} : Finset (Fin C.size)).card = 3 := by simp [hij, his, hjs]
  have lb := Finset.card_le_card sub
  omega

end PEqualNP.Outside.L_meta_17134_aux.Floors

namespace PEqualNP.Outside.L_meta_17134_aux.Graph
open PEqualNP.Outside.L_meta_17134_aux.Generic.Pin
open PEqualNP.Outside.L_meta_17134_aux.OneRead

abbrev G : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11 [
  (0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

abbrev H (A : Finset (Fin 11)) := activeGraph G A

abbrev start (v : Fin 11) : Finset (Fin 11) := Finset.univ.erase v

abbrev pin (A : Finset (Fin 11)) (v : Fin 11) : Finset (Fin 11) :=
  A \ closedPin G {v}

instance (A : Finset (Fin 11)) : DecidableRel (H A).Adj :=
  fun a b => inferInstanceAs (Decidable (a ∈ A ∧ b ∈ A ∧ G.Adj a b))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem sq_table : ∀ u z a b : Fin 11, u ≠ z → a ≠ b →
    G.Adj u a → G.Adj u b → G.Adj z a → G.Adj z b → False := by
  decide +kernel

theorem squareFree (A : Finset (Fin 11)) : SquareFree (H A) := by
  intro u z a b uz ab ua ub za zb
  exact sq_table u z a b uz ab ua.2.2 ub.2.2 za.2.2 zb.2.2

end PEqualNP.Outside.L_meta_17134_aux.Graph

/- Concatenate after A14Compile, B14OneRead, A14Floors and A14Graph.
   All concrete circuit-independent checks are small finite graph facts. -/
namespace PEqualNP.Outside.L_meta_17134_aux.V123
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_17134_aux.Generic.Pin
open PEqualNP.Outside.L_meta_17134_aux.Generic.Slot
open PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm
open PEqualNP.Outside.L_meta_17134_aux.OneRead
open PEqualNP.Outside.L_meta_17134_aux.Floors
open PEqualNP.Outside.L_meta_17134_aux.Graph

private lemma observed {n : Nat} {G : SimpleGraph (Fin n)} {C : AndCountCircuit n}
    (comp : C.Computes G) (out : C.outVars = ∅) (clean : Clean C)
    {u w : Fin n} {s : Side C} (owner : IsOne C u s) (edge : G.Adj u w) :
    s.1 ∈ readers C w :=
  (mem_other_iff C s w).mp (Or.inr (one_neighbor G C comp out clean owner edge))

private lemma three_readers {n : Nat} {C : AndCountCircuit n} {v : Fin n} {i j k : Fin C.size}
    (hi : i ∈ readers C v) (hj : j ∈ readers C v) (hk : k ∈ readers C v)
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) : 3 ≤ (readers C v).card := by
  have sub : ({i,j,k} : Finset (Fin C.size)) ⊆ readers C v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  have card : ({i,j,k} : Finset (Fin C.size)).card = 3 := by simp [ij,ik,jk]
  simpa only [card] using Finset.card_le_card sub

private lemma owner1_0 : Lower (H (pin (start 1) 0)) 4 := by
  apply pin_floor (v := 2) (k := 3) (by decide +kernel)
  apply pin_floor (v := 4) (k := 2) (by decide +kernel)
  exact triangle (a := 3) (b := 6) (c := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private lemma owner1_2 : Lower (H (pin (start 1) 2)) 4 := by
  apply pin_floor (v := 0) (k := 3) (by decide +kernel)
  apply pin_floor (v := 4) (k := 2) (by decide +kernel)
  exact triangle (a := 3) (b := 6) (c := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private lemma owner1_4 : Lower (H (pin (start 1) 4)) 4 := by
  apply pin_floor (v := 0) (k := 3) (by decide +kernel)
  apply pin_floor (v := 2) (k := 2) (by decide +kernel)
  exact triangle (a := 3) (b := 6) (c := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private lemma cap1_10 : Lower (H (pin (start 1) 10)) 3 := by
  apply pin_floor (v := 3) (k := 2) (by decide +kernel)
  exact triangle (a := 5) (b := 8) (c := 9) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem caseOne : Lower (H (start 1)) 6 := by
  intro C wf comp
  by_contra! hsmall
  obtain ⟨R⟩ := normalizeActive C G (start 1) wf comp
  have bud : R.circuit.size ≤ 5 := by have h := R.size_le; omega
  obtain ⟨s,hs⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner1_0
  obtain ⟨t,ht⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner1_2
  obtain ⟨q,hq⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner1_4
  have d0 : DegreeTwo (H (start 1)) 0 := ⟨9,10,by decide,by decide +kernel,by decide +kernel⟩
  have d2 : DegreeTwo (H (start 1)) 2 := ⟨5,10,by decide,by decide +kernel,by decide +kernel⟩
  have d4 : DegreeTwo (H (start 1)) 4 := ⟨8,10,by decide,by decide +kernel,by decide +kernel⟩
  have dist {u w : Fin 11} {i j : Side R.circuit} (uw : u ≠ w)
      (hu : IsOne R.circuit u i) (hw : IsOne R.circuit w j)
      (du : DegreeTwo (H (start 1)) u) (dw : DegreeTwo (H (start 1)) w) : i.1 ≠ j.1 :=
    owners_distinct _ R.circuit R.comp R.out R.clean R.disjoint (squareFree _) uw hu hw du dw
  have a := observed R.comp R.out R.clean hs (w := 10) (by decide +kernel)
  have b := observed R.comp R.out R.clean ht (w := 10) (by decide +kernel)
  have c := observed R.comp R.out R.clean hq (w := 10) (by decide +kernel)
  have low := three_readers a b c (dist (by decide) hs ht d0 d2)
    (dist (by decide) hs hq d0 d4) (dist (by decide) ht hq d2 d4)
  have high := reader_cap R.wf R.comp bud cap1_10
  omega

private lemma owner2_1 : Lower (H (pin (start 2) 1)) 4 := by
  apply pin_floor (v := 5) (k := 3) (by decide +kernel)
  apply pin_floor (v := 0) (k := 2) (by decide +kernel)
  exact triangle (a := 3) (b := 6) (c := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private lemma owner2_5 : Lower (H (pin (start 2) 5)) 4 := by
  apply pin_floor (v := 0) (k := 3) (by decide +kernel)
  apply pin_floor (v := 1) (k := 2) (by decide +kernel)
  exact triangle (a := 3) (b := 6) (c := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private lemma cap2_8 : Lower (H (pin (start 2) 8)) 3 := by
  apply pin_floor (v := 0) (k := 2) (by decide +kernel)
  exact triangle (a := 3) (b := 6) (c := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem caseTwo : Lower (H (start 2)) 6 := by
  intro C wf comp
  by_contra! hsmall
  obtain ⟨R⟩ := normalizeActive C G (start 2) wf comp
  have bud : R.circuit.size ≤ 5 := by have h := R.size_le; omega
  obtain ⟨s,hs⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner2_1
  obtain ⟨t,ht⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner2_5
  have d1 : DegreeTwo (H (start 2)) 1 := ⟨4,8,by decide,by decide +kernel,by decide +kernel⟩
  have d5 : DegreeTwo (H (start 2)) 5 := ⟨8,9,by decide,by decide +kernel,by decide +kernel⟩
  have pureS := one_pure _ R.circuit R.comp R.out R.clean R.disjoint (squareFree _) hs d1
  have pureT := one_pure _ R.circuit R.comp R.out R.clean R.disjoint (squareFree _) ht d5
  have st := owners_distinct _ R.circuit R.comp R.out R.clean R.disjoint (squareFree _)
    (by decide) hs ht d1 d5
  have a := observed R.comp R.out R.clean hs (w := 8) (by decide +kernel)
  have b := observed R.comp R.out R.clean ht (w := 8) (by decide +kernel)
  obtain ⟨q,hq⟩ := edge_birth _ R.circuit R.disjoint R.comp R.out (u := 4) (w := 8) (by decide +kernel)
  have low := three_readers a b (birth_readers R.circuit hq).2 st
    (Ne.symm (birth_not_owner R.circuit hq pureS (by decide) (by decide)))
    (Ne.symm (birth_not_owner R.circuit hq pureT (by decide) (by decide)))
  have high := reader_cap R.wf R.comp bud cap2_8
  omega

private lemma owner3_6 : Lower (H (pin (start 3) 6)) 4 := by
  apply pin_floor (v := 0) (k := 3) (by decide +kernel)
  apply pin_floor (v := 2) (k := 2) (by decide +kernel)
  exact triangle (a := 1) (b := 4) (c := 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private lemma owner3_7 : Lower (H (pin (start 3) 7)) 4 := by
  apply pin_floor (v := 0) (k := 3) (by decide +kernel)
  apply pin_floor (v := 2) (k := 2) (by decide +kernel)
  exact triangle (a := 1) (b := 4) (c := 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem caseThree : Lower (H (start 3)) 6 := by
  intro C wf comp
  by_contra! hsmall
  obtain ⟨R⟩ := normalizeActive C G (start 3) wf comp
  have bud : R.circuit.size ≤ 5 := by have h := R.size_le; omega
  obtain ⟨s,hs⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner3_6
  obtain ⟨t,ht⟩ := owner_of_floor R.wf R.comp R.disjoint bud (by decide +kernel) owner3_7
  have d6 : DegreeTwo (H (start 3)) 6 := ⟨7,10,by decide,by decide +kernel,by decide +kernel⟩
  have d7 : DegreeTwo (H (start 3)) 7 := ⟨6,9,by decide,by decide +kernel,by decide +kernel⟩
  exact adjacent_owners_impossible _ R.circuit R.comp R.out R.clean R.disjoint (squareFree _)
    (by decide +kernel) hs ht d6 d7

end PEqualNP.Outside.L_meta_17134_aux.V123

namespace PEqualNP.Outside.L_meta_17134_aux.V0
open PEqualNP.Outside.L_meta_17134_aux.Generic.Pin
open PEqualNP.Outside.L_meta_17134_aux.Generic.Slot
open PEqualNP.Outside.L_meta_17134_aux.Generic.ActiveNorm
open PEqualNP.Outside.L_meta_17134_aux.OneRead
open PEqualNP.Outside.L_meta_17134_aux.Floors
open PEqualNP.Outside.L_meta_17134_aux.Graph

private abbrev A := start (0 : Fin 11)

private theorem owner1_floor : Lower (H (pin A 1)) 4 := by
  apply adjacent_four (G := G) (A := pin A 1) (u := 2) (v := 5) (squareFree _)
  · decide +kernel
  · exact ⟨5, 10, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨2, 9, by decide, by decide +kernel, by decide +kernel⟩
  · exact triangle (a := 3) (b := 6) (c := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact triangle (a := 3) (b := 6) (c := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem owner2_floor : Lower (H (pin A 2)) 4 := by
  apply adjacent_four (G := G) (A := pin A 2) (u := 1) (v := 4) (squareFree _)
  · decide +kernel
  · exact ⟨4, 8, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨1, 8, by decide, by decide +kernel, by decide +kernel⟩
  · exact triangle (a := 3) (b := 6) (c := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact triangle (a := 3) (b := 6) (c := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem five_floor : Lower (H (pin A 5)) 3 := by
  apply pin_floor (G := G) (A := pin A 5) (v := 1) (k := 2)
  · exact ⟨4, by decide +kernel⟩
  · exact triangle (a := 3) (b := 6) (c := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem eight_floor : Lower (H (pin A 8)) 3 := by
  apply pin_floor (G := G) (A := pin A 8) (v := 2) (k := 2)
  · exact ⟨10, by decide +kernel⟩
  · exact triangle (a := 3) (b := 6) (c := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem caseZero : Lower (H (start 0)) 6 := by
  intro C wf comp
  by_contra! small
  obtain ⟨R⟩ := normalizeActive C G A wf comp
  have bud : R.circuit.size ≤ 5 := by have h := R.size_le; omega
  have e18 : (H A).Adj 1 8 := by decide +kernel
  have e25 : (H A).Adj 2 5 := by decide +kernel
  obtain ⟨g1,hg1⟩ := owner_of_floor R.wf R.comp R.disjoint bud ⟨8,e18⟩ owner1_floor
  obtain ⟨g2,hg2⟩ := owner_of_floor R.wf R.comp R.disjoint bud ⟨5,e25⟩ owner2_floor
  have p1 := one_pure (H A) R.circuit R.comp R.out R.clean R.disjoint
    (squareFree A) hg1 ⟨4,8,by decide,by decide +kernel,e18⟩
  have p2 := one_pure (H A) R.circuit R.comp R.out R.clean R.disjoint
    (squareFree A) hg2 ⟨5,10,by decide,e25,by decide +kernel⟩
  have r8 : g1.1 ∈ readers R.circuit 8 :=
    (mem_other_iff R.circuit g1 8).mp (.inr (one_neighbor (H A) R.circuit R.comp R.out R.clean hg1 e18))
  have r5 : g2.1 ∈ readers R.circuit 5 :=
    (mem_other_iff R.circuit g2 5).mp (.inr (one_neighbor (H A) R.circuit R.comp R.out R.clean hg2 e25))
  have cap5 : (readers R.circuit 5).card ≤ 2 := reader_cap R.wf R.comp bud five_floor
  have cap8 : (readers R.circuit 8).card ≤ 2 := reader_cap R.wf R.comp bud eight_floor
  obtain ⟨s,hs⟩ := edge_birth (H A) R.circuit R.disjoint R.comp R.out
    (show (H A).Adj 5 8 by decide +kernel)
  obtain ⟨t,ht⟩ := edge_birth (H A) R.circuit R.disjoint R.comp R.out
    (show (H A).Adj 5 9 by decide +kernel)
  obtain ⟨q,hq⟩ := edge_birth (H A) R.circuit R.disjoint R.comp R.out
    (show (H A).Adj 8 9 by decide +kernel)
  have st := unique_other_reader cap5 r5 (birth_readers R.circuit hs).1
    (birth_readers R.circuit ht).1
    (birth_not_owner R.circuit hs p2 (by decide) (by decide))
    (birth_not_owner R.circuit ht p2 (by decide) (by decide))
  have sq := unique_other_reader cap8 r8 (birth_readers R.circuit hs).2
    (birth_readers R.circuit hq).1
    (birth_not_owner R.circuit hs p1 (by decide) (by decide))
    (birth_not_owner R.circuit hq p1 (by decide) (by decide))
  exact triangle_birth R.disjoint hs ht hq st sq

end PEqualNP.Outside.L_meta_17134_aux.V0


theorem PEqualNP.Outside.L_meta_17134 : (
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (6 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates
)
 := by
  dsimp only
  intro v C hv ao agree
  obtain ⟨D,wf,comp,bound⟩ := PEqualNP.Outside.L_meta_17134_aux.Compile.compilePinned
    PEqualNP.Outside.L_meta_17134_aux.Graph.G v C ao agree
  have q : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 := by omega
  have low : 6 ≤ D.size := by
    rcases q with h | h | h | h
    · have e : v = 0 := Fin.ext h
      subst v
      exact PEqualNP.Outside.L_meta_17134_aux.V0.caseZero D wf comp
    · have e : v = 1 := Fin.ext h
      subst v
      exact PEqualNP.Outside.L_meta_17134_aux.V123.caseOne D wf comp
    · have e : v = 2 := Fin.ext h
      subst v
      exact PEqualNP.Outside.L_meta_17134_aux.V123.caseTwo D wf comp
    · have e : v = 3 := Fin.ext h
      subst v
      exact PEqualNP.Outside.L_meta_17134_aux.V123.caseThree D wf comp
  exact low.trans bound

