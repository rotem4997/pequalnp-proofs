import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_7875_731 :
(let A := Finset (Fin 13) × Finset (Fin 13)
 let D : Finset (Fin 13) := {0, 1, 3, 9}
 let col : Fin 25 → Set A := fun i =>
   {s | if i.val < 12 then Fin.ofNat 13 (i.val + 1) ∈ s.1 else Fin.ofNat 13 (i.val - 12) ∈ s.2}
 let edge : Set A := {s | ∃ p ∈ s.1, p ≠ 0 ∧ ∃ l ∈ s.2, p + l ∈ D}
 let flag : Set A := {s | ∃ l ∈ s.2, l ∈ D}
 ∃ (prog : List (Bool × ℕ × ℕ)) (o q : ℕ),
   let rows := prog.foldl (fun (w : List (Set A)) g =>
     w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅))
     (List.ofFn col)
   prog.length ≤ 61 ∧ o < 25 + prog.length ∧ q < 25 + prog.length ∧
     rows.getD o ∅ = edge ∧ (flag \ edge) ⊆ rows.getD q ∅ ∧ rows.getD q ∅ ⊆ flag ∪ edge) →
(let A := Finset (Fin 13) × Finset (Fin 13);
 ∀ (col : Fin 25 → Set A) (prog : List (Bool × ℕ × ℕ)) (o : ℕ),
   ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
     PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = prog.length ∧ C.output = o ∧
     ∀ (s : A) (v : Fin 25 → Bool), (∀ i, v i = true ↔ s ∈ col i) →
       ∀ j : ℕ, (C.wires (List.ofFn v)).getD j false = true ↔
         s ∈ (prog.foldl (fun (w : List (Set A)) g => w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)) (List.ofFn col)).getD j ∅) →
(have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (25 : ℕ) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (25 : ℕ)) => if ↑x4 < (12 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) (↑x4 + (1 : ℕ)) ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) (↑x4 - (12 : ℕ)) ∈ x3); have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, x5 + x4 ∉ x1}; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x4 ∧     x4.size ≤ (61 : ℕ) ∧       x4.output < (25 : ℕ) + x4.size ∧         x5 < (25 : ℕ) + x4.size ∧           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x2 x6 x7));           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) => (x4.wires (List.ofFn (x2 x7 x8))).getD x5 Bool.false;           (∀ (x8 x9 : Fin (13 : ℕ)), x8 + x9 ∈ x1 → (x8 ≠ (0 : Fin (13 : ℕ)) → x6 {x8} {x9} = Bool.true) ∧ (x8 = (0 : Fin (13 : ℕ)) → x7 ∅ {x9} = Bool.true)) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (3 : ℕ) → x6 x8 (x3 x8) = Bool.false ∧ x6 (x3 x8) x8 = Bool.false ∧ x7 x8 (x3 x8 \ x1) = Bool.false ∧ x7 (x3 x8) (x8 \ x1) = Bool.false) := by
  intro search compile
  let A := Finset (Fin 13) × Finset (Fin 13)
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let col : Fin 25 → Set A := fun i => {s |
    if i.val < 12 then Fin.ofNat 13 (i.val + 1) ∈ s.1 else Fin.ofNat 13 (i.val - 12) ∈ s.2}
  let edge : Set A := {s | ∃ p ∈ s.1, p ≠ 0 ∧ ∃ l ∈ s.2, p + l ∈ D}
  let flag : Set A := {s | ∃ l ∈ s.2, l ∈ D}
  let bits (s t : Finset (Fin 13)) (i : Fin 25) :=
    if i.val < 12 then decide (Fin.ofNat 13 (i.val + 1) ∈ s)
    else decide (Fin.ofNat 13 (i.val - 12) ∈ t)
  let off (s : Finset (Fin 13)) : Finset (Fin 13) := {l : Fin 13 | ∀ p ∈ s, p + l ∉ D}
  obtain ⟨prog, o, q, hsize, ho, hq, main, lower, upper⟩ := search
  obtain ⟨C, mono, sz, out, wire⟩ := compile col prog o
  let rows := prog.foldl (fun (w : List (Set A)) g => w.concat (if g.1 = true then w.getD g.2.1 ∅ ∩ w.getD g.2.2 ∅ else w.getD g.2.1 ∅ ∪ w.getD g.2.2 ∅)) (List.ofFn col)
  change rows.getD o ∅ = edge at main
  change flag \ edge ⊆ rows.getD q ∅ at lower
  change rows.getD q ∅ ⊆ flag ∪ edge at upper
  have hw (s t : Finset (Fin 13)) (j : ℕ) :
      (C.wires (List.ofFn (bits s t))).getD j false = true ↔ (s,t) ∈ rows.getD j ∅ := by
    apply wire
    intro i
    change bits s t i = true ↔ (if i.val < 12 then Fin.ofNat 13 (i.val + 1) ∈ s else Fin.ofNat 13 (i.val - 12) ∈ t)
    by_cases h : i.val < 12 <;> simp [bits, h]
  have hm (s t : Finset (Fin 13)) :
      C.eval (List.ofFn (bits s t)) = true ↔ (s,t) ∈ edge := by
    change (C.wires (List.ofFn (bits s t))).getD C.output false = true ↔ (s,t) ∈ edge
    simpa only [out, main] using hw s t o
  have miss (s t : Finset (Fin 13)) (h : ∀ p ∈ s, ∀ l ∈ t, p + l ∉ D) :
      (s,t) ∉ edge := by
    rintro ⟨p, hp, _, l, hl, hpl⟩
    exact h p hp l hl hpl
  have missMain (s t : Finset (Fin 13)) (h : (s,t) ∉ edge) :
      C.eval (List.ofFn (bits s t)) = false :=
    Bool.eq_false_iff.mpr (fun yes => h ((hm s t).mp yes))
  have missAux (s t : Finset (Fin 13)) (h : (s,t) ∉ edge) (f : (s,t) ∉ flag) :
      (C.wires (List.ofFn (bits s t))).getD q false = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    exact (upper ((hw s t q).mp yes)).elim f h
  refine ⟨C, q, mono, by simpa [sz] using hsize, by simpa [out, sz] using ho,
    by simpa [sz] using hq, ?_, ?_⟩
  · intro p l hpl
    constructor
    · intro hn
      exact (hm {p} {l}).mpr ⟨p, by simp, hn, l, by simp, hpl⟩
    · rintro rfl
      apply (hw ∅ {l} q).mpr
      apply lower
      exact ⟨⟨l, by simp, by simpa [D] using hpl⟩, by rintro ⟨p, hp, _⟩; exact Finset.notMem_empty p hp⟩
  · intro s _
    have left : ∀ p ∈ s, ∀ l ∈ off s, p + l ∉ D := by
      intro p hp l hl
      exact (Finset.mem_filter.mp hl).2 p hp
    have right : ∀ p ∈ off s, ∀ l ∈ s, p + l ∉ D := by
      intro p hp l hl
      simpa only [add_comm p l] using left l hl p hp
    refine ⟨missMain _ _ (miss _ _ left), missMain _ _ (miss _ _ right), ?_, ?_⟩
    · apply missAux s (off s \ D)
      · exact miss _ _ fun p hp l hl => left p hp l (Finset.mem_sdiff.mp hl).1
      · rintro ⟨l, hl, hd⟩
        exact (Finset.mem_sdiff.mp hl).2 hd
    · apply missAux (off s) (s \ D)
      · exact miss _ _ fun p hp l hl => right p hp l (Finset.mem_sdiff.mp hl).1
      · rintro ⟨l, hl, hd⟩
        exact (Finset.mem_sdiff.mp hl).2 hd
