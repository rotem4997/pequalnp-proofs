import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_5919_53
    (raw : ∀ (C : Circuit) (U : Finset ℕ) (w : ℕ), w ∈ U → w < 26 → let accepts := fun (U : Finset ℕ) (v : List Bool) => ∀ w ∈ U, (C.wires v).getD w false = true; let edges : Finset ℕ → Finset (Fin 13 × Fin 13) := fun U => (incidences singerLines3).filter fun e => accepts U (incidenceInput {e.1} {e.2}); (edges U).card ≤ 4)
    (remaining : ∀ (C : Circuit) (G : Finset (Finset ℕ)) (A : Finset ℕ), let accepts := fun (U : Finset ℕ) (v : List Bool) => ∀ w ∈ U, (C.wires v).getD w false = true; let edges : Finset ℕ → Finset (Fin 13 × Fin 13) := fun U => (incidences singerLines3).filter fun e => accepts U (incidenceInput {e.1} {e.2}); Monotone2 C → G.card ≤ 12 → C.size + 2 * G.card ≤ 64 → (∀ U ∈ G, U.card ≤ 2 ∧ U ⊆ Finset.range (26 + C.size)) → (∀ U ∈ G, ∃ e ∈ edges U, ∀ V ∈ G, V ≠ U → e ∉ edges V) → (∀ (X Y : Finset (Fin 13)), IsMaximalFalse singerLines3 X Y → ¬InNoLine singerLines3 X ∨ ¬InNoPencil singerLines3 Y → ∀ U ∈ G, ¬accepts U (incidenceInput X Y)) → A ∈ G → (∀ w ∈ A, 26 ≤ w) → 5 ≤ (edges A).card → (∃ e ∈ edges A, ∃ f ∈ edges A, e.1 ∉ singerLines3 f.2 ∧ ¬accepts A (incidenceInput {e.1} {f.2})) → ∃ e ∈ incidences singerLines3, ∀ U ∈ G, e ∉ edges U) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => {x3 : Fin (13 : ℕ) | x3 - x2 ∈ x1}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset (Finset ℕ)),   PEqualNP.MetaComplexity.Monotone2 x3 →     x4.card ≤ (12 : ℕ) →       x3.size + (2 : ℕ) * x4.card ≤ (64 : ℕ) →         (∀ x8 ∈ x4, x8.card ≤ (2 : ℕ) ∧ x8 ⊆ Finset.range ((26 : ℕ) + x3.size)) →           let x9 : Finset ℕ → List Bool → Prop := fun (x9 : Finset ℕ) (x10 : List Bool) => ∀ x11 ∈ x9, (x3.wires x10).getD x11 Bool.false = Bool.true;           (∀ x10 ∈ x4, ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 ∈ x2 x13 ∧ x9 x10 (PEqualNP.GenericRejection.incidenceInput {x12} {x13}) ∧ ∀ x14 ∈ x4, x14 ≠ x10 → ¬x9 x14 (PEqualNP.GenericRejection.incidenceInput {x12} {x13})) →             (∀ (x11 x12 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse x2 x11 x12 → ¬PEqualNP.GenericRejection.InNoLine x2 x11 ∨ ¬PEqualNP.GenericRejection.InNoPencil x2 x12 → ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput x11 x12)) →               (∃ x12 ∈ x4,                   have x13 : Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := {x13 ∈ PEqualNP.HeptadCover.incidences x2 | x9 x12 (PEqualNP.GenericRejection.incidenceInput {x13.1} {x13.2})};                   (5 : ℕ) ≤ x13.card ∧ ∃ x14 ∈ x13, ∃ x15 ∈ x13, x14.1 ∉ x2 x15.2 ∧ ¬x9 x12 (PEqualNP.GenericRejection.incidenceInput {x14.1} {x15.2})) →                 ∃ (x13 : Fin (13 : ℕ)) (x14 : Fin (13 : ℕ)), x13 ∈ x2 x14 ∧ ∀ x15 ∈ x4, ¬x9 x15 (PEqualNP.GenericRejection.incidenceInput {x13} {x14})) := by
  intro ds S C G mono count budget size accepts privateEdge rejects heavy
  have geometry : S = singerLines3 := by
    funext l
    ext p
    have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ ds := by
      change ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13))
      decide +kernel
    change p ∈ Finset.univ.filter (fun q : Fin 13 => q-l ∈ ds) ↔ p ∈ singerLines3 l
    rw [Finset.mem_filter]
    exact (and_iff_right (Finset.mem_univ _)).trans (geom p l).symm
  have agree : ∀ p l, p ∈ S l ↔ p ∈ singerLines3 l := by rw [geometry]; exact fun _ _ => Iff.rfl
  let edges : Finset ℕ → Finset (Fin 13 × Fin 13) := fun U => (incidences singerLines3).filter fun e => accepts U (incidenceInput {e.1} {e.2})
  have mem (e : Fin 13 × Fin 13) (U : Finset ℕ) : e ∈ edges U ↔
      e.1 ∈ S e.2 ∧ accepts U (incidenceInput {e.1} {e.2}) := by
    have inside : e ∈ incidences singerLines3 ↔ e.1 ∈ singerLines3 e.2 :=
      Finset.mem_filter.trans (and_iff_right (Finset.mem_univ e))
    exact Finset.mem_filter.trans (and_congr (inside.trans (agree e.1 e.2).symm) Iff.rfl)
  obtain ⟨A,hA,hbig,hcross⟩ := heavy
  have many : 5 ≤ (edges A).card := by
    rw [geometry] at hbig
    exact hbig
  have byGate : ∀ w ∈ A, 26 ≤ w := by
    intro w hw
    by_contra h
    have cap : (edges A).card ≤ 4 := raw C A w hw (by omega)
    omega
  have cross : ∃ e ∈ edges A, ∃ f ∈ edges A, e.1 ∉ singerLines3 f.2 ∧
      ¬accepts A (incidenceInput {e.1} {f.2}) := by
    rw [geometry] at hcross
    exact hcross
  have exclusive : ∀ U ∈ G, ∃ e ∈ edges U, ∀ V ∈ G, V ≠ U → e ∉ edges V := by
    intro U hU
    obtain ⟨p,l,hl,ha,hprivate⟩ := privateEdge U hU
    refine ⟨(p,l),(mem _ _).mpr ⟨hl,ha⟩,?_⟩
    intro V hV ne hv
    exact hprivate V hV ne ((mem _ _).mp hv).2
  have rejects' : ∀ X Y, IsMaximalFalse singerLines3 X Y →
      ¬InNoLine singerLines3 X ∨ ¬InNoPencil singerLines3 Y →
      ∀ U ∈ G, ¬accepts U (incidenceInput X Y) := by
    simpa only [geometry] using rejects
  obtain ⟨⟨p,l⟩,hl,hmiss⟩ := remaining C G A mono count budget size exclusive rejects'
    hA byGate many cross
  have line : p ∈ S l := by
    apply (agree p l).mpr
    exact (Finset.mem_filter.mp hl).2
  refine ⟨p,l,line,?_⟩
  intro U hU hu
  exact hmiss U hU ((mem _ _).mpr ⟨line,hu⟩)
