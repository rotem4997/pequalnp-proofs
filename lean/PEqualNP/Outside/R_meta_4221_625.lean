import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4221_625
    (normalize : ∀ (m k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ k →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = k ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ i : Fin D.gates.length, ∀ w ∈ (D.gates.get i).inputs, w ≤ m + i.val) ∧
        ∀ xs : List Bool, xs.length = m → ∀ w : ℕ, (D.wires xs).getD w false = (C.wires xs).getD w false)
    (pair : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ws : List ℕ) (u v : Fin 26 → Bool),
      ws ≠ [] → ws.length ≤ 2 → (∀ i, u i = false ∨ v i = false) →
      (∀ z ∈ [u,v], PEqualNP.CircuitLowerBounds.GateOp.and.eval
        (ws.map (fun w => (C.wires (List.ofFn z)).getD w false)) = true) →
      ∃ a b : Fin C.size, a ≤ b ∧ ∀ z : Fin 26 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (ws.map (fun w => (C.wires (List.ofFn z)).getD w false)) =
          ((C.wires (List.ofFn z)).getD (26+a.val) false &&
           (C.wires (List.ofFn z)).getD (26+b.val) false))
    (finish : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin C.size),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w ≤ m + i.val) → a ≤ b →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ i : Fin D.gates.length, ∀ w ∈ (D.gates.get i).inputs, w ≤ m + i.val) ∧
        ∀ xs : List Bool, xs.length = m →
          ((D.wires xs).getD (m+a.val) false && (D.wires xs).getD (m+(D.size-1)) false) =
          ((C.wires xs).getD (m+a.val) false && (C.wires xs).getD (m+b.val) false))
    (search :
      let E := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
      let row := fun (P L : Finset (Fin 13)) (v : Fin 26) =>
        if v.val < 13 then decide (Fin.ofNat 13 v.val ∈ P) else decide (Fin.ofNat 13 v.val ∈ L)
      let avoid := fun S : Finset (Fin 13) => Finset.univ.filter (fun l => ∀ p ∈ S, ¬ E p l)
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a : ℕ),
        D.size = 62 → PEqualNP.MetaComplexity.Monotone2 D →
        (∀ i : Fin D.gates.length, ∀ w ∈ (D.gates.get i).inputs, w ≤ 26 + i.val) → a < D.size →
        let f := fun P L =>
          let wires := D.wires (List.ofFn (row P L))
          wires.getD (26+a) false && wires.getD 87 false
        (∀ p l, E p l → f {p} {l} = true) →
        (∀ S, S.card ≤ 3 → f S (avoid S) = false ∧ f (avoid S) S = false) → False) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),
     PEqualNP.MetaComplexity.Monotone2 x1 →
       x2.length ≤ (2 : ℕ) →
         (∃ x5 ∈ x2, (26 : ℕ) ≤ x5) →
           (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
             have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);
             have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};
             have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x11 : ℕ) => (x1.wires (List.ofFn (x7 x9 x10))).getD x11 Bool.false) x2);
             (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →
             (63 : ℕ) ≤ x1.size := by
  intro C ws mono len contains spec
  by_contra! small
  have hsize : C.size ≤ 62 := by omega
  obtain ⟨D, hk, hmono, bounds, same⟩ := normalize 26 62 C mono hsize
  let E := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
  let row := fun (P L : Finset (Fin 13)) (v : Fin 26) =>
    if v.val < 13 then decide (Fin.ofNat 13 v.val ∈ P) else decide (Fin.ofNat 13 v.val ∈ L)
  let avoid := fun S : Finset (Fin 13) => Finset.univ.filter (fun l => ∀ p ∈ S, ¬ E p l)
  let sig := fun (A : PEqualNP.CircuitLowerBounds.Circuit) (z : Fin 26 → Bool) =>
    PEqualNP.CircuitLowerBounds.GateOp.and.eval (ws.map (fun w => (A.wires (List.ofFn z)).getD w false))
  change (∀ p l, E p l → sig C (row {p} {l}) = true) ∧
    (∀ S, S.card ≤ 3 → sig C (row S (avoid S)) = false ∧ sig C (row (avoid S) S) = false) at spec
  have transfer (z : Fin 26 → Bool) : sig D z = sig C z := by
    dsimp only [sig]
    congr 1
    apply List.map_congr_left
    intro w _
    exact same (List.ofFn z) (by simp) w
  have nonempty : ws ≠ [] := by
    rintro rfl
    simp at contains
  have split : ∀ i, row {0} {0} i = false ∨ row {1} {2} i = false := by decide
  have both : ∀ z ∈ [row {0} {0}, row {1} {2}], sig D z = true := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact (transfer _).trans (spec.1 0 0 (by decide))
    · exact (transfer _).trans (spec.1 1 2 (by decide))
  obtain ⟨a,b,hab,hpair⟩ := pair D ws (row {0} {0}) (row {1} {2}) nonempty len split both
  obtain ⟨F, hlen, fmono, fbounds, finalPair⟩ := finish 26 D a b hmono bounds hab
  have last (z : Fin 26 → Bool) :
      ((F.wires (List.ofFn z)).getD (26+a.val) false && (F.wires (List.ofFn z)).getD 87 false) = sig C z := by
    have h := finalPair (List.ofFn z) (by simp)
    have num : 26 + (F.size - 1) = 87 := by omega
    rw [num] at h
    exact h.trans ((hpair z).symm.trans (transfer z))
  apply search F a.val (hlen.trans hk) fmono fbounds (hlen.symm ▸ a.isLt)
  · intro p l e
    exact (last _).trans (spec.1 p l e)
  · intro S hS
    obtain ⟨left, right⟩ := spec.2 S hS
    exact ⟨(last _).trans left,
           (last _).trans right⟩