import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each node lists the positive and negative inputs for which it takes responsibility.
-- An OR node may divide the positive inputs between its children. An AND node may divide the negatives.
theorem PEqualNP.Outside.R_meta_2567_527
    (protocol :
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, near p l ∧ x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ b ∈ ([1, 13, 15] : List (Fin 26)), ∃ o : Bool,
      let s := (List.ofFn fun (i : Fin 26) (x : Fin 26 → Bool) => x i) ++
          [fun x => if o then x 0 || x b else x 0 && x b]
      let init := s.map fun f (q : Bool) => {x | f x = q}
      ∃ (t : List (Bool → Set (Fin 26 → Bool))) (r : Bool → Set (Fin 26 → Bool)),
        t.length ≤ 62 ∧ r ∈ init ++ t ∧ (∀ i : Fin t.length,
        let avail := init ++ t.take i.val
        ∃ u ∈ avail, ∃ v ∈ avail, ∃ k : Bool, ∀ q : Bool,
          (t.get i) q ⊆ if q = k then u q ∪ v q else u q ∩ v q) ∧
          ∀ x, (Minimal F x → x ∈ r true) ∧ (Maximal (fun y => ¬ F y) x → x ∈ r false))
    (compile : ∀ (n : ℕ) (s : List ((Fin n → Bool) → Bool))
        (t : List (Bool → Set (Fin n → Bool))) (r : Bool → Set (Fin n → Bool)),
      let init := s.map fun f (q : Bool) => {x | f x = q}
      r ∈ init ++ t → (∀ i : Fin t.length,
        let avail := init ++ t.take i.val
        ∃ u ∈ avail, ∃ v ∈ avail, ∃ k : Bool, ∀ q : Bool,
          (t.get i) q ⊆ if q = k then u q ∪ v q else u q ∩ v q) →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ t.length ∧
        ∀ (x : Fin n → Bool) (q : Bool), x ∈ r q → C.eval (s.map fun f => f x) = q)
    (boundary :
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, near p l ∧ x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
      (∀ p l, near p l → Minimal F (vec {p} {l})) ∧
        ∀ s, s.card ≤ 3 → Maximal (fun x => ¬ F x) (vec s (off s)) ∧
          Maximal (fun x => ¬ F x) (vec (off s) s)) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, near p l ∧ x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
  obtain ⟨b, hb, o, t, r, ht, hr, hbuild, hroot⟩ := protocol
  let s := (List.ofFn fun (i : Fin 26) (x : Fin 26 → Bool) => x i) ++
          [fun x => if o then x 0 || x b else x 0 && x b]
  obtain ⟨C, hmono, hsize, hrun⟩ := compile 26 s t r hr hbuild
  let op : GateOp := if o then .or else .and
  have eval (x : Fin 26 → Bool) (q : Bool) (h : x ∈ r q) :
      C.eval (List.ofFn x ++ [op.eval [x 0, x b]]) = q := by
    have eq : s.map (fun f => f x) = List.ofFn x ++ [op.eval [x 0, x b]] := by
      have operation (a c : Bool) : op.eval [a, c] = (if o then a || c else a && c) := by
        cases o <;> cases a <;> cases c <;> rfl
      simp [s, operation]
    rw [← eq]
    exact hrun x q h
  have op_ok : op = .and ∨ op = .or := by cases o <;> simp [op, *]
  have pair_ok : ((0 : Fin 26), b) ∈ ([(0, 1), (0, 13), (0, 15)] : List (Fin 26 × Fin 26)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    rcases hb with h | h | h <;> simp [h]
  refine ⟨op, 0, b, C, op_ok, pair_ok, hmono, hsize.trans ht, ?_, ?_⟩
  · intro p l hadj
    exact eval (vec {p} {l}) true ((hroot _).1 (boundary.1 p l hadj))
  · intro a ha
    obtain ⟨hleft, hright⟩ := boundary.2 a ha
    exact ⟨eval (vec a (off a)) false ((hroot _).2 hleft),
      eval (vec (off a) a) false ((hroot _).2 hright)⟩
