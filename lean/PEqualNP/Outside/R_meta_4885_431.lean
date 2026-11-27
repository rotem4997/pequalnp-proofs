import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The four lines through point zero form the pencil. Removing them leaves
-- nine lines and twelve points, the dual affine plane of order three.
-- The shared input is the first gate, the disjunction of points zero and one.
theorem PEqualNP.Outside.R_meta_4885_431
    (affine :
      let U := ((List.ofFn fun i : Fin 26 => fun x : Fin 26 → Bool => x i) ++
        [fun x : Fin 26 → Bool => x 0 || x 1]).map fun f (q : Bool) => {x | f x = q}
      let hit := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        l.val ∉ ([0, 1, 3, 9] : List ℕ) ∧
        (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ (t : List (Bool → Set (Fin 26 → Bool))) (r : Bool → Set (Fin 26 → Bool)),
        t.length ≤ 43 ∧ r ∈ U ++ t ∧
        (∀ i : Fin t.length, let W := U ++ t.take i.val
          ∃ a ∈ W, ∃ b ∈ W, ∃ op : Bool, ∀ q : Bool,
            t.get i q ⊆ if q = op then a q ∪ b q else a q ∩ b q) ∧
        ∀ x, (hit x → x ∈ r true) ∧ (¬hit x → x ∈ r false))
    (pencil :
      let U := ((List.ofFn fun i : Fin 26 => fun x : Fin 26 → Bool => x i) ++
        [fun x : Fin 26 → Bool => x 0 || x 1]).map fun f (q : Bool) => {x | f x = q}
      let hit := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        l.val ∈ ([0, 1, 3, 9] : List ℕ) ∧
        (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ (t : List (Bool → Set (Fin 26 → Bool))) (r : Bool → Set (Fin 26 → Bool)),
        t.length ≤ 18 ∧ r ∈ U ++ t ∧
        (∀ i : Fin t.length, let W := U ++ t.take i.val
          ∃ a ∈ W, ∃ b ∈ W, ∃ op : Bool, ∀ q : Bool,
            t.get i q ⊆ if q = op then a q ∪ b q else a q ∩ b q) ∧
        ∀ x, (hit x → x ∈ r true) ∧ (¬hit x → x ∈ r false)) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ x3 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ))],   ∃ (x4 : Bool),     have x5 : List ((Fin (26 : ℕ) → Bool) → Bool) := (List.ofFn fun (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (26 : ℕ) → Bool) => if x4 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x3 else x5 (0 : Fin (26 : ℕ)) && x5 x3];     have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x6 : (Fin (26 : ℕ) → Bool) → Bool) (x7 : Bool) => {x8 : Fin (26 : ℕ) → Bool | x6 x8 = x7}) x5;     ∃ (x7 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x8 : Bool → Set (Fin (26 : ℕ) → Bool)),       x7.length ≤ (62 : ℕ) ∧         x8 ∈ x6 ++ x7 ∧           (∀ (x9 : Fin x7.length),               have x10 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x6 ++ List.take (↑x9) x7;               ∃ x11 ∈ x10, ∃ x12 ∈ x10, ∃ (x13 : Bool), ∀ (x14 : Bool), x7.get x9 x14 ⊆ if x14 = x13 then x11 x14 ∪ x12 x14 else x11 x14 ∩ x12 x14) ∧             ∀ (x9 : Fin (26 : ℕ) → Bool), (Minimal x2 x9 → x9 ∈ x8 Bool.true) ∧ (Maximal (fun (x10 : Fin (26 : ℕ) → Bool) => ¬x2 x10) x9 → x9 ∈ x8 Bool.false) := by
  let U := ((List.ofFn fun i : Fin 26 => fun x : Fin 26 → Bool => x i) ++
    [fun x : Fin 26 → Bool => x 0 || x 1]).map fun f (q : Bool) => {x | f x = q}
  let W := Bool → Set (Fin 26 → Bool)
  let step := fun (bank : List W) (w : W) =>
    ∃ a ∈ bank, ∃ b ∈ bank, ∃ op : Bool, ∀ q : Bool,
      w q ⊆ if q = op then a q ∪ b q else a q ∩ b q
  let good := fun (bank t : List W) => ∀ i : Fin t.length, step (bank ++ t.take i.val) (t.get i)
  have weaken (a b : List W) (inc : ∀ w ∈ a, w ∈ b) (w : W) (h : step a w) : step b w := by
    obtain ⟨u, hu, v, hv, op, hc⟩ := h
    exact ⟨u, inc _ hu, v, inc _ hv, op, hc⟩
  have join (bank a b : List W) (ha : good bank a) (hb : good (bank ++ a) b) : good bank (a ++ b) := by
    intro i
    change step (bank ++ (a ++ b).take i.val) (a ++ b)[i.val]
    by_cases h : i.val < a.length
    · rw [List.take_append_of_le_length (Nat.le_of_lt h), List.getElem_append_left h]
      exact ha ⟨i.val, h⟩
    · have hle : a.length ≤ i.val := Nat.le_of_not_lt h
      have hi : i.val < a.length + b.length := i.isLt.trans_le (List.length_append ..).le
      rw [List.take_append, List.take_of_length_le hle, List.getElem_append_right hle, ← List.append_assoc]
      exact hb ⟨i.val - a.length, by omega⟩
  obtain ⟨a, u, ha, hu, ga, coverA⟩ := affine
  obtain ⟨b, v, hb, hv, gb, coverB⟩ := pencil
  let out : W := fun q => if q then u q ∪ v q else u q ∩ v q
  have g : good U (a ++ b) := by
    apply join U a b ga
    intro i
    apply weaken _ _ _ _ (gb i)
    intro w hw
    simp only [List.mem_append] at hw ⊢
    tauto
  have root : step (U ++ (a ++ b)) out := by
    refine ⟨u, ?_, v, ?_, true, ?_⟩
    · change u ∈ U ++ a at hu
      simp only [List.mem_append] at hu ⊢
      tauto
    · change v ∈ U ++ b at hv
      simp only [List.mem_append] at hv ⊢
      tauto
    · intro q
      cases q <;> exact fun _ h => h
  have ext : good U ((a ++ b) ++ [out]) := by
    apply join U (a ++ b) [out] g
    rintro ⟨n, hn⟩
    have hz : n = 0 := by change n < 1 at hn; omega
    subst n
    simpa using root
  refine ⟨1, by decide, true, (a ++ b) ++ [out], out, ?_, ?_, ext, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp
  · intro x
    constructor
    · intro h
      obtain ⟨p, l, hi, hp, hl⟩ := h.1
      by_cases hL : l.val ∈ ([0, 1, 3, 9] : List ℕ)
      · exact Or.inr ((coverB x).1 ⟨p, l, hL, hi, hp, hl⟩)
      · exact Or.inl ((coverA x).1 ⟨p, l, hL, hi, hp, hl⟩)
    · intro h
      constructor
      · apply (coverA x).2
        rintro ⟨p, l, _, hi, hp, hl⟩
        exact h.1 ⟨p, l, hi, hp, hl⟩
      · apply (coverB x).2
        rintro ⟨p, l, _, hi, hp, hl⟩
        exact h.1 ⟨p, l, hi, hp, hl⟩
