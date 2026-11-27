import Mathlib
import PEqualNP.Defs

-- Restore the four flags of line zero using the prescribed first OR of points zero and one.
theorem PEqualNP.Outside.R_meta_4885_17
    (core : let U : List (Bool → Set (Fin 26 → Bool)) := (List.ofFn (fun i : Fin 26 => fun x : Fin 26 → Bool => x i) ++
        [fun x : Fin 26 → Bool => x 0 || x 1]).map (fun h c => {x | h x = c})
      let hit := fun (x : Fin 26 → Bool) (p l : Fin 13) =>
        (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      let f := fun x => ∃ p l, hit x p l
      ∃ (A : List (Bool → Set (Fin 26 → Bool))) (y : Bool → Set (Fin 26 → Bool)),
        A.length ≤ 58 ∧ y ∈ U ++ A ∧ (∀ i : Fin A.length, let P := U ++ A.take i.val
          ∃ a ∈ P, ∃ b ∈ P, ∃ d : Bool, ∀ c : Bool,
            A.get i c ⊆ if c = d then a c ∪ b c else a c ∩ b c) ∧
          ∀ x, (Minimal f x → (∀ p, ¬hit x p 0) → x ∈ y true) ∧
            (Maximal (fun z => ¬f z) x → x ∈ y false))
    (restore : ∀ (X : Type) (U : List (Bool → Set X)),
      let m := fun (d : Bool) (a b : Bool → Set X) (c : Bool) =>
        if c = d then a c ∪ b c else a c ∩ b c
      let ok := fun (A : List (Bool → Set X)) => ∀ i : Fin A.length, let P := U ++ A.take i.val
          ∃ a ∈ P, ∃ b ∈ P, ∃ d : Bool, ∀ c : Bool,
            A.get i c ⊆ if c = d then a c ∪ b c else a c ∩ b c
      ∀ A, ok A → ∀ q ∈ U ++ A, ∀ a ∈ U ++ A, ∀ b ∈ U ++ A,
        ∀ l ∈ U ++ A, ∀ y ∈ U ++ A, ∃ G : List (Bool → Set X),
        G.length = A.length + 4 ∧ ok G ∧
          m true y (m false l (m true (m true q a) b)) ∈ U ++ G) :
  have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ x3 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ))],   ∃ (x4 : Bool),     have x5 : List ((Fin (26 : ℕ) → Bool) → Bool) := (List.ofFn fun (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (26 : ℕ) → Bool) => if x4 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x3 else x5 (0 : Fin (26 : ℕ)) && x5 x3];     have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x6 : (Fin (26 : ℕ) → Bool) → Bool) (x7 : Bool) => {x8 : Fin (26 : ℕ) → Bool | x6 x8 = x7}) x5;     ∃ (x7 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x8 : Bool → Set (Fin (26 : ℕ) → Bool)),       x7.length ≤ (62 : ℕ) ∧         x8 ∈ x6 ++ x7 ∧           (∀ (x9 : Fin x7.length),               have x10 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x6 ++ List.take (↑x9) x7;               ∃ x11 ∈ x10, ∃ x12 ∈ x10, ∃ (x13 : Bool), ∀ (x14 : Bool), x7.get x9 x14 ⊆ if x14 = x13 then x11 x14 ∪ x12 x14 else x11 x14 ∩ x12 x14) ∧             ∀ (x9 : Fin (26 : ℕ) → Bool), (Minimal x2 x9 → x9 ∈ x8 Bool.true) ∧ (Maximal (fun (x10 : Fin (26 : ℕ) → Bool) => ¬x2 x10) x9 → x9 ∈ x8 Bool.false) := by
  classical
  let U : List (Bool → Set (Fin 26 → Bool)) :=
    (List.ofFn (fun i : Fin 26 => fun x : Fin 26 → Bool => x i) ++
      [fun x : Fin 26 → Bool => x 0 || x 1]).map (fun h c => {x | h x = c})
  let z := fun (i : Fin 26) (c : Bool) => {x : Fin 26 → Bool | x i = c}
  let q := fun (c : Bool) => {x : Fin 26 → Bool | (x 0 || x 1) = c}
  let m := fun (d : Bool) (a b : Bool → Set (Fin 26 → Bool)) (c : Bool) =>
    if c = d then a c ∪ b c else a c ∩ b c
  obtain ⟨A,y,hA,hy,valid,bound⟩ := core
  have raw (i : Fin 26) : z i ∈ U := by
    apply List.mem_map.mpr
    exact ⟨fun x => x i, List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩),rfl⟩
  have seed : q ∈ U := by
    apply List.mem_map.mpr
    exact ⟨fun x => x 0 || x 1, List.mem_append_right _ (by simp),rfl⟩
  obtain ⟨G,hG,gvalid,gy⟩ := restore (Fin 26 → Bool) U A valid q
    (List.mem_append_left _ seed) (z 3) (List.mem_append_left _ (raw 3))
    (z 9) (List.mem_append_left _ (raw 9)) (z 13) (List.mem_append_left _ (raw 13)) y hy
  refine ⟨1, by simp, true, G, m true y (m false (z 13) (m true (m true q (z 3)) (z 9))),
    by omega, gy, gvalid, ?_⟩
  have inc0 : ∀ p : Fin 13, (p.val + (0 : Fin 13).val) % 13 ∈ ([0,1,3,9] : List ℕ) ↔
      p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by decide
  intro x
  constructor
  · intro minimal
    change x ∈ y true ∪ ((z 13) true ∩ ((q true ∪ (z 3) true) ∪ (z 9) true))
    by_cases off : ∀ p : Fin 13, ¬ ((p.val + (0 : Fin 13).val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 (0 : Fin 13)) = true)
    · exact Or.inl ((bound x).1 minimal off)
    · obtain ⟨p,hp⟩ := Classical.not_forall.mp off
      obtain ⟨adj,pt,ln⟩ := Classical.not_not.mp hp
      right
      refine ⟨ln,?_⟩
      rcases (inc0 p).mp adj with rfl | rfl | rfl | rfl
      · have h : x 0 = true := pt
        exact Or.inl (Or.inl (by simp [q,h]))
      · have h : x 1 = true := pt
        exact Or.inl (Or.inl (by simp [q,h]))
      · exact Or.inl (Or.inr pt)
      · exact Or.inr pt
  · intro maximal
    change x ∈ y false ∩ ((z 13) false ∪ ((q false ∩ (z 3) false) ∩ (z 9) false))
    refine ⟨(bound x).2 maximal,?_⟩
    by_cases line : x 13 = true
    · right
      have each (p : Fin 13) (hp : p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9) :
          x (Fin.castAdd 13 p) = false := by
        cases hx : x (Fin.castAdd 13 p) with
        | false => rfl
        | true => exact False.elim (maximal.1 ⟨p,0,(inc0 p).mpr hp,hx,line⟩)
      have h0 : x 0 = false := each 0 (by simp)
      have h1 : x 1 = false := each 1 (by simp)
      have h3 : x 3 = false := each 3 (by simp)
      have h9 : x 9 = false := each 9 (by simp)
      simp [z,q,h0,h1,h3,h9]
    · left
      simpa [z] using line
