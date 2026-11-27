import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 9000000 in
theorem PEqualNP.Outside.R_meta_18415_615
    (tests : let E := fun (p l : Fin 17) => ([33216, 36352, 61440, 70208, 74880, 84224] : List ℕ).getD p.val 0 |>.testBit l.val
     ∃ (C : Circuit) (w : ℕ), Monotone2 C ∧ C.size ≤ 29 ∧ C.output < 17+C.size ∧ w < 17+C.size ∧
       (∀ p l, E p l = true → C.eval (List.ofFn fun i : Fin 17 => decide (i = p ∨ i = l)) = true) ∧
       (∀ j ∈ ([15,16] : List (Fin 17)), (C.wires (List.ofFn fun i => decide (i = j))).getD w false = true) ∧
       ∀ (b : Bool) (P : Finset (Fin 17)), (∀ i ∈ P, i.val < 6) →
         let L := fun j : Fin 17 => (b = false ∨ j.val < 15) ∧ ∀ i ∈ P, E i j = false
         ∀ u : Fin 17 → Bool,
           (∀ i, u i = true ↔ if i.val < 6 then ∀ j, E i j = true → ¬ L j else L i) →
             (C.wires (List.ofFn u)).getD (if b then w else C.output) false = false)
    (mono : ∀ (C : Circuit), Monotone2 C → ∀ a b : List Bool, List.Forall₂ (· ≤ ·) a b → ∀ i : ℕ, (C.wires a).getD i false ≤ (C.wires b).getD i false) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (29 : ℕ) ∧       x1.output < (17 : ℕ) + x1.size ∧         x2 < (17 : ℕ) + x1.size ∧           ∀ (x3 : Fin (17 : ℕ) → Bool),             have x4 : Fin (17 : ℕ) → Fin (17 : ℕ) → Prop := fun (x4 x5 : Fin (17 : ℕ)) => ↑x4 < (6 : ℕ) ∧ (↑x5 = (15 : ℕ) + ↑x4 / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑x5 ∧ ↑x5 < (15 : ℕ) ∧ (if ↑x4 < (3 : ℕ) then (↑x5 - (6 : ℕ)) / (3 : ℕ) else (↑x5 - (6 : ℕ)) % (3 : ℕ)) = ↑x4 % (3 : ℕ));             (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (17 : ℕ)) (x6 : Fin (17 : ℕ)), x4 x5 x6 ∧ x3 x5 = Bool.true ∧ x3 x6 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (15 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ))))) := by
  classical
  let E := fun (p l : Fin 17) => ([33216, 36352, 61440, 70208, 74880, 84224] : List ℕ).getD p.val 0 |>.testBit l.val
  have edge : ∀ p l : Fin 17, E p l = true ↔ ↑p < (6 : ℕ) ∧ (↑l = (15 : ℕ) + ↑p / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑l ∧ ↑l < (15 : ℕ) ∧ (if ↑p < (3 : ℕ) then (↑l - (6 : ℕ)) / (3 : ℕ) else (↑l - (6 : ℕ)) % (3 : ℕ)) = ↑p % (3 : ℕ)) := by decide +kernel
  have sides : ∀ p l, E p l = true → p.val < 6 ∧ 6 ≤ l.val := by decide +kernel
  obtain ⟨C,w,hm,hs,ho,hw,hp,ha,hn⟩ := tests
  refine ⟨C,w,hm,hs,ho,hw,?_⟩
  intro x
  dsimp only
  let W := fun (y : Fin 17 → Bool) (i : ℕ) => (C.wires (List.ofFn y)).getD i false
  have leW (a b : Fin 17 → Bool) (h : a ≤ b) (w' : ℕ) : W a w' ≤ W b w' := by
    apply mono C hm
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp only [List.length_ofFn], ?_⟩
    intro i hi hj
    rw [List.get_ofFn, List.get_ofFn]
    exact h _
  let H := ∃ p l, E p l = true ∧ x p = true ∧ x l = true
  have positive (h : H) : W x C.output = true := by
    obtain ⟨p,l,he,hp',hl⟩ := h
    have hd : (fun i : Fin 17 => decide (i = p ∨ i = l)) ≤ x := by
      intro i
      by_cases hh : i = p ∨ i = l
      · rcases hh with rfl | rfl
        · rw [hp']; exact Bool.le_true _
        · rw [hl]; exact Bool.le_true _
      · simp [hh]
    have z := leW _ _ hd C.output
    have ht : W (fun i : Fin 17 => decide (i = p ∨ i = l)) C.output = true := hp p l he
    rw [ht] at z
    exact le_antisymm (Bool.le_true _) z
  have negative (absent : ¬ H) (b : Bool)
      (special : b = true → x 15 = false ∧ x 16 = false) : W x (if b then w else C.output) = false := by
    let P := Finset.univ.filter fun i : Fin 17 => i.val < 6 ∧ x i = true
    let L := fun j : Fin 17 => (b = false ∨ j.val < 15) ∧ ∀ i ∈ P, E i j = false
    let U := fun i : Fin 17 => if i.val < 6 then @decide (∀ j, E i j = true → ¬ L j) (Classical.propDecidable _) else @decide (L i) (Classical.propDecidable _)
    have allowed : ∀ i ∈ P, i.val < 6 := by intro i hi; exact (Finset.mem_filter.mp hi).2.1
    have up : x ≤ U := by
      intro i
      cases hx : x i with
      | false => exact Bool.false_le _
      | true =>
        by_cases hleft : i.val < 6
        · have hi : i ∈ P := by simp [P,hleft,hx]
          have no : ∀ j, E i j = true → ¬ L j := by
            intro j ej lj
            exact Bool.noConfusion (ej.symm.trans (lj.2 i hi))
          simp only [U, if_pos hleft]
          exact le_of_eq (@decide_eq_true _ (Classical.propDecidable _) no).symm
        · have yes : L i := by
            constructor
            · cases b with
              | false => exact Or.inl rfl
              | true =>
                right
                have hh := special rfl
                by_contra! high
                have : i = 15 ∨ i = 16 := by omega
                rcases this with rfl | rfl
                · exact Bool.noConfusion (hx.symm.trans hh.1)
                · exact Bool.noConfusion (hx.symm.trans hh.2)
            · intro p mem
              have active := (Finset.mem_filter.mp mem).2.2
              cases he : E p i with
              | false => rfl
              | true => exact False.elim (absent ⟨p,i,he,active,hx⟩)
          simp only [U, if_neg hleft]
          exact le_of_eq (@decide_eq_true _ (Classical.propDecidable _) yes).symm
    have z := leW x U up (if b then w else C.output)
    have hzero : W U (if b then w else C.output) = false := by
      apply hn b P allowed U
      intro i
      change U i = true ↔ if i.val < 6 then ∀ j, E i j = true → ¬ L j else L i
      by_cases hi : i.val < 6
      · simp only [U, if_pos hi, decide_eq_true_eq]
      · simp only [U, if_neg hi, decide_eq_true_eq]
    exact le_antisymm (hzero ▸ z) (Bool.false_le _)
  have main : W x C.output = true ↔ H := by
    constructor
    · intro eq; by_contra h
      have off : W x C.output = false := negative h false (by simp)
      exact Bool.noConfusion (eq.symm.trans off)
    · exact positive
  constructor
  · change W x C.output = true ↔ _
    rw [main]
    change (∃ p l, E p l = true ∧ x p = true ∧ x l = true) ↔ _
    simp only [edge, and_assoc]
  · intro low
    change W x C.output = false at low
    have absent : ¬H := fun h => Bool.noConfusion ((positive h).symm.trans low)
    by_cases hit : x 15 = true ∨ x 16 = true
    · obtain ⟨j,hj,hx⟩ : ∃ j ∈ ([15,16] : List (Fin 17)), x j = true := by
        rcases hit with h|h
        · exact ⟨15,by simp,h⟩
        · exact ⟨16,by simp,h⟩
      have dir : (fun i : Fin 17 => decide (i = j)) ≤ x := by
        intro i; by_cases e : i = j
        · subst i; simp [hx]
        · simp [e]
      have good : W (fun i : Fin 17 => decide (i = j)) w = true := ha j hj
      have z := leW _ _ dir w
      rw [good] at z
      have on := le_antisymm (Bool.le_true _) z
      change W x w = _
      rcases hit with h | h <;> simp [on,h]
    · have hh : x 15 = false ∧ x 16 = false := by simpa using hit
      have off := negative absent true (fun _ => hh)
      change W x w = _
      simpa [hh] using off
