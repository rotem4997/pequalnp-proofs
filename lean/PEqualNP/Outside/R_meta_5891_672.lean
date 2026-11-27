import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 50000 in
set_option synthInstance.maxSize 2048 in
theorem PEqualNP.Outside.R_meta_5891_672
    (grid : ∃ (C : Circuit) (q : ℕ), MetaComplexity.Monotone2 C ∧ C.size ≤ 29 ∧
      C.output < 17+C.size ∧ q < 17+C.size ∧ ∀ x : Fin 17 → Bool,
      let h := fun (i j : Fin 17) => i.val < 6 ∧
        (j.val = 15 + i.val / 3 ∨ (6 ≤ j.val ∧ j.val < 15 ∧
        (if i.val < 3 then (j.val - 6) / 3 else (j.val - 6) % 3) = i.val % 3))
      (C.eval (List.ofFn x) = true ↔ ∃ i j, h i j ∧ x i = true ∧ x j = true) ∧
      (C.eval (List.ofFn x) = false →
        (C.wires (List.ofFn x)).getD q false = (x 15 || x 16)))
    (parallelCopies : ∀ (C : Circuit) (q : ℕ), MetaComplexity.Monotone2 C →
      C.output < 17+C.size → q < 17+C.size → ∀ (f g : Fin 17 → Fin 25),
      ∃ (B : Circuit) (r : ℕ), MetaComplexity.Monotone2 B ∧ B.size ≤ 2*C.size+2 ∧
      B.output < 25+B.size ∧ r < 25+B.size ∧ ∀ x : Fin 25 → Bool,
      let a := List.ofFn (fun i => x (f i))
      let b := List.ofFn (fun i => x (g i))
      B.eval (List.ofFn x) = (C.eval a || C.eval b) ∧
      (B.wires (List.ofFn x)).getD r false = ((C.wires a).getD q false || (C.wires b).getD q false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (60 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let E := fun (i j : Fin 25) => i.val < 12 ∧ 12 ≤ j.val ∧
    (i.val+j.val+2)%13 ∈ ([0,1,3,9] : List ℕ)
  let H := fun (i j : Fin 17) => i.val < 6 ∧
    (j.val = 15 + i.val / 3 ∨ (6 ≤ j.val ∧ j.val < 15 ∧
    (if i.val < 3 then (j.val - 6) / 3 else (j.val - 6) % 3) = i.val % 3))
  let f : Fin 17 → Fin 25 := ![0,2,8,1,7,11,24,20,14,23,18,22,19,17,16,12,13]
  let g : Fin 17 → Fin 25 := ![5,9,10,3,4,6,22,20,19,24,16,18,17,23,14,15,21]
  have liftEdge : ∀ i j : Fin 17, H i j → E (f i) (f j) ∧ E (g i) (g j) := by decide +kernel
  have cover : ∀ i j : Fin 25, E i j →
      (∃ a b, H a b ∧ f a = i ∧ f b = j) ∨
      (∃ a b, H a b ∧ g a = i ∧ g b = j) := by decide +kernel
  let full := fun (x : Fin 25 → Bool) => ∃ i j, E i j ∧ x i = true ∧ x j = true
  let half := fun (x : Fin 17 → Bool) => ∃ i j, H i j ∧ x i = true ∧ x j = true
  have parts (x : Fin 25 → Bool) : full x ↔ half (fun i => x (f i)) ∨ half (fun i => x (g i)) := by
    constructor
    · rintro ⟨i,j,he,xi,xj⟩
      rcases cover i j he with ⟨a,b,h,rfl,rfl⟩ | ⟨a,b,h,rfl,rfl⟩
      · exact Or.inl ⟨a,b,h,xi,xj⟩
      · exact Or.inr ⟨a,b,h,xi,xj⟩
    · rintro (⟨a,b,h,xa,xb⟩ | ⟨a,b,h,xa,xb⟩)
      · exact ⟨f a,f b,(liftEdge a b h).1,xa,xb⟩
      · exact ⟨g a,g b,(liftEdge a b h).2,xa,xb⟩
  obtain ⟨C,q,cm,cs,co,cq,hC⟩ := grid
  obtain ⟨B,r,bm,bs,bo,br,hB⟩ := parallelCopies C q cm co cq f g
  refine ⟨B,r,bm,by omega,bo,br,?_⟩
  intro x
  let xf := fun i => x (f i)
  let xg := fun i => x (g i)
  obtain ⟨ofst,afst⟩ := hC xf
  obtain ⟨osnd,asnd⟩ := hC xg
  obtain ⟨out,aux⟩ := hB x
  change (B.eval (List.ofFn x) = true ↔ full x) ∧ _
  constructor
  · rw [out,Bool.or_eq_true]
    exact (or_congr ofst osnd).trans (parts x).symm
  · intro hz
    have h : C.eval (List.ofFn xf) = false ∧ C.eval (List.ofFn xg) = false := by
      rw [out] at hz
      exact Bool.or_eq_false_iff.mp hz
    rw [aux,afst h.1,asnd h.2]
    change ((x 12 || x 13) || (x 15 || x 21)) = _
    simp only [Bool.or_assoc]
