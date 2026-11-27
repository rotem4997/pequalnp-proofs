import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4241_369
    (cover :
      let D : Finset (Fin 13) := {0,1,3,9}
      let I := fun (p l : Fin 13) => p-l ∈ D
      let W := fun (A : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ A, ¬ I p l
      ∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬ I p l) →
        ((∃ l, ∀ p ∈ P, I p l) ∨ (∃ p, ∀ l ∈ Q, I p l)) →
        ∃ A : Finset (Fin 13), (∀ p ∉ A, ∃ l, W A l ∧ I p l) ∧
          (A.card ≤ 2 ∨ Nat.card { l : Fin 13 // W A l } ≤ 2 ∨ A.card = 3 ∧ ∃ l, ∀ p ∈ A, I p l) ∧
          P ⊆ A ∧ ∀ l ∈ Q, W A l)
    (lower :
      let D : Finset (Fin 13) := {0,1,3,9}
      let I := fun (p l : Fin 13) => p-l ∈ D
      let row := fun (P Q : Finset (Fin 13)) (i : Fin 26) =>
        decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ Q, i = Fin.natAdd 13 l)
      let w := fun (C : Circuit) (o : ℕ) (x : Fin 26 → Bool) => (C.wires (List.ofFn x)).getD o false
      ∀ C : Circuit, Monotone2 C → ∀ a b : Fin (26+C.size), a ≠ b →
        (∀ p l, I p l → (w C a.val (row {p} {l}) && w C b.val (row {p} {l})) = true) →
        (∀ P Q : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ Q, ¬ I p l) →
          ((∃ l, ∀ p ∈ P, I p l) ∨ (∃ p, ∀ l ∈ Q, I p l)) →
          (w C a.val (row P Q) && w C b.val (row P Q)) = false) → 63 ≤ C.size) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → ∀ (x9 x10 : Fin ((26 : ℕ) + x7.size)), x9 ≠ x10 → (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x4 x12 x13), x6 x7 (↑x10) (x4 x12 x13)] = Bool.true) → (∀ (x13 : Finset (Fin (13 : ℕ))), (∀ x14 ∉ x13, ∃ (x16 : Fin (13 : ℕ)), x3 x13 x16 ∧ x2 x14 x16) → (x13.card ≤ (2 : ℕ) ∨ Nat.card { x15 : Fin (13 : ℕ) // x3 x13 x15 } ≤ (2 : ℕ) ∨ x13.card = (3 : ℕ) ∧ ∃ (x15 : Fin (13 : ℕ)), ∀ x16 ∈ x13, x2 x16 x15) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x5 x13), x6 x7 (↑x10) (x5 x13)] = Bool.false) → (63 : ℕ) ≤ x7.size := by
  dsimp only
  intro C mono a b distinct pos deg
  let D : Finset (Fin 13) := {0,1,3,9}
  let row (P Q : Finset (Fin 13)) (i : Fin 26) :=
    decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l ∈ Q, i = Fin.natAdd 13 l)
  have same (p l : Fin 13) : (∃ d ∈ D, p = l+d) ↔ p-l∈D := by
    constructor
    · rintro ⟨d, hd, he⟩
      have eq : p-l=d := sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))
      rwa [eq]
    · intro h
      exact ⟨p-l,h,(sub_add_cancel p l).symm.trans (add_comm _ _)⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have monotone_fold (gs : List Gate) (law : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ w v : List Bool, w.length = v.length →
        (∀ i, w.getD i false = true → v.getD i false = true) →
        ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step v).getD i false = true := by
    induction gs with
    | nil => intro w v len old i h; exact old i h
    | cons g gs ih =>
      intro w v len old
      simp only [List.foldl_cons]
      apply ih (fun h hh => law h (List.mem_cons_of_mem _ hh)) _ _ (by simp [step,len])
      intro i on
      unfold step at on ⊢
      by_cases before : i < w.length
      · rw [List.getD_append _ _ _ _ before] at on
        rw [List.getD_append _ _ _ _ (by omega)]
        exact old i on
      · rw [List.getD_append_right _ _ _ _ (by omega)] at on
        rw [List.getD_append_right _ _ _ _ (by omega),← len]
        have localStep : g.op.eval (g.inputs.map (fun j => w.getD j false)) = true →
            g.op.eval (g.inputs.map (fun j => v.getD j false)) = true := by
          rcases law g List.mem_cons_self with and | or
          · rw [and]
            change ((g.inputs.map fun j => w.getD j false).all id = true) →
              ((g.inputs.map fun j => v.getD j false).all id = true)
            simp only [List.all_eq_true,id_eq]
            intro ready t member
            obtain ⟨j,p,rfl⟩ := List.mem_map.mp member
            exact old j (ready _ (List.mem_map.mpr ⟨j,p,rfl⟩))
          · rw [or]
            change ((g.inputs.map fun j => w.getD j false).any id = true) →
              ((g.inputs.map fun j => v.getD j false).any id = true)
            simp only [List.any_eq_true,id_eq]
            rintro ⟨t,member,eq⟩
            obtain ⟨j,p,rfl⟩ := List.mem_map.mp member
            exact ⟨_,List.mem_map.mpr ⟨j,p,rfl⟩,old j eq⟩
        cases idx : i-w.length with
        | zero => simpa [idx] using localStep (by simpa [idx] using on)
        | succ k =>
          cases k <;> simp [idx] at on
  have wmono (x y : Fin 26 → Bool) (le : ∀ i, x i = true → y i = true) (o : ℕ) :
      (C.wires (List.ofFn x)).getD o false = true → (C.wires (List.ofFn y)).getD o false = true := by
    change (C.gates.foldl step (List.ofFn x)).getD o false = true →
      (C.gates.foldl step (List.ofFn y)).getD o false = true
    apply monotone_fold C.gates (fun g h => (mono g h).1) _ _ (by simp)
    intro i trueI
    by_cases hi : i < 26
    · let j : Fin 26 := ⟨i,hi⟩
      rw [List.getD_eq_getElem _ _ (by simpa using hi)] at trueI ⊢
      simp only [List.getElem_ofFn] at trueI ⊢
      exact le j trueI
    · rw [List.getD_eq_default _ _ (by simp; omega)] at trueI
      contradiction
  apply lower C mono a b distinct
  · intro p l e
    have k := pos p l ((same p l).mpr e)
    have sameRow : row {p} {l} =
        (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) := by
      funext i
      apply decide_eq_decide.mpr
      simp [row,Finset.mem_singleton]
    change ((C.wires (List.ofFn (row {p} {l}))).getD a.val false &&
      (C.wires (List.ofFn (row {p} {l}))).getD b.val false) = true
    rw [sameRow]
    let pair : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    change ([(C.wires (List.ofFn pair)).getD a.val false,
      (C.wires (List.ofFn pair)).getD b.val false].all id) = true at k
    simpa only [List.all_cons,List.all_nil,id_eq,Bool.and_true] using k
  · intro P Q absent rankTwo
    obtain ⟨A,closed,limited,points,lines⟩ := cover P Q absent rankTwo
    have shut := deg A
      (fun p miss => by
        obtain ⟨l,avoid,inc⟩ := closed p miss
        exact ⟨l,fun q h e => avoid q h ((same q l).mp e),(same p l).mpr inc⟩)
      (by
        rcases limited with left | right | ⟨card,l,yes⟩
        · exact Or.inl left
        · right; left
          let e : { l : Fin 13 // ∀ p ∈ A, p-l ∉ D } ≃
              { l : Fin 13 // ∀ p ∈ A, ¬∃ d ∈ D, p=l+d } :=
            { toFun := fun l => ⟨l.val,fun p hp e => l.property p hp ((same p l.val).mp e)⟩
              invFun := fun l => ⟨l.val,fun p hp e => l.property p hp ((same p l.val).mpr e)⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          have counts := Nat.card_congr e
          rw [← counts]
          exact right
        · exact Or.inr (Or.inr ⟨card,l,fun p hp => (same p l).mpr (yes p hp)⟩))
    let big : Fin 26 → Bool := fun j => decide
      ((∃ p ∈ A, j=Fin.castAdd 13 p) ∨ ∃ l : Fin 13, j=Fin.natAdd 13 l ∧ (∀ p ∈ A, ¬∃ d ∈ D, p=l+d))
    have hOrder (i : Fin 26) (e : row P Q i = true) : big i = true := by
      unfold row at e
      rw [decide_eq_true_eq] at e
      unfold big
      apply decide_eq_true_eq.mpr
      rcases e with ⟨p,mem,eq⟩ | ⟨l,mem,eq⟩
      · exact Or.inl ⟨p,points mem,eq⟩
      · exact Or.inr ⟨l,eq,fun p hp edge => (lines l mem p hp) ((same p l).mp edge)⟩
    apply Bool.eq_false_iff.mpr
    intro accepted
    obtain ⟨u,v⟩ := Bool.and_eq_true_iff.mp accepted
    have yesA := wmono (row P Q) big hOrder a.val u
    have yesB := wmono (row P Q) big hOrder b.val v
    change (GateOp.and.eval [(C.wires (List.ofFn big)).getD a.val false,
      (C.wires (List.ofFn big)).getD b.val false]) = false at shut
    rw [yesA,yesB] at shut
    contradiction
