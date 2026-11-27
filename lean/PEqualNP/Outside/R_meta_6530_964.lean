import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_6530_964
    (compiler :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    let X := Fin n → Bool
    let B : Set (Set X) := {∅, Set.univ} ∪ Set.range (fun i : Fin n => {x | x i = true})
    ∃ F : Finset (Set X), F.card ≤ C.size ∧ (∀ z ∈ F, z ∉ B) ∧
      (∀ U : Set (Set X), B ⊆ U →
        (∀ a ∈ U, ∀ b ∈ U, ∀ z ∈ F, z = a ∩ b ∨ z = a ∪ b → z ∈ U) →
        ∀ z ∈ F, z ∈ U) ∧
      ∀ j : ℕ, {x : X | (C.wires (List.ofFn x)).getD j false = true} ∈ B ∪ (F : Set (Set X)))
    (barrier :
      let X := Fin 26 → Bool
      let B : Set (Set X) := {∅, Set.univ} ∪ Set.range (fun i : Fin 26 => {x | x i = true})
      let G : Set X := {x | ∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
        x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true}
      ∀ F : Finset (Set X), F.card ≤ 62 → (∀ z ∈ F, z ∉ B) →
        ∃ U : Set (Set X), B ⊆ U ∧
          (∀ a ∈ U, ∀ b ∈ U, ∀ z ∈ F, z = a ∩ b ∨ z = a ∪ b → z ∈ U) ∧
          ∀ a ∈ U, ∀ b ∈ U, a ∩ b ≠ G) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size := by
  intro C pins hm plen hfun
  let X := Fin 26 → Bool
  let B : Set (Set X) := {∅, Set.univ} ∪ Set.range (fun i : Fin 26 => {x | x i = true})
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let pt (p : Fin 13) := p.castAdd 13
  let ln (l : Fin 13) := Fin.natAdd 13 l
  let G : Set X := {x | ∃ p l : Fin 13, near p l ∧ x (pt p) = true ∧ x (ln l) = true}
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let wire (i : ℕ) : Set X := {x | (C.wires (List.ofFn x)).getD i false = true}
  let yes : Set X := {x | PEqualNP.CircuitLowerBounds.GateOp.and.eval
    (pins.map fun j => (C.wires (List.ofFn x)).getD j false) = true}
  obtain ⟨F, hc, fresh, ground, wires⟩ := compiler 26 C hm
  change ∀ i, wire i ∈ B ∪ (F : Set (Set X)) at wires
  have topB : (Set.univ : Set X) ∈ B := Or.inl (by simp)
  have eval_and (l : List Bool) : PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := rfl
  have ends : ∃ a ∈ B ∪ (F : Set (Set X)), ∃ b ∈ B ∪ (F : Set (Set X)), yes = a ∩ b := by
    cases e : pins with
    | nil =>
      refine ⟨_, Or.inl topB, _, Or.inl topB, ?_⟩
      ext x
      simp [yes,e,eval_and]
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨_, wires i, _, Or.inl topB, ?_⟩
        ext x
        simp [yes,e,eval_and,wire]
      | cons j tail =>
        cases tail with
        | nil =>
          refine ⟨_, wires i, _, wires j, ?_⟩
          ext x
          simp [yes,e,eval_and,wire]
        | cons k tail => simp [e] at plen
  obtain ⟨a,ha,b,hb,meet⟩ := ends
  have exactPG : yes = G := by
    ext x
    let s := Finset.univ.filter fun p : Fin 13 => x (pt p) = true
    let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
    have repr : vec s t = x := by
      funext i
      by_cases hi : i.val < 13
      · have hp : pt (Fin.ofNat 13 i.val) = i := Fin.ext (Nat.mod_eq_of_lt hi)
        simp only [vec,ite_eq_left hi,s,Finset.mem_filter,Finset.mem_univ,true_and,hp]
        simp
      · have hl : ln (Fin.ofNat 13 i.val) = i := by
          apply Fin.ext
          change 13+i.val % 13 = i.val
          omega
        simp only [vec,ite_eq_right hi,t,Finset.mem_filter,Finset.mem_univ,true_and,hl]
        simp
    have giff : x ∈ G ↔ ∃ p ∈ s, ∃ l ∈ t, near p l := by
      change (∃ p l, near p l ∧ _ ∧ _) ↔ _
      simp only [s,t,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨p,l,h,hp,hl⟩
        exact ⟨p,hp,l,hl,h⟩
      · rintro ⟨p,hp,l,hl,h⟩
        exact ⟨p,l,h,hp,hl⟩
    rw [giff,←repr]
    exact hfun s t
  by_contra short
  obtain ⟨U,base,locked,blocked⟩ := barrier F (by omega) fresh
  have lift : B ∪ (F : Set (Set X)) ⊆ U := fun z hz => hz.elim (fun h => base h) (ground U base locked z)
  exact blocked a (lift ha) b (lift hb) (meet.symm.trans exactPG)
