import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7840_2
  (perGate : ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.WellFormed → C.Computes (SimpleGraph.fromRel (fun a b : Fin 42 => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ))) →
  (∀ g, Disjoint (C.leftVars g) (C.rightVars g)) → C.size ≤ 20 →
  let D : Finset (Fin 21) := {0,5,7,17,20}
  let E := fun (d i : Fin 21) => ({Fin.castAdd 21 i, Fin.natAdd 21 (i + d)} : Finset (Fin 42))
  let hit := fun (g : Fin C.size) (d i : Fin 21) => (∃ v ∈ C.leftVars g, v ∈ E d i) ∧ ∃ v ∈ C.rightVars g, v ∈ E d i
  let own := fun (g : Fin C.size) (d i : Fin 21) => hit g d i ∧ ∀ k < g, ¬ hit k d i
  let dup := fun (g : Fin C.size) (d : Fin 21) => ∃ i j : Fin 21, i ≠ j ∧ own g d i ∧ own g d j
  ∀ g, {d : Fin 21 | d ∈ D ∧ dup g d}.ncard ≤ 2)
  (allGates : ∀ C : PEqualNP.AndCount.AndCountCircuit 42, C.WellFormed → C.Computes (SimpleGraph.fromRel (fun a b : Fin 42 => a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0,5,7,17,20] : List ℕ))) →
  (∀ g, Disjoint (C.leftVars g) (C.rightVars g)) → C.size ≤ 20 →
  let D : Finset (Fin 21) := {0,5,7,17,20}
  let E := fun (d i : Fin 21) => ({Fin.castAdd 21 i, Fin.natAdd 21 (i + d)} : Finset (Fin 42))
  let hit := fun (g : Fin C.size) (d i : Fin 21) => (∃ v ∈ C.leftVars g, v ∈ E d i) ∧ ∃ v ∈ C.rightVars g, v ∈ E d i
  let own := fun (g : Fin C.size) (d i : Fin 21) => hit g d i ∧ ∀ k < g, ¬ hit k d i
  let dup := fun (g : Fin C.size) (d : Fin 21) => ∃ i j : Fin 21, i ≠ j ∧ own g d i ∧ own g d j
  {g : Fin C.size | ∃ d ∈ D, dup g d}.ncard ≤ 2) :
  have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → (∃ (x8 : Fin x2.size), ∃ x9 ∈ x2.leftVars x8, ∃ x10 ∈ x2.rightVars x8, ¬x1.Adj x9 x10) → (21 : ℕ) ≤ x2.size := by
  classical
  intro G C wf computes empty _ apart _
  by_contra! low
  have small : C.size ≤ 20 := by omega
  let D : Finset (Fin 21) := {0,5,7,17,20}
  let E := fun (d i : Fin 21) => ({Fin.castAdd 21 i, Fin.natAdd 21 (i + d)} : Finset (Fin 42))
  let hit := fun (g : Fin C.size) (d i : Fin 21) => (∃ v ∈ C.leftVars g, v ∈ E d i) ∧ ∃ v ∈ C.rightVars g, v ∈ E d i
  let own := fun (g : Fin C.size) (d i : Fin 21) => hit g d i ∧ ∀ k < g, ¬ hit k d i
  let dup := fun (g : Fin C.size) (d : Fin 21) => ∃ i j : Fin 21, i ≠ j ∧ own g d i ∧ own g d j
  have each (g : Fin C.size) : (D.filter (dup g)).card ≤ 2 := by
    have equal : (↑(D.filter (dup g)) : Set (Fin 21)) = {d | d ∈ D ∧ dup g d} := by ext; simp
    rw [←Set.ncard_coe_finset, equal]
    exact perGate C wf computes apart small g
  let B := Finset.univ.filter (fun g => ∃ d ∈ D, dup g d)
  have few : B.card ≤ 2 := by
    have equal : (↑B : Set (Fin C.size)) = {g | ∃ d ∈ D, dup g d} := by ext; simp [B]
    rw [←Set.ncard_coe_finset, equal]
    exact allGates C wf computes apart small
  have flags : ∀ d ∈ D, ∀ i : Fin 21, G.Adj (Fin.castAdd 21 i) (Fin.natAdd 21 (i+d)) := by decide +kernel
  have hitFrom (d i : Fin 21) (t : ℕ) (g : Fin C.size) (on : C.gateValFuel (E d i) t g = true) : ∃ k, hit k d i := by
    induction t generalizing g with
    | zero => contradiction
    | succ t ih =>
      change (_ && _) = true at on
      obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp on
      rcases of_decide_eq_true left with L | ⟨k, _, _, hk⟩
      · rcases of_decide_eq_true right with R | ⟨k, _, _, hk⟩
        · exact ⟨g,L,R⟩
        · exact ih k hk
      · exact ih k hk
  have chooseOwner (d : Fin 21) (hd : d ∈ D) (i : Fin 21) : ∃ g, own g d i := by
    have on : C.eval (E d i) = true := (computes _).mpr
      ⟨Fin.castAdd 21 i, by simp [E], Fin.natAdd 21 (i+d), by simp [E], flags d hd i⟩
    obtain bad | ⟨g, _, hg⟩ := of_decide_eq_true on
    · simp [empty] at bad
    obtain ⟨k,hk⟩ := hitFrom d i C.size g hg
    let S := Finset.univ.filter (fun j => hit j d i)
    have mem (j : Fin C.size) : j ∈ S ↔ hit j d i := by simp [S]
    have nonempty : S.Nonempty := ⟨k,(mem k).mpr hk⟩
    refine ⟨S.min' nonempty,(mem _).mp (S.min'_mem nonempty),?_⟩
    intro j hj hh
    exact (not_lt_of_ge (S.min'_le j ((mem _).mpr hh))) hj
  have repeated (d : Fin 21) (hd : d ∈ D) : ∃ g, dup g d := by
    choose f hf using chooseOwner d hd
    by_contra none
    have inj : Function.Injective f := by
      intro i j eq
      by_contra ij
      exact none ⟨f i,i,j,ij,hf i,eq.symm ▸ hf j⟩
    have bound := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_fin] at bound
    omega
  have cover : D ⊆ B.biUnion (fun g => D.filter (dup g)) := by
    intro d hd
    obtain ⟨g,hg⟩ := repeated d hd
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,d,hd,hg⟩,Finset.mem_filter.mpr ⟨hd,hg⟩⟩
  have count := (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul B (fun g => D.filter (dup g)) 2 (fun g _ => each g))
  have five : D.card = 5 := by decide
  omega
