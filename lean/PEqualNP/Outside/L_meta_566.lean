import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_566_aux

open PEqualNP.AndCount

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (v₁ v₂ : Fin k → Bool)
    (h : ∀ j : Fin k, j < i → v₁ j = v₂ j) :
    AndCountCircuit.sideTrue U B F i v₁ = AndCountCircuit.sideTrue U B F i v₂ := by
  unfold AndCountCircuit.sideTrue
  congr 1
  apply propext
  constructor
  · rintro (hb | ⟨j, hjF, hji, hv⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨j, hjF, hji, h j hji ▸ hv⟩
  · rintro (hb | ⟨j, hjF, hji, hv⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨j, hjF, hji, (h j hji).symm ▸ hv⟩

private lemma gateValFuel_eq_of_gt {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val = m → ∀ d : ℕ, m < d →
      C.gateValFuel U d i = C.gateValFuel U (m + 1) i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi d hd
    cases d with
    | zero => omega
    | succ d' =>
      simp only [AndCountCircuit.gateValFuel]
      have hagree : ∀ j : Fin C.size, j < i →
          C.gateValFuel U d' j = C.gateValFuel U m j := by
        intro j hji
        have hjlt : j.val < m := hi ▸ hji
        have h1 := ih j.val hjlt j rfl d' (by omega)
        have h2 := ih j.val hjlt j rfl m hjlt
        exact h1.trans h2.symm
      rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hagree,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hagree]

private lemma gateVal_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i =
      (AndCountCircuit.sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
        AndCountCircuit.sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have hfuel : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_eq_of_gt C U i.val i rfl C.size i.isLt
  rw [hfuel]
  simp only [AndCountCircuit.gateValFuel]
  have hagree : ∀ j : Fin C.size, j < i →
      C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    have h1 := gateValFuel_eq_of_gt C U j.val j rfl i.val hji
    have h2 := gateValFuel_eq_of_gt C U j.val j rfl C.size j.isLt
    exact h1.trans h2.symm
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hagree,
    sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hagree]

private lemma gateVal_mono {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)} (hUV : U ⊆ V) :
    ∀ (m : ℕ) (i : Fin C.size), i.val = m → C.gateVal U i = true → C.gateVal V i = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi htrue
    rw [gateVal_eq] at htrue ⊢
    rw [Bool.and_eq_true] at htrue ⊢
    obtain ⟨hL, hR⟩ := htrue
    constructor
    · simp only [AndCountCircuit.sideTrue, decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjT⟩
      · exact Or.inl ⟨v, hvB, hUV hvU⟩
      · exact Or.inr ⟨j, hjF, hji, ih j.val (hi ▸ hji) j rfl hjT⟩
    · simp only [AndCountCircuit.sideTrue, decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjT⟩
      · exact Or.inl ⟨v, hvB, hUV hvU⟩
      · exact Or.inr ⟨j, hjF, hji, ih j.val (hi ▸ hji) j rfl hjT⟩

end PEqualNP.Outside.L_meta_566_aux

open PEqualNP.AndCount PEqualNP.Outside.L_meta_566_aux in
theorem PEqualNP.Outside.L_meta_566 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n)
    (S : Finset (Fin n)),
    C.WellFormed → C.Computes G →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
        C'.WellFormed ∧
        (∀ U : Finset (Fin n),
          C'.eval U = true ↔ ∃ a ∈ U, ∃ c ∈ U, G.Adj a c ∧ a ∉ S ∧ c ∉ S) ∧
        C'.size + (Finset.univ.filter
          (fun i : Fin C.size => C.gateVal (Finset.univ \ S) i = false)).card ≤ C.size := by
  classical
  intro n G C S hWF hComp
  let D : Finset (Fin C.size) :=
    Finset.univ.filter (fun i : Fin C.size => C.gateVal (Finset.univ \ S) i = false)
  let K : Finset (Fin C.size) :=
    Finset.univ.filter (fun i : Fin C.size => C.gateVal (Finset.univ \ S) i = true)
  let e : Fin K.card ↪o Fin C.size := K.orderEmbOfFin rfl
  have he_mem : ∀ a : Fin K.card, e a ∈ K := fun a => Finset.orderEmbOfFin_mem K rfl a
  have he_surj : ∀ j : Fin C.size, j ∈ K → ∃ a : Fin K.card, e a = j := by
    intro j hj
    have hrange : Set.range e = (K : Set (Fin C.size)) := Finset.range_orderEmbOfFin K rfl
    have : j ∈ Set.range e := hrange ▸ hj
    exact this
  let C' : AndCountCircuit n :=
    { size := K.card
      leftVars := fun a => C.leftVars (e a) \ S
      leftGates := fun a => Finset.univ.filter (fun b : Fin K.card => e b ∈ C.leftGates (e a))
      rightVars := fun a => C.rightVars (e a) \ S
      rightGates := fun a => Finset.univ.filter (fun b : Fin K.card => e b ∈ C.rightGates (e a))
      outVars := C.outVars \ S
      outGates := Finset.univ.filter (fun b : Fin K.card => e b ∈ C.outGates) }
  have hWF' : C'.WellFormed := by
    intro a
    constructor
    · intro b hb
      have hmem : e b ∈ C.leftGates (e a) := (Finset.mem_filter.mp hb).2
      exact e.lt_iff_lt.mp ((hWF (e a)).1 (e b) hmem)
    · intro b hb
      have hmem : e b ∈ C.rightGates (e a) := (Finset.mem_filter.mp hb).2
      exact e.lt_iff_lt.mp ((hWF (e a)).2 (e b) hmem)
  have hval : ∀ (U : Finset (Fin n)) (m : ℕ) (a : Fin C'.size), a.val = m →
      C'.gateVal U a = C.gateVal (U \ S) (e a) := by
    intro U m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro a ha
      rw [gateVal_eq C' U a, gateVal_eq C (U \ S) (e a)]
      have hside : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
          AndCountCircuit.sideTrue U (B \ S)
            (Finset.univ.filter (fun b : Fin K.card => e b ∈ F)) a (C'.gateVal U) =
          AndCountCircuit.sideTrue (U \ S) B F (e a) (C.gateVal (U \ S)) := by
        intro B F
        unfold AndCountCircuit.sideTrue
        congr 1
        apply propext
        constructor
        · rintro (⟨v, hvBS, hvU⟩ | ⟨b, hbF, hba, hbv⟩)
          · obtain ⟨hvB, hvS⟩ := Finset.mem_sdiff.mp hvBS
            exact Or.inl ⟨v, hvB, Finset.mem_sdiff.mpr ⟨hvU, hvS⟩⟩
          · have hebF : e b ∈ F := (Finset.mem_filter.mp hbF).2
            have heba : e b < e a := e.lt_iff_lt.mpr hba
            have hih := ih b.val (ha ▸ hba) b rfl
            exact Or.inr ⟨e b, hebF, heba, hih ▸ hbv⟩
        · rintro (⟨v, hvB, hvUS⟩ | ⟨j, hjF, hjea, hjv⟩)
          · obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hvUS
            exact Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨hvB, hvS⟩, hvU⟩
          · have hsub : U \ S ⊆ Finset.univ \ S :=
              Finset.sdiff_subset_sdiff (Finset.subset_univ U) (Finset.Subset.refl S)
            have hjK : j ∈ K :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ j, gateVal_mono C hsub j.val j rfl hjv⟩
            obtain ⟨b, rfl⟩ := he_surj j hjK
            have hba : b < a := e.lt_iff_lt.mp hjea
            have hih := ih b.val (ha ▸ hba) b rfl
            exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hjF⟩, hba, hih.symm ▸ hjv⟩
      dsimp only [C']
      rw [hside (C.leftVars (e a)) (C.leftGates (e a)),
        hside (C.rightVars (e a)) (C.rightGates (e a))]
  have heval : ∀ U : Finset (Fin n),
      C'.eval U = true ↔ ∃ a ∈ U, ∃ c ∈ U, G.Adj a c ∧ a ∉ S ∧ c ∉ S := by
    intro U
    have heq : C'.eval U = true ↔ C.eval (U \ S) = true := by
      simp only [AndCountCircuit.eval, decide_eq_true_eq]
      constructor
      · rintro (⟨v, hv, hvU⟩ | ⟨b, hb, hbv⟩)
        · obtain ⟨hvO, hvS⟩ := Finset.mem_sdiff.mp hv
          exact Or.inl ⟨v, hvO, Finset.mem_sdiff.mpr ⟨hvU, hvS⟩⟩
        · have hebO : e b ∈ C.outGates := (Finset.mem_filter.mp hb).2
          exact Or.inr ⟨e b, hebO, (hval U b.val b rfl) ▸ hbv⟩
      · rintro (⟨v, hvO, hvUS⟩ | ⟨j, hjO, hjv⟩)
        · obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hvUS
          exact Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨hvO, hvS⟩, hvU⟩
        · have hsub : U \ S ⊆ Finset.univ \ S :=
            Finset.sdiff_subset_sdiff (Finset.subset_univ U) (Finset.Subset.refl S)
          have hjK : j ∈ K :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, gateVal_mono C hsub j.val j rfl hjv⟩
          obtain ⟨b, rfl⟩ := he_surj j hjK
          exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hjO⟩,
            (hval U b.val b rfl).symm ▸ hjv⟩
    rw [heq, hComp (U \ S)]
    constructor
    · rintro ⟨a, ha, c, hc, hadj⟩
      obtain ⟨haU, haS⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hcU, hcS⟩ := Finset.mem_sdiff.mp hc
      exact ⟨a, haU, c, hcU, hadj, haS, hcS⟩
    · rintro ⟨a, haU, c, hcU, hadj, haS, hcS⟩
      exact ⟨a, Finset.mem_sdiff.mpr ⟨haU, haS⟩, c, Finset.mem_sdiff.mpr ⟨hcU, hcS⟩, hadj⟩
  have hcard : K.card + D.card = C.size := by
    have hdisj : Disjoint K D := by
      rw [Finset.disjoint_left]
      intro i hiK hiD
      have h1 := (Finset.mem_filter.mp hiK).2
      have h2 := (Finset.mem_filter.mp hiD).2
      rw [h1] at h2
      exact Bool.false_ne_true h2.symm
    have hunion : K ∪ D = Finset.univ := by
      ext i
      simp only [K, D, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases C.gateVal (Finset.univ \ S) i <;> simp
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  exact ⟨C', hWF', heval, by change K.card + D.card ≤ C.size; omega⟩
