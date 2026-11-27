import Mathlib
import PEqualNP.Defs

namespace Gap634

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

theorem gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]

theorem gateVal_iff_wf {n : ℕ} (C : AndCountCircuit n) (hC : C.WellFormed) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true)) := by
  rw [gateVal_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases h2 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hC i).1 j hj, hv⟩
    · rcases h2 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hC i).2 j hj, hv⟩

theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

theorem fuel_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
    ∀ d : ℕ, ∀ i : Fin C.size, gateValFuel C U d i = true → gateValFuel C U' d i = true := by
  intro d
  induction d with
  | zero => intro i h; exact absurd h (by simp [gateValFuel])
  | succ d ih =>
    intro i h
    have h' : (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)) = true := h
    show (sideTrue U' (C.leftVars i) (C.leftGates i) i (gateValFuel C U' d) &&
        sideTrue U' (C.rightVars i) (C.rightGates i) i (gateValFuel C U' d)) = true
    rw [Bool.and_eq_true] at h' ⊢
    exact ⟨sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.1,
      sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.2⟩

theorem gateVal_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
  fuel_mono C U U' hU C.size i h

theorem eval_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (h : C.eval U = true) : C.eval U' = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hU hvU⟩
  · exact Or.inr ⟨j, hj, gateVal_mono C U U' hU j hg⟩

theorem fuel_empty {n : ℕ} (C : AndCountCircuit n) :
    ∀ d : ℕ, ∀ i : Fin C.size, gateValFuel C ∅ d i = false := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    show (sideTrue ∅ (C.leftVars i) (C.leftGates i) i (gateValFuel C ∅ d) &&
        sideTrue ∅ (C.rightVars i) (C.rightGates i) i (gateValFuel C ∅ d)) = false
    have : sideTrue ∅ (C.leftVars i) (C.leftGates i) i (gateValFuel C ∅ d) = false := by
      rw [← Bool.not_eq_true, sideTrue_iff]
      rintro (⟨x, _, hx⟩ | ⟨j, _, _, hv⟩)
      · exact absurd hx (Finset.notMem_empty x)
      · rw [ih j] at hv; exact Bool.noConfusion hv
    rw [this, Bool.false_and]

theorem gateVal_empty {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    C.gateVal ∅ i = false :=
  fuel_empty C C.size i

theorem eval_empty {n : ℕ} (C : AndCountCircuit n) : C.eval ∅ = false := by
  rw [← Bool.not_eq_true, eval_iff]
  rintro (⟨x, _, hx⟩ | ⟨j, _, hv⟩)
  · exact absurd hx (Finset.notMem_empty x)
  · rw [gateVal_empty] at hv; exact Bool.noConfusion hv

theorem outVars_empty {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (h : C.Computes G) : C.outVars = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have h1 : C.eval {v} = true := by
    rw [eval_iff]
    exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
  obtain ⟨a, ha, c, hc, hadj⟩ := (h {v}).1 h1
  rw [Finset.mem_singleton] at ha hc
  rw [ha, hc] at hadj
  exact G.loopless.irrefl v hadj

theorem eval_iff_of_computes {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (h : C.Computes G) (U : Finset (Fin n)) :
    C.eval U = true ↔ ∃ j ∈ C.outGates, C.gateVal U j = true := by
  rw [eval_iff, outVars_empty C G h]
  constructor
  · rintro (⟨x, hx, _⟩ | h2)
    · exact absurd hx (Finset.notMem_empty x)
    · exact h2
  · exact Or.inr

theorem gateVal_unique {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (val : Fin C.size → Bool)
    (hval : ∀ i, val i = (sideTrue U (C.leftVars i) (C.leftGates i) i val &&
      sideTrue U (C.rightVars i) (C.rightGates i) i val)) :
    ∀ i, val i = C.gateVal U i := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → val i = C.gateVal U i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      have hc : ∀ j : Fin C.size, j < i → val j = C.gateVal U j := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      rw [hval i, gateVal_rec C U i,
        sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem wit_gate {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (u : Fin n) :
    ∀ m : ℕ, ∀ i : Fin C.size, i.val < m →
      C.gateVal (insert u I) i = true → C.gateVal I i = false →
      ∃ k : Fin C.size, k ≤ i ∧ C.gateVal (insert u I) k = true ∧ C.gateVal I k = false ∧
        ((u ∈ C.leftVars k ∧ Disjoint (C.leftVars k) I ∧
            ∀ j ∈ C.leftGates k, j < k → C.gateVal I j = false) ∨
         (u ∈ C.rightVars k ∧ Disjoint (C.rightVars k) I ∧
            ∀ j ∈ C.rightGates k, j < k → C.gateVal I j = false)) := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi h1 h0
    have side : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)),
        ((∃ x ∈ B, x ∈ insert u I) ∨ ∃ j ∈ F, j < i ∧ C.gateVal (insert u I) j = true) →
        ¬ ((∃ x ∈ B, x ∈ I) ∨ ∃ j ∈ F, j < i ∧ C.gateVal I j = true) →
        (u ∈ B ∧ Disjoint B I ∧ ∀ j ∈ F, j < i → C.gateVal I j = false) ∨
        ∃ j : Fin C.size, j < i ∧ C.gateVal (insert u I) j = true ∧ C.gateVal I j = false := by
      intro B F hT hF
      have hg : ∀ j ∈ F, j < i → C.gateVal I j = false := by
        intro j hj hji
        rw [← Bool.not_eq_true]
        intro hv
        exact hF (Or.inr ⟨j, hj, hji, hv⟩)
      rcases hT with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
      · rcases Finset.mem_insert.1 hxU with hxu | hxI
        · refine Or.inl ⟨hxu ▸ hx, ?_, hg⟩
          exact Finset.disjoint_left.2 (fun y hy hyI => hF (Or.inl ⟨y, hy, hyI⟩))
        · exact absurd (Or.inl ⟨x, hx, hxI⟩) hF
      · exact Or.inr ⟨j, hji, hv, hg j hj hji⟩
    have down : (∃ j : Fin C.size, j < i ∧ C.gateVal (insert u I) j = true ∧
        C.gateVal I j = false) →
        ∃ k : Fin C.size, k ≤ i ∧ C.gateVal (insert u I) k = true ∧ C.gateVal I k = false ∧
        ((u ∈ C.leftVars k ∧ Disjoint (C.leftVars k) I ∧
            ∀ j ∈ C.leftGates k, j < k → C.gateVal I j = false) ∨
         (u ∈ C.rightVars k ∧ Disjoint (C.rightVars k) I ∧
            ∀ j ∈ C.rightGates k, j < k → C.gateVal I j = false)) := by
      rintro ⟨j, hji, hv1, hv0⟩
      have hlt : j.val < m := by
        have : j.val < i.val := hji
        omega
      obtain ⟨k, hk, r⟩ := ih j hlt hv1 hv0
      exact ⟨k, le_trans hk (le_of_lt hji), r⟩
    have g1 := (gateVal_iff C (insert u I) i).1 h1
    have g0 : ¬ _ := fun hh => Bool.noConfusion (h0.symm.trans ((gateVal_iff C I i).2 hh))
    by_cases hL : (∃ x ∈ C.leftVars i, x ∈ I) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal I j = true
    · have hR : ¬ ((∃ x ∈ C.rightVars i, x ∈ I) ∨
          ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal I j = true) := fun hh => g0 ⟨hL, hh⟩
      rcases side _ _ g1.2 hR with hs | hs
      · exact ⟨i, le_refl i, h1, h0, Or.inr hs⟩
      · exact down hs
    · rcases side _ _ g1.1 hL with hs | hs
      · exact ⟨i, le_refl i, h1, h0, Or.inl hs⟩
      · exact down hs

theorem wit_strong {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (hC : C.Computes G) (I : Finset (Fin n)) (hI : ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c)
    (u x : Fin n) (hx : x ∈ I) (hux : G.Adj u x) :
    ∃ k : Fin C.size, C.gateVal (insert u I) k = true ∧ C.gateVal I k = false ∧
        ((u ∈ C.leftVars k ∧ Disjoint (C.leftVars k) I ∧
            ∀ j ∈ C.leftGates k, j < k → C.gateVal I j = false) ∨
         (u ∈ C.rightVars k ∧ Disjoint (C.rightVars k) I ∧
            ∀ j ∈ C.rightGates k, j < k → C.gateVal I j = false)) := by
  have e1 : C.eval (insert u I) = true :=
    (hC _).2 ⟨u, Finset.mem_insert_self u I, x, Finset.mem_insert_of_mem hx, hux⟩
  obtain ⟨o, ho, hv1⟩ := (eval_iff_of_computes C G hC _).1 e1
  have hv0 : C.gateVal I o = false := by
    rw [← Bool.not_eq_true]
    intro hv
    have e0 : C.eval I = true := (eval_iff_of_computes C G hC _).2 ⟨o, ho, hv⟩
    obtain ⟨a, ha, c, hc, hadj⟩ := (hC I).1 e0
    exact hI a ha c hc hadj
  obtain ⟨k, _, r⟩ := wit_gate C I u (o.val + 1) o (Nat.lt_succ_self _) hv1 hv0
  exact ⟨k, r⟩

theorem wit {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (hC : C.Computes G) (I : Finset (Fin n)) (hI : ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c)
    (u x : Fin n) (hx : x ∈ I) (hux : G.Adj u x) :
    ∃ i : Fin C.size, (u ∈ C.leftVars i ∧ Disjoint (C.leftVars i) I) ∨
      (u ∈ C.rightVars i ∧ Disjoint (C.rightVars i) I) := by
  obtain ⟨k, _, _, r⟩ := wit_strong C G hC I hI u x hx hux
  rcases r with ⟨a, b, _⟩ | ⟨a, b, _⟩
  · exact ⟨k, Or.inl ⟨a, b⟩⟩
  · exact ⟨k, Or.inr ⟨a, b⟩⟩

def sL {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) : Bool :=
  sideTrue {v} (C.leftVars i) (C.leftGates i) i (C.gateVal {v})

def sR {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) : Bool :=
  sideTrue {v} (C.rightVars i) (C.rightGates i) i (C.gateVal {v})

def norm {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := Finset.univ.filter (fun v => sL C i v = true ∧ sR C i v = false)
  leftGates := C.leftGates
  rightVars i := Finset.univ.filter (fun v => sR C i v = true ∧ sL C i v = false)
  rightGates := C.rightGates
  outVars := C.outVars ∪
    Finset.univ.filter (fun v => ∃ j ∈ C.outGates, C.gateVal {v} j = true)
  outGates := C.outGates

theorem norm_size {n : ℕ} (C : AndCountCircuit n) : (norm C).size = C.size := rfl

theorem norm_wf {n : ℕ} (C : AndCountCircuit n) (h : C.WellFormed) : (norm C).WellFormed := h

theorem norm_mem_left {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (x : Fin n) :
    x ∈ (norm C).leftVars i ↔ (sL C i x = true ∧ sR C i x = false) := by
  show x ∈ Finset.univ.filter (fun v => sL C i v = true ∧ sR C i v = false) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

theorem norm_mem_right {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (x : Fin n) :
    x ∈ (norm C).rightVars i ↔ (sR C i x = true ∧ sL C i x = false) := by
  show x ∈ Finset.univ.filter (fun v => sR C i v = true ∧ sL C i v = false) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

theorem norm_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((norm C).leftVars i) ((norm C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [norm_mem_left] at hx
  rw [norm_mem_right] at hx'
  exact Bool.noConfusion (hx.1.symm.trans hx'.2)

theorem single_gate {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    C.gateVal {v} i = true ↔ (sL C i v = true ∧ sR C i v = true) := by
  rw [gateVal_rec, Bool.and_eq_true]
  rfl

theorem side_split {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (ih : ∀ j : Fin C.size, j < i →
      (C.gateVal U j = true ↔ (∃ v ∈ U, C.gateVal {v} j = true) ∨ (norm C).gateVal U j = true))
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
    sideTrue U B F i (C.gateVal U) = true ↔
      ((∃ v ∈ U, sideTrue {v} B F i (C.gateVal {v}) = true) ∨
        ∃ j ∈ F, j < i ∧ (norm C).gateVal U j = true) := by
  rw [sideTrue_iff]
  constructor
  · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
    · exact Or.inl ⟨x, hxU, (sideTrue_iff _ _ _ _ _).2
        (Or.inl ⟨x, hx, Finset.mem_singleton_self x⟩)⟩
    · rcases (ih j hji).1 hv with ⟨v, hvU, hg⟩ | hd
      · exact Or.inl ⟨v, hvU, (sideTrue_iff _ _ _ _ _).2 (Or.inr ⟨j, hj, hji, hg⟩)⟩
      · exact Or.inr ⟨j, hj, hji, hd⟩
  · rintro (⟨v, hvU, hs⟩ | ⟨j, hj, hji, hd⟩)
    · rcases (sideTrue_iff _ _ _ _ _).1 hs with ⟨x, hx, hxv⟩ | ⟨j, hj, hji, hg⟩
      · rw [Finset.mem_singleton] at hxv
        exact Or.inl ⟨x, hx, hxv ▸ hvU⟩
      · exact Or.inr ⟨j, hj, hji, gateVal_mono C {v} U
          (Finset.singleton_subset_iff.2 hvU) j hg⟩
    · exact Or.inr ⟨j, hj, hji, (ih j hji).2 (Or.inr hd)⟩

theorem norm_gate_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    (norm C).gateVal U i = true ↔
      (((∃ x ∈ U, sL C i x = true ∧ sR C i x = false) ∨
          ∃ j ∈ C.leftGates i, j < i ∧ (norm C).gateVal U j = true) ∧
       ((∃ x ∈ U, sR C i x = true ∧ sL C i x = false) ∨
          ∃ j ∈ C.rightGates i, j < i ∧ (norm C).gateVal U j = true)) := by
  have h := gateVal_iff (norm C) U i
  rw [h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨x, hx, hxU⟩ | h1
      · exact Or.inl ⟨x, hxU, (norm_mem_left C i x).1 hx⟩
      · exact Or.inr h1
    · rcases h2 with ⟨x, hx, hxU⟩ | h2
      · exact Or.inl ⟨x, hxU, (norm_mem_right C i x).1 hx⟩
      · exact Or.inr h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with ⟨x, hxU, hx⟩ | h1
      · exact Or.inl ⟨x, (norm_mem_left C i x).2 hx, hxU⟩
      · exact Or.inr h1
    · rcases h2 with ⟨x, hxU, hx⟩ | h2
      · exact Or.inl ⟨x, (norm_mem_right C i x).2 hx, hxU⟩
      · exact Or.inr h2

theorem norm_gate {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ i : Fin C.size, (C.gateVal U i = true ↔
      (∃ v ∈ U, C.gateVal {v} i = true) ∨ (norm C).gateVal U i = true) := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → (C.gateVal U i = true ↔
      (∃ v ∈ U, C.gateVal {v} i = true) ∨ (norm C).gateVal U i = true) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      have ih' : ∀ j : Fin C.size, j < i → (C.gateVal U j = true ↔
          (∃ v ∈ U, C.gateVal {v} j = true) ∨ (norm C).gateVal U j = true) := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      have eL := side_split C U i ih' (C.leftVars i) (C.leftGates i)
      have eR := side_split C U i ih' (C.rightVars i) (C.rightGates i)
      rw [gateVal_rec C U i, Bool.and_eq_true, eL, eR, norm_gate_iff]
      constructor
      · rintro ⟨hl, hr⟩
        by_cases hW : ∃ v ∈ U, C.gateVal {v} i = true
        · exact Or.inl hW
        · refine Or.inr ⟨?_, ?_⟩
          · rcases hl with ⟨v, hvU, hs⟩ | hl
            · refine Or.inl ⟨v, hvU, hs, ?_⟩
              rw [← Bool.not_eq_true]
              intro hs'
              exact hW ⟨v, hvU, (single_gate C i v).2 ⟨hs, hs'⟩⟩
            · exact Or.inr hl
          · rcases hr with ⟨v, hvU, hs⟩ | hr
            · refine Or.inl ⟨v, hvU, hs, ?_⟩
              rw [← Bool.not_eq_true]
              intro hs'
              exact hW ⟨v, hvU, (single_gate C i v).2 ⟨hs', hs⟩⟩
            · exact Or.inr hr
      · rintro (⟨v, hvU, hg⟩ | ⟨hl, hr⟩)
        · have := (single_gate C i v).1 hg
          exact ⟨Or.inl ⟨v, hvU, this.1⟩, Or.inl ⟨v, hvU, this.2⟩⟩
        · refine ⟨?_, ?_⟩
          · rcases hl with ⟨v, hvU, hs, _⟩ | hl
            · exact Or.inl ⟨v, hvU, hs⟩
            · exact Or.inr hl
          · rcases hr with ⟨v, hvU, hs, _⟩ | hr
            · exact Or.inl ⟨v, hvU, hs⟩
            · exact Or.inr hr
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem norm_single {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ i : Fin C.size, (norm C).gateVal {v} i = false := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → (norm C).gateVal {v} i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      have ih' : ∀ j : Fin C.size, j < i → ¬ (norm C).gateVal {v} j = true := by
        intro j hji hv
        have hlt : j.val < m := by
          have : j.val < i.val := hji
          omega
        rw [ih j hlt] at hv
        exact Bool.noConfusion hv
      rw [← Bool.not_eq_true, norm_gate_iff]
      rintro ⟨hl, hr⟩
      rcases hl with ⟨x, hx, h1, _⟩ | ⟨j, _, hji, hv⟩
      · rcases hr with ⟨y, hy, _, h2⟩ | ⟨j, _, hji, hv⟩
        · rw [Finset.mem_singleton] at hx hy
          rw [hx] at h1
          rw [hy] at h2
          exact Bool.noConfusion (h1.symm.trans h2)
        · exact ih' j hji hv
      · exact ih' j hji hv
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem norm_eval {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (norm C).eval U = C.eval U := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  have mo : ∀ x, x ∈ (norm C).outVars ↔
      (x ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {x} j = true) := by
    intro x
    show x ∈ C.outVars ∪
      Finset.univ.filter (fun v => ∃ j ∈ C.outGates, C.gateVal {v} j = true) ↔ _
    rw [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.imp id (fun h => h.2), fun h => h.imp id (fun h => ⟨Finset.mem_univ x, h⟩)⟩
  constructor
  · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
    · rcases (mo x).1 hx with hx | ⟨j, hj, hv⟩
      · exact Or.inl ⟨x, hx, hxU⟩
      · exact Or.inr ⟨j, hj, gateVal_mono C {x} U (Finset.singleton_subset_iff.2 hxU) j hv⟩
    · exact Or.inr ⟨j, hj, (norm_gate C U j).2 (Or.inr hv)⟩
  · rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
    · exact Or.inl ⟨x, (mo x).2 (Or.inl hx), hxU⟩
    · rcases (norm_gate C U j).1 hv with ⟨x, hxU, hg⟩ | hd
      · exact Or.inl ⟨x, (mo x).2 (Or.inr ⟨j, hj, hg⟩), hxU⟩
      · exact Or.inr ⟨j, hj, hd⟩

theorem norm_computes {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (h : C.Computes G) : (norm C).Computes G := by
  intro U
  rw [norm_eval]
  exact h U

theorem exists_norm {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (hw : C.WellFormed) (h : C.Computes G) :
    ∃ D : AndCountCircuit n, D.WellFormed ∧ D.Computes G ∧ D.size = C.size ∧
      (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧
      (∀ v i, D.gateVal {v} i = false) ∧ D.outVars = ∅ :=
  ⟨norm C, norm_wf C hw, norm_computes C G h, rfl, norm_disjoint C, norm_single C,
    outVars_empty (norm C) G (norm_computes C G h)⟩

def sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
    (C.gateVal X)

theorem gate_false_iff {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
  rw [gateVal_rec, Bool.and_eq_false_iff]
  rfl

theorem sv_hit {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (s : Bool)
    (h : ¬ Disjoint (cond s (C.rightVars i) (C.leftVars i)) U) : sv C X i s = true := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨x, hx, hxU⟩ := h
  exact (sideTrue_iff _ _ _ _ _).2 (Or.inl ⟨x, hx, hU hxU⟩)

theorem sv_merge {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) (hX : sv C X i s = false) (hY : sv C Y i s = false)
    (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
      C.gateVal (X ∪ Y) j = false) : sv C (X ∪ Y) i s = false := by
  rw [← Bool.not_eq_true] at hX hY ⊢
  unfold sv at hX hY ⊢
  rw [sideTrue_iff] at hX hY ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact hX (Or.inl ⟨x, hx, h⟩)
    · exact hY (Or.inl ⟨x, hx, h⟩)
  · have h1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

def code {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (i : Fin C.size) : Bool :=
  if ¬ Disjoint (C.leftVars i) U then true
  else if ¬ Disjoint (C.rightVars i) U then false
  else sv C X i false

theorem code_ok {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (code C U X i) = false := by
  rw [gate_false_iff] at h
  unfold code
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · rw [ite_eq_left hl]
    have := sv_hit C U X hU i false hl
    rcases h with h | h
    · rw [this] at h; exact Bool.noConfusion h
    · exact h
  · rw [ite_eq_right hl]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · rw [ite_eq_left hr]
      have := sv_hit C U X hU i true hr
      rcases h with h | h
      · exact h
      · rw [this] at h; exact Bool.noConfusion h
    · rw [ite_eq_right hr]
      cases hb : sv C X i false with
      | false => exact hb
      | true =>
        rcases h with h | h
        · rw [hb] at h; exact Bool.noConfusion h
        · exact h

theorem code_hit {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (i : Fin C.size)
    (h : ¬ Disjoint (C.leftVars i ∪ C.rightVars i) U) : code C U X i = code C U Y i := by
  unfold code
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · rw [ite_eq_left hl, ite_eq_left hl]
  · rw [ite_eq_right hl, ite_eq_right hl]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · rw [ite_eq_left hr, ite_eq_left hr]
    · exfalso
      apply h
      rw [Finset.disjoint_union_left]
      exact ⟨not_not.1 hl, not_not.1 hr⟩

theorem merge_gate {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, code C U X i = code C U Y i) :
    ∀ i : Fin C.size, C.gateVal X i = false → C.gateVal Y i = false →
      C.gateVal (X ∪ Y) i = false := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → C.gateVal X i = false →
      C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi h1 h2
      have ih' : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
          C.gateVal (X ∪ Y) j = false := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      have c1 := code_ok C U X hX i h1
      have c2 := code_ok C U Y hY i h2
      rw [← hc i] at c2
      have hm := sv_merge C X Y i _ c1 c2 ih'
      rw [gate_false_iff]
      cases hb : code C U X i with
      | false => rw [hb] at hm; exact Or.inl hm
      | true => rw [hb] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem merge_eval {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, code C U X i = code C U Y i)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  rw [← Bool.not_eq_true, eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [merge_gate C U X Y hX hY hc j g1 g2] at hv
    exact Bool.noConfusion hv

theorem proj_count {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (m : ℕ)
    (M : Fin m → Finset (Fin n)) (hU : ∀ a, U ⊆ M a) (h0 : ∀ a, C.eval (M a) = false)
    (h1 : ∀ a b, a ≠ b → C.eval (M a ∪ M b) = true) :
    m ≤ 2 ^ (Finset.univ.filter
      (fun i : Fin C.size => Disjoint (C.leftVars i ∪ C.rightVars i) U)).card := by
  let f : Fin m → ({i : Fin C.size // Disjoint (C.leftVars i ∪ C.rightVars i) U} → Bool) :=
    fun a i => code C U (M a) i.1
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hc : ∀ i, code C U (M a) i = code C U (M b) i := by
      intro i
      by_cases hi : Disjoint (C.leftVars i ∪ C.rightVars i) U
      · exact congrFun hab ⟨i, hi⟩
      · exact code_hit C U _ _ i hi
    have := merge_eval C U (M a) (M b) (hU a) (hU b) hc (h0 a) (h0 b)
    rw [h1 a b hne] at this
    exact Bool.noConfusion this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at hcard
  exact hcard

abbrev E634 : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10),
    (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)]

abbrev IHAdj (v u : Fin 14) : Prop := (v, u) ∈ E634 ∨ (u, v) ∈ E634

abbrev IHOpp (v u : Fin 14) : Prop := (v.val < 7 ∧ 7 ≤ u.val) ∨ (u.val < 7 ∧ 7 ≤ v.val)

def Model634 (W : Fin 14 → Finset (Fin 6 × Bool)) : Prop :=
  (∀ v, (W v).Nonempty ∧ (W v).card ≤ 2 ∧ ∀ g, ¬ ((g, false) ∈ W v ∧ (g, true) ∈ W v)) ∧
  (∀ v u, IHAdj v u → ∃ g b, (g, b) ∈ W v ∧ (g, !b) ∈ W u) ∧
  (∀ v u, IHOpp v u → ¬ IHAdj v u → ((W v ∪ W u).image Prod.fst).card ≤ 3) ∧
  (∀ v a b, v ≠ a → v ≠ b → ¬ IHAdj a b → ¬ W v ⊆ W a ∪ W b)

def Indep (S : Finset (Fin 14)) : Prop := ∀ x ∈ S, ∀ y ∈ S, ¬ IHAdj x y

def Mis12 : Prop :=
  ∀ v : Fin 14, ∃ M : Fin 12 → Finset (Fin 14),
    (∀ a, v ∈ M a) ∧ (∀ a, Indep (M a)) ∧ ∀ a b, a ≠ b → ¬ Indep (M a ∪ M b)

def Mis5 : Prop :=
  ∀ v u : Fin 14, IHOpp v u → ¬ IHAdj v u → ∃ M : Fin 5 → Finset (Fin 14),
    (∀ a, v ∈ M a ∧ u ∈ M a) ∧ (∀ a, Indep (M a)) ∧ ∀ a b, a ≠ b → ¬ Indep (M a ∪ M b)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem adj_dec : ∀ a c : Fin 14,
    ((a = 0 ∧ c = 7 ∨ a = 7 ∧ c = 0) ∨ (a = 1 ∧ c = 7 ∨ a = 7 ∧ c = 1) ∨
      (a = 3 ∧ c = 7 ∨ a = 7 ∧ c = 3) ∨ (a = 1 ∧ c = 8 ∨ a = 8 ∧ c = 1) ∨
      (a = 2 ∧ c = 8 ∨ a = 8 ∧ c = 2) ∨ (a = 4 ∧ c = 8 ∨ a = 8 ∧ c = 4) ∨
      (a = 2 ∧ c = 9 ∨ a = 9 ∧ c = 2) ∨ (a = 3 ∧ c = 9 ∨ a = 9 ∧ c = 3) ∨
      (a = 5 ∧ c = 9 ∨ a = 9 ∧ c = 5) ∨ (a = 3 ∧ c = 10 ∨ a = 10 ∧ c = 3) ∨
      (a = 4 ∧ c = 10 ∨ a = 10 ∧ c = 4) ∨ (a = 6 ∧ c = 10 ∨ a = 10 ∧ c = 6) ∨
      (a = 4 ∧ c = 11 ∨ a = 11 ∧ c = 4) ∨ (a = 5 ∧ c = 11 ∨ a = 11 ∧ c = 5) ∨
      (a = 0 ∧ c = 11 ∨ a = 11 ∧ c = 0) ∨ (a = 5 ∧ c = 12 ∨ a = 12 ∧ c = 5) ∨
      (a = 6 ∧ c = 12 ∨ a = 12 ∧ c = 6) ∨ (a = 1 ∧ c = 12 ∨ a = 12 ∧ c = 1) ∨
      (a = 6 ∧ c = 13 ∨ a = 13 ∧ c = 6) ∨ (a = 0 ∧ c = 13 ∨ a = 13 ∧ c = 0) ∨
      (a = 2 ∧ c = 13 ∨ a = 13 ∧ c = 2)) ↔ IHAdj a c := by
  decide

theorem adj_iff (G : SimpleGraph (Fin 14))
    (h : G.edgeSet = {s(0, 7), s(1, 7), s(3, 7), s(1, 8), s(2, 8), s(4, 8), s(2, 9), s(3, 9),
      s(5, 9), s(3, 10), s(4, 10), s(6, 10), s(4, 11), s(5, 11), s(0, 11), s(5, 12), s(6, 12),
      s(1, 12), s(6, 13), s(0, 13), s(2, 13)}) (a c : Fin 14) :
    G.Adj a c ↔ IHAdj a c := by
  rw [← adj_dec a c, ← SimpleGraph.mem_edgeSet, h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]

theorem ih_irr : ∀ a : Fin 14, ¬ IHAdj a a := by decide

theorem ih_nb : ∀ v : Fin 14, ∃ x, IHAdj v x := by decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem free_nb : ∀ v a b : Fin 14, v ≠ a → v ≠ b → ¬ IHAdj a b →
    ∃ x, IHAdj v x ∧ ¬ IHAdj x a ∧ ¬ IHAdj x b := by
  decide

theorem indep3 (a b x : Fin 14) (hab : ¬ IHAdj a b) (hxa : ¬ IHAdj x a) (hxb : ¬ IHAdj x b) :
    Indep {a, b, x} := by
  intro p hp q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> rw [hp, hq] <;>
    first
      | exact ih_irr _
      | exact hab
      | exact hxa
      | exact hxb
      | exact fun hh => hab (Or.symm hh)
      | exact fun hh => hxa (Or.symm hh)
      | exact fun hh => hxb (Or.symm hh)

theorem first_gate {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) :
    ∀ i : Fin C.size, C.gateVal X i = true →
      ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
        (∃ y ∈ C.rightVars k, y ∈ X) := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → C.gateVal X i = true →
      ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
        (∃ y ∈ C.rightVars k, y ∈ X) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hv
      have g := (gateVal_iff C X i).1 hv
      have down : ∀ j : Fin C.size, j < i → C.gateVal X j = true →
          ∃ k : Fin C.size, C.gateVal X k = true ∧ (∃ x ∈ C.leftVars k, x ∈ X) ∧
            (∃ y ∈ C.rightVars k, y ∈ X) := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      rcases g.1 with hl | ⟨j, _, hji, hj⟩
      · rcases g.2 with hr | ⟨j, _, hji, hj⟩
        · exact ⟨i, hv, hl, hr⟩
        · exact down j hji hj
      · exact down j hji hj
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

open Classical in
def WW (D : AndCountCircuit 14) (v : Fin 14) : Finset (Fin 6 × Bool) :=
  Finset.univ.filter (fun p => ∃ h : p.1.val < D.size,
    v ∈ cond p.2 (D.rightVars ⟨p.1.val, h⟩) (D.leftVars ⟨p.1.val, h⟩))

theorem mem_WW (D : AndCountCircuit 14) (v : Fin 14) (g : Fin 6) (b : Bool) :
    (g, b) ∈ WW D v ↔ ∃ h : g.val < D.size,
      v ∈ cond b (D.rightVars ⟨g.val, h⟩) (D.leftVars ⟨g.val, h⟩) := by
  unfold WW
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_of_side (D : AndCountCircuit 14) (hs : D.size ≤ 6) (v : Fin 14) (i : Fin D.size)
    (b : Bool) (hv : v ∈ cond b (D.rightVars i) (D.leftVars i)) :
    (Fin.castLE hs i, b) ∈ WW D v :=
  (mem_WW D v _ b).2 ⟨i.isLt, hv⟩

theorem WW_hit (D : AndCountCircuit 14) (v : Fin 14) (U : Finset (Fin 14)) (hv : v ∈ U)
    (g : Fin 6) (b : Bool) (h : (g, b) ∈ WW D v) :
    ∃ h : g.val < D.size,
      ¬ Disjoint (D.leftVars ⟨g.val, h⟩ ∪ D.rightVars ⟨g.val, h⟩) U := by
  obtain ⟨hg, hm⟩ := (mem_WW D v g b).1 h
  refine ⟨hg, ?_⟩
  rw [Finset.not_disjoint_iff]
  refine ⟨v, ?_, hv⟩
  cases b with
  | false => exact Finset.mem_union_left _ hm
  | true => exact Finset.mem_union_right _ hm

theorem hit_bound (D : AndCountCircuit 14) (hs : D.size ≤ 6) (U : Finset (Fin 14))
    (S : Finset (Fin 6))
    (hS : ∀ g ∈ S, ∃ h : g.val < D.size,
      ¬ Disjoint (D.leftVars ⟨g.val, h⟩ ∪ D.rightVars ⟨g.val, h⟩) U)
    (m : ℕ) (M : Fin m → Finset (Fin 14)) (hU : ∀ a, U ⊆ M a)
    (h0 : ∀ a, D.eval (M a) = false) (h1 : ∀ a b, a ≠ b → D.eval (M a ∪ M b) = true) :
    m ≤ 2 ^ (6 - S.card) := by
  have hp := proj_count D U m M hU h0 h1
  refine le_trans hp (Nat.pow_le_pow_right (by norm_num) ?_)
  have hsub : S ⊆ (Finset.univ.filter (fun i : Fin D.size =>
      ¬ Disjoint (D.leftVars i ∪ D.rightVars i) U)).image (Fin.castLE hs) := by
    intro g hg
    obtain ⟨h, hd⟩ := hS g hg
    exact Finset.mem_image.2 ⟨⟨g.val, h⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩,
      Fin.ext rfl⟩
  have c1 := Finset.card_le_card hsub
  have c2 := Finset.card_image_le (s := Finset.univ.filter (fun i : Fin D.size =>
      ¬ Disjoint (D.leftVars i ∪ D.rightVars i) U)) (f := Fin.castLE hs)
  have c3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin D.size)))
    (fun i : Fin D.size => Disjoint (D.leftVars i ∪ D.rightVars i) U)
  rw [Finset.card_univ, Fintype.card_fin] at c3
  omega

theorem exists_model (G : SimpleGraph (Fin 14))
    (h : G.edgeSet = {s(0, 7), s(1, 7), s(3, 7), s(1, 8), s(2, 8), s(4, 8), s(2, 9), s(3, 9),
      s(5, 9), s(3, 10), s(4, 10), s(6, 10), s(4, 11), s(5, 11), s(0, 11), s(5, 12), s(6, 12),
      s(1, 12), s(6, 13), s(0, 13), s(2, 13)})
    (C : AndCountCircuit 14) (hw : C.WellFormed) (hc : C.Computes G) (hs : C.size ≤ 6)
    (m12 : Mis12) (m5 : Mis5) : ∃ W, Model634 W := by
  obtain ⟨D, _, hDc, hDs, hDd, _, _⟩ := exists_norm C G hw hc
  have hs' : D.size ≤ 6 := le_of_eq_of_le hDs hs
  have adj := adj_iff G h
  have ev0 : ∀ S : Finset (Fin 14), Indep S → D.eval S = false := by
    intro S hS
    rw [← Bool.not_eq_true]
    intro he
    obtain ⟨a, ha, c, hc', hadj⟩ := (hDc S).1 he
    exact hS a ha c hc' ((adj a c).1 hadj)
  have ev1 : ∀ S : Finset (Fin 14), ¬ Indep S → D.eval S = true := by
    intro S hS
    by_contra hne
    apply hS
    intro x hx y hy hxy
    exact hne ((hDc S).2 ⟨x, hx, y, hy, (adj x y).2 hxy⟩)
  have both : ∀ v g, ¬ ((g, false) ∈ WW D v ∧ (g, true) ∈ WW D v) := by
    rintro v g ⟨h1, h2⟩
    obtain ⟨hg, hl⟩ := (mem_WW D v g false).1 h1
    obtain ⟨_, hr⟩ := (mem_WW D v g true).1 h2
    exact Finset.disjoint_left.1 (hDd ⟨g.val, hg⟩) hl hr
  refine ⟨WW D, fun v => ⟨?_, ?_, both v⟩, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := ih_nb v
    have hI : ∀ a ∈ ({x} : Finset (Fin 14)), ∀ c ∈ ({x} : Finset (Fin 14)), ¬ G.Adj a c := by
      intro a ha c hc'
      rw [Finset.mem_singleton] at ha hc'
      rw [ha, hc']
      exact G.loopless.irrefl x
    obtain ⟨i, hi | hi⟩ := wit D G hDc {x} hI v x (Finset.mem_singleton_self x) ((adj v x).2 hx)
    · exact ⟨_, mem_of_side D hs' v i false hi.1⟩
    · exact ⟨_, mem_of_side D hs' v i true hi.1⟩
  · obtain ⟨M, hM1, hM2, hM3⟩ := m12 v
    have hb := hit_bound D hs' {v} ((WW D v).image Prod.fst)
      (by
        intro g hg
        obtain ⟨p, hp, hpg⟩ := Finset.mem_image.1 hg
        rw [← hpg]
        exact WW_hit D v {v} (Finset.mem_singleton_self v) p.1 p.2 hp)
      12 M (fun a => Finset.singleton_subset_iff.2 (hM1 a)) (fun a => ev0 _ (hM2 a))
      (fun a b hab => ev1 _ (hM3 a b hab))
    have hinj : Set.InjOn Prod.fst (↑(WW D v) : Set (Fin 6 × Bool)) := by
      rintro ⟨g, b⟩ hp ⟨g', b'⟩ hq hgg
      have hp' : (g, b) ∈ WW D v := hp
      have hq' : (g', b') ∈ WW D v := hq
      have e : g = g' := hgg
      subst e
      cases b <;> cases b'
      · rfl
      · exact absurd ⟨hp', hq'⟩ (both v g)
      · exact absurd ⟨hq', hp'⟩ (both v g)
      · rfl
    rw [Finset.card_image_of_injOn hinj] at hb
    by_contra hcon
    have h3 : 6 - (WW D v).card ≤ 3 := by omega
    have := le_trans hb (Nat.pow_le_pow_right (by norm_num) h3)
    norm_num at this
  · intro v u hvu
    have he : D.eval {v, u} = true :=
      (hDc {v, u}).2 ⟨v, Finset.mem_insert_self v _, u,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self u), (adj v u).2 hvu⟩
    obtain ⟨o, _, ho⟩ := (eval_iff_of_computes D G hDc _).1 he
    obtain ⟨k, _, ⟨x, hxL, hxX⟩, ⟨y, hyR, hyX⟩⟩ := first_gate D {v, u} o ho
    rw [Finset.mem_insert, Finset.mem_singleton] at hxX hyX
    rcases hxX with hx | hx <;> rcases hyX with hy | hy
    · rw [hx] at hxL
      rw [hy] at hyR
      exact absurd hyR (Finset.disjoint_left.1 (hDd k) hxL)
    · rw [hx] at hxL
      rw [hy] at hyR
      exact ⟨_, false, mem_of_side D hs' v k false hxL, mem_of_side D hs' u k true hyR⟩
    · rw [hx] at hxL
      rw [hy] at hyR
      exact ⟨_, true, mem_of_side D hs' v k true hyR, mem_of_side D hs' u k false hxL⟩
    · rw [hx] at hxL
      rw [hy] at hyR
      exact absurd hyR (Finset.disjoint_left.1 (hDd k) hxL)
  · intro v u hopp hna
    obtain ⟨M, hM1, hM2, hM3⟩ := m5 v u hopp hna
    have hb := hit_bound D hs' {v, u} ((WW D v ∪ WW D u).image Prod.fst)
      (by
        intro g hg
        obtain ⟨p, hp, hpg⟩ := Finset.mem_image.1 hg
        rw [← hpg]
        rcases Finset.mem_union.1 hp with hp | hp
        · exact WW_hit D v {v, u} (Finset.mem_insert_self v _) p.1 p.2 hp
        · exact WW_hit D u {v, u} (Finset.mem_insert_of_mem (Finset.mem_singleton_self u))
            p.1 p.2 hp)
      5 M
      (fun a => by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · rw [hz]; exact (hM1 a).1
        · rw [hz]; exact (hM1 a).2)
      (fun a => ev0 _ (hM2 a)) (fun a b hab => ev1 _ (hM3 a b hab))
    by_contra hcon
    have h3 : 6 - ((WW D v ∪ WW D u).image Prod.fst).card ≤ 2 := by omega
    have := le_trans hb (Nat.pow_le_pow_right (by norm_num) h3)
    norm_num at this
  · intro v a b hva hvb hab hsub
    obtain ⟨x, hvx, hxa, hxb⟩ := free_nb v a b hva hvb hab
    have hI := indep3 a b x hab hxa hxb
    have hI' : ∀ p ∈ ({a, b, x} : Finset (Fin 14)), ∀ q ∈ ({a, b, x} : Finset (Fin 14)),
        ¬ G.Adj p q := fun p hp q hq hpq => hI p hp q hq ((adj p q).1 hpq)
    have ha : a ∈ ({a, b, x} : Finset (Fin 14)) := Finset.mem_insert_self a _
    have hb : b ∈ ({a, b, x} : Finset (Fin 14)) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
    have hx : x ∈ ({a, b, x} : Finset (Fin 14)) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self x))
    have fin : ∀ (i : Fin D.size) (s : Bool),
        v ∈ cond s (D.rightVars i) (D.leftVars i) →
        Disjoint (cond s (D.rightVars i) (D.leftVars i)) ({a, b, x} : Finset (Fin 14)) →
        False := by
      intro i s hv hd
      rcases Finset.mem_union.1 (hsub (mem_of_side D hs' v i s hv)) with hm | hm
      · obtain ⟨_, hm'⟩ := (mem_WW D a _ s).1 hm
        exact Finset.disjoint_left.1 hd hm' ha
      · obtain ⟨_, hm'⟩ := (mem_WW D b _ s).1 hm
        exact Finset.disjoint_left.1 hd hm' hb
    obtain ⟨i, hi | hi⟩ := wit D G hDc {a, b, x} hI' v x hx ((adj v x).2 hvx)
    · exact fin i false hi.1 hi.2
    · exact fin i true hi.1 hi.2

def adjMask (v : Fin 14) : Nat :=
  match v.val with
  | 0 => 10368
  | 1 => 4480
  | 2 => 8960
  | 3 => 1664
  | 4 => 3328
  | 5 => 6656
  | 6 => 13312
  | 7 => 11
  | 8 => 22
  | 9 => 44
  | 10 => 88
  | 11 => 49
  | 12 => 98
  | 13 => 69
  | _ => 0

def adjB (v u : Fin 14) : Bool := Nat.testBit (adjMask v) u.val

theorem adjB_iff (v u : Fin 14) : adjB v u = true ↔ IHAdj v u := by
  revert v u
  decide

def mis37 (k : Fin 37) : List (Fin 14) :=
  match k.val with
  | 0 => [0, 1, 2, 3, 4, 5, 6]
  | 1 => [2, 4, 5, 6, 7]
  | 2 => [0, 3, 5, 6, 8]
  | 3 => [5, 6, 7, 8]
  | 4 => [0, 1, 4, 6, 9]
  | 5 => [4, 6, 7, 9]
  | 6 => [0, 6, 8, 9]
  | 7 => [0, 1, 2, 5, 10]
  | 8 => [2, 5, 7, 10]
  | 9 => [0, 5, 8, 10]
  | 10 => [0, 1, 9, 10]
  | 11 => [1, 2, 3, 6, 11]
  | 12 => [2, 6, 7, 11]
  | 13 => [3, 6, 8, 11]
  | 14 => [1, 6, 9, 11]
  | 15 => [6, 7, 8, 9, 11]
  | 16 => [1, 2, 10, 11]
  | 17 => [0, 2, 3, 4, 12]
  | 18 => [2, 4, 7, 12]
  | 19 => [0, 3, 8, 12]
  | 20 => [0, 4, 9, 12]
  | 21 => [0, 2, 10, 12]
  | 22 => [0, 8, 9, 10, 12]
  | 23 => [2, 3, 11, 12]
  | 24 => [2, 7, 10, 11, 12]
  | 25 => [1, 3, 4, 5, 13]
  | 26 => [4, 5, 7, 13]
  | 27 => [3, 5, 8, 13]
  | 28 => [1, 4, 9, 13]
  | 29 => [1, 5, 10, 13]
  | 30 => [5, 7, 8, 10, 13]
  | 31 => [1, 3, 11, 13]
  | 32 => [1, 9, 10, 11, 13]
  | 33 => [3, 4, 12, 13]
  | 34 => [4, 7, 9, 12, 13]
  | 35 => [3, 8, 11, 12, 13]
  | 36 => [7, 8, 9, 10, 11, 12, 13]
  | _ => []

def idx12 (v : Fin 14) (a : Fin 12) : Fin 37 :=
  match v.val, a.val with
  | 0, 0 => ⟨0, by omega⟩
  | 0, 1 => ⟨2, by omega⟩
  | 0, 2 => ⟨4, by omega⟩
  | 0, 3 => ⟨6, by omega⟩
  | 0, 4 => ⟨7, by omega⟩
  | 0, 5 => ⟨9, by omega⟩
  | 0, 6 => ⟨10, by omega⟩
  | 0, 7 => ⟨17, by omega⟩
  | 0, 8 => ⟨19, by omega⟩
  | 0, 9 => ⟨20, by omega⟩
  | 0, 10 => ⟨21, by omega⟩
  | 0, 11 => ⟨22, by omega⟩
  | 1, 0 => ⟨0, by omega⟩
  | 1, 1 => ⟨4, by omega⟩
  | 1, 2 => ⟨7, by omega⟩
  | 1, 3 => ⟨10, by omega⟩
  | 1, 4 => ⟨11, by omega⟩
  | 1, 5 => ⟨14, by omega⟩
  | 1, 6 => ⟨16, by omega⟩
  | 1, 7 => ⟨25, by omega⟩
  | 1, 8 => ⟨28, by omega⟩
  | 1, 9 => ⟨29, by omega⟩
  | 1, 10 => ⟨31, by omega⟩
  | 1, 11 => ⟨32, by omega⟩
  | 2, 0 => ⟨0, by omega⟩
  | 2, 1 => ⟨1, by omega⟩
  | 2, 2 => ⟨7, by omega⟩
  | 2, 3 => ⟨8, by omega⟩
  | 2, 4 => ⟨11, by omega⟩
  | 2, 5 => ⟨12, by omega⟩
  | 2, 6 => ⟨16, by omega⟩
  | 2, 7 => ⟨17, by omega⟩
  | 2, 8 => ⟨18, by omega⟩
  | 2, 9 => ⟨21, by omega⟩
  | 2, 10 => ⟨23, by omega⟩
  | 2, 11 => ⟨24, by omega⟩
  | 3, 0 => ⟨0, by omega⟩
  | 3, 1 => ⟨2, by omega⟩
  | 3, 2 => ⟨11, by omega⟩
  | 3, 3 => ⟨13, by omega⟩
  | 3, 4 => ⟨17, by omega⟩
  | 3, 5 => ⟨19, by omega⟩
  | 3, 6 => ⟨23, by omega⟩
  | 3, 7 => ⟨25, by omega⟩
  | 3, 8 => ⟨27, by omega⟩
  | 3, 9 => ⟨31, by omega⟩
  | 3, 10 => ⟨33, by omega⟩
  | 3, 11 => ⟨35, by omega⟩
  | 4, 0 => ⟨0, by omega⟩
  | 4, 1 => ⟨1, by omega⟩
  | 4, 2 => ⟨4, by omega⟩
  | 4, 3 => ⟨5, by omega⟩
  | 4, 4 => ⟨17, by omega⟩
  | 4, 5 => ⟨18, by omega⟩
  | 4, 6 => ⟨20, by omega⟩
  | 4, 7 => ⟨25, by omega⟩
  | 4, 8 => ⟨26, by omega⟩
  | 4, 9 => ⟨28, by omega⟩
  | 4, 10 => ⟨33, by omega⟩
  | 4, 11 => ⟨34, by omega⟩
  | 5, 0 => ⟨0, by omega⟩
  | 5, 1 => ⟨1, by omega⟩
  | 5, 2 => ⟨2, by omega⟩
  | 5, 3 => ⟨3, by omega⟩
  | 5, 4 => ⟨7, by omega⟩
  | 5, 5 => ⟨8, by omega⟩
  | 5, 6 => ⟨9, by omega⟩
  | 5, 7 => ⟨25, by omega⟩
  | 5, 8 => ⟨26, by omega⟩
  | 5, 9 => ⟨27, by omega⟩
  | 5, 10 => ⟨29, by omega⟩
  | 5, 11 => ⟨30, by omega⟩
  | 6, 0 => ⟨0, by omega⟩
  | 6, 1 => ⟨1, by omega⟩
  | 6, 2 => ⟨2, by omega⟩
  | 6, 3 => ⟨3, by omega⟩
  | 6, 4 => ⟨4, by omega⟩
  | 6, 5 => ⟨5, by omega⟩
  | 6, 6 => ⟨6, by omega⟩
  | 6, 7 => ⟨11, by omega⟩
  | 6, 8 => ⟨12, by omega⟩
  | 6, 9 => ⟨13, by omega⟩
  | 6, 10 => ⟨14, by omega⟩
  | 6, 11 => ⟨15, by omega⟩
  | 7, 0 => ⟨1, by omega⟩
  | 7, 1 => ⟨3, by omega⟩
  | 7, 2 => ⟨5, by omega⟩
  | 7, 3 => ⟨8, by omega⟩
  | 7, 4 => ⟨12, by omega⟩
  | 7, 5 => ⟨15, by omega⟩
  | 7, 6 => ⟨18, by omega⟩
  | 7, 7 => ⟨24, by omega⟩
  | 7, 8 => ⟨26, by omega⟩
  | 7, 9 => ⟨30, by omega⟩
  | 7, 10 => ⟨34, by omega⟩
  | 7, 11 => ⟨36, by omega⟩
  | 8, 0 => ⟨2, by omega⟩
  | 8, 1 => ⟨3, by omega⟩
  | 8, 2 => ⟨6, by omega⟩
  | 8, 3 => ⟨9, by omega⟩
  | 8, 4 => ⟨13, by omega⟩
  | 8, 5 => ⟨15, by omega⟩
  | 8, 6 => ⟨19, by omega⟩
  | 8, 7 => ⟨22, by omega⟩
  | 8, 8 => ⟨27, by omega⟩
  | 8, 9 => ⟨30, by omega⟩
  | 8, 10 => ⟨35, by omega⟩
  | 8, 11 => ⟨36, by omega⟩
  | 9, 0 => ⟨4, by omega⟩
  | 9, 1 => ⟨5, by omega⟩
  | 9, 2 => ⟨6, by omega⟩
  | 9, 3 => ⟨10, by omega⟩
  | 9, 4 => ⟨14, by omega⟩
  | 9, 5 => ⟨15, by omega⟩
  | 9, 6 => ⟨20, by omega⟩
  | 9, 7 => ⟨22, by omega⟩
  | 9, 8 => ⟨28, by omega⟩
  | 9, 9 => ⟨32, by omega⟩
  | 9, 10 => ⟨34, by omega⟩
  | 9, 11 => ⟨36, by omega⟩
  | 10, 0 => ⟨7, by omega⟩
  | 10, 1 => ⟨8, by omega⟩
  | 10, 2 => ⟨9, by omega⟩
  | 10, 3 => ⟨10, by omega⟩
  | 10, 4 => ⟨16, by omega⟩
  | 10, 5 => ⟨21, by omega⟩
  | 10, 6 => ⟨22, by omega⟩
  | 10, 7 => ⟨24, by omega⟩
  | 10, 8 => ⟨29, by omega⟩
  | 10, 9 => ⟨30, by omega⟩
  | 10, 10 => ⟨32, by omega⟩
  | 10, 11 => ⟨36, by omega⟩
  | 11, 0 => ⟨11, by omega⟩
  | 11, 1 => ⟨12, by omega⟩
  | 11, 2 => ⟨13, by omega⟩
  | 11, 3 => ⟨14, by omega⟩
  | 11, 4 => ⟨15, by omega⟩
  | 11, 5 => ⟨16, by omega⟩
  | 11, 6 => ⟨23, by omega⟩
  | 11, 7 => ⟨24, by omega⟩
  | 11, 8 => ⟨31, by omega⟩
  | 11, 9 => ⟨32, by omega⟩
  | 11, 10 => ⟨35, by omega⟩
  | 11, 11 => ⟨36, by omega⟩
  | 12, 0 => ⟨17, by omega⟩
  | 12, 1 => ⟨18, by omega⟩
  | 12, 2 => ⟨19, by omega⟩
  | 12, 3 => ⟨20, by omega⟩
  | 12, 4 => ⟨21, by omega⟩
  | 12, 5 => ⟨22, by omega⟩
  | 12, 6 => ⟨23, by omega⟩
  | 12, 7 => ⟨24, by omega⟩
  | 12, 8 => ⟨33, by omega⟩
  | 12, 9 => ⟨34, by omega⟩
  | 12, 10 => ⟨35, by omega⟩
  | 12, 11 => ⟨36, by omega⟩
  | 13, 0 => ⟨25, by omega⟩
  | 13, 1 => ⟨26, by omega⟩
  | 13, 2 => ⟨27, by omega⟩
  | 13, 3 => ⟨28, by omega⟩
  | 13, 4 => ⟨29, by omega⟩
  | 13, 5 => ⟨30, by omega⟩
  | 13, 6 => ⟨31, by omega⟩
  | 13, 7 => ⟨32, by omega⟩
  | 13, 8 => ⟨33, by omega⟩
  | 13, 9 => ⟨34, by omega⟩
  | 13, 10 => ⟨35, by omega⟩
  | 13, 11 => ⟨36, by omega⟩
  | _, _ => ⟨0, by omega⟩

def idx5Aux (p l : Fin 7) (a : Fin 5) : Fin 37 :=
  match p.val, l.val, a.val with
  | 0, 1, 0 => ⟨2, by omega⟩
  | 0, 1, 1 => ⟨6, by omega⟩
  | 0, 1, 2 => ⟨9, by omega⟩
  | 0, 1, 3 => ⟨19, by omega⟩
  | 0, 1, 4 => ⟨22, by omega⟩
  | 0, 2, 0 => ⟨4, by omega⟩
  | 0, 2, 1 => ⟨6, by omega⟩
  | 0, 2, 2 => ⟨10, by omega⟩
  | 0, 2, 3 => ⟨20, by omega⟩
  | 0, 2, 4 => ⟨22, by omega⟩
  | 0, 3, 0 => ⟨7, by omega⟩
  | 0, 3, 1 => ⟨9, by omega⟩
  | 0, 3, 2 => ⟨10, by omega⟩
  | 0, 3, 3 => ⟨21, by omega⟩
  | 0, 3, 4 => ⟨22, by omega⟩
  | 0, 5, 0 => ⟨17, by omega⟩
  | 0, 5, 1 => ⟨19, by omega⟩
  | 0, 5, 2 => ⟨20, by omega⟩
  | 0, 5, 3 => ⟨21, by omega⟩
  | 0, 5, 4 => ⟨22, by omega⟩
  | 1, 2, 0 => ⟨4, by omega⟩
  | 1, 2, 1 => ⟨10, by omega⟩
  | 1, 2, 2 => ⟨14, by omega⟩
  | 1, 2, 3 => ⟨28, by omega⟩
  | 1, 2, 4 => ⟨32, by omega⟩
  | 1, 3, 0 => ⟨7, by omega⟩
  | 1, 3, 1 => ⟨10, by omega⟩
  | 1, 3, 2 => ⟨16, by omega⟩
  | 1, 3, 3 => ⟨29, by omega⟩
  | 1, 3, 4 => ⟨32, by omega⟩
  | 1, 4, 0 => ⟨11, by omega⟩
  | 1, 4, 1 => ⟨14, by omega⟩
  | 1, 4, 2 => ⟨16, by omega⟩
  | 1, 4, 3 => ⟨31, by omega⟩
  | 1, 4, 4 => ⟨32, by omega⟩
  | 1, 6, 0 => ⟨25, by omega⟩
  | 1, 6, 1 => ⟨28, by omega⟩
  | 1, 6, 2 => ⟨29, by omega⟩
  | 1, 6, 3 => ⟨31, by omega⟩
  | 1, 6, 4 => ⟨32, by omega⟩
  | 2, 0, 0 => ⟨1, by omega⟩
  | 2, 0, 1 => ⟨8, by omega⟩
  | 2, 0, 2 => ⟨12, by omega⟩
  | 2, 0, 3 => ⟨18, by omega⟩
  | 2, 0, 4 => ⟨24, by omega⟩
  | 2, 3, 0 => ⟨7, by omega⟩
  | 2, 3, 1 => ⟨8, by omega⟩
  | 2, 3, 2 => ⟨16, by omega⟩
  | 2, 3, 3 => ⟨21, by omega⟩
  | 2, 3, 4 => ⟨24, by omega⟩
  | 2, 4, 0 => ⟨11, by omega⟩
  | 2, 4, 1 => ⟨12, by omega⟩
  | 2, 4, 2 => ⟨16, by omega⟩
  | 2, 4, 3 => ⟨23, by omega⟩
  | 2, 4, 4 => ⟨24, by omega⟩
  | 2, 5, 0 => ⟨17, by omega⟩
  | 2, 5, 1 => ⟨18, by omega⟩
  | 2, 5, 2 => ⟨21, by omega⟩
  | 2, 5, 3 => ⟨23, by omega⟩
  | 2, 5, 4 => ⟨24, by omega⟩
  | 3, 1, 0 => ⟨2, by omega⟩
  | 3, 1, 1 => ⟨13, by omega⟩
  | 3, 1, 2 => ⟨19, by omega⟩
  | 3, 1, 3 => ⟨27, by omega⟩
  | 3, 1, 4 => ⟨35, by omega⟩
  | 3, 4, 0 => ⟨11, by omega⟩
  | 3, 4, 1 => ⟨13, by omega⟩
  | 3, 4, 2 => ⟨23, by omega⟩
  | 3, 4, 3 => ⟨31, by omega⟩
  | 3, 4, 4 => ⟨35, by omega⟩
  | 3, 5, 0 => ⟨17, by omega⟩
  | 3, 5, 1 => ⟨19, by omega⟩
  | 3, 5, 2 => ⟨23, by omega⟩
  | 3, 5, 3 => ⟨33, by omega⟩
  | 3, 5, 4 => ⟨35, by omega⟩
  | 3, 6, 0 => ⟨25, by omega⟩
  | 3, 6, 1 => ⟨27, by omega⟩
  | 3, 6, 2 => ⟨31, by omega⟩
  | 3, 6, 3 => ⟨33, by omega⟩
  | 3, 6, 4 => ⟨35, by omega⟩
  | 4, 0, 0 => ⟨1, by omega⟩
  | 4, 0, 1 => ⟨5, by omega⟩
  | 4, 0, 2 => ⟨18, by omega⟩
  | 4, 0, 3 => ⟨26, by omega⟩
  | 4, 0, 4 => ⟨34, by omega⟩
  | 4, 2, 0 => ⟨4, by omega⟩
  | 4, 2, 1 => ⟨5, by omega⟩
  | 4, 2, 2 => ⟨20, by omega⟩
  | 4, 2, 3 => ⟨28, by omega⟩
  | 4, 2, 4 => ⟨34, by omega⟩
  | 4, 5, 0 => ⟨17, by omega⟩
  | 4, 5, 1 => ⟨18, by omega⟩
  | 4, 5, 2 => ⟨20, by omega⟩
  | 4, 5, 3 => ⟨33, by omega⟩
  | 4, 5, 4 => ⟨34, by omega⟩
  | 4, 6, 0 => ⟨25, by omega⟩
  | 4, 6, 1 => ⟨26, by omega⟩
  | 4, 6, 2 => ⟨28, by omega⟩
  | 4, 6, 3 => ⟨33, by omega⟩
  | 4, 6, 4 => ⟨34, by omega⟩
  | 5, 0, 0 => ⟨1, by omega⟩
  | 5, 0, 1 => ⟨3, by omega⟩
  | 5, 0, 2 => ⟨8, by omega⟩
  | 5, 0, 3 => ⟨26, by omega⟩
  | 5, 0, 4 => ⟨30, by omega⟩
  | 5, 1, 0 => ⟨2, by omega⟩
  | 5, 1, 1 => ⟨3, by omega⟩
  | 5, 1, 2 => ⟨9, by omega⟩
  | 5, 1, 3 => ⟨27, by omega⟩
  | 5, 1, 4 => ⟨30, by omega⟩
  | 5, 3, 0 => ⟨7, by omega⟩
  | 5, 3, 1 => ⟨8, by omega⟩
  | 5, 3, 2 => ⟨9, by omega⟩
  | 5, 3, 3 => ⟨29, by omega⟩
  | 5, 3, 4 => ⟨30, by omega⟩
  | 5, 6, 0 => ⟨25, by omega⟩
  | 5, 6, 1 => ⟨26, by omega⟩
  | 5, 6, 2 => ⟨27, by omega⟩
  | 5, 6, 3 => ⟨29, by omega⟩
  | 5, 6, 4 => ⟨30, by omega⟩
  | 6, 0, 0 => ⟨1, by omega⟩
  | 6, 0, 1 => ⟨3, by omega⟩
  | 6, 0, 2 => ⟨5, by omega⟩
  | 6, 0, 3 => ⟨12, by omega⟩
  | 6, 0, 4 => ⟨15, by omega⟩
  | 6, 1, 0 => ⟨2, by omega⟩
  | 6, 1, 1 => ⟨3, by omega⟩
  | 6, 1, 2 => ⟨6, by omega⟩
  | 6, 1, 3 => ⟨13, by omega⟩
  | 6, 1, 4 => ⟨15, by omega⟩
  | 6, 2, 0 => ⟨4, by omega⟩
  | 6, 2, 1 => ⟨5, by omega⟩
  | 6, 2, 2 => ⟨6, by omega⟩
  | 6, 2, 3 => ⟨14, by omega⟩
  | 6, 2, 4 => ⟨15, by omega⟩
  | 6, 4, 0 => ⟨11, by omega⟩
  | 6, 4, 1 => ⟨12, by omega⟩
  | 6, 4, 2 => ⟨13, by omega⟩
  | 6, 4, 3 => ⟨14, by omega⟩
  | 6, 4, 4 => ⟨15, by omega⟩
  | _, _, _ => ⟨0, by omega⟩

theorem mis37_indep_b : ∀ k : Fin 37, (mis37 k).all (fun x => (mis37 k).all (fun y => !adjB x y)) = true := by
  decide

theorem mis37_incomp_b : ∀ k₁ k₂ : Fin 37, k₁ ≠ k₂ →
    (mis37 k₁).any (fun x => (mis37 k₂).any (fun y => adjB x y)) = true := by
  decide

theorem idx12_mem : ∀ v : Fin 14, ∀ a : Fin 12, (mis37 (idx12 v a)).any (fun x => x == v) = true := by
  decide

theorem idx12_inj : ∀ v : Fin 14, ∀ a b : Fin 12, a ≠ b → idx12 v a ≠ idx12 v b := by
  decide

theorem idx5_mem : ∀ p l : Fin 7, adjB ⟨p.val, by omega⟩ ⟨l.val + 7, by omega⟩ = false →
    ∀ a : Fin 5, (mis37 (idx5Aux p l a)).any (fun x => x == ⟨p.val, by omega⟩) = true ∧
      (mis37 (idx5Aux p l a)).any (fun x => x == ⟨l.val + 7, by omega⟩) = true := by
  decide

theorem idx5_inj : ∀ p l : Fin 7, adjB ⟨p.val, by omega⟩ ⟨l.val + 7, by omega⟩ = false →
    ∀ a b : Fin 5, a ≠ b → idx5Aux p l a ≠ idx5Aux p l b := by
  decide

theorem mis37_indep (k : Fin 37) : Indep (mis37 k).toFinset := by
  intro x hx y hy hadj
  have h1 := List.all_eq_true.1 (mis37_indep_b k) x (List.mem_toFinset.1 hx)
  have h2 := List.all_eq_true.1 h1 y (List.mem_toFinset.1 hy)
  rw [Bool.not_eq_true'] at h2
  have h3 := (adjB_iff x y).2 hadj
  rw [h2] at h3
  exact Bool.noConfusion h3

theorem mis37_not_indep_union (k₁ k₂ : Fin 37) (hne : k₁ ≠ k₂) :
    ¬ Indep ((mis37 k₁).toFinset ∪ (mis37 k₂).toFinset) := by
  intro hind
  obtain ⟨x, hx, hy⟩ := List.any_eq_true.1 (mis37_incomp_b k₁ k₂ hne)
  obtain ⟨y, hy', hadj⟩ := List.any_eq_true.1 hy
  exact hind x (Finset.mem_union_left _ (List.mem_toFinset.2 hx))
    y (Finset.mem_union_right _ (List.mem_toFinset.2 hy')) ((adjB_iff x y).1 hadj)

theorem mis12 : Mis12 := by
  intro v
  refine ⟨fun a => (mis37 (idx12 v a)).toFinset, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨x, hx, hxv⟩ := List.any_eq_true.1 (idx12_mem v a)
    rw [beq_iff_eq] at hxv
    exact List.mem_toFinset.2 (hxv ▸ hx)
  · intro a
    exact mis37_indep (idx12 v a)
  · intro a b hab
    exact mis37_not_indep_union (idx12 v a) (idx12 v b) (idx12_inj v a b hab)

theorem mis9 : ∀ v : Fin 14, ∃ M : Fin 9 → Finset (Fin 14),
    (∀ a, v ∈ M a) ∧ (∀ a, Indep (M a)) ∧ ∀ a b, a ≠ b → ¬ Indep (M a ∪ M b) := by
  intro v
  obtain ⟨M, hm, hi, hn⟩ := mis12 v
  refine ⟨fun a => M (Fin.castLE (by omega) a), fun a => hm _, fun a => hi _, ?_⟩
  intro a b hab
  exact hn _ _ (fun h => hab (Fin.ext (by simpa using congrArg Fin.val h)))

theorem mis5_aux (p l : Fin 7) (h : ¬ IHAdj ⟨p.val, by omega⟩ ⟨l.val + 7, by omega⟩) :
    ∃ M : Fin 5 → Finset (Fin 14),
      (∀ a, ⟨p.val, by omega⟩ ∈ M a ∧ ⟨l.val + 7, by omega⟩ ∈ M a) ∧
      (∀ a, Indep (M a)) ∧ ∀ a b, a ≠ b → ¬ Indep (M a ∪ M b) := by
  have hb : adjB ⟨p.val, by omega⟩ ⟨l.val + 7, by omega⟩ = false := by
    cases hval : adjB ⟨p.val, by omega⟩ ⟨l.val + 7, by omega⟩ with
    | false => rfl
    | true => exact absurd ((adjB_iff _ _).1 hval) h
  refine ⟨fun a => (mis37 (idx5Aux p l a)).toFinset, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨h1, h2⟩ := idx5_mem p l hb a
    obtain ⟨x, hx, hxp⟩ := List.any_eq_true.1 h1
    obtain ⟨y, hy, hyl⟩ := List.any_eq_true.1 h2
    rw [beq_iff_eq] at hxp hyl
    exact ⟨List.mem_toFinset.2 (hxp ▸ hx), List.mem_toFinset.2 (hyl ▸ hy)⟩
  · intro a
    exact mis37_indep (idx5Aux p l a)
  · intro a b hab
    exact mis37_not_indep_union _ _ (idx5_inj p l hb a b hab)

theorem mis5 : Mis5 := by
  intro v u hopp hna
  rcases hopp with ⟨hv, hu⟩ | ⟨hu, hv⟩
  · have ev : (⟨v.val, by omega⟩ : Fin 14) = v := Fin.ext rfl
    have eu : (⟨(u.val - 7) + 7, by omega⟩ : Fin 14) = u := Fin.ext (by dsimp; omega)
    have hna' : ¬ IHAdj ⟨v.val, by omega⟩ ⟨(u.val - 7) + 7, by omega⟩ := by
      rw [ev, eu]
      exact hna
    obtain ⟨M, hm, hi, hn⟩ := mis5_aux ⟨v.val, hv⟩ ⟨u.val - 7, by omega⟩ hna'
    refine ⟨M, ?_, hi, hn⟩
    intro a
    obtain ⟨h1, h2⟩ := hm a
    rw [ev] at h1
    rw [eu] at h2
    exact ⟨h1, h2⟩
  · have eu : (⟨u.val, by omega⟩ : Fin 14) = u := Fin.ext rfl
    have ev : (⟨(v.val - 7) + 7, by omega⟩ : Fin 14) = v := Fin.ext (by dsimp; omega)
    have hna' : ¬ IHAdj ⟨u.val, by omega⟩ ⟨(v.val - 7) + 7, by omega⟩ := by
      rw [eu, ev]
      exact fun h => hna h.symm
    obtain ⟨M, hm, hi, hn⟩ := mis5_aux ⟨u.val, hu⟩ ⟨v.val - 7, by omega⟩ hna'
    refine ⟨M, ?_, hi, hn⟩
    intro a
    obtain ⟨h1, h2⟩ := hm a
    rw [eu] at h1
    rw [ev] at h2
    exact ⟨h2, h1⟩

def upNb : Fin 7 → Finset (Fin 14) :=
  ![{7, 11, 13}, {7, 8, 12}, {8, 9, 13}, {7, 9, 10}, {8, 10, 11}, {9, 11, 12}, {10, 12, 13}]

def upL (i : Fin 7) : Fin 14 := Fin.castLE (by omega) i

def upC : AndCountCircuit 14 where
  size := 7
  leftVars i := {upL i}
  leftGates _ := ∅
  rightVars i := upNb i
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
theorem up_adj_dec : ∀ a c : Fin 14,
    ((a = 0 ∧ c = 7 ∨ a = 7 ∧ c = 0) ∨ (a = 1 ∧ c = 7 ∨ a = 7 ∧ c = 1) ∨
      (a = 3 ∧ c = 7 ∨ a = 7 ∧ c = 3) ∨ (a = 1 ∧ c = 8 ∨ a = 8 ∧ c = 1) ∨
      (a = 2 ∧ c = 8 ∨ a = 8 ∧ c = 2) ∨ (a = 4 ∧ c = 8 ∨ a = 8 ∧ c = 4) ∨
      (a = 2 ∧ c = 9 ∨ a = 9 ∧ c = 2) ∨ (a = 3 ∧ c = 9 ∨ a = 9 ∧ c = 3) ∨
      (a = 5 ∧ c = 9 ∨ a = 9 ∧ c = 5) ∨ (a = 3 ∧ c = 10 ∨ a = 10 ∧ c = 3) ∨
      (a = 4 ∧ c = 10 ∨ a = 10 ∧ c = 4) ∨ (a = 6 ∧ c = 10 ∨ a = 10 ∧ c = 6) ∨
      (a = 4 ∧ c = 11 ∨ a = 11 ∧ c = 4) ∨ (a = 5 ∧ c = 11 ∨ a = 11 ∧ c = 5) ∨
      (a = 0 ∧ c = 11 ∨ a = 11 ∧ c = 0) ∨ (a = 5 ∧ c = 12 ∨ a = 12 ∧ c = 5) ∨
      (a = 6 ∧ c = 12 ∨ a = 12 ∧ c = 6) ∨ (a = 1 ∧ c = 12 ∨ a = 12 ∧ c = 1) ∨
      (a = 6 ∧ c = 13 ∨ a = 13 ∧ c = 6) ∨ (a = 0 ∧ c = 13 ∨ a = 13 ∧ c = 0) ∨
      (a = 2 ∧ c = 13 ∨ a = 13 ∧ c = 2)) ↔
    ∃ i : Fin 7, (a = upL i ∧ c ∈ upNb i) ∨ (c = upL i ∧ a ∈ upNb i) := by
  decide

theorem up_adj (G : SimpleGraph (Fin 14))
    (h : G.edgeSet = {s(0, 7), s(1, 7), s(3, 7), s(1, 8), s(2, 8), s(4, 8), s(2, 9), s(3, 9),
      s(5, 9), s(3, 10), s(4, 10), s(6, 10), s(4, 11), s(5, 11), s(0, 11), s(5, 12), s(6, 12),
      s(1, 12), s(6, 13), s(0, 13), s(2, 13)}) (a c : Fin 14) :
    G.Adj a c ↔ ∃ i : Fin 7, (a = upL i ∧ c ∈ upNb i) ∨ (c = upL i ∧ a ∈ upNb i) := by
  rw [← up_adj_dec a c, ← SimpleGraph.mem_edgeSet, h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]

theorem up_gate (U : Finset (Fin 14)) (i : Fin 7) :
    upC.gateVal U i = true ↔ upL i ∈ U ∧ ∃ v ∈ upNb i, v ∈ U := by
  have e : upC.gateVal U i =
      (sideTrue U {upL i} (∅ : Finset (Fin 7)) i (gateValFuel upC U 6) &&
        sideTrue U (upNb i) (∅ : Finset (Fin 7)) i (gateValFuel upC U 6)) := rfl
  rw [e, Bool.and_eq_true]
  unfold sideTrue
  simp

theorem upper (G : SimpleGraph (Fin 14))
    (h : G.edgeSet = {s(0, 7), s(1, 7), s(3, 7), s(1, 8), s(2, 8), s(4, 8), s(2, 9), s(3, 9),
      s(5, 9), s(3, 10), s(4, 10), s(6, 10), s(4, 11), s(5, 11), s(0, 11), s(5, 12), s(6, 12),
      s(1, 12), s(6, 13), s(0, 13), s(2, 13)}) :
    ∃ C : PEqualNP.AndCount.AndCountCircuit 14, C.WellFormed ∧ C.Computes G ∧ C.size = 7 := by
  refine ⟨upC, ?_, ?_, rfl⟩
  · intro i
    exact ⟨fun j hj => absurd hj (Finset.notMem_empty j),
      fun j hj => absurd hj (Finset.notMem_empty j)⟩
  · intro U
    have e : upC.eval U = true ↔ ∃ j : Fin 7, upC.gateVal U j = true := by
      unfold AndCountCircuit.eval
      rw [decide_eq_true_iff]
      constructor
      · rintro (⟨v, hv, _⟩ | ⟨j, _, hj⟩)
        · exact absurd hv (Finset.notMem_empty v)
        · exact ⟨j, hj⟩
      · rintro ⟨j, hj⟩
        exact Or.inr ⟨j, Finset.mem_univ j, hj⟩
    rw [e]
    constructor
    · rintro ⟨j, hj⟩
      rw [up_gate] at hj
      obtain ⟨h1, v, hv, hvU⟩ := hj
      exact ⟨upL j, h1, v, hvU, (up_adj G h _ _).2 ⟨j, Or.inl ⟨rfl, hv⟩⟩⟩
    · rintro ⟨a, ha, c, hc, hadj⟩
      obtain ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := (up_adj G h a c).1 hadj
      · exact ⟨i, (up_gate U i).2 ⟨h1 ▸ ha, c, h2, hc⟩⟩
      · exact ⟨i, (up_gate U i).2 ⟨h1 ▸ hc, a, h2, ha⟩⟩

theorem lower_of_no_model (nm : ∀ W, ¬ Model634 W) (G : SimpleGraph (Fin 14))
    (h : G.edgeSet = {s(0, 7), s(1, 7), s(3, 7), s(1, 8), s(2, 8), s(4, 8), s(2, 9), s(3, 9),
      s(5, 9), s(3, 10), s(4, 10), s(6, 10), s(4, 11), s(5, 11), s(0, 11), s(5, 12), s(6, 12),
      s(1, 12), s(6, 13), s(0, 13), s(2, 13)}) :
    ∀ C : PEqualNP.AndCount.AndCountCircuit 14, C.WellFormed → C.Computes G → ¬ C.size ≤ 6 := by
  intro C hw hc hs
  obtain ⟨W, hW⟩ := exists_model G h C hw hc hs mis12 mis5
  exact nm W hW

def sRename (π : Equiv.Perm (Fin 6)) (flip : Fin 6 → Bool)
    (w : Finset (Fin 6 × Bool)) : Finset (Fin 6 × Bool) :=
  w.image (fun x => (π x.1, Bool.xor x.2 (flip x.1)))

def Canon634 (ord : Fin 14 → Fin 14) (W : Fin 14 → Finset (Fin 6 × Bool)) : Prop :=
  ∃ h : ℕ → ℕ, h 0 = 0 ∧ ∀ i : Fin 14,
    h i.val ≤ h (i.val+1) ∧ h (i.val+1) ≤ 6 ∧
    (∀ g b, (g,b) ∈ W (ord i) → g.val < h (i.val+1)) ∧
    (∀ g : Fin 6, h i.val ≤ g.val → g.val < h (i.val+1) → (g,false) ∈ W (ord i)) ∧
    (∀ g : Fin 6, (g,true) ∈ W (ord i) → g.val < h i.val)
def mid (w : Nat) : Nat := (w ||| (w >>> 6)) &&& 63

def msub (a b : Nat) : Bool := (a &&& b) == a

def mcross (a b : Nat) : Bool := (((a >>> 6) &&& b) ||| ((b >>> 6) &&& a)) != 0

def msmall (x : Nat) : Bool := ((x &&& (x-1)) &&& ((x &&& (x-1))-1)) &&& ((((x &&& (x-1)) &&& ((x &&& (x-1))-1)))-1) == 0

def morder : Fin 14 → Fin 14 := ![0, 7, 1, 3, 11, 13, 8, 2, 4, 9, 5, 10, 6, 12]

def mwords : List Nat := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 64, 66, 68, 72, 80, 96, 128, 129, 132, 136, 144, 160, 192, 256, 257, 258, 264, 272, 288, 320, 384, 512, 513, 514, 516, 528, 544, 576, 640, 768, 1024, 1025, 1026, 1028, 1032, 1056, 1088, 1152, 1280, 1536, 2048, 2049, 2050, 2052, 2056, 2064, 2112, 2176, 2304, 2560, 3072]

def mopts (x : Nat) : List Nat :=
  if x = 0 then [1, 3] else
  if x = 1 then [1, 2, 3, 6, 64, 66] else
  if x = 3 then [1, 2, 3, 4, 5, 6, 12, 64, 66, 68, 128, 129, 132, 192] else
  if x = 7 then [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 24, 64, 66, 68, 72, 128, 129, 132, 136, 192, 256, 257, 258, 264, 320, 384] else
  if x = 15 then [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 48, 64, 66, 68, 72, 80, 128, 129, 132, 136, 144, 192, 256, 257, 258, 264, 272, 320, 384, 512, 513, 514, 516, 528, 576, 640, 768] else
  if x = 31 then [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 64, 66, 68, 72, 80, 96, 128, 129, 132, 136, 144, 160, 192, 256, 257, 258, 264, 272, 288, 320, 384, 512, 513, 514, 516, 528, 544, 576, 640, 768, 1024, 1025, 1026, 1028, 1032, 1056, 1088, 1152, 1280, 1536] else
  mwords

def mseen (w : Fin 14 → Nat) : Nat → Nat
  | 0 => 0
  | d+1 => mseen w d ||| mid (w (Fin.ofNat 14 d))

def MModel (w : Fin 14 → Nat) : Prop :=
  (∀ d, w d ∈ mopts (mseen w d.val)) ∧
  (∀ d i, IHAdj (morder d) (morder i) → mcross (w d) (w i) = true) ∧
  (∀ d i, IHOpp (morder d) (morder i) → ¬IHAdj (morder d) (morder i) →
    msmall (mid (w d) ||| mid (w i)) = true) ∧
  (∀ d i j, d ≠ i → d ≠ j → ¬IHAdj (morder i) (morder j) →
    msub (w d) (w i ||| w j) = false)
theorem sRenP_injective (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool) :
    Function.Injective (fun x : Fin 6 × Bool => (π x.1, Bool.xor x.2 (s x.1))) := by
  rintro ⟨g, b⟩ ⟨g', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hg : g = g' := π.injective h1
  subst hg
  have hb : b = b' := by
    revert h2
    cases b <;> cases b' <;> cases s g <;> simp
  rw [hb]

theorem mem_sRename (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) (g : Fin 6) (b : Bool) :
    (π g, b) ∈ sRename π s c ↔ (g, Bool.xor b (s g)) ∈ c := by
  unfold sRename
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨g', b'⟩, hm, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hg : g' = g := π.injective h1
    subst hg
    have hb : Bool.xor b (s g') = b' := by
      rw [← h2]
      cases b' <;> cases s g' <;> rfl
    rw [hb]
    exact hm
  · intro hm
    refine ⟨(g, Bool.xor b (s g)), hm, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    cases b <;> cases s g <;> rfl

theorem mem_sRename' (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) (g : Fin 6) (b : Bool) :
    (g, b) ∈ sRename π s c ↔ (π.symm g, Bool.xor b (s (π.symm g))) ∈ c := by
  rw [← mem_sRename π s c (π.symm g) b, Equiv.apply_symm_apply]

theorem mem_sRename_of_mem (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) (g : Fin 6) (b : Bool) (h : (g, b) ∈ c) :
    (π g, Bool.xor b (s g)) ∈ sRename π s c := by
  rw [mem_sRename]
  have hb : Bool.xor (Bool.xor b (s g)) (s g) = b := by
    cases b <;> cases s g <;> rfl
  rw [hb]
  exact h

theorem sRename_union (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c c' : Finset (Fin 6 × Bool)) : sRename π s (c ∪ c') = sRename π s c ∪ sRename π s c' :=
  Finset.image_union c c'

theorem sRename_subset_iff (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c c' : Finset (Fin 6 × Bool)) : sRename π s c ⊆ sRename π s c' ↔ c ⊆ c' :=
  Finset.image_subset_image_iff (sRenP_injective π s)

theorem sRename_subset_union_iff (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c a b : Finset (Fin 6 × Bool)) :
    sRename π s c ⊆ sRename π s a ∪ sRename π s b ↔ c ⊆ a ∪ b := by
  rw [← sRename_union, sRename_subset_iff]

theorem sRename_card (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) : (sRename π s c).card = c.card :=
  Finset.card_image_of_injective c (sRenP_injective π s)

theorem sRename_nonempty (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) : (sRename π s c).Nonempty ↔ c.Nonempty :=
  Finset.image_nonempty

theorem sRename_eq_iff (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c c' : Finset (Fin 6 × Bool)) : sRename π s c = sRename π s c' ↔ c = c' :=
  (Finset.image_injective (sRenP_injective π s)).eq_iff

theorem sRename_ids (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) :
    (sRename π s c).image Prod.fst = (c.image Prod.fst).image π := by
  unfold sRename
  rw [Finset.image_image, Finset.image_image]
  rfl

theorem sRename_ids_card (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) :
    ((sRename π s c).image Prod.fst).card = (c.image Prod.fst).card := by
  rw [sRename_ids, Finset.card_image_of_injective _ π.injective]

theorem sRename_union_ids_card (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c c' : Finset (Fin 6 × Bool)) :
    ((sRename π s c ∪ sRename π s c').image Prod.fst).card = ((c ∪ c').image Prod.fst).card := by
  rw [← sRename_union, sRename_ids_card]

theorem sRename_valid (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c : Finset (Fin 6 × Bool)) :
    (∀ g, ¬ ((g, false) ∈ sRename π s c ∧ (g, true) ∈ sRename π s c)) ↔
      ∀ g, ¬ ((g, false) ∈ c ∧ (g, true) ∈ c) := by
  constructor
  · intro h g hg
    apply h (π g)
    rw [mem_sRename, mem_sRename]
    cases s g
    · exact hg
    · exact ⟨hg.2, hg.1⟩
  · intro h g hg
    rw [mem_sRename', mem_sRename'] at hg
    apply h (π.symm g)
    generalize s (π.symm g) = t at hg
    cases t
    · exact hg
    · exact ⟨hg.2, hg.1⟩

theorem sRename_opp (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (c c' : Finset (Fin 6 × Bool)) :
    (∃ g b, (g, b) ∈ sRename π s c ∧ (g, !b) ∈ sRename π s c') ↔
      ∃ g b, (g, b) ∈ c ∧ (g, !b) ∈ c' := by
  constructor
  · rintro ⟨g, b, h1, h2⟩
    rw [mem_sRename'] at h1 h2
    refine ⟨π.symm g, Bool.xor b (s (π.symm g)), h1, ?_⟩
    have hb : (!(Bool.xor b (s (π.symm g)))) = Bool.xor (!b) (s (π.symm g)) := by
      cases b <;> cases s (π.symm g) <;> rfl
    rw [hb]
    exact h2
  · rintro ⟨g, b, h1, h2⟩
    refine ⟨π g, Bool.xor b (s g), mem_sRename_of_mem π s c g b h1, ?_⟩
    have hb : (!(Bool.xor b (s g))) = Bool.xor (!b) (s g) := by
      cases b <;> cases s g <;> rfl
    rw [hb]
    exact mem_sRename_of_mem π s c' g (!b) h2

theorem model_inv (π : Equiv.Perm (Fin 6)) (s : Fin 6 → Bool)
    (W : Fin 14 → Finset (Fin 6 × Bool)) (h : Model634 W) :
    Model634 (fun v => sRename π s (W v)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun v => ⟨(sRename_nonempty π s (W v)).2 (h1 v).1,
      le_of_eq_of_le (sRename_card π s (W v)) (h1 v).2.1,
      (sRename_valid π s (W v)).2 (h1 v).2.2⟩,
    fun v u hvu => (sRename_opp π s (W v) (W u)).2 (h2 v u hvu),
    fun v u ho ha => le_of_eq_of_le (sRename_union_ids_card π s (W v) (W u)) (h3 v u ho ha),
    fun v a b hva hvb hab hsub =>
      h4 v a b hva hvb hab ((sRename_subset_union_iff π s (W v) (W a) (W b)).1 hsub)⟩

theorem exists_perm_mono {k : ℕ} (f : Fin k → ℕ) :
    ∃ π : Equiv.Perm (Fin k), ∀ a b, f a < f b → π a < π b := by
  refine ⟨(Tuple.sort f)⁻¹, ?_⟩
  intro a b hab
  by_contra hcon
  have hle : (Tuple.sort f)⁻¹ b ≤ (Tuple.sort f)⁻¹ a := not_lt.mp hcon
  have hm := Tuple.monotone_sort f hle
  have e1 : (Tuple.sort f) ((Tuple.sort f)⁻¹ a) = a := Equiv.apply_symm_apply _ a
  have e2 : (Tuple.sort f) ((Tuple.sort f)⁻¹ b) = b := Equiv.apply_symm_apply _ b
  simp only [Function.comp_apply, e1, e2] at hm
  omega

theorem down_closed {k : ℕ} (T : Finset (Fin k)) (hT : ∀ x ∈ T, ∀ y, y < x → y ∈ T)
    (x : Fin k) : x ∈ T ↔ x.val < T.card := by
  constructor
  · intro hx
    have hsub : Finset.Iic x ⊆ T := by
      intro y hy
      rw [Finset.mem_Iic] at hy
      rcases lt_or_eq_of_le hy with h | h
      · exact hT x hx y h
      · rw [h]
        exact hx
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hx
    by_contra hcon
    have hsub : T ⊆ Finset.Iio x := by
      intro y hy
      rw [Finset.mem_Iio]
      by_contra hyx
      rcases lt_or_eq_of_le (not_lt.mp hyx) with h | h
      · exact hcon (hT y hy x h)
      · rw [h] at hcon
        exact hcon hy
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem exists_canon (ord : Fin 14 → Fin 14) (W : Fin 14 → Finset (Fin 6 × Bool))
    (clean : ∀ v g, ¬ ((g, false) ∈ W v ∧ (g, true) ∈ W v)) :
    ∃ (π : Equiv.Perm (Fin 6)) (flip : Fin 6 → Bool),
      Canon634 ord (fun v => sRename π flip (W v)) := by
  classical
  have hf : ∃ f : Fin 6 → ℕ, (∀ g d b, (g, b) ∈ W (ord d) → f g ≤ d.val) ∧
      (∀ g (d : Fin 14), (∀ j, j ≤ d → ∀ b, (g, b) ∉ W (ord j)) → d.val < f g) := by
    refine ⟨fun g => if h : ∃ m : ℕ, ∃ hm : m < 14, ∃ b, (g, b) ∈ W (ord ⟨m, hm⟩)
      then Nat.find h else 14, ?_, ?_⟩
    · intro g d b hgb
      have h : ∃ m : ℕ, ∃ hm : m < 14, ∃ b, (g, b) ∈ W (ord ⟨m, hm⟩) :=
        ⟨d.val, d.isLt, b, hgb⟩
      simp only [h, ↓reduceDIte]
      exact Nat.find_min' h ⟨d.isLt, b, hgb⟩
    · intro g d hd
      by_cases h : ∃ m : ℕ, ∃ hm : m < 14, ∃ b, (g, b) ∈ W (ord ⟨m, hm⟩)
      · simp only [h, ↓reduceDIte]
        obtain ⟨hm, b, hb⟩ := Nat.find_spec h
        by_contra hcon
        exact hd ⟨Nat.find h, hm⟩ (Fin.mk_le_of_le_val (not_lt.mp hcon)) b hb
      · simp only [h, ↓reduceDIte]
        exact d.isLt
  obtain ⟨f, hf1, hf2⟩ := hf
  obtain ⟨π, hπ⟩ := exists_perm_mono f
  have hs : ∃ s : Fin 6 → Bool, ∀ g (d : Fin 14) b, (g, b) ∈ W (ord d) → f g = d.val →
      s g = b := by
    refine ⟨fun g => decide (∃ d : Fin 14, (g, true) ∈ W (ord d) ∧ f g = d.val), ?_⟩
    intro g d b hgb hfd
    cases b
    · apply decide_eq_false
      rintro ⟨d', hd', hfd'⟩
      have hdd : d' = d := Fin.ext (by omega)
      rw [hdd] at hd'
      exact clean (ord d) g ⟨hgb, hd'⟩
    · exact decide_eq_true ⟨d, hgb, hfd⟩
  obtain ⟨s, hs⟩ := hs
  have hfirst : ∀ g (d : Fin 14), f g = d.val → ∃ b, (g, b) ∈ W (ord d) := by
    intro g d hfd
    by_contra hcon
    have := hf2 g d (by
      intro j hj b hb
      have h1 := hf1 g j b hb
      have h2 : j.val ≤ d.val := hj
      have hjd : j = d := Fin.ext (by omega)
      rw [hjd] at hb
      exact hcon ⟨b, hb⟩)
    omega
  have hK : ∀ (g : Fin 6) (i : ℕ),
      (π g).val < (Finset.univ.filter (fun g' : Fin 6 => f g' < i)).card ↔ f g < i := by
    intro g i
    have hdc := down_closed ((Finset.univ.filter (fun g' : Fin 6 => f g' < i)).image π) (by
      intro x hx y hyx
      rw [Finset.mem_image] at hx ⊢
      obtain ⟨a, ha, rfl⟩ := hx
      rw [Finset.mem_filter] at ha
      refine ⟨π.symm y, ?_, Equiv.apply_symm_apply π y⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hcon
      have := hπ a (π.symm y) (by omega)
      rw [Equiv.apply_symm_apply] at this
      exact absurd hyx (not_lt.mpr this.le)) (π g)
    rw [Finset.card_image_of_injective _ π.injective] at hdc
    rw [← hdc, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hag⟩
      rw [Finset.mem_filter] at ha
      rw [← π.injective hag]
      exact ha.2
    · intro hg
      exact ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩, rfl⟩
  refine ⟨π, s, fun i => (Finset.univ.filter (fun g' : Fin 6 => f g' < i)).card, ?_, ?_⟩
  · simp
  · intro i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · have := Finset.card_le_univ (Finset.univ.filter (fun g' : Fin 6 => f g' < i.val + 1))
      rw [Fintype.card_fin] at this
      exact this
    · intro g b hgb
      rw [mem_sRename'] at hgb
      have h1 := hf1 _ _ _ hgb
      have h2 := (hK (π.symm g) (i.val + 1)).2 (by omega)
      rw [Equiv.apply_symm_apply] at h2
      exact h2
    · intro g hlo hhi
      beta_reduce at hlo hhi
      have h1 := hK (π.symm g) i.val
      have h2 := hK (π.symm g) (i.val + 1)
      rw [Equiv.apply_symm_apply] at h1 h2
      have hfi : f (π.symm g) = i.val := by
        have a1 := h2.1 hhi
        have a2 : ¬ f (π.symm g) < i.val := fun hh => absurd (h1.2 hh) (by omega)
        omega
      obtain ⟨b, hb⟩ := hfirst _ i hfi
      have hsb := hs _ i b hb hfi
      have := mem_sRename_of_mem π s _ _ b hb
      rw [Equiv.apply_symm_apply, hsb] at this
      have hbb : Bool.xor b b = false := by cases b <;> rfl
      rw [hbb] at this
      exact this
    · intro g hgt
      have h1 := hK (π.symm g) i.val
      rw [Equiv.apply_symm_apply] at h1
      rw [h1]
      rw [mem_sRename'] at hgt
      have hle := hf1 _ _ _ hgt
      by_contra hcon
      have hfi : f (π.symm g) = i.val := by omega
      have hsb := hs _ i _ hgt hfi
      revert hsb
      cases s (π.symm g) <;> simp

def mbit (i : Fin 12) : Fin 6 × Bool :=
  (⟨i.val % 6, Nat.mod_lt _ (by decide)⟩, decide (6 ≤ i.val))

def mask (c : Finset (Fin 6 × Bool)) : Nat :=
  Nat.ofBits (fun i : Fin 12 => decide (mbit i ∈ c))

theorem mask_lo (c : Finset (Fin 6 × Bool)) (g : Fin 6) :
    (mask c).testBit g.val = decide ((g, false) ∈ c) := by
  have hg := g.isLt
  unfold mask
  rw [Nat.testBit_ofBits_lt _ _ (by omega)]
  have e : mbit ⟨g.val, by omega⟩ = (g, false) := by
    apply Prod.ext
    · exact Fin.ext (Nat.mod_eq_of_lt g.isLt)
    · exact decide_eq_false (by show ¬ 6 ≤ g.val; omega)
  rw [e]

theorem mask_hi (c : Finset (Fin 6 × Bool)) (g : Fin 6) :
    (mask c).testBit (6 + g.val) = decide ((g, true) ∈ c) := by
  have hg := g.isLt
  unfold mask
  rw [Nat.testBit_ofBits_lt _ _ (by omega)]
  have e : mbit ⟨6 + g.val, by omega⟩ = (g, true) := by
    apply Prod.ext
    · exact Fin.ext (by show (6 + g.val) % 6 = g.val; omega)
    · exact decide_eq_true (by show 6 ≤ 6 + g.val; omega)
  rw [e]

theorem mask_ge (c : Finset (Fin 6 × Bool)) (i : ℕ) (h : 12 ≤ i) :
    (mask c).testBit i = false :=
  Nat.testBit_ofBits_ge _ _ h

theorem forall_bits (P : ℕ → Prop) (h1 : ∀ g : Fin 6, P g.val) (h2 : ∀ g : Fin 6, P (6 + g.val))
    (h3 : ∀ i, 12 ≤ i → P i) : ∀ i, P i := by
  intro i
  by_cases a : i < 6
  · exact h1 ⟨i, a⟩
  · by_cases b : i < 12
    · have := h2 ⟨i - 6, by omega⟩
      have e : 6 + (i - 6) = i := by omega
      simp only [e] at this
      exact this
    · exact h3 i (by omega)

theorem mask_union (a b : Finset (Fin 6 × Bool)) : mask (a ∪ b) = mask a ||| mask b := by
  apply Nat.eq_of_testBit_eq
  refine forall_bits _ ?_ ?_ ?_
  · intro g
    rw [Nat.testBit_or, mask_lo, mask_lo, mask_lo]
    simp [Finset.mem_union]
  · intro g
    rw [Nat.testBit_or, mask_hi, mask_hi, mask_hi]
    simp [Finset.mem_union]
  · intro i hi
    rw [Nat.testBit_or, mask_ge _ i hi, mask_ge _ i hi, mask_ge _ i hi]
    rfl

theorem msub_tb (x y : Nat) :
    msub x y = true ↔ ∀ i, x.testBit i = true → y.testBit i = true := by
  unfold msub
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    rw [← h, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i
    · rfl
    · rw [h i hx]
      rfl

theorem msub_iff (a b : Finset (Fin 6 × Bool)) : msub (mask a) (mask b) = true ↔ a ⊆ b := by
  rw [msub_tb]
  constructor
  · rintro h ⟨g, t⟩ hp
    cases t
    · have := h g.val (by rw [mask_lo]; exact decide_eq_true hp)
      rw [mask_lo] at this
      exact of_decide_eq_true this
    · have := h (6 + g.val) (by rw [mask_hi]; exact decide_eq_true hp)
      rw [mask_hi] at this
      exact of_decide_eq_true this
  · intro h
    refine forall_bits _ ?_ ?_ ?_
    · intro g hg
      rw [mask_lo] at hg ⊢
      exact decide_eq_true (h (of_decide_eq_true hg))
    · intro g hg
      rw [mask_hi] at hg ⊢
      exact decide_eq_true (h (of_decide_eq_true hg))
    · intro i hi hx
      rw [mask_ge _ i hi] at hx
      exact Bool.noConfusion hx

theorem mcross_tb (x y : Nat) :
    mcross x y = true ↔ ∃ i, (x.testBit (6 + i) = true ∧ y.testBit i = true) ∨
      (y.testBit (6 + i) = true ∧ x.testBit i = true) := by
  unfold mcross
  rw [bne_iff_ne]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    refine ⟨i, ?_⟩
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hi
    exact hi
  · rintro ⟨i, hi⟩ h0
    have ht : ((x >>> 6 &&& y) ||| (y >>> 6 &&& x)).testBit i = true := by
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
        Nat.testBit_shiftRight, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      exact hi
    rw [h0, Nat.zero_testBit] at ht
    exact Bool.noConfusion ht

theorem mcross_iff (a b : Finset (Fin 6 × Bool)) :
    mcross (mask a) (mask b) = true ↔ ∃ g t, (g, t) ∈ a ∧ (g, !t) ∈ b := by
  rw [mcross_tb]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h6 : i < 6
    · have e1 := mask_lo a ⟨i, h6⟩
      have e2 := mask_lo b ⟨i, h6⟩
      have e3 := mask_hi a ⟨i, h6⟩
      have e4 := mask_hi b ⟨i, h6⟩
      simp only at e1 e2 e3 e4
      rw [e1, e2, e3, e4] at hi
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨i, h6⟩, true, of_decide_eq_true h1, of_decide_eq_true h2⟩
      · exact ⟨⟨i, h6⟩, false, of_decide_eq_true h2, of_decide_eq_true h1⟩
    · rw [mask_ge a (6 + i) (by omega), mask_ge b (6 + i) (by omega)] at hi
      rcases hi with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Bool.noConfusion h1
      · exact Bool.noConfusion h1
  · rintro ⟨g, t, h1, h2⟩
    refine ⟨g.val, ?_⟩
    rw [mask_lo, mask_lo, mask_hi, mask_hi]
    cases t
    · exact Or.inr ⟨decide_eq_true h2, decide_eq_true h1⟩
    · exact Or.inl ⟨decide_eq_true h1, decide_eq_true h2⟩

theorem tb63 : ∀ g : Fin 6, Nat.testBit 63 g.val = true := by decide

theorem mid_lo (x : Nat) (g : Fin 6) :
    (mid x).testBit g.val = (x.testBit g.val || x.testBit (6 + g.val)) := by
  unfold mid
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, tb63 g, Bool.and_true]

theorem mid_ge (x : Nat) (i : ℕ) (h : 6 ≤ i) : (mid x).testBit i = false := by
  unfold mid
  have h63 : Nat.testBit 63 i = false := by
    apply Nat.testBit_lt_two_pow
    have : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
    omega
  rw [Nat.testBit_and, h63, Bool.and_false]

theorem mid_lt (x : Nat) : mid x < 64 := by
  unfold mid
  have : (x ||| x >>> 6) &&& 63 ≤ 63 := Nat.and_le_right
  omega

theorem mid_or (x y : Nat) : mid (x ||| y) = mid x ||| mid y := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold mid
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight]
  cases x.testBit i <;> cases y.testBit i <;> cases x.testBit (6 + i) <;>
    cases y.testBit (6 + i) <;> cases Nat.testBit 63 i <;> rfl

theorem mid_mask_ids (c : Finset (Fin 6 × Bool)) :
    c.image Prod.fst = Finset.univ.filter (fun g : Fin 6 => (mid (mask c)).testBit g.val = true) := by
  ext g
  rw [Finset.mem_image, Finset.mem_filter, mid_lo, mask_lo, mask_hi, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨g', t⟩, hm, rfl⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    cases t
    · exact Or.inl (decide_eq_true hm)
    · exact Or.inr (decide_eq_true hm)
  · rintro ⟨_, h | h⟩
    · exact ⟨(g, false), of_decide_eq_true h, rfl⟩
    · exact ⟨(g, true), of_decide_eq_true h, rfl⟩

theorem msmall_dec : ∀ x : Fin 64,
    (Finset.univ.filter (fun g : Fin 6 => x.val.testBit g.val = true)).card ≤ 3 →
      msmall x.val = true := by decide

theorem msmall_ids (c : Finset (Fin 6 × Bool)) (h : (c.image Prod.fst).card ≤ 3) :
    msmall (mid (mask c)) = true := by
  rw [mid_mask_ids] at h
  exact msmall_dec ⟨mid (mask c), mid_lt _⟩ h

theorem mask_one : ∀ p : Fin 6 × Bool, mask {p} ∈ mwords := by decide

theorem mask_two : ∀ p q : Fin 6 × Bool, p.1 ≠ q.1 → mask {p, q} ∈ mwords := by decide

theorem mask_words (c : Finset (Fin 6 × Bool)) (hn : c.Nonempty) (hc : c.card ≤ 2)
    (hv : ∀ g, ¬ ((g, false) ∈ c ∧ (g, true) ∈ c)) : mask c ∈ mwords := by
  have hpos := Finset.card_pos.2 hn
  have h12 : c.card = 1 ∨ c.card = 2 := by omega
  rcases h12 with h | h
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 h
    exact mask_one p
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 h
    apply mask_two
    intro h1
    obtain ⟨g, t⟩ := p
    obtain ⟨g', t'⟩ := q
    simp only at h1
    subst h1
    apply hv g
    cases t <;> cases t'
    · exact absurd rfl hpq
    · simp
    · simp
    · exact absurd rfl hpq

set_option maxRecDepth 100000 in
theorem mopts_dec : ∀ h h' : Fin 7, ∀ x ∈ mwords,
    (2 ^ h.val - 1) ||| mid x = 2 ^ h'.val - 1 → msub (x >>> 6) (2 ^ h.val - 1) = true →
      x ∈ mopts (2 ^ h.val - 1) := by decide

theorem canon_step (c : Finset (Fin 6 × Bool)) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 6)
    (c1 : ∀ g t, (g, t) ∈ c → g.val < b)
    (c2 : ∀ g : Fin 6, a ≤ g.val → g.val < b → (g, false) ∈ c) :
    (2 ^ a - 1) ||| mid (mask c) = 2 ^ b - 1 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 6
  · have e := mid_lo (mask c) ⟨j, hj⟩
    have e1 := mask_lo c ⟨j, hj⟩
    have e2 := mask_hi c ⟨j, hj⟩
    simp only at e e1 e2
    rw [e, e1, e2]
    by_cases h1 : j < b
    · by_cases h2 : j < a
      · simp [h1, h2]
      · have := c2 ⟨j, hj⟩ (by simp only; omega) h1
        simp [h1, this]
    · have n1 : (⟨j, hj⟩, false) ∉ c := fun hh => h1 (c1 _ _ hh)
      have n2 : (⟨j, hj⟩, true) ∉ c := fun hh => h1 (c1 _ _ hh)
      have n3 : ¬ j < a := by omega
      simp [h1, n1, n2, n3]
  · rw [mid_ge _ j (by omega), decide_eq_false (by omega), decide_eq_false (by omega)]
    rfl

theorem canon_hi (c : Finset (Fin 6 × Bool)) (a : ℕ)
    (c3 : ∀ g : Fin 6, (g, true) ∈ c → g.val < a) :
    msub (mask c >>> 6) (2 ^ a - 1) = true := by
  rw [msub_tb]
  intro j hj
  rw [Nat.testBit_shiftRight] at hj
  rw [Nat.testBit_two_pow_sub_one]
  by_cases h6 : j < 6
  · have e := mask_hi c ⟨j, h6⟩
    simp only at e
    rw [e] at hj
    exact decide_eq_true (c3 _ (of_decide_eq_true hj))
  · rw [mask_ge c (6 + j) (by omega)] at hj
    exact Bool.noConfusion hj

theorem morder_inj : ∀ a b : Fin 14, morder a = morder b → a = b := by decide

theorem mask_model (V : Fin 14 → Finset (Fin 6 × Bool)) (hV : Model634 V)
    (hC : Canon634 morder V) : MModel (fun d => mask (V (morder d))) := by
  obtain ⟨h1, h2, h3, h4⟩ := hV
  obtain ⟨h, h0, hh⟩ := hC
  have hseen : ∀ d : ℕ, d ≤ 14 →
      mseen (fun d => mask (V (morder d))) d = 2 ^ h d - 1 := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [h0]
      rfl
    | succ d ih =>
      intro hd
      have e : Fin.ofNat 14 d = (⟨d, by omega⟩ : Fin 14) :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      show mseen (fun d => mask (V (morder d))) d |||
        mid (mask (V (morder (Fin.ofNat 14 d)))) = _
      rw [e, ih (by omega)]
      obtain ⟨a1, a2, a3, a4, _⟩ := hh ⟨d, by omega⟩
      exact canon_step _ _ _ a1 a2 a3 a4
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    show mask (V (morder d)) ∈ mopts (mseen (fun d => mask (V (morder d))) d.val)
    rw [hseen d.val (by omega)]
    obtain ⟨a1, a2, a3, a4, a5⟩ := hh d
    exact mopts_dec ⟨h d.val, by omega⟩ ⟨h (d.val + 1), by omega⟩ _
      (mask_words _ (h1 _).1 (h1 _).2.1 (h1 _).2.2)
      (canon_step _ _ _ a1 a2 a3 a4) (canon_hi _ _ a5)
  · intro d i hadj
    exact (mcross_iff _ _).2 (h2 _ _ hadj)
  · intro d i ho ha
    show msmall (mid (mask (V (morder d))) ||| mid (mask (V (morder i)))) = true
    rw [← mid_or, ← mask_union]
    exact msmall_ids _ (h3 _ _ ho ha)
  · intro d i j hdi hdj ha
    show msub (mask (V (morder d))) (mask (V (morder i)) ||| mask (V (morder j))) = false
    rw [← mask_union]
    apply Bool.eq_false_iff.2
    intro hs
    exact h4 _ _ _ (fun e => hdi (morder_inj _ _ e)) (fun e => hdj (morder_inj _ _ e)) ha
      ((msub_iff _ _).1 hs)

theorem exists_mask (W : Fin 14 → Finset (Fin 6 × Bool)) (h : Model634 W) :
    ∃ w, MModel w := by
  obtain ⟨π, s, hC⟩ := exists_canon morder W (fun v => (h.1 v).2.2)
  exact ⟨_, mask_model _ (model_inv π s W h) hC⟩
def ckt10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Nat) : Bool :=
  ((((((((mcross x10 x4) && (mcross x10 x9)) && ((msmall (mid x10 ||| mid x1)) && (msmall (mid x10 ||| mid x5)))) && (((msmall (mid x10 ||| mid x6)) && (!(msub x10 x0))) && ((!(msub x0 x10)) && (!(msub x10 x1))))) && ((((!(msub x1 x10)) && (!(msub x10 x2))) && ((!(msub x2 x10)) && (!(msub x10 x3)))) && (((!(msub x3 x10)) && (!(msub x10 x4))) && ((!(msub x4 x10)) && (!(msub x10 x5)))))) && (((((!(msub x5 x10)) && (!(msub x10 x6))) && ((!(msub x6 x10)) && (!(msub x10 x7)))) && (((!(msub x7 x10)) && (!(msub x10 x8))) && ((!(msub x8 x10)) && (!(msub x10 x9))))) && ((((!(msub x9 x10)) && (!(msub x1 (x10 ||| x0)))) && ((!(msub x0 (x10 ||| x1))) && (!(msub x10 (x2 ||| x0))))) && (((!(msub x2 (x10 ||| x0))) && (!(msub x0 (x10 ||| x2)))) && ((!(msub x2 (x10 ||| x1))) && (!(msub x1 (x10 ||| x2)))))))) && ((((((!(msub x10 (x3 ||| x0))) && (!(msub x3 (x10 ||| x0)))) && ((!(msub x0 (x10 ||| x3))) && (!(msub x3 (x10 ||| x1))))) && (((!(msub x1 (x10 ||| x3))) && (!(msub x10 (x3 ||| x2)))) && ((!(msub x3 (x10 ||| x2))) && (!(msub x2 (x10 ||| x3)))))) && ((((!(msub x4 (x10 ||| x0))) && (!(msub x10 (x4 ||| x1)))) && ((!(msub x4 (x10 ||| x1))) && (!(msub x10 (x4 ||| x2))))) && (((!(msub x4 (x10 ||| x2))) && (!(msub x10 (x4 ||| x3)))) && ((!(msub x4 (x10 ||| x3))) && (!(msub x5 (x10 ||| x0))))))) && (((((!(msub x0 (x10 ||| x5))) && (!(msub x10 (x5 ||| x1)))) && ((!(msub x5 (x10 ||| x1))) && (!(msub x1 (x10 ||| x5))))) && (((!(msub x10 (x5 ||| x2))) && (!(msub x5 (x10 ||| x2)))) && ((!(msub x2 (x10 ||| x5))) && (!(msub x10 (x5 ||| x3)))))) && ((((!(msub x5 (x10 ||| x3))) && (!(msub x3 (x10 ||| x5)))) && ((!(msub x10 (x5 ||| x4))) && (!(msub x4 (x10 ||| x5))))) && (((!(msub x10 (x6 ||| x0))) && (!(msub x6 (x10 ||| x0)))) && ((!(msub x0 (x10 ||| x6))) && ((!(msub x10 (x6 ||| x1))) && (!(msub x6 (x10 ||| x1)))))))))) && (((((((!(msub x1 (x10 ||| x6))) && (!(msub x6 (x10 ||| x2)))) && ((!(msub x2 (x10 ||| x6))) && (!(msub x10 (x6 ||| x3))))) && (((!(msub x6 (x10 ||| x3))) && (!(msub x3 (x10 ||| x6)))) && ((!(msub x10 (x6 ||| x4))) && (!(msub x4 (x10 ||| x6)))))) && ((((!(msub x10 (x6 ||| x5))) && (!(msub x6 (x10 ||| x5)))) && ((!(msub x5 (x10 ||| x6))) && (!(msub x10 (x7 ||| x0))))) && (((!(msub x7 (x10 ||| x0))) && (!(msub x0 (x10 ||| x7)))) && ((!(msub x10 (x7 ||| x1))) && (!(msub x7 (x10 ||| x1))))))) && (((((!(msub x1 (x10 ||| x7))) && (!(msub x10 (x7 ||| x2)))) && ((!(msub x7 (x10 ||| x2))) && (!(msub x2 (x10 ||| x7))))) && (((!(msub x10 (x7 ||| x3))) && (!(msub x7 (x10 ||| x3)))) && ((!(msub x3 (x10 ||| x7))) && (!(msub x10 (x7 ||| x4)))))) && ((((!(msub x4 (x10 ||| x7))) && (!(msub x7 (x10 ||| x5)))) && ((!(msub x5 (x10 ||| x7))) && (!(msub x7 (x10 ||| x6))))) && (((!(msub x6 (x10 ||| x7))) && (!(msub x10 (x8 ||| x0)))) && ((!(msub x8 (x10 ||| x0))) && (!(msub x0 (x10 ||| x8)))))))) && ((((((!(msub x10 (x8 ||| x1))) && (!(msub x8 (x10 ||| x1)))) && ((!(msub x1 (x10 ||| x8))) && (!(msub x10 (x8 ||| x2))))) && (((!(msub x8 (x10 ||| x2))) && (!(msub x2 (x10 ||| x8)))) && ((!(msub x10 (x8 ||| x3))) && (!(msub x8 (x10 ||| x3)))))) && ((((!(msub x3 (x10 ||| x8))) && (!(msub x4 (x10 ||| x8)))) && ((!(msub x10 (x8 ||| x5))) && (!(msub x8 (x10 ||| x5))))) && (((!(msub x5 (x10 ||| x8))) && (!(msub x8 (x10 ||| x6)))) && ((!(msub x6 (x10 ||| x8))) && (!(msub x10 (x8 ||| x7))))))) && (((((!(msub x8 (x10 ||| x7))) && (!(msub x7 (x10 ||| x8)))) && ((!(msub x10 (x9 ||| x0))) && (!(msub x9 (x10 ||| x0))))) && (((!(msub x10 (x9 ||| x1))) && (!(msub x9 (x10 ||| x1)))) && ((!(msub x10 (x9 ||| x2))) && (!(msub x9 (x10 ||| x2)))))) && ((((!(msub x9 (x10 ||| x3))) && (!(msub x10 (x9 ||| x4)))) && ((!(msub x10 (x9 ||| x5))) && (!(msub x9 (x10 ||| x5))))) && (((!(msub x10 (x9 ||| x6))) && (!(msub x9 (x10 ||| x6)))) && ((!(msub x9 (x10 ||| x7))) && ((!(msub x10 (x9 ||| x8))) && (!(msub x9 (x10 ||| x8)))))))))))

def runM10 (s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) : Bool :=
  (mopts s).any (fun x10 => ckt10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 && true)

set_option maxHeartbeats 4000000 in
theorem passM10 (w : Fin 14 → Nat) (h : MModel w) : ckt10 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) (w 10) = true := by
  simp only [ckt10, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨(h.2.1 10 4 (by decide)), (h.2.1 10 9 (by decide))⟩, ⟨(h.2.2.1 10 1 (by decide) (by decide)), (h.2.2.1 10 5 (by decide) (by decide))⟩⟩, ⟨⟨(h.2.2.1 10 6 (by decide) (by decide)), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 0 0 (by decide) (by decide) (by decide)) : msub (w 10) (w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 10 10 (by decide) (by decide) (by decide)) : msub (w 0) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 1 1 (by decide) (by decide) (by decide)) : msub (w 10) (w 1) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 10 10 (by decide) (by decide) (by decide)) : msub (w 1) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 2 2 (by decide) (by decide) (by decide)) : msub (w 10) (w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 10 10 (by decide) (by decide) (by decide)) : msub (w 2) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 3 3 (by decide) (by decide) (by decide)) : msub (w 10) (w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 10 10 (by decide) (by decide) (by decide)) : msub (w 3) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 4 4 (by decide) (by decide) (by decide)) : msub (w 10) (w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 10 10 (by decide) (by decide) (by decide)) : msub (w 4) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 5 5 (by decide) (by decide) (by decide)) : msub (w 10) (w 5) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 10 10 (by decide) (by decide) (by decide)) : msub (w 5) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 6 6 (by decide) (by decide) (by decide)) : msub (w 10) (w 6) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 10 10 (by decide) (by decide) (by decide)) : msub (w 6) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 7 7 (by decide) (by decide) (by decide)) : msub (w 10) (w 7) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 10 10 (by decide) (by decide) (by decide)) : msub (w 7) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 8 8 (by decide) (by decide) (by decide)) : msub (w 10) (w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 10 10 (by decide) (by decide) (by decide)) : msub (w 8) (w 10) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 10 9 9 (by decide) (by decide) (by decide)) : msub (w 10) (w 9) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 10 10 (by decide) (by decide) (by decide)) : msub (w 9) (w 10) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 10 0 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 0 10 1 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 2 0 (by decide) (by decide) (by decide) : msub (w 10) (w 2 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 2 10 0 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 10 2 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 2 10 1 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 10 2 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 2) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(by simp only [(h.2.2.2 10 3 0 (by decide) (by decide) (by decide) : msub (w 10) (w 3 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 10 0 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 0 10 3 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 10 1 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 1) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 1 10 3 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 3 2 (by decide) (by decide) (by decide) : msub (w 10) (w 3 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 3 10 2 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 10 3 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 3) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 4 10 0 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 4 1 (by decide) (by decide) (by decide) : msub (w 10) (w 4 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 4 10 1 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 4 2 (by decide) (by decide) (by decide) : msub (w 10) (w 4 ||| w 2) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 4 10 2 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 4 3 (by decide) (by decide) (by decide) : msub (w 10) (w 4 ||| w 3) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 4 10 3 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 10 0 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 0) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 0 10 5 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 5 1 (by decide) (by decide) (by decide) : msub (w 10) (w 5 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 10 1 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 10 5 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 5) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 10 5 2 (by decide) (by decide) (by decide) : msub (w 10) (w 5 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 10 2 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 2 10 5 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 5 3 (by decide) (by decide) (by decide) : msub (w 10) (w 5 ||| w 3) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 5 10 3 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 10 5 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 5) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 5 4 (by decide) (by decide) (by decide) : msub (w 10) (w 5 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 10 5 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 5) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 10 6 0 (by decide) (by decide) (by decide) : msub (w 10) (w 6 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 10 0 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 0 10 6 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 6) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 10 6 1 (by decide) (by decide) (by decide) : msub (w 10) (w 6 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 10 1 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 1) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨⟨(by simp only [(h.2.2.2 1 10 6 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 6) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 10 2 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 2 10 6 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 6) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 6 3 (by decide) (by decide) (by decide) : msub (w 10) (w 6 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 6 10 3 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 10 6 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 6) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 6 4 (by decide) (by decide) (by decide) : msub (w 10) (w 6 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 10 6 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 6) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 10 6 5 (by decide) (by decide) (by decide) : msub (w 10) (w 6 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 10 5 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 5) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 10 6 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 6) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 7 0 (by decide) (by decide) (by decide) : msub (w 10) (w 7 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 7 10 0 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 10 7 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 7) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 7 1 (by decide) (by decide) (by decide) : msub (w 10) (w 7 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 10 1 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 1) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 1 10 7 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 7 2 (by decide) (by decide) (by decide) : msub (w 10) (w 7 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 7 10 2 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 10 7 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 7) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 10 7 3 (by decide) (by decide) (by decide) : msub (w 10) (w 7 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 10 3 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 3) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 3 10 7 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 7 4 (by decide) (by decide) (by decide) : msub (w 10) (w 7 ||| w 4) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 4 10 7 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 10 5 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 5) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 10 7 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 10 6 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 6) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 6 10 7 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 8 0 (by decide) (by decide) (by decide) : msub (w 10) (w 8 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 10 0 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 10 8 (by decide) (by decide) (by decide) : msub (w 0) (w 10 ||| w 8) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(by simp only [(h.2.2.2 10 8 1 (by decide) (by decide) (by decide) : msub (w 10) (w 8 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 10 1 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 1 10 8 (by decide) (by decide) (by decide) : msub (w 1) (w 10 ||| w 8) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 8 2 (by decide) (by decide) (by decide) : msub (w 10) (w 8 ||| w 2) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 8 10 2 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 10 8 (by decide) (by decide) (by decide) : msub (w 2) (w 10 ||| w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 8 3 (by decide) (by decide) (by decide) : msub (w 10) (w 8 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 10 3 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 3) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 3 10 8 (by decide) (by decide) (by decide) : msub (w 3) (w 10 ||| w 8) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 10 8 (by decide) (by decide) (by decide) : msub (w 4) (w 10 ||| w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 8 5 (by decide) (by decide) (by decide) : msub (w 10) (w 8 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 10 5 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 5) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 5 10 8 (by decide) (by decide) (by decide) : msub (w 5) (w 10 ||| w 8) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 10 6 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 6) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 6 10 8 (by decide) (by decide) (by decide) : msub (w 6) (w 10 ||| w 8) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 8 7 (by decide) (by decide) (by decide) : msub (w 10) (w 8 ||| w 7) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 8 10 7 (by decide) (by decide) (by decide) : msub (w 8) (w 10 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 10 8 (by decide) (by decide) (by decide) : msub (w 7) (w 10 ||| w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 9 0 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 10 0 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 10 9 1 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 10 1 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 9 2 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 10 2 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 9 10 3 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 10 9 4 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 10 9 5 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 10 5 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 5) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 10 9 6 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 6) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 10 6 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 6) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 9 10 7 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 7) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 10 9 8 (by decide) (by decide) (by decide) : msub (w 10) (w 9 ||| w 8) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 10 8 (by decide) (by decide) (by decide) : msub (w 9) (w 10 ||| w 8) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩⟩⟩

theorem goodM10 (w : Fin 14 → Nat) (h : MModel w) : runM10 (mseen w 10) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 10, h.1 10, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM10 w h, ?_⟩
  rfl

def ckt9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) : Bool :=
  (((((((mcross x9 x3) && ((mcross x9 x7) && (msmall (mid x9 ||| mid x0)))) && ((msmall (mid x9 ||| mid x2)) && ((msmall (mid x9 ||| mid x8)) && (!(msub x9 x0))))) && (((!(msub x0 x9)) && ((!(msub x9 x1)) && (!(msub x1 x9)))) && (((!(msub x9 x2)) && (!(msub x2 x9))) && ((!(msub x9 x3)) && (!(msub x3 x9)))))) && ((((!(msub x9 x4)) && ((!(msub x4 x9)) && (!(msub x9 x5)))) && ((!(msub x5 x9)) && ((!(msub x9 x6)) && (!(msub x6 x9))))) && (((!(msub x9 x7)) && ((!(msub x7 x9)) && (!(msub x9 x8)))) && (((!(msub x8 x9)) && (!(msub x1 (x9 ||| x0)))) && ((!(msub x0 (x9 ||| x1))) && (!(msub x9 (x2 ||| x0)))))))) && (((((!(msub x2 (x9 ||| x0))) && ((!(msub x0 (x9 ||| x2))) && (!(msub x2 (x9 ||| x1))))) && ((!(msub x1 (x9 ||| x2))) && ((!(msub x9 (x3 ||| x0))) && (!(msub x3 (x9 ||| x0)))))) && (((!(msub x3 (x9 ||| x1))) && ((!(msub x9 (x3 ||| x2))) && (!(msub x3 (x9 ||| x2))))) && (((!(msub x4 (x9 ||| x0))) && (!(msub x0 (x9 ||| x4)))) && ((!(msub x9 (x4 ||| x1))) && (!(msub x4 (x9 ||| x1))))))) && ((((!(msub x1 (x9 ||| x4))) && ((!(msub x9 (x4 ||| x2))) && (!(msub x4 (x9 ||| x2))))) && ((!(msub x2 (x9 ||| x4))) && ((!(msub x9 (x4 ||| x3))) && (!(msub x3 (x9 ||| x4)))))) && (((!(msub x5 (x9 ||| x0))) && ((!(msub x0 (x9 ||| x5))) && (!(msub x9 (x5 ||| x1))))) && (((!(msub x5 (x9 ||| x1))) && (!(msub x1 (x9 ||| x5)))) && ((!(msub x9 (x5 ||| x2))) && (!(msub x5 (x9 ||| x2))))))))) && ((((((!(msub x2 (x9 ||| x5))) && ((!(msub x9 (x5 ||| x3))) && (!(msub x3 (x9 ||| x5))))) && ((!(msub x9 (x5 ||| x4))) && ((!(msub x5 (x9 ||| x4))) && (!(msub x4 (x9 ||| x5)))))) && (((!(msub x9 (x6 ||| x0))) && ((!(msub x6 (x9 ||| x0))) && (!(msub x0 (x9 ||| x6))))) && (((!(msub x9 (x6 ||| x1))) && (!(msub x6 (x9 ||| x1)))) && ((!(msub x1 (x9 ||| x6))) && (!(msub x6 (x9 ||| x2))))))) && ((((!(msub x2 (x9 ||| x6))) && ((!(msub x9 (x6 ||| x3))) && (!(msub x3 (x9 ||| x6))))) && ((!(msub x9 (x6 ||| x4))) && ((!(msub x6 (x9 ||| x4))) && (!(msub x4 (x9 ||| x6)))))) && (((!(msub x9 (x6 ||| x5))) && ((!(msub x6 (x9 ||| x5))) && (!(msub x5 (x9 ||| x6))))) && (((!(msub x9 (x7 ||| x0))) && (!(msub x7 (x9 ||| x0)))) && ((!(msub x9 (x7 ||| x1))) && (!(msub x7 (x9 ||| x1)))))))) && (((((!(msub x9 (x7 ||| x2))) && ((!(msub x7 (x9 ||| x2))) && (!(msub x9 (x7 ||| x3))))) && ((!(msub x9 (x7 ||| x4))) && ((!(msub x7 (x9 ||| x4))) && (!(msub x7 (x9 ||| x5)))))) && (((!(msub x7 (x9 ||| x6))) && ((!(msub x9 (x8 ||| x0))) && (!(msub x8 (x9 ||| x0))))) && (((!(msub x0 (x9 ||| x8))) && (!(msub x9 (x8 ||| x1)))) && ((!(msub x8 (x9 ||| x1))) && (!(msub x1 (x9 ||| x8))))))) && ((((!(msub x9 (x8 ||| x2))) && ((!(msub x8 (x9 ||| x2))) && (!(msub x2 (x9 ||| x8))))) && (((!(msub x9 (x8 ||| x3))) && (!(msub x3 (x9 ||| x8)))) && ((!(msub x8 (x9 ||| x4))) && (!(msub x4 (x9 ||| x8)))))) && (((!(msub x9 (x8 ||| x5))) && ((!(msub x8 (x9 ||| x5))) && (!(msub x5 (x9 ||| x8))))) && (((!(msub x8 (x9 ||| x6))) && (!(msub x6 (x9 ||| x8)))) && ((!(msub x9 (x8 ||| x7))) && (!(msub x7 (x9 ||| x8))))))))))

def runM9 (s x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) : Bool :=
  (mopts s).any (fun x9 => ckt9 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 && runM10 (s ||| mid x9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)

set_option maxHeartbeats 4000000 in
theorem passM9 (w : Fin 14 → Nat) (h : MModel w) : ckt9 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9) = true := by
  simp only [ckt9, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨(h.2.1 9 3 (by decide)), ⟨(h.2.1 9 7 (by decide)), (h.2.2.1 9 0 (by decide) (by decide))⟩⟩, ⟨(h.2.2.1 9 2 (by decide) (by decide)), ⟨(h.2.2.1 9 8 (by decide) (by decide)), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 0 0 (by decide) (by decide) (by decide)) : msub (w 9) (w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 9 9 (by decide) (by decide) (by decide)) : msub (w 0) (w 9) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 1 1 (by decide) (by decide) (by decide)) : msub (w 9) (w 1) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 9 9 (by decide) (by decide) (by decide)) : msub (w 1) (w 9) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 2 2 (by decide) (by decide) (by decide)) : msub (w 9) (w 2) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 9 9 (by decide) (by decide) (by decide)) : msub (w 2) (w 9) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 3 3 (by decide) (by decide) (by decide)) : msub (w 9) (w 3) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 9 9 (by decide) (by decide) (by decide)) : msub (w 3) (w 9) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 4 4 (by decide) (by decide) (by decide)) : msub (w 9) (w 4) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 9 9 (by decide) (by decide) (by decide)) : msub (w 4) (w 9) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 5 5 (by decide) (by decide) (by decide)) : msub (w 9) (w 5) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 9 9 (by decide) (by decide) (by decide)) : msub (w 5) (w 9) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 6 6 (by decide) (by decide) (by decide)) : msub (w 9) (w 6) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 9 9 (by decide) (by decide) (by decide)) : msub (w 6) (w 9) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 7 7 (by decide) (by decide) (by decide)) : msub (w 9) (w 7) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 9 9 (by decide) (by decide) (by decide)) : msub (w 7) (w 9) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 9 8 8 (by decide) (by decide) (by decide)) : msub (w 9) (w 8) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 9 9 (by decide) (by decide) (by decide)) : msub (w 8) (w 9) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 9 0 (by decide) (by decide) (by decide) : msub (w 1) (w 9 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 0 9 1 (by decide) (by decide) (by decide) : msub (w 0) (w 9 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 2 0 (by decide) (by decide) (by decide) : msub (w 9) (w 2 ||| w 0) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 2 9 0 (by decide) (by decide) (by decide) : msub (w 2) (w 9 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 0 9 2 (by decide) (by decide) (by decide) : msub (w 0) (w 9 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 9 1 (by decide) (by decide) (by decide) : msub (w 2) (w 9 ||| w 1) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 1 9 2 (by decide) (by decide) (by decide) : msub (w 1) (w 9 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 3 0 (by decide) (by decide) (by decide) : msub (w 9) (w 3 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 9 0 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 3 9 1 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 1) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 3 2 (by decide) (by decide) (by decide) : msub (w 9) (w 3 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 9 2 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 2) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 4 9 0 (by decide) (by decide) (by decide) : msub (w 4) (w 9 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 9 4 (by decide) (by decide) (by decide) : msub (w 0) (w 9 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 9 4 1 (by decide) (by decide) (by decide) : msub (w 9) (w 4 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 9 1 (by decide) (by decide) (by decide) : msub (w 4) (w 9 ||| w 1) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 1 9 4 (by decide) (by decide) (by decide) : msub (w 1) (w 9 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 4 2 (by decide) (by decide) (by decide) : msub (w 9) (w 4 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 9 2 (by decide) (by decide) (by decide) : msub (w 4) (w 9 ||| w 2) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 2 9 4 (by decide) (by decide) (by decide) : msub (w 2) (w 9 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 4 3 (by decide) (by decide) (by decide) : msub (w 9) (w 4 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 9 4 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 4) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 5 9 0 (by decide) (by decide) (by decide) : msub (w 5) (w 9 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 0 9 5 (by decide) (by decide) (by decide) : msub (w 0) (w 9 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 5 1 (by decide) (by decide) (by decide) : msub (w 9) (w 5 ||| w 1) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 5 9 1 (by decide) (by decide) (by decide) : msub (w 5) (w 9 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 9 5 (by decide) (by decide) (by decide) : msub (w 1) (w 9 ||| w 5) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 9 5 2 (by decide) (by decide) (by decide) : msub (w 9) (w 5 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 9 2 (by decide) (by decide) (by decide) : msub (w 5) (w 9 ||| w 2) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(by simp only [(h.2.2.2 2 9 5 (by decide) (by decide) (by decide) : msub (w 2) (w 9 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 5 3 (by decide) (by decide) (by decide) : msub (w 9) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 9 5 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 5) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 9 5 4 (by decide) (by decide) (by decide) : msub (w 9) (w 5 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 5 9 4 (by decide) (by decide) (by decide) : msub (w 5) (w 9 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 9 5 (by decide) (by decide) (by decide) : msub (w 4) (w 9 ||| w 5) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 9 6 0 (by decide) (by decide) (by decide) : msub (w 9) (w 6 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 9 0 (by decide) (by decide) (by decide) : msub (w 6) (w 9 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 9 6 (by decide) (by decide) (by decide) : msub (w 0) (w 9 ||| w 6) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 9 6 1 (by decide) (by decide) (by decide) : msub (w 9) (w 6 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 9 1 (by decide) (by decide) (by decide) : msub (w 6) (w 9 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 1 9 6 (by decide) (by decide) (by decide) : msub (w 1) (w 9 ||| w 6) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 9 2 (by decide) (by decide) (by decide) : msub (w 6) (w 9 ||| w 2) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 2 9 6 (by decide) (by decide) (by decide) : msub (w 2) (w 9 ||| w 6) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 6 3 (by decide) (by decide) (by decide) : msub (w 9) (w 6 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 9 6 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 6) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 9 6 4 (by decide) (by decide) (by decide) : msub (w 9) (w 6 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 9 4 (by decide) (by decide) (by decide) : msub (w 6) (w 9 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 9 6 (by decide) (by decide) (by decide) : msub (w 4) (w 9 ||| w 6) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 9 6 5 (by decide) (by decide) (by decide) : msub (w 9) (w 6 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 9 5 (by decide) (by decide) (by decide) : msub (w 6) (w 9 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 9 6 (by decide) (by decide) (by decide) : msub (w 5) (w 9 ||| w 6) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 9 7 0 (by decide) (by decide) (by decide) : msub (w 9) (w 7 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 9 0 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 9 7 1 (by decide) (by decide) (by decide) : msub (w 9) (w 7 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 9 1 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 1) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 9 7 2 (by decide) (by decide) (by decide) : msub (w 9) (w 7 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 7 9 2 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 7 3 (by decide) (by decide) (by decide) : msub (w 9) (w 7 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 9 7 4 (by decide) (by decide) (by decide) : msub (w 9) (w 7 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 7 9 4 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 9 5 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 5) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 7 9 6 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 6) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 9 8 0 (by decide) (by decide) (by decide) : msub (w 9) (w 8 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 9 0 (by decide) (by decide) (by decide) : msub (w 8) (w 9 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 0 9 8 (by decide) (by decide) (by decide) : msub (w 0) (w 9 ||| w 8) = false), Bool.not_false]), (by simp only [(h.2.2.2 9 8 1 (by decide) (by decide) (by decide) : msub (w 9) (w 8 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 9 1 (by decide) (by decide) (by decide) : msub (w 8) (w 9 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 9 8 (by decide) (by decide) (by decide) : msub (w 1) (w 9 ||| w 8) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 9 8 2 (by decide) (by decide) (by decide) : msub (w 9) (w 8 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 8 9 2 (by decide) (by decide) (by decide) : msub (w 8) (w 9 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 9 8 (by decide) (by decide) (by decide) : msub (w 2) (w 9 ||| w 8) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 9 8 3 (by decide) (by decide) (by decide) : msub (w 9) (w 8 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 9 8 (by decide) (by decide) (by decide) : msub (w 3) (w 9 ||| w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 9 4 (by decide) (by decide) (by decide) : msub (w 8) (w 9 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 9 8 (by decide) (by decide) (by decide) : msub (w 4) (w 9 ||| w 8) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 9 8 5 (by decide) (by decide) (by decide) : msub (w 9) (w 8 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 8 9 5 (by decide) (by decide) (by decide) : msub (w 8) (w 9 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 9 8 (by decide) (by decide) (by decide) : msub (w 5) (w 9 ||| w 8) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 8 9 6 (by decide) (by decide) (by decide) : msub (w 8) (w 9 ||| w 6) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 9 8 (by decide) (by decide) (by decide) : msub (w 6) (w 9 ||| w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 9 8 7 (by decide) (by decide) (by decide) : msub (w 9) (w 8 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 9 8 (by decide) (by decide) (by decide) : msub (w 7) (w 9 ||| w 8) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩⟩

theorem goodM9 (w : Fin 14 → Nat) (h : MModel w) : runM9 (mseen w 9) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 9, h.1 9, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM9 w h, ?_⟩
  exact goodM10 w h

def ckt8 (x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat) : Bool :=
  (((((((mcross x8 x4) && (mcross x8 x6)) && ((msmall (mid x8 ||| mid x1)) && ((msmall (mid x8 ||| mid x5)) && (!(msub x8 x0))))) && (((!(msub x0 x8)) && (!(msub x8 x1))) && ((!(msub x1 x8)) && ((!(msub x8 x2)) && (!(msub x2 x8)))))) && ((((!(msub x8 x3)) && (!(msub x3 x8))) && ((!(msub x8 x4)) && ((!(msub x4 x8)) && (!(msub x8 x5))))) && (((!(msub x5 x8)) && (!(msub x8 x6))) && ((!(msub x6 x8)) && ((!(msub x8 x7)) && (!(msub x7 x8))))))) && (((((!(msub x1 (x8 ||| x0))) && (!(msub x0 (x8 ||| x1)))) && ((!(msub x8 (x2 ||| x0))) && ((!(msub x2 (x8 ||| x0))) && (!(msub x0 (x8 ||| x2)))))) && (((!(msub x2 (x8 ||| x1))) && (!(msub x1 (x8 ||| x2)))) && ((!(msub x8 (x3 ||| x0))) && ((!(msub x3 (x8 ||| x0))) && (!(msub x0 (x8 ||| x3))))))) && ((((!(msub x3 (x8 ||| x1))) && (!(msub x1 (x8 ||| x3)))) && ((!(msub x8 (x3 ||| x2))) && ((!(msub x3 (x8 ||| x2))) && (!(msub x2 (x8 ||| x3)))))) && (((!(msub x4 (x8 ||| x0))) && ((!(msub x8 (x4 ||| x1))) && (!(msub x4 (x8 ||| x1))))) && ((!(msub x8 (x4 ||| x2))) && ((!(msub x4 (x8 ||| x2))) && (!(msub x8 (x4 ||| x3))))))))) && ((((((!(msub x4 (x8 ||| x3))) && (!(msub x5 (x8 ||| x0)))) && ((!(msub x0 (x8 ||| x5))) && ((!(msub x8 (x5 ||| x1))) && (!(msub x5 (x8 ||| x1)))))) && (((!(msub x1 (x8 ||| x5))) && (!(msub x8 (x5 ||| x2)))) && ((!(msub x5 (x8 ||| x2))) && ((!(msub x2 (x8 ||| x5))) && (!(msub x8 (x5 ||| x3))))))) && ((((!(msub x5 (x8 ||| x3))) && (!(msub x3 (x8 ||| x5)))) && ((!(msub x8 (x5 ||| x4))) && ((!(msub x4 (x8 ||| x5))) && (!(msub x8 (x6 ||| x0)))))) && (((!(msub x6 (x8 ||| x0))) && (!(msub x8 (x6 ||| x1)))) && ((!(msub x6 (x8 ||| x1))) && ((!(msub x6 (x8 ||| x2))) && (!(msub x8 (x6 ||| x3)))))))) && (((((!(msub x6 (x8 ||| x3))) && (!(msub x8 (x6 ||| x4)))) && ((!(msub x8 (x6 ||| x5))) && ((!(msub x6 (x8 ||| x5))) && (!(msub x8 (x7 ||| x0)))))) && (((!(msub x7 (x8 ||| x0))) && (!(msub x0 (x8 ||| x7)))) && ((!(msub x8 (x7 ||| x1))) && ((!(msub x7 (x8 ||| x1))) && (!(msub x1 (x8 ||| x7))))))) && ((((!(msub x8 (x7 ||| x2))) && (!(msub x7 (x8 ||| x2)))) && ((!(msub x2 (x8 ||| x7))) && ((!(msub x8 (x7 ||| x3))) && (!(msub x7 (x8 ||| x3)))))) && (((!(msub x3 (x8 ||| x7))) && ((!(msub x8 (x7 ||| x4))) && (!(msub x4 (x8 ||| x7))))) && ((!(msub x7 (x8 ||| x5))) && ((!(msub x5 (x8 ||| x7))) && (!(msub x6 (x8 ||| x7))))))))))

def runM8 (s x0 x1 x2 x3 x4 x5 x6 x7 : Nat) : Bool :=
  (mopts s).any (fun x8 => ckt8 x0 x1 x2 x3 x4 x5 x6 x7 x8 && runM9 (s ||| mid x8) x0 x1 x2 x3 x4 x5 x6 x7 x8)

set_option maxHeartbeats 4000000 in
theorem passM8 (w : Fin 14 → Nat) (h : MModel w) : ckt8 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) = true := by
  simp only [ckt8, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨(h.2.1 8 4 (by decide)), (h.2.1 8 6 (by decide))⟩, ⟨(h.2.2.1 8 1 (by decide) (by decide)), ⟨(h.2.2.1 8 5 (by decide) (by decide)), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 0 0 (by decide) (by decide) (by decide)) : msub (w 8) (w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 8 8 (by decide) (by decide) (by decide)) : msub (w 0) (w 8) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 1 1 (by decide) (by decide) (by decide)) : msub (w 8) (w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 8 8 (by decide) (by decide) (by decide)) : msub (w 1) (w 8) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 2 2 (by decide) (by decide) (by decide)) : msub (w 8) (w 2) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 8 8 (by decide) (by decide) (by decide)) : msub (w 2) (w 8) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 3 3 (by decide) (by decide) (by decide)) : msub (w 8) (w 3) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 8 8 (by decide) (by decide) (by decide)) : msub (w 3) (w 8) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 4 4 (by decide) (by decide) (by decide)) : msub (w 8) (w 4) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 8 8 (by decide) (by decide) (by decide)) : msub (w 4) (w 8) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 5 5 (by decide) (by decide) (by decide)) : msub (w 8) (w 5) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 8 8 (by decide) (by decide) (by decide)) : msub (w 5) (w 8) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 6 6 (by decide) (by decide) (by decide)) : msub (w 8) (w 6) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 8 8 (by decide) (by decide) (by decide)) : msub (w 6) (w 8) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 8 7 7 (by decide) (by decide) (by decide)) : msub (w 8) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 8 8 (by decide) (by decide) (by decide)) : msub (w 7) (w 8) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 1 8 0 (by decide) (by decide) (by decide) : msub (w 1) (w 8 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 8 1 (by decide) (by decide) (by decide) : msub (w 0) (w 8 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 2 0 (by decide) (by decide) (by decide) : msub (w 8) (w 2 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 2 8 0 (by decide) (by decide) (by decide) : msub (w 2) (w 8 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 8 2 (by decide) (by decide) (by decide) : msub (w 0) (w 8 ||| w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 2 8 1 (by decide) (by decide) (by decide) : msub (w 2) (w 8 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 8 2 (by decide) (by decide) (by decide) : msub (w 1) (w 8 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 3 0 (by decide) (by decide) (by decide) : msub (w 8) (w 3 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 3 8 0 (by decide) (by decide) (by decide) : msub (w 3) (w 8 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 8 3 (by decide) (by decide) (by decide) : msub (w 0) (w 8 ||| w 3) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 3 8 1 (by decide) (by decide) (by decide) : msub (w 3) (w 8 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 8 3 (by decide) (by decide) (by decide) : msub (w 1) (w 8 ||| w 3) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 3 2 (by decide) (by decide) (by decide) : msub (w 8) (w 3 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 3 8 2 (by decide) (by decide) (by decide) : msub (w 3) (w 8 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 8 3 (by decide) (by decide) (by decide) : msub (w 2) (w 8 ||| w 3) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 4 8 0 (by decide) (by decide) (by decide) : msub (w 4) (w 8 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 8 4 1 (by decide) (by decide) (by decide) : msub (w 8) (w 4 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 8 1 (by decide) (by decide) (by decide) : msub (w 4) (w 8 ||| w 1) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 8 4 2 (by decide) (by decide) (by decide) : msub (w 8) (w 4 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 4 8 2 (by decide) (by decide) (by decide) : msub (w 4) (w 8 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 4 3 (by decide) (by decide) (by decide) : msub (w 8) (w 4 ||| w 3) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(by simp only [(h.2.2.2 4 8 3 (by decide) (by decide) (by decide) : msub (w 4) (w 8 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 8 0 (by decide) (by decide) (by decide) : msub (w 5) (w 8 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 0 8 5 (by decide) (by decide) (by decide) : msub (w 0) (w 8 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 8 5 1 (by decide) (by decide) (by decide) : msub (w 8) (w 5 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 8 1 (by decide) (by decide) (by decide) : msub (w 5) (w 8 ||| w 1) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 1 8 5 (by decide) (by decide) (by decide) : msub (w 1) (w 8 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 5 2 (by decide) (by decide) (by decide) : msub (w 8) (w 5 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 8 2 (by decide) (by decide) (by decide) : msub (w 5) (w 8 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 2 8 5 (by decide) (by decide) (by decide) : msub (w 2) (w 8 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 5 3 (by decide) (by decide) (by decide) : msub (w 8) (w 5 ||| w 3) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 5 8 3 (by decide) (by decide) (by decide) : msub (w 5) (w 8 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 8 5 (by decide) (by decide) (by decide) : msub (w 3) (w 8 ||| w 5) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 5 4 (by decide) (by decide) (by decide) : msub (w 8) (w 5 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 4 8 5 (by decide) (by decide) (by decide) : msub (w 4) (w 8 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 6 0 (by decide) (by decide) (by decide) : msub (w 8) (w 6 ||| w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 6 8 0 (by decide) (by decide) (by decide) : msub (w 6) (w 8 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 6 1 (by decide) (by decide) (by decide) : msub (w 8) (w 6 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 6 8 1 (by decide) (by decide) (by decide) : msub (w 6) (w 8 ||| w 1) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 8 2 (by decide) (by decide) (by decide) : msub (w 6) (w 8 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 6 3 (by decide) (by decide) (by decide) : msub (w 8) (w 6 ||| w 3) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 6 8 3 (by decide) (by decide) (by decide) : msub (w 6) (w 8 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 6 4 (by decide) (by decide) (by decide) : msub (w 8) (w 6 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 6 5 (by decide) (by decide) (by decide) : msub (w 8) (w 6 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 8 5 (by decide) (by decide) (by decide) : msub (w 6) (w 8 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 8 7 0 (by decide) (by decide) (by decide) : msub (w 8) (w 7 ||| w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 7 8 0 (by decide) (by decide) (by decide) : msub (w 7) (w 8 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 8 7 (by decide) (by decide) (by decide) : msub (w 0) (w 8 ||| w 7) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 8 7 1 (by decide) (by decide) (by decide) : msub (w 8) (w 7 ||| w 1) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 7 8 1 (by decide) (by decide) (by decide) : msub (w 7) (w 8 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 8 7 (by decide) (by decide) (by decide) : msub (w 1) (w 8 ||| w 7) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 8 7 2 (by decide) (by decide) (by decide) : msub (w 8) (w 7 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 8 2 (by decide) (by decide) (by decide) : msub (w 7) (w 8 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 2 8 7 (by decide) (by decide) (by decide) : msub (w 2) (w 8 ||| w 7) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 8 7 3 (by decide) (by decide) (by decide) : msub (w 8) (w 7 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 8 3 (by decide) (by decide) (by decide) : msub (w 7) (w 8 ||| w 3) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 3 8 7 (by decide) (by decide) (by decide) : msub (w 3) (w 8 ||| w 7) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 8 7 4 (by decide) (by decide) (by decide) : msub (w 8) (w 7 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 8 7 (by decide) (by decide) (by decide) : msub (w 4) (w 8 ||| w 7) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 7 8 5 (by decide) (by decide) (by decide) : msub (w 7) (w 8 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 5 8 7 (by decide) (by decide) (by decide) : msub (w 5) (w 8 ||| w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 8 7 (by decide) (by decide) (by decide) : msub (w 6) (w 8 ||| w 7) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩⟩

theorem goodM8 (w : Fin 14 → Nat) (h : MModel w) : runM8 (mseen w 8) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 8, h.1 8, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM8 w h, ?_⟩
  exact goodM9 w h

def ckt7 (x0 x1 x2 x3 x4 x5 x6 x7 : Nat) : Bool :=
  ((((((mcross x7 x5) && ((mcross x7 x6) && (msmall (mid x7 ||| mid x1)))) && (((msmall (mid x7 ||| mid x4)) && (!(msub x7 x0))) && ((!(msub x0 x7)) && (!(msub x7 x1))))) && ((((!(msub x1 x7)) && (!(msub x7 x2))) && ((!(msub x2 x7)) && (!(msub x7 x3)))) && (((!(msub x3 x7)) && (!(msub x7 x4))) && ((!(msub x4 x7)) && (!(msub x7 x5)))))) && (((((!(msub x5 x7)) && (!(msub x7 x6))) && ((!(msub x6 x7)) && (!(msub x1 (x7 ||| x0))))) && (((!(msub x0 (x7 ||| x1))) && (!(msub x7 (x2 ||| x0)))) && ((!(msub x2 (x7 ||| x0))) && (!(msub x0 (x7 ||| x2)))))) && ((((!(msub x2 (x7 ||| x1))) && (!(msub x1 (x7 ||| x2)))) && ((!(msub x7 (x3 ||| x0))) && (!(msub x3 (x7 ||| x0))))) && (((!(msub x0 (x7 ||| x3))) && (!(msub x3 (x7 ||| x1)))) && ((!(msub x1 (x7 ||| x3))) && (!(msub x7 (x3 ||| x2)))))))) && ((((((!(msub x3 (x7 ||| x2))) && (!(msub x2 (x7 ||| x3)))) && ((!(msub x4 (x7 ||| x0))) && (!(msub x0 (x7 ||| x4))))) && (((!(msub x7 (x4 ||| x1))) && (!(msub x4 (x7 ||| x1)))) && ((!(msub x1 (x7 ||| x4))) && (!(msub x7 (x4 ||| x2)))))) && ((((!(msub x4 (x7 ||| x2))) && (!(msub x2 (x7 ||| x4)))) && ((!(msub x7 (x4 ||| x3))) && (!(msub x4 (x7 ||| x3))))) && (((!(msub x3 (x7 ||| x4))) && (!(msub x5 (x7 ||| x0)))) && ((!(msub x7 (x5 ||| x1))) && (!(msub x5 (x7 ||| x1))))))) && (((((!(msub x7 (x5 ||| x2))) && (!(msub x5 (x7 ||| x2)))) && ((!(msub x7 (x5 ||| x3))) && (!(msub x5 (x7 ||| x3))))) && (((!(msub x7 (x5 ||| x4))) && (!(msub x5 (x7 ||| x4)))) && ((!(msub x7 (x6 ||| x0))) && (!(msub x6 (x7 ||| x0)))))) && ((((!(msub x7 (x6 ||| x1))) && (!(msub x6 (x7 ||| x1)))) && ((!(msub x6 (x7 ||| x2))) && (!(msub x7 (x6 ||| x3))))) && (((!(msub x6 (x7 ||| x3))) && (!(msub x7 (x6 ||| x4)))) && ((!(msub x6 (x7 ||| x4))) && (!(msub x7 (x6 ||| x5)))))))))

def runM7 (s x0 x1 x2 x3 x4 x5 x6 : Nat) : Bool :=
  (mopts s).any (fun x7 => ckt7 x0 x1 x2 x3 x4 x5 x6 x7 && runM8 (s ||| mid x7) x0 x1 x2 x3 x4 x5 x6 x7)

set_option maxHeartbeats 4000000 in
theorem passM7 (w : Fin 14 → Nat) (h : MModel w) : ckt7 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) = true := by
  simp only [ckt7, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨(h.2.1 7 5 (by decide)), ⟨(h.2.1 7 6 (by decide)), (h.2.2.1 7 1 (by decide) (by decide))⟩⟩, ⟨⟨(h.2.2.1 7 4 (by decide) (by decide)), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 0 0 (by decide) (by decide) (by decide)) : msub (w 7) (w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 7 7 (by decide) (by decide) (by decide)) : msub (w 0) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 1 1 (by decide) (by decide) (by decide)) : msub (w 7) (w 1) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 7 7 (by decide) (by decide) (by decide)) : msub (w 1) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 2 2 (by decide) (by decide) (by decide)) : msub (w 7) (w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 7 7 (by decide) (by decide) (by decide)) : msub (w 2) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 3 3 (by decide) (by decide) (by decide)) : msub (w 7) (w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 7 7 (by decide) (by decide) (by decide)) : msub (w 3) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 4 4 (by decide) (by decide) (by decide)) : msub (w 7) (w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 7 7 (by decide) (by decide) (by decide)) : msub (w 4) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 5 5 (by decide) (by decide) (by decide)) : msub (w 7) (w 5) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 7 7 (by decide) (by decide) (by decide)) : msub (w 5) (w 7) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 7 6 6 (by decide) (by decide) (by decide)) : msub (w 7) (w 6) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 7 7 (by decide) (by decide) (by decide)) : msub (w 6) (w 7) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 7 0 (by decide) (by decide) (by decide) : msub (w 1) (w 7 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 0 7 1 (by decide) (by decide) (by decide) : msub (w 0) (w 7 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 2 0 (by decide) (by decide) (by decide) : msub (w 7) (w 2 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 2 7 0 (by decide) (by decide) (by decide) : msub (w 2) (w 7 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 7 2 (by decide) (by decide) (by decide) : msub (w 0) (w 7 ||| w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 2 7 1 (by decide) (by decide) (by decide) : msub (w 2) (w 7 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 7 2 (by decide) (by decide) (by decide) : msub (w 1) (w 7 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 7 3 0 (by decide) (by decide) (by decide) : msub (w 7) (w 3 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 7 0 (by decide) (by decide) (by decide) : msub (w 3) (w 7 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 0 7 3 (by decide) (by decide) (by decide) : msub (w 0) (w 7 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 7 1 (by decide) (by decide) (by decide) : msub (w 3) (w 7 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 1 7 3 (by decide) (by decide) (by decide) : msub (w 1) (w 7 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 3 2 (by decide) (by decide) (by decide) : msub (w 7) (w 3 ||| w 2) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨(by simp only [(h.2.2.2 3 7 2 (by decide) (by decide) (by decide) : msub (w 3) (w 7 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 7 3 (by decide) (by decide) (by decide) : msub (w 2) (w 7 ||| w 3) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 4 7 0 (by decide) (by decide) (by decide) : msub (w 4) (w 7 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 7 4 (by decide) (by decide) (by decide) : msub (w 0) (w 7 ||| w 4) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 7 4 1 (by decide) (by decide) (by decide) : msub (w 7) (w 4 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 7 1 (by decide) (by decide) (by decide) : msub (w 4) (w 7 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 1 7 4 (by decide) (by decide) (by decide) : msub (w 1) (w 7 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 4 2 (by decide) (by decide) (by decide) : msub (w 7) (w 4 ||| w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 4 7 2 (by decide) (by decide) (by decide) : msub (w 4) (w 7 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 7 4 (by decide) (by decide) (by decide) : msub (w 2) (w 7 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 7 4 3 (by decide) (by decide) (by decide) : msub (w 7) (w 4 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 7 3 (by decide) (by decide) (by decide) : msub (w 4) (w 7 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 3 7 4 (by decide) (by decide) (by decide) : msub (w 3) (w 7 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 7 0 (by decide) (by decide) (by decide) : msub (w 5) (w 7 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 7 5 1 (by decide) (by decide) (by decide) : msub (w 7) (w 5 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 7 1 (by decide) (by decide) (by decide) : msub (w 5) (w 7 ||| w 1) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 7 5 2 (by decide) (by decide) (by decide) : msub (w 7) (w 5 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 7 2 (by decide) (by decide) (by decide) : msub (w 5) (w 7 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 7 5 3 (by decide) (by decide) (by decide) : msub (w 7) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 7 3 (by decide) (by decide) (by decide) : msub (w 5) (w 7 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 7 5 4 (by decide) (by decide) (by decide) : msub (w 7) (w 5 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 7 4 (by decide) (by decide) (by decide) : msub (w 5) (w 7 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 7 6 0 (by decide) (by decide) (by decide) : msub (w 7) (w 6 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 7 0 (by decide) (by decide) (by decide) : msub (w 6) (w 7 ||| w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 7 6 1 (by decide) (by decide) (by decide) : msub (w 7) (w 6 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 7 1 (by decide) (by decide) (by decide) : msub (w 6) (w 7 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 6 7 2 (by decide) (by decide) (by decide) : msub (w 6) (w 7 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 6 3 (by decide) (by decide) (by decide) : msub (w 7) (w 6 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 6 7 3 (by decide) (by decide) (by decide) : msub (w 6) (w 7 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 6 4 (by decide) (by decide) (by decide) : msub (w 7) (w 6 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 6 7 4 (by decide) (by decide) (by decide) : msub (w 6) (w 7 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 7 6 5 (by decide) (by decide) (by decide) : msub (w 7) (w 6 ||| w 5) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩

theorem goodM7 (w : Fin 14 → Nat) (h : MModel w) : runM7 (mseen w 7) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 7, h.1 7, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM7 w h, ?_⟩
  exact goodM8 w h

def ckt6 (x0 x1 x2 x3 x4 x5 x6 : Nat) : Bool :=
  ((((((mcross x6 x2) && ((msmall (mid x6 ||| mid x0)) && (msmall (mid x6 ||| mid x3)))) && ((!(msub x6 x0)) && ((!(msub x0 x6)) && (!(msub x6 x1))))) && (((!(msub x1 x6)) && ((!(msub x6 x2)) && (!(msub x2 x6)))) && ((!(msub x6 x3)) && ((!(msub x3 x6)) && (!(msub x6 x4)))))) && ((((!(msub x4 x6)) && ((!(msub x6 x5)) && (!(msub x5 x6)))) && ((!(msub x1 (x6 ||| x0))) && ((!(msub x0 (x6 ||| x1))) && (!(msub x6 (x2 ||| x0)))))) && (((!(msub x2 (x6 ||| x0))) && ((!(msub x2 (x6 ||| x1))) && (!(msub x6 (x3 ||| x0))))) && (((!(msub x3 (x6 ||| x0))) && (!(msub x0 (x6 ||| x3)))) && ((!(msub x3 (x6 ||| x1))) && (!(msub x1 (x6 ||| x3)))))))) && (((((!(msub x6 (x3 ||| x2))) && ((!(msub x2 (x6 ||| x3))) && (!(msub x4 (x6 ||| x0))))) && ((!(msub x0 (x6 ||| x4))) && ((!(msub x6 (x4 ||| x1))) && (!(msub x4 (x6 ||| x1)))))) && (((!(msub x1 (x6 ||| x4))) && ((!(msub x6 (x4 ||| x2))) && (!(msub x2 (x6 ||| x4))))) && ((!(msub x6 (x4 ||| x3))) && ((!(msub x4 (x6 ||| x3))) && (!(msub x3 (x6 ||| x4))))))) && ((((!(msub x5 (x6 ||| x0))) && ((!(msub x0 (x6 ||| x5))) && (!(msub x6 (x5 ||| x1))))) && ((!(msub x5 (x6 ||| x1))) && ((!(msub x1 (x6 ||| x5))) && (!(msub x6 (x5 ||| x2)))))) && (((!(msub x2 (x6 ||| x5))) && ((!(msub x6 (x5 ||| x3))) && (!(msub x5 (x6 ||| x3))))) && (((!(msub x3 (x6 ||| x5))) && (!(msub x6 (x5 ||| x4)))) && ((!(msub x5 (x6 ||| x4))) && (!(msub x4 (x6 ||| x5)))))))))

def runM6 (s x0 x1 x2 x3 x4 x5 : Nat) : Bool :=
  (mopts s).any (fun x6 => ckt6 x0 x1 x2 x3 x4 x5 x6 && runM7 (s ||| mid x6) x0 x1 x2 x3 x4 x5 x6)

set_option maxHeartbeats 4000000 in
theorem passM6 (w : Fin 14 → Nat) (h : MModel w) : ckt6 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) = true := by
  simp only [ckt6, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨(h.2.1 6 2 (by decide)), ⟨(h.2.2.1 6 0 (by decide) (by decide)), (h.2.2.1 6 3 (by decide) (by decide))⟩⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 0 0 (by decide) (by decide) (by decide)) : msub (w 6) (w 0) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 6 6 (by decide) (by decide) (by decide)) : msub (w 0) (w 6) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 1 1 (by decide) (by decide) (by decide)) : msub (w 6) (w 1) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 6 6 (by decide) (by decide) (by decide)) : msub (w 1) (w 6) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 2 2 (by decide) (by decide) (by decide)) : msub (w 6) (w 2) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 6 6 (by decide) (by decide) (by decide)) : msub (w 2) (w 6) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 3 3 (by decide) (by decide) (by decide)) : msub (w 6) (w 3) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 6 6 (by decide) (by decide) (by decide)) : msub (w 3) (w 6) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 4 4 (by decide) (by decide) (by decide)) : msub (w 6) (w 4) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 6 6 (by decide) (by decide) (by decide)) : msub (w 4) (w 6) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 6 5 5 (by decide) (by decide) (by decide)) : msub (w 6) (w 5) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 6 6 (by decide) (by decide) (by decide)) : msub (w 5) (w 6) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 1 6 0 (by decide) (by decide) (by decide) : msub (w 1) (w 6 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 0 6 1 (by decide) (by decide) (by decide) : msub (w 0) (w 6 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 2 0 (by decide) (by decide) (by decide) : msub (w 6) (w 2 ||| w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 2 6 0 (by decide) (by decide) (by decide) : msub (w 2) (w 6 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 2 6 1 (by decide) (by decide) (by decide) : msub (w 2) (w 6 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 3 0 (by decide) (by decide) (by decide) : msub (w 6) (w 3 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 3 6 0 (by decide) (by decide) (by decide) : msub (w 3) (w 6 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 6 3 (by decide) (by decide) (by decide) : msub (w 0) (w 6 ||| w 3) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 3 6 1 (by decide) (by decide) (by decide) : msub (w 3) (w 6 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 6 3 (by decide) (by decide) (by decide) : msub (w 1) (w 6 ||| w 3) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 6 3 2 (by decide) (by decide) (by decide) : msub (w 6) (w 3 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 2 6 3 (by decide) (by decide) (by decide) : msub (w 2) (w 6 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 6 0 (by decide) (by decide) (by decide) : msub (w 4) (w 6 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 0 6 4 (by decide) (by decide) (by decide) : msub (w 0) (w 6 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 4 1 (by decide) (by decide) (by decide) : msub (w 6) (w 4 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 6 1 (by decide) (by decide) (by decide) : msub (w 4) (w 6 ||| w 1) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 1 6 4 (by decide) (by decide) (by decide) : msub (w 1) (w 6 ||| w 4) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 4 2 (by decide) (by decide) (by decide) : msub (w 6) (w 4 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 6 4 (by decide) (by decide) (by decide) : msub (w 2) (w 6 ||| w 4) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 6 4 3 (by decide) (by decide) (by decide) : msub (w 6) (w 4 ||| w 3) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 4 6 3 (by decide) (by decide) (by decide) : msub (w 4) (w 6 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 6 4 (by decide) (by decide) (by decide) : msub (w 3) (w 6 ||| w 4) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 5 6 0 (by decide) (by decide) (by decide) : msub (w 5) (w 6 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 0 6 5 (by decide) (by decide) (by decide) : msub (w 0) (w 6 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 5 1 (by decide) (by decide) (by decide) : msub (w 6) (w 5 ||| w 1) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 5 6 1 (by decide) (by decide) (by decide) : msub (w 5) (w 6 ||| w 1) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 1 6 5 (by decide) (by decide) (by decide) : msub (w 1) (w 6 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 5 2 (by decide) (by decide) (by decide) : msub (w 6) (w 5 ||| w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 2 6 5 (by decide) (by decide) (by decide) : msub (w 2) (w 6 ||| w 5) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 6 5 3 (by decide) (by decide) (by decide) : msub (w 6) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 6 3 (by decide) (by decide) (by decide) : msub (w 5) (w 6 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 3 6 5 (by decide) (by decide) (by decide) : msub (w 3) (w 6 ||| w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 6 5 4 (by decide) (by decide) (by decide) : msub (w 6) (w 5 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 6 4 (by decide) (by decide) (by decide) : msub (w 5) (w 6 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 6 5 (by decide) (by decide) (by decide) : msub (w 4) (w 6 ||| w 5) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩

theorem goodM6 (w : Fin 14 → Nat) (h : MModel w) : runM6 (mseen w 6) (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 6, h.1 6, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM6 w h, ?_⟩
  exact goodM7 w h

def ckt5 (x0 x1 x2 x3 x4 x5 : Nat) : Bool :=
  ((((((mcross x5 x0) && (msmall (mid x5 ||| mid x2))) && ((msmall (mid x5 ||| mid x3)) && (!(msub x5 x0)))) && (((!(msub x0 x5)) && (!(msub x5 x1))) && ((!(msub x1 x5)) && (!(msub x5 x2))))) && ((((!(msub x2 x5)) && (!(msub x5 x3))) && ((!(msub x3 x5)) && (!(msub x5 x4)))) && (((!(msub x4 x5)) && (!(msub x0 (x5 ||| x1)))) && ((!(msub x5 (x2 ||| x0))) && ((!(msub x0 (x5 ||| x2))) && (!(msub x2 (x5 ||| x1)))))))) && (((((!(msub x1 (x5 ||| x2))) && (!(msub x5 (x3 ||| x0)))) && ((!(msub x0 (x5 ||| x3))) && (!(msub x3 (x5 ||| x1))))) && (((!(msub x1 (x5 ||| x3))) && (!(msub x5 (x3 ||| x2)))) && ((!(msub x3 (x5 ||| x2))) && ((!(msub x2 (x5 ||| x3))) && (!(msub x0 (x5 ||| x4))))))) && ((((!(msub x5 (x4 ||| x1))) && (!(msub x4 (x5 ||| x1)))) && ((!(msub x1 (x5 ||| x4))) && (!(msub x5 (x4 ||| x2))))) && (((!(msub x4 (x5 ||| x2))) && (!(msub x2 (x5 ||| x4)))) && ((!(msub x5 (x4 ||| x3))) && ((!(msub x4 (x5 ||| x3))) && (!(msub x3 (x5 ||| x4)))))))))

def runM5 (s x0 x1 x2 x3 x4 : Nat) : Bool :=
  (mopts s).any (fun x5 => ckt5 x0 x1 x2 x3 x4 x5 && runM6 (s ||| mid x5) x0 x1 x2 x3 x4 x5)

set_option maxHeartbeats 4000000 in
theorem passM5 (w : Fin 14 → Nat) (h : MModel w) : ckt5 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) = true := by
  simp only [ckt5, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨(h.2.1 5 0 (by decide)), (h.2.2.1 5 2 (by decide) (by decide))⟩, ⟨(h.2.2.1 5 3 (by decide) (by decide)), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 0 0 (by decide) (by decide) (by decide)) : msub (w 5) (w 0) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 5 5 (by decide) (by decide) (by decide)) : msub (w 0) (w 5) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 1 1 (by decide) (by decide) (by decide)) : msub (w 5) (w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 5 5 (by decide) (by decide) (by decide)) : msub (w 1) (w 5) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 2 2 (by decide) (by decide) (by decide)) : msub (w 5) (w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 5 5 (by decide) (by decide) (by decide)) : msub (w 2) (w 5) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 3 3 (by decide) (by decide) (by decide)) : msub (w 5) (w 3) = false), Bool.not_false])⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 5 5 (by decide) (by decide) (by decide)) : msub (w 3) (w 5) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 5 4 4 (by decide) (by decide) (by decide)) : msub (w 5) (w 4) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 5 5 (by decide) (by decide) (by decide)) : msub (w 4) (w 5) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 5 1 (by decide) (by decide) (by decide) : msub (w 0) (w 5 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 2 0 (by decide) (by decide) (by decide) : msub (w 5) (w 2 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 0 5 2 (by decide) (by decide) (by decide) : msub (w 0) (w 5 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 5 1 (by decide) (by decide) (by decide) : msub (w 2) (w 5 ||| w 1) = false), Bool.not_false])⟩⟩⟩⟩⟩, ⟨⟨⟨⟨(by simp only [(h.2.2.2 1 5 2 (by decide) (by decide) (by decide) : msub (w 1) (w 5 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 3 0 (by decide) (by decide) (by decide) : msub (w 5) (w 3 ||| w 0) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 0 5 3 (by decide) (by decide) (by decide) : msub (w 0) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 5 1 (by decide) (by decide) (by decide) : msub (w 3) (w 5 ||| w 1) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 1 5 3 (by decide) (by decide) (by decide) : msub (w 1) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 3 2 (by decide) (by decide) (by decide) : msub (w 5) (w 3 ||| w 2) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 3 5 2 (by decide) (by decide) (by decide) : msub (w 3) (w 5 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 2 5 3 (by decide) (by decide) (by decide) : msub (w 2) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 5 4 (by decide) (by decide) (by decide) : msub (w 0) (w 5 ||| w 4) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 5 4 1 (by decide) (by decide) (by decide) : msub (w 5) (w 4 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 5 1 (by decide) (by decide) (by decide) : msub (w 4) (w 5 ||| w 1) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 1 5 4 (by decide) (by decide) (by decide) : msub (w 1) (w 5 ||| w 4) = false), Bool.not_false]), (by simp only [(h.2.2.2 5 4 2 (by decide) (by decide) (by decide) : msub (w 5) (w 4 ||| w 2) = false), Bool.not_false])⟩⟩, ⟨⟨(by simp only [(h.2.2.2 4 5 2 (by decide) (by decide) (by decide) : msub (w 4) (w 5 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 5 4 (by decide) (by decide) (by decide) : msub (w 2) (w 5 ||| w 4) = false), Bool.not_false])⟩, ⟨(by simp only [(h.2.2.2 5 4 3 (by decide) (by decide) (by decide) : msub (w 5) (w 4 ||| w 3) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 4 5 3 (by decide) (by decide) (by decide) : msub (w 4) (w 5 ||| w 3) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 5 4 (by decide) (by decide) (by decide) : msub (w 3) (w 5 ||| w 4) = false), Bool.not_false])⟩⟩⟩⟩⟩⟩

theorem goodM5 (w : Fin 14 → Nat) (h : MModel w) : runM5 (mseen w 5) (w 0) (w 1) (w 2) (w 3) (w 4) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 5, h.1 5, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM5 w h, ?_⟩
  exact goodM6 w h

def ckt4 (x0 x1 x2 x3 x4 : Nat) : Bool :=
  (((((mcross x4 x0) && (msmall (mid x4 ||| mid x2))) && ((msmall (mid x4 ||| mid x3)) && ((!(msub x4 x0)) && (!(msub x0 x4))))) && (((!(msub x4 x1)) && ((!(msub x1 x4)) && (!(msub x4 x2)))) && ((!(msub x2 x4)) && ((!(msub x4 x3)) && (!(msub x3 x4)))))) && ((((!(msub x0 (x4 ||| x1))) && ((!(msub x4 (x2 ||| x0))) && (!(msub x0 (x4 ||| x2))))) && ((!(msub x2 (x4 ||| x1))) && ((!(msub x1 (x4 ||| x2))) && (!(msub x4 (x3 ||| x0)))))) && (((!(msub x0 (x4 ||| x3))) && ((!(msub x3 (x4 ||| x1))) && (!(msub x1 (x4 ||| x3))))) && ((!(msub x4 (x3 ||| x2))) && ((!(msub x3 (x4 ||| x2))) && (!(msub x2 (x4 ||| x3))))))))

def runM4 (s x0 x1 x2 x3 : Nat) : Bool :=
  (mopts s).any (fun x4 => ckt4 x0 x1 x2 x3 x4 && runM5 (s ||| mid x4) x0 x1 x2 x3 x4)

set_option maxHeartbeats 4000000 in
theorem passM4 (w : Fin 14 → Nat) (h : MModel w) : ckt4 (w 0) (w 1) (w 2) (w 3) (w 4) = true := by
  simp only [ckt4, Bool.and_eq_true]
  exact ⟨⟨⟨⟨(h.2.1 4 0 (by decide)), (h.2.2.1 4 2 (by decide) (by decide))⟩, ⟨(h.2.2.1 4 3 (by decide) (by decide)), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 0 0 (by decide) (by decide) (by decide)) : msub (w 4) (w 0) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 4 4 (by decide) (by decide) (by decide)) : msub (w 0) (w 4) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 1 1 (by decide) (by decide) (by decide)) : msub (w 4) (w 1) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 4 4 (by decide) (by decide) (by decide)) : msub (w 1) (w 4) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 2 2 (by decide) (by decide) (by decide)) : msub (w 4) (w 2) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 4 4 (by decide) (by decide) (by decide)) : msub (w 2) (w 4) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 4 3 3 (by decide) (by decide) (by decide)) : msub (w 4) (w 3) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 4 4 (by decide) (by decide) (by decide)) : msub (w 3) (w 4) = false), Bool.not_false])⟩⟩⟩⟩, ⟨⟨⟨(by simp only [(h.2.2.2 0 4 1 (by decide) (by decide) (by decide) : msub (w 0) (w 4 ||| w 1) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 4 2 0 (by decide) (by decide) (by decide) : msub (w 4) (w 2 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 0 4 2 (by decide) (by decide) (by decide) : msub (w 0) (w 4 ||| w 2) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 2 4 1 (by decide) (by decide) (by decide) : msub (w 2) (w 4 ||| w 1) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 1 4 2 (by decide) (by decide) (by decide) : msub (w 1) (w 4 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 4 3 0 (by decide) (by decide) (by decide) : msub (w 4) (w 3 ||| w 0) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(h.2.2.2 0 4 3 (by decide) (by decide) (by decide) : msub (w 0) (w 4 ||| w 3) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 3 4 1 (by decide) (by decide) (by decide) : msub (w 3) (w 4 ||| w 1) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 4 3 (by decide) (by decide) (by decide) : msub (w 1) (w 4 ||| w 3) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 4 3 2 (by decide) (by decide) (by decide) : msub (w 4) (w 3 ||| w 2) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 3 4 2 (by decide) (by decide) (by decide) : msub (w 3) (w 4 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 2 4 3 (by decide) (by decide) (by decide) : msub (w 2) (w 4 ||| w 3) = false), Bool.not_false])⟩⟩⟩⟩⟩

theorem goodM4 (w : Fin 14 → Nat) (h : MModel w) : runM4 (mseen w 4) (w 0) (w 1) (w 2) (w 3) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 4, h.1 4, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM4 w h, ?_⟩
  exact goodM5 w h

def ckt3 (x0 x1 x2 x3 : Nat) : Bool :=
  ((((mcross x3 x1) && ((!(msub x3 x0)) && (!(msub x0 x3)))) && ((!(msub x3 x1)) && ((!(msub x1 x3)) && (!(msub x3 x2))))) && (((!(msub x2 x3)) && ((!(msub x1 (x3 ||| x0))) && (!(msub x3 (x2 ||| x0))))) && ((!(msub x2 (x3 ||| x0))) && ((!(msub x0 (x3 ||| x2))) && (!(msub x1 (x3 ||| x2)))))))

def runM3 (s x0 x1 x2 : Nat) : Bool :=
  (mopts s).any (fun x3 => ckt3 x0 x1 x2 x3 && runM4 (s ||| mid x3) x0 x1 x2 x3)

set_option maxHeartbeats 4000000 in
theorem passM3 (w : Fin 14 → Nat) (h : MModel w) : ckt3 (w 0) (w 1) (w 2) (w 3) = true := by
  simp only [ckt3, Bool.and_eq_true]
  exact ⟨⟨⟨(h.2.1 3 1 (by decide)), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 0 0 (by decide) (by decide) (by decide)) : msub (w 3) (w 0) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 3 3 (by decide) (by decide) (by decide)) : msub (w 0) (w 3) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 1 1 (by decide) (by decide) (by decide)) : msub (w 3) (w 1) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 3 3 (by decide) (by decide) (by decide)) : msub (w 1) (w 3) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 3 2 2 (by decide) (by decide) (by decide)) : msub (w 3) (w 2) = false), Bool.not_false])⟩⟩⟩, ⟨⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 3 3 (by decide) (by decide) (by decide)) : msub (w 2) (w 3) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 1 3 0 (by decide) (by decide) (by decide) : msub (w 1) (w 3 ||| w 0) = false), Bool.not_false]), (by simp only [(h.2.2.2 3 2 0 (by decide) (by decide) (by decide) : msub (w 3) (w 2 ||| w 0) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(h.2.2.2 2 3 0 (by decide) (by decide) (by decide) : msub (w 2) (w 3 ||| w 0) = false), Bool.not_false]), ⟨(by simp only [(h.2.2.2 0 3 2 (by decide) (by decide) (by decide) : msub (w 0) (w 3 ||| w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 3 2 (by decide) (by decide) (by decide) : msub (w 1) (w 3 ||| w 2) = false), Bool.not_false])⟩⟩⟩⟩

theorem goodM3 (w : Fin 14 → Nat) (h : MModel w) : runM3 (mseen w 3) (w 0) (w 1) (w 2) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 3, h.1 3, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM3 w h, ?_⟩
  exact goodM4 w h

def ckt2 (x0 x1 x2 : Nat) : Bool :=
  (((mcross x2 x1) && ((!(msub x2 x0)) && (!(msub x0 x2)))) && ((!(msub x2 x1)) && ((!(msub x1 x2)) && (!(msub x1 (x2 ||| x0))))))

def runM2 (s x0 x1 : Nat) : Bool :=
  (mopts s).any (fun x2 => ckt2 x0 x1 x2 && runM3 (s ||| mid x2) x0 x1 x2)

set_option maxHeartbeats 4000000 in
theorem passM2 (w : Fin 14 → Nat) (h : MModel w) : ckt2 (w 0) (w 1) (w 2) = true := by
  simp only [ckt2, Bool.and_eq_true]
  exact ⟨⟨(h.2.1 2 1 (by decide)), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 0 0 (by decide) (by decide) (by decide)) : msub (w 2) (w 0) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 2 2 (by decide) (by decide) (by decide)) : msub (w 0) (w 2) = false), Bool.not_false])⟩⟩, ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 2 1 1 (by decide) (by decide) (by decide)) : msub (w 2) (w 1) = false), Bool.not_false]), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 2 2 (by decide) (by decide) (by decide)) : msub (w 1) (w 2) = false), Bool.not_false]), (by simp only [(h.2.2.2 1 2 0 (by decide) (by decide) (by decide) : msub (w 1) (w 2 ||| w 0) = false), Bool.not_false])⟩⟩⟩

theorem goodM2 (w : Fin 14 → Nat) (h : MModel w) : runM2 (mseen w 2) (w 0) (w 1) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 2, h.1 2, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM2 w h, ?_⟩
  exact goodM3 w h

def ckt1 (x0 x1 : Nat) : Bool :=
  ((mcross x1 x0) && ((!(msub x1 x0)) && (!(msub x0 x1))))

def runM1 (s x0 : Nat) : Bool :=
  (mopts s).any (fun x1 => ckt1 x0 x1 && runM2 (s ||| mid x1) x0 x1)

set_option maxHeartbeats 4000000 in
theorem passM1 (w : Fin 14 → Nat) (h : MModel w) : ckt1 (w 0) (w 1) = true := by
  simp only [ckt1, Bool.and_eq_true]
  exact ⟨(h.2.1 1 0 (by decide)), ⟨(by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 1 0 0 (by decide) (by decide) (by decide)) : msub (w 1) (w 0) = false), Bool.not_false]), (by simp only [(by simpa only [Nat.or_self] using (h.2.2.2 0 1 1 (by decide) (by decide) (by decide)) : msub (w 0) (w 1) = false), Bool.not_false])⟩⟩

theorem goodM1 (w : Fin 14 → Nat) (h : MModel w) : runM1 (mseen w 1) (w 0) = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 1, h.1 1, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM1 w h, ?_⟩
  exact goodM2 w h

def ckt0 (x0 : Nat) : Bool :=
  true

def runM0 (s  : Nat) : Bool :=
  (mopts s).any (fun x0 => ckt0 x0 && runM1 (s ||| mid x0) x0)

set_option maxHeartbeats 4000000 in
theorem passM0 (w : Fin 14 → Nat) (h : MModel w) : ckt0 (w 0) = true := by
  rfl

theorem goodM0 (w : Fin 14 → Nat) (h : MModel w) : runM0 (mseen w 0)  = true := by
  apply List.any_eq_true.mpr
  refine ⟨w 0, h.1 0, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨passM0 w h, ?_⟩
  exact goodM1 w h
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_144_1152 : runM6 31 3 192 6 10 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_144_640 : runM6 31 3 192 6 10 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_144_384 : runM6 31 3 192 6 10 144 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_144_160 : runM6 63 3 192 6 10 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_80_1088 : runM6 31 3 192 5 9 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_80_576 : runM6 31 3 192 5 9 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_80_320 : runM6 31 3 192 5 9 80 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_80_96 : runM6 63 3 192 5 9 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_144_1152 : runM6 31 3 132 258 10 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_144_640 : runM6 31 3 132 258 10 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_144_192 : runM6 31 3 132 258 10 144 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_144_160 : runM6 63 3 132 258 10 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_144_66 : runM6 31 3 132 258 10 144 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_144_64 : runM6 31 3 132 258 10 144 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_10_144_1152 : runM6 31 3 132 66 10 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_10_144_640 : runM6 31 3 132 66 10 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_10_144_384 : runM6 31 3 132 66 10 144 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_10_144_160 : runM6 63 3 132 66 10 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_144_1152 : runM6 31 3 132 10 514 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_144_384 : runM6 31 3 132 10 514 144 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_144_192 : runM6 31 3 132 10 514 144 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_144_160 : runM6 63 3 132 10 514 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_144_66 : runM6 31 3 132 10 514 144 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_144_64 : runM6 31 3 132 10 514 144 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_144_1152 : runM6 31 3 132 10 384 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_144_640 : runM6 31 3 132 10 384 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_144_192 : runM6 31 3 132 10 384 144 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_144_160 : runM6 63 3 132 10 384 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_144_66 : runM6 31 3 132 10 384 144 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_144_64 : runM6 31 3 132 10 384 144 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_144_1152 : runM6 31 3 132 10 258 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_144_640 : runM6 31 3 132 10 258 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_144_192 : runM6 31 3 132 10 258 144 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_144_160 : runM6 63 3 132 10 258 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_144_66 : runM6 31 3 132 10 258 144 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_144_64 : runM6 31 3 132 10 258 144 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_1152 : runM6 31 3 132 10 256 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_640 : runM6 31 3 132 10 256 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_576 : runM6 31 3 132 10 256 144 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_192 : runM6 31 3 132 10 256 144 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_160 : runM6 63 3 132 10 256 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_72 : runM6 31 3 132 10 256 144 72 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_66 : runM6 31 3 132 10 256 144 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_144_64 : runM6 31 3 132 10 256 144 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_66_144_1152 : runM6 31 3 132 10 66 144 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_66_144_640 : runM6 31 3 132 10 66 144 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_66_144_384 : runM6 31 3 132 10 66 144 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_66_144_160 : runM6 63 3 132 10 66 144 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_1152_640 : runM6 31 3 132 10 18 1152 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_1152_384 : runM6 31 3 132 10 18 1152 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_1152_192 : runM6 31 3 132 10 18 1152 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_1152_160 : runM6 63 3 132 10 18 1152 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_1152_66 : runM6 31 3 132 10 18 1152 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_1152_64 : runM6 31 3 132 10 18 1152 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_640_1152 : runM6 31 3 132 10 18 640 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_640_384 : runM6 31 3 132 10 18 640 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_640_192 : runM6 31 3 132 10 18 640 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_640_160 : runM6 63 3 132 10 18 640 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_640_66 : runM6 31 3 132 10 18 640 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_640_64 : runM6 31 3 132 10 18 640 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_384_1152 : runM6 31 3 132 10 18 384 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_384_640 : runM6 31 3 132 10 18 384 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_384_192 : runM6 31 3 132 10 18 384 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_384_160 : runM6 63 3 132 10 18 384 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_384_66 : runM6 31 3 132 10 18 384 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_384_64 : runM6 31 3 132 10 18 384 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_192_1152 : runM6 31 3 132 10 18 192 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_192_640 : runM6 31 3 132 10 18 192 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_192_384 : runM6 31 3 132 10 18 192 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_192_160 : runM6 63 3 132 10 18 192 160 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_2176 : runM6 63 3 132 10 18 160 2176 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_1152 : runM6 63 3 132 10 18 160 1152 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_640 : runM6 63 3 132 10 18 160 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_384 : runM6 63 3 132 10 18 160 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_192 : runM6 63 3 132 10 18 160 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_66 : runM6 63 3 132 10 18 160 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_160_64 : runM6 63 3 132 10 18 160 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_80_1088 : runM6 31 3 68 257 9 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_80_576 : runM6 31 3 68 257 9 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_80_192 : runM6 31 3 68 257 9 80 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_80_129 : runM6 31 3 68 257 9 80 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_80_128 : runM6 31 3 68 257 9 80 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_80_96 : runM6 63 3 68 257 9 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_9_80_1088 : runM6 31 3 68 129 9 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_9_80_576 : runM6 31 3 68 129 9 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_9_80_320 : runM6 31 3 68 129 9 80 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_9_80_96 : runM6 63 3 68 129 9 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_80_1088 : runM6 31 3 68 9 513 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_80_320 : runM6 31 3 68 9 513 80 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_80_192 : runM6 31 3 68 9 513 80 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_80_129 : runM6 31 3 68 9 513 80 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_80_128 : runM6 31 3 68 9 513 80 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_80_96 : runM6 63 3 68 9 513 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_80_1088 : runM6 31 3 68 9 320 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_80_576 : runM6 31 3 68 9 320 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_80_192 : runM6 31 3 68 9 320 80 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_80_129 : runM6 31 3 68 9 320 80 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_80_128 : runM6 31 3 68 9 320 80 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_80_96 : runM6 63 3 68 9 320 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_80_1088 : runM6 31 3 68 9 257 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_80_576 : runM6 31 3 68 9 257 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_80_192 : runM6 31 3 68 9 257 80 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_80_129 : runM6 31 3 68 9 257 80 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_80_128 : runM6 31 3 68 9 257 80 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_80_96 : runM6 63 3 68 9 257 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_1088 : runM6 31 3 68 9 256 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_640 : runM6 31 3 68 9 256 80 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_576 : runM6 31 3 68 9 256 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_192 : runM6 31 3 68 9 256 80 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_136 : runM6 31 3 68 9 256 80 136 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_129 : runM6 31 3 68 9 256 80 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_128 : runM6 31 3 68 9 256 80 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_80_96 : runM6 63 3 68 9 256 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_129_80_1088 : runM6 31 3 68 9 129 80 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_129_80_576 : runM6 31 3 68 9 129 80 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_129_80_320 : runM6 31 3 68 9 129 80 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_129_80_96 : runM6 63 3 68 9 129 80 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_1088_576 : runM6 31 3 68 9 17 1088 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_1088_320 : runM6 31 3 68 9 17 1088 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_1088_192 : runM6 31 3 68 9 17 1088 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_1088_129 : runM6 31 3 68 9 17 1088 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_1088_128 : runM6 31 3 68 9 17 1088 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_1088_96 : runM6 63 3 68 9 17 1088 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_576_1088 : runM6 31 3 68 9 17 576 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_576_320 : runM6 31 3 68 9 17 576 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_576_192 : runM6 31 3 68 9 17 576 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_576_129 : runM6 31 3 68 9 17 576 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_576_128 : runM6 31 3 68 9 17 576 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_576_96 : runM6 63 3 68 9 17 576 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_320_1088 : runM6 31 3 68 9 17 320 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_320_576 : runM6 31 3 68 9 17 320 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_320_192 : runM6 31 3 68 9 17 320 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_320_129 : runM6 31 3 68 9 17 320 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_320_128 : runM6 31 3 68 9 17 320 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_320_96 : runM6 63 3 68 9 17 320 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_192_1088 : runM6 31 3 68 9 17 192 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_192_576 : runM6 31 3 68 9 17 192 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_192_320 : runM6 31 3 68 9 17 192 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_192_96 : runM6 63 3 68 9 17 192 96 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_2112 : runM6 63 3 68 9 17 96 2112 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_1088 : runM6 63 3 68 9 17 96 1088 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_576 : runM6 63 3 68 9 17 96 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_320 : runM6 63 3 68 9 17 96 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_192 : runM6 63 3 68 9 17 96 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_129 : runM6 63 3 68 9 17 96 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_96_128 : runM6 63 3 68 9 17 96 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_640 : runM5 15 3 192 6 10 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_384 : runM5 15 3 192 6 10 384 = false := by decide +kernel

theorem cutsq_3_192_6_10_144 : (mopts 31).all (fun w => !(ckt5 3 192 6 10 144 w) || w ∈ ([160, 384, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_192_6_10_144 : runM5 31 3 192 6 10 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 192 6 10 144 w && runM6 (31 ||| mid w) 3 192 6 10 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192_6_10_144 w hw
  change (!(ckt5 3 192 6 10 144 w) || decide (w ∈ ([160, 384, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([160, 384, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_6_10_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_10_144_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_10_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_10_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_10_66 : runM5 15 3 192 6 10 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_576 : runM5 15 3 192 5 9 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_320 : runM5 15 3 192 5 9 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_9_129 : runM5 15 3 192 5 9 129 = false := by decide +kernel

theorem cutsq_3_192_5_9_80 : (mopts 31).all (fun w => !(ckt5 3 192 5 9 80 w) || w ∈ ([96, 320, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_192_5_9_80 : runM5 31 3 192 5 9 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 192 5 9 80 w && runM6 (31 ||| mid w) 3 192 5 9 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192_5_9_80 w hw
  change (!(ckt5 3 192 5 9 80 w) || decide (w ∈ ([96, 320, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 320, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_5_9_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_9_80_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_9_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_9_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_640 : runM5 15 3 132 258 10 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_192 : runM5 15 3 132 258 10 192 = false := by decide +kernel

theorem cutsq_3_132_258_10_144 : (mopts 31).all (fun w => !(ckt5 3 132 258 10 144 w) || w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_258_10_144 : runM5 31 3 132 258 10 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 258 10 144 w && runM6 (31 ||| mid w) 3 132 258 10 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_258_10_144 w hw
  change (!(ckt5 3 132 258 10 144 w) || decide (w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_258_10_144_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_144_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_144_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_66 : runM5 15 3 132 258 10 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_10_64 : runM5 15 3 132 258 10 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_10_640 : runM5 15 3 132 66 10 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_10_384 : runM5 15 3 132 66 10 384 = false := by decide +kernel

theorem cutsq_3_132_66_10_144 : (mopts 31).all (fun w => !(ckt5 3 132 66 10 144 w) || w ∈ ([160, 384, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_66_10_144 : runM5 31 3 132 66 10 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 66 10 144 w && runM6 (31 ||| mid w) 3 132 66 10 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_66_10_144 w hw
  change (!(ckt5 3 132 66 10 144 w) || decide (w ∈ ([160, 384, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([160, 384, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_66_10_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_10_144_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_10_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_10_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_384 : runM5 15 3 132 10 514 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_192 : runM5 15 3 132 10 514 192 = false := by decide +kernel

theorem cutsq_3_132_10_514_144 : (mopts 31).all (fun w => !(ckt5 3 132 10 514 144 w) || w ∈ ([64, 66, 160, 192, 384, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_514_144 : runM5 31 3 132 10 514 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 514 144 w && runM6 (31 ||| mid w) 3 132 10 514 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_514_144 w hw
  change (!(ckt5 3 132 10 514 144 w) || decide (w ∈ ([64, 66, 160, 192, 384, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 384, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_514_144_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_144_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_144_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_144_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_66 : runM5 15 3 132 10 514 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_514_64 : runM5 15 3 132 10 514 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_640 : runM5 15 3 132 10 384 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_192 : runM5 15 3 132 10 384 192 = false := by decide +kernel

theorem cutsq_3_132_10_384_144 : (mopts 31).all (fun w => !(ckt5 3 132 10 384 144 w) || w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_384_144 : runM5 31 3 132 10 384 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 384 144 w && runM6 (31 ||| mid w) 3 132 10 384 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_384_144 w hw
  change (!(ckt5 3 132 10 384 144 w) || decide (w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_384_144_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_144_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_144_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_66 : runM5 15 3 132 10 384 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_384_64 : runM5 15 3 132 10 384 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_640 : runM5 15 3 132 10 258 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_192 : runM5 15 3 132 10 258 192 = false := by decide +kernel

theorem cutsq_3_132_10_258_144 : (mopts 31).all (fun w => !(ckt5 3 132 10 258 144 w) || w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_258_144 : runM5 31 3 132 10 258 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 258 144 w && runM6 (31 ||| mid w) 3 132 10 258 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_258_144 w hw
  change (!(ckt5 3 132 10 258 144 w) || decide (w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_258_144_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_144_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_144_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_66 : runM5 15 3 132 10 258 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_258_64 : runM5 15 3 132 10 258 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_640 : runM5 15 3 132 10 256 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_576 : runM5 15 3 132 10 256 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_192 : runM5 15 3 132 10 256 192 = false := by decide +kernel

theorem cutsq_3_132_10_256_144 : (mopts 31).all (fun w => !(ckt5 3 132 10 256 144 w) || w ∈ ([64, 66, 72, 160, 192, 576, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_256_144 : runM5 31 3 132 10 256 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 256 144 w && runM6 (31 ||| mid w) 3 132 10 256 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_256_144 w hw
  change (!(ckt5 3 132 10 256 144 w) || decide (w ∈ ([64, 66, 72, 160, 192, 576, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 72, 160, 192, 576, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_256_144_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_72.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_136 : runM5 15 3 132 10 256 136 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_72 : runM5 15 3 132 10 256 72 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_66 : runM5 15 3 132 10 256 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_256_64 : runM5 15 3 132 10 256 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_66_640 : runM5 15 3 132 10 66 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_66_384 : runM5 15 3 132 10 66 384 = false := by decide +kernel

theorem cutsq_3_132_10_66_144 : (mopts 31).all (fun w => !(ckt5 3 132 10 66 144 w) || w ∈ ([160, 384, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_66_144 : runM5 31 3 132 10 66 144 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 66 144 w && runM6 (31 ||| mid w) 3 132 10 66 144 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_66_144 w hw
  change (!(ckt5 3 132 10 66 144 w) || decide (w ∈ ([160, 384, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([160, 384, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_66_144_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_66_144_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_66_144_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_66_144_1152.symm.trans hnext.2)

theorem cutsq_3_132_10_18_1152 : (mopts 31).all (fun w => !(ckt5 3 132 10 18 1152 w) || w ∈ ([64, 66, 160, 192, 384, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_18_1152 : runM5 31 3 132 10 18 1152 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 18 1152 w && runM6 (31 ||| mid w) 3 132 10 18 1152 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_18_1152 w hw
  change (!(ckt5 3 132 10 18 1152 w) || decide (w ∈ ([64, 66, 160, 192, 384, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 384, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_18_1152_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_1152_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_1152_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_1152_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_1152_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_1152_640.symm.trans hnext.2)

theorem cutsq_3_132_10_18_640 : (mopts 31).all (fun w => !(ckt5 3 132 10 18 640 w) || w ∈ ([64, 66, 160, 192, 384, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_18_640 : runM5 31 3 132 10 18 640 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 18 640 w && runM6 (31 ||| mid w) 3 132 10 18 640 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_18_640 w hw
  change (!(ckt5 3 132 10 18 640 w) || decide (w ∈ ([64, 66, 160, 192, 384, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 384, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_18_640_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_640_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_640_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_640_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_640_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_640_1152.symm.trans hnext.2)

theorem cutsq_3_132_10_18_384 : (mopts 31).all (fun w => !(ckt5 3 132 10 18 384 w) || w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_18_384 : runM5 31 3 132 10 18 384 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 18 384 w && runM6 (31 ||| mid w) 3 132 10 18 384 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_18_384 w hw
  change (!(ckt5 3 132 10 18 384 w) || decide (w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_18_384_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_384_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_384_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_384_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_384_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_384_1152.symm.trans hnext.2)

theorem cutsq_3_132_10_18_192 : (mopts 31).all (fun w => !(ckt5 3 132 10 18 192 w) || w ∈ ([160, 384, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_18_192 : runM5 31 3 132 10 18 192 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 18 192 w && runM6 (31 ||| mid w) 3 132 10 18 192 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_18_192 w hw
  change (!(ckt5 3 132 10 18 192 w) || decide (w ∈ ([160, 384, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([160, 384, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_18_192_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_192_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_192_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_192_1152.symm.trans hnext.2)

theorem cutsq_3_132_10_18_160 : (mopts 63).all (fun w => !(ckt5 3 132 10 18 160 w) || w ∈ ([64, 66, 192, 384, 640, 1152, 2176] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_18_160 : runM5 63 3 132 10 18 160 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 132 10 18 160 w && runM6 (63 ||| mid w) 3 132 10 18 160 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_18_160 w hw
  change (!(ckt5 3 132 10 18 160 w) || decide (w ∈ ([64, 66, 192, 384, 640, 1152, 2176] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 192, 384, 640, 1152, 2176] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_18_160_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160_1152.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160_2176.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_66 : runM5 31 3 132 10 18 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_18_64 : runM5 31 3 132 10 18 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_576 : runM5 15 3 68 257 9 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_192 : runM5 15 3 68 257 9 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_129 : runM5 15 3 68 257 9 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_9_128 : runM5 15 3 68 257 9 128 = false := by decide +kernel

theorem cutsq_3_68_257_9_80 : (mopts 31).all (fun w => !(ckt5 3 68 257 9 80 w) || w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_257_9_80 : runM5 31 3 68 257 9 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 257 9 80 w && runM6 (31 ||| mid w) 3 68 257 9 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_257_9_80 w hw
  change (!(ckt5 3 68 257 9 80 w) || decide (w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_257_9_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_80_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_80_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_80_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_9_576 : runM5 15 3 68 129 9 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_9_320 : runM5 15 3 68 129 9 320 = false := by decide +kernel

theorem cutsq_3_68_129_9_80 : (mopts 31).all (fun w => !(ckt5 3 68 129 9 80 w) || w ∈ ([96, 320, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_129_9_80 : runM5 31 3 68 129 9 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 129 9 80 w && runM6 (31 ||| mid w) 3 68 129 9 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_129_9_80 w hw
  change (!(ckt5 3 68 129 9 80 w) || decide (w ∈ ([96, 320, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 320, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_129_9_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_9_80_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_9_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_9_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_320 : runM5 15 3 68 9 513 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_192 : runM5 15 3 68 9 513 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_129 : runM5 15 3 68 9 513 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_513_128 : runM5 15 3 68 9 513 128 = false := by decide +kernel

theorem cutsq_3_68_9_513_80 : (mopts 31).all (fun w => !(ckt5 3 68 9 513 80 w) || w ∈ ([96, 128, 129, 192, 320, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_513_80 : runM5 31 3 68 9 513 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 513 80 w && runM6 (31 ||| mid w) 3 68 9 513 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_513_80 w hw
  change (!(ckt5 3 68 9 513 80 w) || decide (w ∈ ([96, 128, 129, 192, 320, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 320, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_513_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_80_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_80_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_80_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_80_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_576 : runM5 15 3 68 9 320 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_192 : runM5 15 3 68 9 320 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_129 : runM5 15 3 68 9 320 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_320_128 : runM5 15 3 68 9 320 128 = false := by decide +kernel

theorem cutsq_3_68_9_320_80 : (mopts 31).all (fun w => !(ckt5 3 68 9 320 80 w) || w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_320_80 : runM5 31 3 68 9 320 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 320 80 w && runM6 (31 ||| mid w) 3 68 9 320 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_320_80 w hw
  change (!(ckt5 3 68 9 320 80 w) || decide (w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_320_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_80_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_80_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_80_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_576 : runM5 15 3 68 9 257 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_192 : runM5 15 3 68 9 257 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_129 : runM5 15 3 68 9 257 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_257_128 : runM5 15 3 68 9 257 128 = false := by decide +kernel

theorem cutsq_3_68_9_257_80 : (mopts 31).all (fun w => !(ckt5 3 68 9 257 80 w) || w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_257_80 : runM5 31 3 68 9 257 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 257 80 w && runM6 (31 ||| mid w) 3 68 9 257 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_257_80 w hw
  change (!(ckt5 3 68 9 257 80 w) || decide (w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_257_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_80_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_80_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_80_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_640 : runM5 15 3 68 9 256 640 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_576 : runM5 15 3 68 9 256 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_192 : runM5 15 3 68 9 256 192 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_136 : runM5 15 3 68 9 256 136 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_129 : runM5 15 3 68 9 256 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_128 : runM5 15 3 68 9 256 128 = false := by decide +kernel

theorem cutsq_3_68_9_256_80 : (mopts 31).all (fun w => !(ckt5 3 68 9 256 80 w) || w ∈ ([96, 128, 129, 136, 192, 576, 640, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_256_80 : runM5 31 3 68 9 256 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 256 80 w && runM6 (31 ||| mid w) 3 68 9 256 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_256_80 w hw
  change (!(ckt5 3 68 9 256 80 w) || decide (w ∈ ([96, 128, 129, 136, 192, 576, 640, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 136, 192, 576, 640, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_256_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_136.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_256_72 : runM5 15 3 68 9 256 72 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_129_576 : runM5 15 3 68 9 129 576 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_129_320 : runM5 15 3 68 9 129 320 = false := by decide +kernel

theorem cutsq_3_68_9_129_80 : (mopts 31).all (fun w => !(ckt5 3 68 9 129 80 w) || w ∈ ([96, 320, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_129_80 : runM5 31 3 68 9 129 80 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 129 80 w && runM6 (31 ||| mid w) 3 68 9 129 80 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_129_80 w hw
  change (!(ckt5 3 68 9 129 80 w) || decide (w ∈ ([96, 320, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 320, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_129_80_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_129_80_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_129_80_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_129_80_1088.symm.trans hnext.2)

theorem cutsq_3_68_9_17_1088 : (mopts 31).all (fun w => !(ckt5 3 68 9 17 1088 w) || w ∈ ([96, 128, 129, 192, 320, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_17_1088 : runM5 31 3 68 9 17 1088 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 17 1088 w && runM6 (31 ||| mid w) 3 68 9 17 1088 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_17_1088 w hw
  change (!(ckt5 3 68 9 17 1088 w) || decide (w ∈ ([96, 128, 129, 192, 320, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 320, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_17_1088_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_1088_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_1088_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_1088_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_1088_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_1088_576.symm.trans hnext.2)

theorem cutsq_3_68_9_17_576 : (mopts 31).all (fun w => !(ckt5 3 68 9 17 576 w) || w ∈ ([96, 128, 129, 192, 320, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_17_576 : runM5 31 3 68 9 17 576 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 17 576 w && runM6 (31 ||| mid w) 3 68 9 17 576 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_17_576 w hw
  change (!(ckt5 3 68 9 17 576 w) || decide (w ∈ ([96, 128, 129, 192, 320, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 320, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_17_576_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_576_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_576_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_576_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_576_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_576_1088.symm.trans hnext.2)

theorem cutsq_3_68_9_17_320 : (mopts 31).all (fun w => !(ckt5 3 68 9 17 320 w) || w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_17_320 : runM5 31 3 68 9 17 320 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 17 320 w && runM6 (31 ||| mid w) 3 68 9 17 320 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_17_320 w hw
  change (!(ckt5 3 68 9 17 320 w) || decide (w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_17_320_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_320_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_320_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_320_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_320_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_320_1088.symm.trans hnext.2)

theorem cutsq_3_68_9_17_192 : (mopts 31).all (fun w => !(ckt5 3 68 9 17 192 w) || w ∈ ([96, 320, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_17_192 : runM5 31 3 68 9 17 192 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 17 192 w && runM6 (31 ||| mid w) 3 68 9 17 192 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_17_192 w hw
  change (!(ckt5 3 68 9 17 192 w) || decide (w ∈ ([96, 320, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 320, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_17_192_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_192_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_192_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_192_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_129 : runM5 31 3 68 9 17 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_17_128 : runM5 31 3 68 9 17 128 = false := by decide +kernel

theorem cutsq_3_68_9_17_96 : (mopts 63).all (fun w => !(ckt5 3 68 9 17 96 w) || w ∈ ([128, 129, 192, 320, 576, 1088, 2112] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_17_96 : runM5 63 3 68 9 17 96 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt5 3 68 9 17 96 w && runM6 (63 ||| mid w) 3 68 9 17 96 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_17_96 w hw
  change (!(ckt5 3 68 9 17 96 w) || decide (w ∈ ([128, 129, 192, 320, 576, 1088, 2112] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([128, 129, 192, 320, 576, 1088, 2112] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_17_96_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_96_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_96_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_96_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_96_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_96_1088.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_96_2112.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_258 : runM4 7 3 192 6 258 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_6_66 : runM4 7 3 192 6 66 = false := by decide +kernel

theorem cutsq_3_192_6_10 : (mopts 15).all (fun w => !(ckt4 3 192 6 10 w) || w ∈ ([66, 144, 384, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_192_6_10 : runM4 15 3 192 6 10 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 192 6 10 w && runM5 (15 ||| mid w) 3 192 6 10 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192_6_10 w hw
  change (!(ckt4 3 192 6 10 w) || decide (w ∈ ([66, 144, 384, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([66, 144, 384, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_6_10_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_10_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_10_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_10_640.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_257 : runM4 7 3 192 5 257 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_5_129 : runM4 7 3 192 5 129 = false := by decide +kernel

theorem cutsq_3_192_5_9 : (mopts 15).all (fun w => !(ckt4 3 192 5 9 w) || w ∈ ([80, 129, 320, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_192_5_9 : runM4 15 3 192 5 9 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 192 5 9 w && runM5 (15 ||| mid w) 3 192 5 9 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192_5_9 w hw
  change (!(ckt4 3 192 5 9 w) || decide (w ∈ ([80, 129, 320, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 129, 320, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_5_9_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_9_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_9_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_9_576.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_384_320 : runM4 7 3 132 384 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_384_264 : runM4 15 3 132 384 264 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_384_66 : runM4 7 3 132 384 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_384_10 : runM4 15 3 132 384 10 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_66 : runM4 7 3 132 258 66 = false := by decide +kernel

theorem cutsq_3_132_258_10 : (mopts 15).all (fun w => !(ckt4 3 132 258 10 w) || w ∈ ([64, 66, 144, 192, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_258_10 : runM4 15 3 132 258 10 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 258 10 w && runM5 (15 ||| mid w) 3 132 258 10 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_258_10 w hw
  change (!(ckt4 3 132 258 10 w) || decide (w ∈ ([64, 66, 144, 192, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 144, 192, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_258_10_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10_640.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_258_6 : runM4 7 3 132 258 6 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_384 : runM4 7 3 132 66 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_264 : runM4 15 3 132 66 264 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_258 : runM4 7 3 132 66 258 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_256 : runM4 7 3 132 66 256 = false := by decide +kernel

theorem cutsq_3_132_66_10 : (mopts 15).all (fun w => !(ckt4 3 132 66 10 w) || w ∈ ([144, 384, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_66_10 : runM4 15 3 132 66 10 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 66 10 w && runM5 (15 ||| mid w) 3 132 66 10 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_66_10 w hw
  change (!(ckt4 3 132 66 10 w) || decide (w ∈ ([144, 384, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([144, 384, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_66_10_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_10_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_10_640.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_66_6 : runM4 7 3 132 66 6 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_768 : runM4 15 3 132 10 768 = false := by decide +kernel

theorem cutsq_3_132_10_514 : (mopts 15).all (fun w => !(ckt4 3 132 10 514 w) || w ∈ ([64, 66, 144, 192, 384] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_514 : runM4 15 3 132 10 514 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 10 514 w && runM5 (15 ||| mid w) 3 132 10 514 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_514 w hw
  change (!(ckt4 3 132 10 514 w) || decide (w ∈ ([64, 66, 144, 192, 384] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 144, 192, 384] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_514_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514_384.symm.trans hnext.2)

theorem cutsq_3_132_10_384 : (mopts 15).all (fun w => !(ckt4 3 132 10 384 w) || w ∈ ([64, 66, 144, 192, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_384 : runM4 15 3 132 10 384 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 10 384 w && runM5 (15 ||| mid w) 3 132 10 384 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_384 w hw
  change (!(ckt4 3 132 10 384 w) || decide (w ∈ ([64, 66, 144, 192, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 144, 192, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_384_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384_640.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_320 : runM4 15 3 132 10 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_272 : runM4 31 3 132 10 272 = false := by decide +kernel

theorem cutsq_3_132_10_258 : (mopts 15).all (fun w => !(ckt4 3 132 10 258 w) || w ∈ ([64, 66, 144, 192, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_258 : runM4 15 3 132 10 258 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 10 258 w && runM5 (15 ||| mid w) 3 132 10 258 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_258 w hw
  change (!(ckt4 3 132 10 258 w) || decide (w ∈ ([64, 66, 144, 192, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 144, 192, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_258_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258_640.symm.trans hnext.2)

theorem cutsq_3_132_10_256 : (mopts 15).all (fun w => !(ckt4 3 132 10 256 w) || w ∈ ([64, 66, 72, 136, 144, 192, 576, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_256 : runM4 15 3 132 10 256 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 10 256 w && runM5 (15 ||| mid w) 3 132 10 256 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_256 w hw
  change (!(ckt4 3 132 10 256 w) || decide (w ∈ ([64, 66, 72, 136, 144, 192, 576, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 72, 136, 144, 192, 576, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_256_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_72.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_136.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256_640.symm.trans hnext.2)

theorem cutsq_3_132_10_66 : (mopts 15).all (fun w => !(ckt4 3 132 10 66 w) || w ∈ ([144, 384, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_66 : runM4 15 3 132 10 66 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 10 66 w && runM5 (15 ||| mid w) 3 132 10 66 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_66 w hw
  change (!(ckt4 3 132 10 66 w) || decide (w ∈ ([144, 384, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([144, 384, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_66_144.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_66_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_66_640.symm.trans hnext.2)

theorem cutsq_3_132_10_18 : (mopts 31).all (fun w => !(ckt4 3 132 10 18 w) || w ∈ ([64, 66, 160, 192, 384, 640, 1152] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10_18 : runM4 31 3 132 10 18 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 132 10 18 w && runM5 (31 ||| mid w) 3 132 10 18 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10_18 w hw
  change (!(ckt4 3 132 10 18 w) || decide (w ∈ ([64, 66, 160, 192, 384, 640, 1152] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 160, 192, 384, 640, 1152] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_18_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_160.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_640.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18_1152.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_10_6 : runM4 15 3 132 10 6 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_68_320 : runM4 7 3 129 68 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_68_258 : runM4 7 3 129 68 258 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_68_72 : runM4 15 3 129 68 72 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_68_10 : runM4 15 3 129 68 10 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_320_384 : runM4 7 3 68 320 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_320_264 : runM4 15 3 68 320 264 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_320_129 : runM4 7 3 68 320 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_320_9 : runM4 15 3 68 320 9 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_129 : runM4 7 3 68 257 129 = false := by decide +kernel

theorem cutsq_3_68_257_9 : (mopts 15).all (fun w => !(ckt4 3 68 257 9 w) || w ∈ ([80, 128, 129, 192, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_68_257_9 : runM4 15 3 68 257 9 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 257 9 w && runM5 (15 ||| mid w) 3 68 257 9 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_257_9 w hw
  change (!(ckt4 3 68 257 9 w) || decide (w ∈ ([80, 128, 129, 192, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 128, 129, 192, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_257_9_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9_576.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_257_5 : runM4 7 3 68 257 5 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_320 : runM4 7 3 68 129 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_264 : runM4 15 3 68 129 264 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_257 : runM4 7 3 68 129 257 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_256 : runM4 7 3 68 129 256 = false := by decide +kernel

theorem cutsq_3_68_129_9 : (mopts 15).all (fun w => !(ckt4 3 68 129 9 w) || w ∈ ([80, 320, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_68_129_9 : runM4 15 3 68 129 9 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 129 9 w && runM5 (15 ||| mid w) 3 68 129 9 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_129_9 w hw
  change (!(ckt4 3 68 129 9 w) || decide (w ∈ ([80, 320, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 320, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_129_9_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_9_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_9_576.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_129_5 : runM4 7 3 68 129 5 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_768 : runM4 15 3 68 9 768 = false := by decide +kernel

theorem cutsq_3_68_9_513 : (mopts 15).all (fun w => !(ckt4 3 68 9 513 w) || w ∈ ([80, 128, 129, 192, 320] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_513 : runM4 15 3 68 9 513 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 9 513 w && runM5 (15 ||| mid w) 3 68 9 513 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_513 w hw
  change (!(ckt4 3 68 9 513 w) || decide (w ∈ ([80, 128, 129, 192, 320] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 128, 129, 192, 320] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_513_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513_320.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_384 : runM4 15 3 68 9 384 = false := by decide +kernel

theorem cutsq_3_68_9_320 : (mopts 15).all (fun w => !(ckt4 3 68 9 320 w) || w ∈ ([80, 128, 129, 192, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_320 : runM4 15 3 68 9 320 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 9 320 w && runM5 (15 ||| mid w) 3 68 9 320 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_320 w hw
  change (!(ckt4 3 68 9 320 w) || decide (w ∈ ([80, 128, 129, 192, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 128, 129, 192, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_320_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320_576.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_272 : runM4 31 3 68 9 272 = false := by decide +kernel

theorem cutsq_3_68_9_257 : (mopts 15).all (fun w => !(ckt4 3 68 9 257 w) || w ∈ ([80, 128, 129, 192, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_257 : runM4 15 3 68 9 257 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 9 257 w && runM5 (15 ||| mid w) 3 68 9 257 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_257 w hw
  change (!(ckt4 3 68 9 257 w) || decide (w ∈ ([80, 128, 129, 192, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 128, 129, 192, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_257_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257_576.symm.trans hnext.2)

theorem cutsq_3_68_9_256 : (mopts 15).all (fun w => !(ckt4 3 68 9 256 w) || w ∈ ([72, 80, 128, 129, 136, 192, 576, 640] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_256 : runM4 15 3 68 9 256 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 9 256 w && runM5 (15 ||| mid w) 3 68 9 256 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_256 w hw
  change (!(ckt4 3 68 9 256 w) || decide (w ∈ ([72, 80, 128, 129, 136, 192, 576, 640] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([72, 80, 128, 129, 136, 192, 576, 640] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_256_72.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_136.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256_640.symm.trans hnext.2)

theorem cutsq_3_68_9_129 : (mopts 15).all (fun w => !(ckt4 3 68 9 129 w) || w ∈ ([80, 320, 576] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_129 : runM4 15 3 68 9 129 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 9 129 w && runM5 (15 ||| mid w) 3 68 9 129 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_129 w hw
  change (!(ckt4 3 68 9 129 w) || decide (w ∈ ([80, 320, 576] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([80, 320, 576] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_129_80.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_129_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_129_576.symm.trans hnext.2)

theorem cutsq_3_68_9_17 : (mopts 31).all (fun w => !(ckt4 3 68 9 17 w) || w ∈ ([96, 128, 129, 192, 320, 576, 1088] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9_17 : runM4 31 3 68 9 17 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt4 3 68 9 17 w && runM5 (31 ||| mid w) 3 68 9 17 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9_17 w hw
  change (!(ckt4 3 68 9 17 w) || decide (w ∈ ([96, 128, 129, 192, 320, 576, 1088] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([96, 128, 129, 192, 320, 576, 1088] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_17_96.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_192.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_576.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17_1088.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_9_5 : runM4 15 3 68 9 5 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_132_384 : runM4 7 3 66 132 384 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_132_257 : runM4 7 3 66 132 257 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_132_136 : runM4 15 3 66 132 136 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_132_9 : runM4 15 3 66 132 9 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_129 : runM3 3 3 192 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_192_66 : runM3 3 3 192 66 = false := by decide +kernel

theorem cutsq_3_192_6 : (mopts 7).all (fun w => !(ckt3 3 192 6 w) || w ∈ ([10, 66, 258] : List Nat)) = true := by decide +kernel
theorem sq_3_192_6 : runM3 7 3 192 6 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 192 6 w && runM4 (7 ||| mid w) 3 192 6 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192_6 w hw
  change (!(ckt3 3 192 6 w) || decide (w ∈ ([10, 66, 258] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([10, 66, 258] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_6_10.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6_258.symm.trans hnext.2)

theorem cutsq_3_192_5 : (mopts 7).all (fun w => !(ckt3 3 192 5 w) || w ∈ ([9, 129, 257] : List Nat)) = true := by decide +kernel
theorem sq_3_192_5 : runM3 7 3 192 5 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 192 5 w && runM4 (7 ||| mid w) 3 192 5 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192_5 w hw
  change (!(ckt3 3 192 5 w) || decide (w ∈ ([9, 129, 257] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([9, 129, 257] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_5_9.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_5_257.symm.trans hnext.2)

theorem cutsq_3_132_384 : (mopts 7).all (fun w => !(ckt3 3 132 384 w) || w ∈ ([10, 66, 264, 320] : List Nat)) = true := by decide +kernel
theorem sq_3_132_384 : runM3 7 3 132 384 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 132 384 w && runM4 (7 ||| mid w) 3 132 384 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_384 w hw
  change (!(ckt3 3 132 384 w) || decide (w ∈ ([10, 66, 264, 320] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([10, 66, 264, 320] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_384_10.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_384_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_384_264.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_384_320.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_320 : runM3 7 3 132 320 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_264 : runM3 15 3 132 264 = false := by decide +kernel

theorem cutsq_3_132_258 : (mopts 7).all (fun w => !(ckt3 3 132 258 w) || w ∈ ([6, 10, 66] : List Nat)) = true := by decide +kernel
theorem sq_3_132_258 : runM3 7 3 132 258 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 132 258 w && runM4 (7 ||| mid w) 3 132 258 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_258 w hw
  change (!(ckt3 3 132 258 w) || decide (w ∈ ([6, 10, 66] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([6, 10, 66] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_258_6.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_10.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258_66.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_257 : runM3 7 3 132 257 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_256 : runM3 7 3 132 256 = false := by decide +kernel

theorem cutsq_3_132_66 : (mopts 7).all (fun w => !(ckt3 3 132 66 w) || w ∈ ([6, 10, 256, 258, 264, 384] : List Nat)) = true := by decide +kernel
theorem sq_3_132_66 : runM3 7 3 132 66 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 132 66 w && runM4 (7 ||| mid w) 3 132 66 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_66 w hw
  change (!(ckt3 3 132 66 w) || decide (w ∈ ([6, 10, 256, 258, 264, 384] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([6, 10, 256, 258, 264, 384] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_66_6.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_10.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_256.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_258.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_264.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66_384.symm.trans hnext.2)

theorem cutsq_3_132_10 : (mopts 15).all (fun w => !(ckt3 3 132 10 w) || w ∈ ([6, 18, 66, 256, 258, 272, 320, 384, 514, 768] : List Nat)) = true := by decide +kernel
theorem sq_3_132_10 : runM3 15 3 132 10 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 132 10 w && runM4 (15 ||| mid w) 3 132 10 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132_10 w hw
  change (!(ckt3 3 132 10 w) || decide (w ∈ ([6, 18, 66, 256, 258, 272, 320, 384, 514, 768] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([6, 18, 66, 256, 258, 272, 320, 384, 514, 768] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_10_6.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_18.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_256.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_258.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_272.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_514.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10_768.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_132_6 : runM3 7 3 132 6 = false := by decide +kernel

theorem cutsq_3_129_68 : (mopts 7).all (fun w => !(ckt3 3 129 68 w) || w ∈ ([10, 72, 258, 320] : List Nat)) = true := by decide +kernel
theorem sq_3_129_68 : runM3 7 3 129 68 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 129 68 w && runM4 (7 ||| mid w) 3 129 68 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_129_68 w hw
  change (!(ckt3 3 129 68 w) || decide (w ∈ ([10, 72, 258, 320] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([10, 72, 258, 320] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_129_68_10.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129_68_72.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129_68_258.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129_68_320.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_66 : runM3 3 3 129 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_64 : runM3 3 3 129 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_129_6 : runM3 7 3 129 6 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_384 : runM3 7 3 68 384 = false := by decide +kernel

theorem cutsq_3_68_320 : (mopts 7).all (fun w => !(ckt3 3 68 320 w) || w ∈ ([9, 129, 264, 384] : List Nat)) = true := by decide +kernel
theorem sq_3_68_320 : runM3 7 3 68 320 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 68 320 w && runM4 (7 ||| mid w) 3 68 320 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_320 w hw
  change (!(ckt3 3 68 320 w) || decide (w ∈ ([9, 129, 264, 384] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([9, 129, 264, 384] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_320_9.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_320_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_320_264.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_320_384.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_264 : runM3 15 3 68 264 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_258 : runM3 7 3 68 258 = false := by decide +kernel

theorem cutsq_3_68_257 : (mopts 7).all (fun w => !(ckt3 3 68 257 w) || w ∈ ([5, 9, 129] : List Nat)) = true := by decide +kernel
theorem sq_3_68_257 : runM3 7 3 68 257 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 68 257 w && runM4 (7 ||| mid w) 3 68 257 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_257 w hw
  change (!(ckt3 3 68 257 w) || decide (w ∈ ([5, 9, 129] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([5, 9, 129] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_257_5.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_9.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257_129.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_256 : runM3 7 3 68 256 = false := by decide +kernel

theorem cutsq_3_68_129 : (mopts 7).all (fun w => !(ckt3 3 68 129 w) || w ∈ ([5, 9, 256, 257, 264, 320] : List Nat)) = true := by decide +kernel
theorem sq_3_68_129 : runM3 7 3 68 129 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 68 129 w && runM4 (7 ||| mid w) 3 68 129 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_129 w hw
  change (!(ckt3 3 68 129 w) || decide (w ∈ ([5, 9, 256, 257, 264, 320] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([5, 9, 256, 257, 264, 320] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_129_5.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_9.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_256.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_257.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_264.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129_320.symm.trans hnext.2)

theorem cutsq_3_68_9 : (mopts 15).all (fun w => !(ckt3 3 68 9 w) || w ∈ ([5, 17, 129, 256, 257, 272, 320, 384, 513, 768] : List Nat)) = true := by decide +kernel
theorem sq_3_68_9 : runM3 15 3 68 9 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 68 9 w && runM4 (15 ||| mid w) 3 68 9 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68_9 w hw
  change (!(ckt3 3 68 9 w) || decide (w ∈ ([5, 17, 129, 256, 257, 272, 320, 384, 513, 768] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([5, 17, 129, 256, 257, 272, 320, 384, 513, 768] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_9_5.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_17.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_256.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_257.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_272.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_384.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_513.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9_768.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_68_5 : runM3 7 3 68 5 = false := by decide +kernel

theorem cutsq_3_66_132 : (mopts 7).all (fun w => !(ckt3 3 66 132 w) || w ∈ ([9, 136, 257, 384] : List Nat)) = true := by decide +kernel
theorem sq_3_66_132 : runM3 7 3 66 132 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt3 3 66 132 w && runM4 (7 ||| mid w) 3 66 132 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_66_132 w hw
  change (!(ckt3 3 66 132 w) || decide (w ∈ ([9, 136, 257, 384] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([9, 136, 257, 384] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_66_132_9.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66_132_136.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66_132_257.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66_132_384.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_129 : runM3 3 3 66 129 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_128 : runM3 3 3 66 128 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_66_5 : runM3 7 3 66 5 = false := by decide +kernel

theorem cutsq_3_192 : (mopts 3).all (fun w => !(ckt2 3 192 w) || w ∈ ([5, 6, 66, 129] : List Nat)) = true := by decide +kernel
theorem sq_3_192 : runM2 3 3 192 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt2 3 192 w && runM3 (3 ||| mid w) 3 192 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_192 w hw
  change (!(ckt2 3 192 w) || decide (w ∈ ([5, 6, 66, 129] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([5, 6, 66, 129] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_192_5.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_6.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192_129.symm.trans hnext.2)

theorem cutsq_3_132 : (mopts 7).all (fun w => !(ckt2 3 132 w) || w ∈ ([6, 10, 66, 256, 257, 258, 264, 320, 384] : List Nat)) = true := by decide +kernel
theorem sq_3_132 : runM2 7 3 132 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt2 3 132 w && runM3 (7 ||| mid w) 3 132 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_132 w hw
  change (!(ckt2 3 132 w) || decide (w ∈ ([6, 10, 66, 256, 257, 258, 264, 320, 384] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([6, 10, 66, 256, 257, 258, 264, 320, 384] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_132_6.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_10.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_256.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_257.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_258.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_264.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132_384.symm.trans hnext.2)

theorem cutsq_3_129 : (mopts 3).all (fun w => !(ckt2 3 129 w) || w ∈ ([6, 64, 66, 68] : List Nat)) = true := by decide +kernel
theorem sq_3_129 : runM2 3 3 129 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt2 3 129 w && runM3 (3 ||| mid w) 3 129 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_129 w hw
  change (!(ckt2 3 129 w) || decide (w ∈ ([6, 64, 66, 68] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([6, 64, 66, 68] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_129_6.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129_68.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_128 : runM2 3 3 128 = false := by decide +kernel

theorem cutsq_3_68 : (mopts 7).all (fun w => !(ckt2 3 68 w) || w ∈ ([5, 9, 129, 256, 257, 258, 264, 320, 384] : List Nat)) = true := by decide +kernel
theorem sq_3_68 : runM2 7 3 68 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt2 3 68 w && runM3 (7 ||| mid w) 3 68 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_68 w hw
  change (!(ckt2 3 68 w) || decide (w ∈ ([5, 9, 129, 256, 257, 258, 264, 320, 384] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([5, 9, 129, 256, 257, 258, 264, 320, 384] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_68_5.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_9.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_256.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_257.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_258.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_264.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_320.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68_384.symm.trans hnext.2)

theorem cutsq_3_66 : (mopts 3).all (fun w => !(ckt2 3 66 w) || w ∈ ([5, 128, 129, 132] : List Nat)) = true := by decide +kernel
theorem sq_3_66 : runM2 3 3 66 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt2 3 66 w && runM3 (3 ||| mid w) 3 66 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3_66 w hw
  change (!(ckt2 3 66 w) || decide (w ∈ ([5, 128, 129, 132] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([5, 128, 129, 132] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_66_5.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66_132.symm.trans hnext.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_3_64 : runM2 3 3 64 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_1_66 : runM2 3 1 66 = false := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sq_1_64 : runM2 1 1 64 = false := by decide +kernel

theorem cutsq_3 : (mopts 3).all (fun w => !(ckt1 3 w) || w ∈ ([64, 66, 68, 128, 129, 132, 192] : List Nat)) = true := by decide +kernel
theorem sq_3 : runM1 3 3 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt1 3 w && runM2 (3 ||| mid w) 3 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_3 w hw
  change (!(ckt1 3 w) || decide (w ∈ ([64, 66, 68, 128, 129, 132, 192] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66, 68, 128, 129, 132, 192] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.noConfusion (sq_3_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_66.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_68.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_128.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_129.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_132.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3_192.symm.trans hnext.2)

theorem cutsq_1 : (mopts 1).all (fun w => !(ckt1 1 w) || w ∈ ([64, 66] : List Nat)) = true := by decide +kernel
theorem sq_1 : runM1 1 1 = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt1 1 w && runM2 (1 ||| mid w) 1 w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq_1 w hw
  change (!(ckt1 1 w) || decide (w ∈ ([64, 66] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([64, 66] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl
  · exact Bool.noConfusion (sq_1_64.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_1_66.symm.trans hnext.2)

theorem cutsq : (mopts 0).all (fun w => !(ckt0  w) || w ∈ ([1, 3] : List Nat)) = true := by decide +kernel
theorem emptyM : runM0 0  = false := by
  rw [← Bool.not_eq_true]
  intro bad
  obtain ⟨w, hw, hnext⟩ := List.any_eq_true.mp bad
  change (ckt0  w && runM1 (0 ||| mid w)  w) = true at hnext
  rw [Bool.and_eq_true] at hnext
  have hh := List.all_eq_true.mp cutsq w hw
  change (!(ckt0  w) || decide (w ∈ ([1, 3] : List Nat))) = true at hh
  rw [hnext.1] at hh
  have hwc : w ∈ ([1, 3] : List Nat) := of_decide_eq_true hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwc
  rcases hwc with rfl | rfl
  · exact Bool.noConfusion (sq_1.symm.trans hnext.2)
  · exact Bool.noConfusion (sq_3.symm.trans hnext.2)

theorem no_model : ∀ W : Fin 14 → Finset (Fin 6 × Bool), ¬ Model634 W := by
  intro W hW
  obtain ⟨w, hw⟩ := exists_mask W hW
  exact Bool.noConfusion (emptyM.symm.trans (goodM0 w hw))

end Gap634

theorem PEqualNP.Outside.L_meta_634 : ∀ G : SimpleGraph (Fin 14),
    G.edgeSet = {s(0, 7), s(1, 7), s(3, 7), s(1, 8), s(2, 8), s(4, 8), s(2, 9), s(3, 9), s(5, 9),
      s(3, 10), s(4, 10), s(6, 10), s(4, 11), s(5, 11), s(0, 11), s(5, 12), s(6, 12), s(1, 12),
      s(6, 13), s(0, 13), s(2, 13)} →
    (∃ C : PEqualNP.AndCount.AndCountCircuit 14, C.WellFormed ∧ C.Computes G ∧ C.size = 7) ∧
    ∀ C : PEqualNP.AndCount.AndCountCircuit 14, C.WellFormed → C.Computes G → ¬ C.size ≤ 6 :=
  fun G h => ⟨Gap634.upper G h, Gap634.lower_of_no_model Gap634.no_model G h⟩
