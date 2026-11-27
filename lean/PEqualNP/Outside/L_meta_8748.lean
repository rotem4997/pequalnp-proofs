import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8748

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def T {n : ℕ} (gs : List Gate) (i : ℕ) : Set (Fin n → Bool) :=
  {x | (W gs x).getD i false = true}

def Bs {n : ℕ} (L : List (Set (Fin n → Bool))) (s : Set (Fin n → Bool)) : Prop :=
  s ∈ L ∨ s = Set.univ ∨ ∃ i : Fin n, s = {x : Fin n → Bool | x i = true}

def InU {n : ℕ} (L : List (Set (Fin n → Bool))) (t : Set (Fin n → Bool)) : Prop :=
  ∃ A : Set (Set (Fin n → Bool)), (∀ s ∈ A, Bs L s) ∧ t = ⋃₀ A

def WF {n : ℕ} (L : List (Set (Fin n → Bool))) : Prop :=
  ∀ (k : ℕ) (t : Set (Fin n → Bool)), L[k]? = some t →
    ∃ A B : Set (Set (Fin n → Bool)), (∀ s ∈ A, Bs (L.take k) s) ∧
      (∀ s ∈ B, Bs (L.take k) s) ∧ t = ⋃₀ A ∩ ⋃₀ B

def S (gs : List Gate) : Set ℕ := {k | ∃ g : Gate, gs[k]? = some g ∧ g.op = GateOp.and}

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : (W gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.length_append, ih, List.length_append, List.length_singleton,
      List.length_singleton, Nat.add_assoc]

lemma getD_snoc_ne (l : List Bool) (v : Bool) (i : ℕ) (h : i ≠ l.length) :
    (l ++ [v]).getD i false = l.getD i false := by
  rcases Nat.lt_or_gt_of_ne h with h1 | h1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · have h2 : l.length + 1 ≤ i := h1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; exact h2),
      List.getElem?_eq_none (by omega)]

lemma getD_snoc_eq (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma T_snoc_ne {n : ℕ} (gs : List Gate) (g : Gate) (i : ℕ) (h : i ≠ n + gs.length) :
    (T (gs ++ [g]) i : Set (Fin n → Bool)) = T gs i := by
  ext x
  simp only [T, Set.mem_setOf_eq, W_snoc]
  rw [getD_snoc_ne _ _ _ (by rw [W_len]; exact h)]

lemma T_snoc_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    x ∈ T (gs ++ [g]) (n + gs.length) ↔
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) = true := by
  simp only [T, Set.mem_setOf_eq, W_snoc]
  have h := getD_snoc_eq (W gs x) (g.op.eval (g.inputs.map fun i => (W gs x).getD i false))
  rw [W_len] at h
  rw [h]

lemma InU_empty {n : ℕ} (L : List (Set (Fin n → Bool))) : InU L ∅ :=
  ⟨∅, by simp, by simp⟩

lemma InU_union {n : ℕ} {L : List (Set (Fin n → Bool))} {s t : Set (Fin n → Bool)}
    (hs : InU L s) (ht : InU L t) : InU L (s ∪ t) := by
  obtain ⟨A, hA, rfl⟩ := hs
  obtain ⟨B, hB, rfl⟩ := ht
  exact ⟨A ∪ B, fun s h => h.elim (hA s) (hB s), (Set.sUnion_union A B).symm⟩

lemma InU_mono {n : ℕ} {L L' : List (Set (Fin n → Bool))} (h : ∀ s ∈ L, s ∈ L')
    {t : Set (Fin n → Bool)} (ht : InU L t) : InU L' t := by
  obtain ⟨A, hA, e⟩ := ht
  exact ⟨A, fun s hs => (hA s hs).imp_left (h s), e⟩

lemma InU_mem {n : ℕ} {L : List (Set (Fin n → Bool))} {t : Set (Fin n → Bool)} (h : t ∈ L) :
    InU L t := by
  refine ⟨{t}, ?_, by simp⟩
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact Or.inl h

lemma lt_of_get {gs : List Gate} {k : ℕ} {g : Gate} (hg : gs[k]? = some g) : k < gs.length := by
  by_contra hc
  rw [not_lt] at hc
  rw [List.getElem?_eq_none hc] at hg
  exact absurd hg (by simp)

lemma S_finite (gs : List Gate) : (S gs).Finite := by
  apply (Set.finite_Iio gs.length).subset
  rintro k ⟨g, hg, _⟩
  exact lt_of_get hg

lemma S_sub (gs : List Gate) (g : Gate) : S gs ⊆ S (gs ++ [g]) := by
  rintro k ⟨g', hg, ho⟩
  exact ⟨g', by rw [List.getElem?_append_left (lt_of_get hg)]; exact hg, ho⟩

lemma S_card_or (gs : List Gate) (g : Gate) : (S gs).ncard ≤ (S (gs ++ [g])).ncard :=
  Set.ncard_le_ncard (S_sub gs g) (S_finite _)

lemma S_card_and (gs : List Gate) (g : Gate) (h : g.op = GateOp.and) :
    (S gs).ncard + 1 ≤ (S (gs ++ [g])).ncard := by
  have h1 : gs.length ∉ S gs := by
    rintro ⟨g', hg, _⟩
    exact absurd (lt_of_get hg) (lt_irrefl _)
  have h2 : insert gs.length (S gs) ⊆ S (gs ++ [g]) := by
    intro k hk
    rcases Set.mem_insert_iff.mp hk with hk | hk
    · subst hk
      exact ⟨g, by simp, h⟩
    · exact S_sub gs g hk
  rw [← Set.ncard_insert_of_notMem h1 (S_finite gs)]
  exact Set.ncard_le_ncard h2 (S_finite _)

lemma T_nil {n : ℕ} (L : List (Set (Fin n → Bool))) (i : ℕ) : InU L (T (n := n) [] i) := by
  by_cases h : i < n
  · refine ⟨{ {x : Fin n → Bool | x ⟨i, h⟩ = true} }, ?_, ?_⟩
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      exact Or.inr (Or.inr ⟨⟨i, h⟩, hs⟩)
    · rw [Set.sUnion_singleton]
      ext x
      simp [T, W, List.getD_eq_getElem?_getD, h]
  · have h0 : T (n := n) [] i = ∅ := by
      ext x
      simp [T, W, List.getD_eq_getElem?_getD, h]
    rw [h0]
    exact InU_empty L

lemma T_and0 {n : ℕ} (gs : List Gate) (g : Gate) (hop : g.op = GateOp.and)
    (hin : g.inputs = []) : (T (gs ++ [g]) (n + gs.length) : Set (Fin n → Bool)) = Set.univ := by
  ext x
  rw [T_snoc_eq, hop, hin]
  simp [GateOp.eval]

lemma T_and1 {n : ℕ} (gs : List Gate) (g : Gate) (a : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a]) : (T (gs ++ [g]) (n + gs.length) : Set (Fin n → Bool)) = T gs a := by
  ext x
  rw [T_snoc_eq, hop, hin]
  simp [GateOp.eval, T]

lemma T_and2 {n : ℕ} (gs : List Gate) (g : Gate) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) :
    (T (gs ++ [g]) (n + gs.length) : Set (Fin n → Bool)) = T gs a ∩ T gs b := by
  ext x
  rw [T_snoc_eq, hop, hin]
  simp [GateOp.eval, T]

lemma T_or0 {n : ℕ} (gs : List Gate) (g : Gate) (hop : g.op = GateOp.or)
    (hin : g.inputs = []) : (T (gs ++ [g]) (n + gs.length) : Set (Fin n → Bool)) = ∅ := by
  ext x
  rw [T_snoc_eq, hop, hin]
  simp [GateOp.eval]

lemma T_or1 {n : ℕ} (gs : List Gate) (g : Gate) (a : ℕ) (hop : g.op = GateOp.or)
    (hin : g.inputs = [a]) : (T (gs ++ [g]) (n + gs.length) : Set (Fin n → Bool)) = T gs a := by
  ext x
  rw [T_snoc_eq, hop, hin]
  simp [GateOp.eval, T]

lemma T_or2 {n : ℕ} (gs : List Gate) (g : Gate) (a b : ℕ) (hop : g.op = GateOp.or)
    (hin : g.inputs = [a, b]) :
    (T (gs ++ [g]) (n + gs.length) : Set (Fin n → Bool)) = T gs a ∪ T gs b := by
  ext x
  rw [T_snoc_eq, hop, hin]
  simp [GateOp.eval, T]

lemma main {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ L : List (Set (Fin n → Bool)), L.length ≤ (S gs).ncard ∧ WF L ∧ ∀ i, InU L (T gs i) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, ?_, fun i => T_nil _ i⟩
    intro k t h
    simp at h
  | append_singleton gs g ih =>
    obtain ⟨L, hL, hW, hT⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hm g (by simp)
    rcases hop with hop | hop
    · have key : ∃ A B : Set (Set (Fin n → Bool)), (∀ s ∈ A, Bs L s) ∧ (∀ s ∈ B, Bs L s) ∧
          T (gs ++ [g]) (n + gs.length) = ⋃₀ A ∩ ⋃₀ B := by
        rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · refine ⟨{Set.univ}, {Set.univ}, ?_, ?_, ?_⟩
          · intro s hs
            exact Or.inr (Or.inl hs)
          · intro s hs
            exact Or.inr (Or.inl hs)
          · rw [T_and0 gs g hop hin]
            simp
        · obtain ⟨A, hA, eA⟩ := hT a
          exact ⟨A, A, hA, hA, by rw [T_and1 gs g a hop hin, ← eA, Set.inter_self]⟩
        · obtain ⟨A, hA, eA⟩ := hT a
          obtain ⟨B, hB, eB⟩ := hT b
          exact ⟨A, B, hA, hB, by rw [T_and2 gs g a b hop hin, ← eA, ← eB]⟩
        · rw [hin] at hlen
          simp at hlen
      obtain ⟨A, B, hA, hB, hAB⟩ := key
      refine ⟨L ++ [T (gs ++ [g]) (n + gs.length)], ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        exact le_trans (Nat.add_le_add_right hL 1) (S_card_and gs g hop)
      · intro k t hk
        rcases Nat.lt_trichotomy k L.length with h | h | h
        · rw [List.getElem?_append_left h] at hk
          rw [List.take_append_of_le_length h.le]
          exact hW k t hk
        · subst h
          have ht : (L ++ [T (gs ++ [g]) (n + gs.length)]).take L.length = L := by simp
          have hk2 : T (gs ++ [g]) (n + gs.length) = t := by simpa using hk
          rw [ht, ← hk2]
          exact ⟨A, B, hA, hB, hAB⟩
        · rw [List.getElem?_eq_none
            (by rw [List.length_append, List.length_singleton]; omega)] at hk
          exact absurd hk (by simp)
      · intro i
        by_cases hi : i = n + gs.length
        · subst hi
          exact InU_mem (by simp)
        · rw [T_snoc_ne _ _ _ hi]
          exact InU_mono (fun s hs => by simp [hs]) (hT i)
    · refine ⟨L, le_trans hL (S_card_or gs g), hW, ?_⟩
      intro i
      by_cases hi : i = n + gs.length
      · subst hi
        rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rw [T_or0 gs g hop hin]
          exact InU_empty L
        · rw [T_or1 gs g a hop hin]
          exact hT a
        · rw [T_or2 gs g a b hop hin]
          exact InU_union (hT a) (hT b)
        · rw [hin] at hlen
          simp at hlen
      · rw [T_snoc_ne _ _ _ hi]
        exact hT i

end PEqualNP.Outside.L_meta_8748

theorem PEqualNP.Outside.L_meta_8748 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∃ (x4 : List (Set (Fin x1 → Bool))), x4.length ≤ {x5 : ℕ | ∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ∧ (∀ (x5 : Fin x4.length), ∃ (x6 : Set (Set (Fin x1 → Bool))) (x7 : Set (Set (Fin x1 → Bool))), (∀ x8 ∈ x6, x8 ∈ List.take (↑x5) x4 ∨ x8 = Set.univ ∨ ∃ (x10 : Fin x1), x8 = {x11 : Fin x1 → Bool | x11 x10 = Bool.true}) ∧ (∀ x8 ∈ x7, x8 ∈ List.take (↑x5) x4 ∨ x8 = Set.univ ∨ ∃ (x10 : Fin x1), x8 = {x11 : Fin x1 → Bool | x11 x10 = Bool.true}) ∧ x4.get x5 = ⋃₀ x6 ∩ ⋃₀ x7) ∧ ∀ (x5 : ℕ), ∃ (x6 : Set (Set (Fin x1 → Bool))), (∀ x7 ∈ x6, x7 ∈ x4 ∨ x7 = Set.univ ∨ ∃ (x9 : Fin x1), x7 = {x10 : Fin x1 → Bool | x10 x9 = Bool.true}) ∧ {x7 : Fin x1 → Bool | (x2.wires (List.ofFn x7)).getD x5 Bool.false = Bool.true} = ⋃₀ x6 := by
  intro x1 x2 hm
  obtain ⟨L, hL, hW, hT⟩ := PEqualNP.Outside.L_meta_8748.main (n := x1) x2.gates
    (fun g hg => ⟨by have h := (hm g hg).1; simpa using h, (hm g hg).2⟩)
  refine ⟨L, hL, ?_, ?_⟩
  · intro k
    obtain ⟨A, B, hA, hB, e⟩ := hW k.1 (L.get k) (by simp)
    exact ⟨A, B, hA, hB, e⟩
  · intro i
    obtain ⟨A, hA, e⟩ := hT i
    exact ⟨A, hA, e⟩
