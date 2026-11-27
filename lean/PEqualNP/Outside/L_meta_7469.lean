import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7469

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

def fam (n : ℕ) (L : List (Set (Finset (Fin n)))) : List (Set (Finset (Fin n))) :=
  ∅ :: {∅} :: ((List.ofFn fun (i : Fin n) => {{i}}) ++ L)

def prod (P Q : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {T | ∃ S ∈ P, ∃ U ∈ Q, T = S ∪ U}

def good (L : List (Set (Finset (Fin n)))) : Prop :=
  ∀ k : Fin L.length, ∃ P ∈ fam n (L.take k), ∃ Q ∈ fam n (L.take k),
    L.get k = P ∪ Q ∨ L.get k = prod P Q

def sem (F : Set (Finset (Fin n))) (x : Fin n → Bool) : Prop :=
  ¬ ∃ S ∈ F, ∀ j ∈ S, x j = false

def W (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

theorem sem_union (P Q : Set (Finset (Fin n))) (x : Fin n → Bool) :
    sem (P ∪ Q) x ↔ sem P x ∧ sem Q x := by
  unfold sem
  constructor
  · intro h
    exact ⟨fun ⟨S, hS, h2⟩ => h ⟨S, Or.inl hS, h2⟩, fun ⟨S, hS, h2⟩ => h ⟨S, Or.inr hS, h2⟩⟩
  · rintro ⟨h1, h2⟩ ⟨S, hS | hS, h3⟩
    · exact h1 ⟨S, hS, h3⟩
    · exact h2 ⟨S, hS, h3⟩

theorem sem_prod (P Q : Set (Finset (Fin n))) (x : Fin n → Bool) :
    sem (prod P Q) x ↔ sem P x ∨ sem Q x := by
  unfold sem prod
  constructor
  · intro h
    by_contra hc
    simp only [not_or, not_not] at hc
    obtain ⟨⟨S, hS, h1⟩, ⟨U, hU, h2⟩⟩ := hc
    exact h ⟨S ∪ U, ⟨S, hS, U, hU, rfl⟩,
      fun j hj => (Finset.mem_union.1 hj).elim (h1 j) (h2 j)⟩
  · rintro (h | h) ⟨T, ⟨S, hS, U, hU, rfl⟩, h3⟩
    · exact h ⟨S, hS, fun j hj => h3 j (Finset.mem_union_left _ hj)⟩
    · exact h ⟨U, hU, fun j hj => h3 j (Finset.mem_union_right _ hj)⟩

theorem andLemma (A : List (Set (Finset (Fin n)))) (w : (Fin n → Bool) → ℕ → Bool)
    (hw : ∀ i, ∃ F ∈ A, ∀ x, (w x i = true ↔ sem F x)) (h0 : (∅ : Set (Finset (Fin n))) ∈ A)
    (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ P ∈ A, ∃ Q ∈ A, ∀ x, (GateOp.and.eval (ins.map (w x)) = true ↔ sem (P ∪ Q) x) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨∅, h0, ∅, h0, fun x => ?_⟩
    rw [sem_union]; simp [GateOp.eval, sem]
  · obtain ⟨F, hF, hF'⟩ := hw a
    refine ⟨F, hF, F, hF, fun x => ?_⟩
    rw [sem_union, ← hF' x]; simp [GateOp.eval]
  · obtain ⟨F, hF, hF'⟩ := hw a
    obtain ⟨G, hG, hG'⟩ := hw b
    refine ⟨F, hF, G, hG, fun x => ?_⟩
    rw [sem_union, ← hF' x, ← hG' x]; simp [GateOp.eval]
  · simp at hl

theorem orLemma (A : List (Set (Finset (Fin n)))) (w : (Fin n → Bool) → ℕ → Bool)
    (hw : ∀ i, ∃ F ∈ A, ∀ x, (w x i = true ↔ sem F x)) (h1 : ({∅} : Set (Finset (Fin n))) ∈ A)
    (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ P ∈ A, ∃ Q ∈ A, ∀ x, (GateOp.or.eval (ins.map (w x)) = true ↔ sem (prod P Q) x) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨{∅}, h1, {∅}, h1, fun x => ?_⟩
    rw [sem_prod]; simp [GateOp.eval, sem]
  · obtain ⟨F, hF, hF'⟩ := hw a
    refine ⟨F, hF, F, hF, fun x => ?_⟩
    rw [sem_prod, ← hF' x]; simp [GateOp.eval]
  · obtain ⟨F, hF, hF'⟩ := hw a
    obtain ⟨G, hG, hG'⟩ := hw b
    refine ⟨F, hF, G, hG, fun x => ?_⟩
    rw [sem_prod, ← hF' x, ← hG' x]; simp [GateOp.eval]
  · simp at hl

theorem fam_mono {L M : List (Set (Finset (Fin n)))} {F : Set (Finset (Fin n))}
    (h : F ∈ fam n L) : F ∈ fam n (L ++ M) := by
  simp only [fam, List.mem_cons, List.mem_append] at h ⊢
  tauto

theorem good_snoc {L : List (Set (Finset (Fin n)))} {F : Set (Finset (Fin n))} (hL : good L)
    (hF : ∃ P ∈ fam n L, ∃ Q ∈ fam n L, F = P ∪ Q ∨ F = prod P Q) : good (L ++ [F]) := by
  intro k
  have hk := k.isLt
  simp only [List.length_append, List.length_singleton] at hk
  by_cases h : (k : ℕ) < L.length
  · obtain ⟨P, hP, Q, hQ, hPQ⟩ := hL ⟨k, h⟩
    have ht : (L ++ [F]).take k = L.take k := List.take_append_of_le_length h.le
    have hg : (L ++ [F]).get k = L.get ⟨k, h⟩ := by
      simp [List.getElem_append_left, h]
    rw [ht, hg]
    exact ⟨P, hP, Q, hQ, hPQ⟩
  · have hk' : (k : ℕ) = L.length := by omega
    have ht : (L ++ [F]).take k = L := by rw [hk']; simp
    have hg : (L ++ [F]).get k = F := by
      simp [hk']
    rw [ht, hg]
    exact hF

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  unfold W
  rw [List.foldl_append]
  rfl

theorem W_length (gs : List Gate) (x : Fin n → Bool) : (W gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc]
    simp [ih]
    omega

theorem getD_snoc_ne (l : List Bool) (v : Bool) (i : ℕ) (h : i ≠ l.length) :
    (l ++ [v]).getD i false = l.getD i false := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem main (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ L : List (Set (Finset (Fin n))), L.length = gs.length ∧ good L ∧
      ∀ i : ℕ, ∃ F ∈ fam n L, ∀ x : Fin n → Bool, ((W gs x).getD i false = true ↔ sem F x) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], rfl, fun k => k.elim0, fun i => ?_⟩
    by_cases hi : i < n
    · refine ⟨{{⟨i, hi⟩}}, ?_, fun x => ?_⟩
      · simp [fam]
      · simp [W, sem, List.getD_eq_getElem?_getD, hi]
    · refine ⟨{∅}, by simp [fam], fun x => ?_⟩
      have : (List.ofFn x).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      simp [W, sem, hi]
  | append_singleton gs g ih =>
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    obtain ⟨L, hlen, hgood, hw⟩ := ih hg'
    obtain ⟨hop, hil⟩ := hg g (List.mem_append_right _ (List.mem_singleton_self _))
    have h0 : (∅ : Set (Finset (Fin n))) ∈ fam n L := by simp [fam]
    have h1 : ({∅} : Set (Finset (Fin n))) ∈ fam n L := by simp [fam]
    obtain ⟨F, hFstep, hF⟩ : ∃ F, (∃ P ∈ fam n L, ∃ Q ∈ fam n L, F = P ∪ Q ∨ F = prod P Q) ∧
        ∀ x, (g.op.eval (g.inputs.map fun i => (W gs x).getD i false) = true ↔ sem F x) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop
      · obtain ⟨P, hP, Q, hQ, h⟩ :=
          andLemma (fam n L) (fun x i => (W gs x).getD i false) hw h0 g.inputs hil
        exact ⟨P ∪ Q, ⟨P, hP, Q, hQ, Or.inl rfl⟩, fun x => by rw [hop]; exact h x⟩
      · obtain ⟨P, hP, Q, hQ, h⟩ :=
          orLemma (fam n L) (fun x i => (W gs x).getD i false) hw h1 g.inputs hil
        exact ⟨prod P Q, ⟨P, hP, Q, hQ, Or.inr rfl⟩, fun x => by rw [hop]; exact h x⟩
    refine ⟨L ++ [F], by simp [hlen], good_snoc hgood hFstep, fun i => ?_⟩
    by_cases hi : i = n + gs.length
    · refine ⟨F, by simp [fam], fun x => ?_⟩
      have hl := W_length gs x
      rw [W_snoc, hi, ← hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]
      exact hF x
    · obtain ⟨G, hG, hG'⟩ := hw i
      refine ⟨G, fam_mono hG, fun x => ?_⟩
      rw [W_snoc, getD_snoc_ne _ _ _ (by rw [W_length]; exact hi)]
      exact hG' x

end PEqualNP.Outside.L_meta_7469

open PEqualNP.Outside.L_meta_7469 in
theorem PEqualNP.Outside.L_meta_7469 : ∀ (x1 : ℕ),   have x2 : List (Set (Finset (Fin x1))) → List (Set (Finset (Fin x1))) := fun (x2 : List (Set (Finset (Fin x1)))) => ∅ :: {∅} :: ((List.ofFn fun (x3 : Fin x1) => {{x3}}) ++ x2);   have x3 : List (Set (Finset (Fin x1))) → Prop := fun (x3 : List (Set (Finset (Fin x1)))) => ∀ (x4 : Fin x3.length), ∃ x5 ∈ x2 (List.take (↑x4) x3), ∃ x6 ∈ x2 (List.take (↑x4) x3), x3.get x4 = x5 ∪ x6 ∨ x3.get x4 = {x7 : Finset (Fin x1) | ∃ x8 ∈ x5, ∃ x9 ∈ x6, x7 = x8 ∪ x9};   ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → x5.length ≤ (2 : ℕ) → ∃ (x8 : List (Set (Finset (Fin x1)))), x8.length ≤ x4.size ∧ x3 x8 ∧ ∃ x9 ∈ x2 x8, ∃ x10 ∈ x2 x8, ∀ (x11 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x12 : ℕ) => (x4.wires (List.ofFn x11)).getD x12 Bool.false) x5) = Bool.false ↔ ∃ x12 ∈ x9 ∪ x10, ∀ x13 ∈ x12, x11 x13 = Bool.false := by
  intro n
  show ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ins : List ℕ),
    PEqualNP.MetaComplexity.Monotone2 C → ins.length ≤ 2 →
    ∃ L : List (Set (Finset (Fin n))), L.length ≤ C.size ∧ good L ∧
      ∃ P ∈ fam n L, ∃ Q ∈ fam n L, ∀ x : Fin n → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun i => (C.wires (List.ofFn x)).getD i false) ins) = false ↔
        ∃ S ∈ P ∪ Q, ∀ j ∈ S, x j = false
  intro C ins hC hins
  obtain ⟨L, hlen, hgood, hw⟩ := main (n := n) C.gates hC
  have h0 : (∅ : Set (Finset (Fin n))) ∈ fam n L := by simp [fam]
  obtain ⟨P, hP, Q, hQ, h⟩ :=
    andLemma (fam n L) (fun x i => (W C.gates x).getD i false) hw h0 ins hins
  refine ⟨L, hlen.le, hgood, P, hP, Q, hQ, fun x => ?_⟩
  have hx : PEqualNP.CircuitLowerBounds.GateOp.and.eval
      (List.map (fun i => (C.wires (List.ofFn x)).getD i false) ins) = true ↔
      sem (P ∪ Q) x := h x
  rw [Bool.eq_false_iff, Ne, hx]
  simp only [sem, not_not]
