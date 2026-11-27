import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8195

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  ({ gates := gs, output := 0 } : Circuit).wires x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, Circuit.wires, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W, Circuit.wires]
  | append_singleton gs g ih =>
    rw [W_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

theorem getD_left (l : List Bool) (b : Bool) (n : ℕ) (h : n < l.length) :
    (l ++ [b]).getD n false = l.getD n false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_new (l : List Bool) (b : Bool) (n : ℕ) (h : n = l.length) :
    (l ++ [b]).getD n false = b := by
  subst h
  simp [List.getD_eq_getElem?_getD]

def Sa {α β : Type} {n : ℕ} (gs : List Gate) (R : Set (α × β)) (f : α → Fin n → Bool) (w : ℕ) :
    Prop :=
  ∀ p ∈ R, (W gs (List.ofFn (f p.1))).getD w false = true

def Sb {α β : Type} {n : ℕ} (gs : List Gate) (R : Set (α × β)) (f : β → Fin n → Bool) (w : ℕ) :
    Prop :=
  ∀ p ∈ R, (W gs (List.ofFn (f p.2))).getD w false = false

theorem build (x1 x2 : ℕ) (x3 x4 : Type) (x5 : x3 → Fin x1 → Bool) (x6 : x4 → Fin x1 → Bool)
    (x7 : ℕ → Set (x3 × x4))
    (h1 : ∀ (x8 : Fin x1), ∀ x9 ∈ x7 ↑x8, x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false)
    (h2 : ∀ x9 < x2, (∀ x11 ∈ x7 (x1 + x9), ∀ x13 ∈ x7 (x1 + x9), (x11.1, x13.2) ∈ x7 (x1 + x9)) ∧
      ∃ x11 < x1 + x9, ∃ x12 < x1 + x9, x7 (x1 + x9) ⊆ x7 x11 ∪ x7 x12) :
    ∀ k, k ≤ x2 → ∃ gs : List Gate, gs.length = k ∧
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ w < x1 + k, ∀ p ∈ x7 w, (W gs (List.ofFn (x5 p.1))).getD w false = true ∧
        (W gs (List.ofFn (x6 p.2))).getD w false = false := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], rfl, by simp, ?_⟩
    intro w hw p hp
    have hw' : w < x1 := by omega
    have := h1 ⟨w, hw'⟩ p hp
    simp [W, Circuit.wires, List.getD_eq_getElem?_getD, hw', this.1, this.2]
  | succ k ih =>
    intro hk
    obtain ⟨gs, hlen, hmono, hsep⟩ := ih (by omega)
    obtain ⟨hclos, u, hu, v, hv, hcov⟩ := h2 k (by omega)
    have D1 : Sa gs (x7 (x1 + k)) x5 u ∨ Sb gs (x7 (x1 + k)) x6 v := by
      by_contra hc
      rw [not_or] at hc
      obtain ⟨hA, hB⟩ := hc
      simp only [Sa, Sb, not_forall] at hA hB
      obtain ⟨p, hp, hpf⟩ := hA
      obtain ⟨q, hq, hqf⟩ := hB
      rcases hcov (hclos p hp q hq) with hm | hm
      · exact hpf (hsep u hu _ hm).1
      · exact hqf (hsep v hv _ hm).2
    have D2 : Sa gs (x7 (x1 + k)) x5 v ∨ Sb gs (x7 (x1 + k)) x6 u := by
      by_contra hc
      rw [not_or] at hc
      obtain ⟨hA, hB⟩ := hc
      simp only [Sa, Sb, not_forall] at hA hB
      obtain ⟨p, hp, hpf⟩ := hA
      obtain ⟨q, hq, hqf⟩ := hB
      rcases hcov (hclos p hp q hq) with hm | hm
      · exact hqf (hsep u hu _ hm).2
      · exact hpf (hsep v hv _ hm).1
    let g : Gate :=
      if Sa gs (x7 (x1 + k)) x5 u ∧ Sa gs (x7 (x1 + k)) x5 v then ⟨GateOp.and, [u, v]⟩
      else if Sb gs (x7 (x1 + k)) x6 u ∧ Sb gs (x7 (x1 + k)) x6 v then ⟨GateOp.or, [u, v]⟩
      else if Sa gs (x7 (x1 + k)) x5 u ∧ Sb gs (x7 (x1 + k)) x6 u then ⟨GateOp.and, [u]⟩
      else ⟨GateOp.and, [v]⟩
    refine ⟨gs ++ [g], by simp [hlen], ?_, ?_⟩
    · intro g' hg'
      rcases List.mem_append.1 hg' with h | h
      · exact hmono g' h
      · simp only [List.mem_singleton] at h
        subst h
        simp only [g]
        split_ifs <;> simp
    · intro w hw p hp
      have hL5 : (W gs (List.ofFn (x5 p.1))).length = x1 + k := by
        rw [W_length, List.length_ofFn, hlen]
      have hL6 : (W gs (List.ofFn (x6 p.2))).length = x1 + k := by
        rw [W_length, List.length_ofFn, hlen]
      rcases Nat.lt_or_ge w (x1 + k) with hlt | hge
      · rw [W_snoc, W_snoc, getD_left _ _ _ (by omega), getD_left _ _ _ (by omega)]
        exact hsep w hlt p hp
      · have hwe : w = x1 + k := by omega
        subst hwe
        rw [W_snoc, W_snoc, getD_new _ _ _ hL5.symm, getD_new _ _ _ hL6.symm]
        simp only [g]
        split_ifs with c1 c2 c3
        · refine ⟨?_, ?_⟩
          · simp only [GateOp.eval, List.map_cons, List.map_nil, c1.1 p hp, c1.2 p hp] <;> simp
          · rcases hcov hp with hm | hm
            · simp only [GateOp.eval, List.map_cons, List.map_nil, (hsep u hu p hm).2] <;> simp
            · simp only [GateOp.eval, List.map_cons, List.map_nil, (hsep v hv p hm).2] <;> simp
        · refine ⟨?_, ?_⟩
          · rcases hcov hp with hm | hm
            · simp only [GateOp.eval, List.map_cons, List.map_nil, (hsep u hu p hm).1] <;> simp
            · simp only [GateOp.eval, List.map_cons, List.map_nil, (hsep v hv p hm).1] <;> simp
          · simp only [GateOp.eval, List.map_cons, List.map_nil, c2.1 p hp, c2.2 p hp] <;> simp
        · simp only [GateOp.eval, List.map_cons, List.map_nil, c3.1 p hp, c3.2 p hp] <;> simp
        · have hv' : Sa gs (x7 (x1 + k)) x5 v ∧ Sb gs (x7 (x1 + k)) x6 v := by tauto
          simp only [GateOp.eval, List.map_cons, List.map_nil, hv'.1 p hp, hv'.2 p hp] <;> simp

end PEqualNP.Outside.L_meta_8195

theorem PEqualNP.Outside.L_meta_8195 : ∀ (x1 x2 : ℕ) (x3 x4 : Type) (x5 : x3 → Fin x1 → Bool) (x6 : x4 → Fin x1 → Bool) (x7 : ℕ → Set (x3 × x4)), (∀ (x8 : Fin x1), ∀ x9 ∈ x7 ↑x8, x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false) → (∀ x9 < x2, (∀ x11 ∈ x7 (x1 + x9), ∀ x13 ∈ x7 (x1 + x9), (x11.1, x13.2) ∈ x7 (x1 + x9)) ∧ ∃ x11 < x1 + x9, ∃ x12 < x1 + x9, x7 (x1 + x9) ⊆ x7 x11 ∪ x7 x12) → ∀ x10 < x1 + x2, ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ x12.size ≤ x2 ∧ ∀ x13 ∈ x7 x10, x12.eval (List.ofFn (x5 x13.1)) = Bool.true ∧ x12.eval (List.ofFn (x6 x13.2)) = Bool.false := by
  intro x1 x2 x3 x4 x5 x6 x7 h1 h2 x10 hx10
  obtain ⟨gs, hlen, hmono, hsep⟩ :=
    PEqualNP.Outside.L_meta_8195.build x1 x2 x3 x4 x5 x6 x7 h1 h2 x2 le_rfl
  refine ⟨⟨gs, x10⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hmono g hg
  · show gs.length ≤ x2
    omega
  · intro p hp
    exact hsep x10 hx10 p hp
