import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755

def tbl (a b : Fin 6) : Bool :=
  (a.val = 0 && (b.val = 1 || b.val = 2 || b.val = 3)) ||
  (b.val = 0 && (a.val = 1 || a.val = 2 || a.val = 3)) ||
  (a.val = 4 && b.val = 5) || (a.val = 5 && b.val = 4)

def G : SimpleGraph (Fin 6) where
  Adj a b := tbl a b = true
  symm := ⟨by intro a b h; revert a b; decide⟩
  loopless := ⟨by intro a h; revert a; decide⟩

theorem reach_const {H : SimpleGraph (Fin 6)} (phi : Fin 6 → Prop)
    (hphi : ∀ x y, H.Adj x y → (phi x ↔ phi y)) {u v : Fin 6} (h : H.Reachable u v) :
    (phi u ↔ phi v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Iff.rfl
  | cons hadj _ ih => exact (hphi _ _ hadj).trans ih

theorem acyclic : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [SimpleGraph.isBridge_iff]
    intro hr
    have key : ∀ x y, (G.deleteEdges {s(a, b)}).Adj x y →
        (x = max a b ↔ y = max a b) := by
      intro x y hxy
      simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hxy
      change tbl a b = true at he
      change tbl x y = true ∧ _ at hxy
      clear hr
      revert a b x y
      decide
    have := reach_const (fun z => z = max a b) key hr
    change tbl a b = true at he
    clear key hr
    revert this he
    revert a b
    decide

theorem cover (T : Finset (Fin 6)) (hT : ∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  have h01 := hT 0 1 (show tbl 0 1 = true from rfl)
  have h02 := hT 0 2 (show tbl 0 2 = true from rfl)
  have h03 := hT 0 3 (show tbl 0 3 = true from rfl)
  have h45 := hT 4 5 (show tbl 4 5 = true from rfl)
  by_cases h0 : (0 : Fin 6) ∈ T
  · rcases h45 with h | h
    · have : ({0, 4} : Finset (Fin 6)) ⊆ T := by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      exact le_trans (by decide) (Finset.card_le_card this)
    · have : ({0, 5} : Finset (Fin 6)) ⊆ T := by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      exact le_trans (by decide) (Finset.card_le_card this)
  · have h1 := h01.resolve_left h0
    have h2 := h02.resolve_left h0
    have : ({1, 2} : Finset (Fin 6)) ⊆ T := by
      intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
    exact le_trans (by decide) (Finset.card_le_card this)

end PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  open PEqualNP.Outside.L_meta_755 in
  intro s
  let _ : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (tbl a b = true))
  have fun_eq : (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true))
      = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by
    funext x
    revert x
    decide
  have edges : G.edgeFinset.card = 4 := by decide
  rw [← fun_eq]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G acyclic ⟨0, 1, show tbl 0 1 = true from rfl⟩ cover h
    rw [edges] at this
    omega
  · intro hs
    have h5 := PEqualNP.MetaComplexity.L105 6 G {0, 4} ⟨0, 1, show tbl 0 1 = true from rfl⟩
      (by intro i j h; change tbl i j = true at h; revert i j; decide)
    rw [edges] at h5
    obtain ⟨C, hC, hsz, hev⟩ := h5
    have hc : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
    rw [hc] at hsz
    exact ⟨C, hC, by omega, hev⟩
