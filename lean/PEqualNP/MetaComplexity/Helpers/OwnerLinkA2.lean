import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkP4

/-!
# The owner link, clause (a), step A2: the heads of `OWN'` (conjecture until checked)

The leading entries of `OWN' E k ψ` are, up to order, the heads of every `innerF` call
(`callsF`) followed by the vertex heads `vtxF` (`heads_perm`).
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

/-- The heads of the `innerF` block of a call. -/
def hdF (E k : ℕ) (c : ℕ × ℕ × Bool) : List ℕ :=
  (innerF E k c.1 c.2.1 c.2.2).map (fun l : List ℕ => l.headD 0)

/-- The vertex heads of item `(i, j)`. -/
def vtxI (E : ℕ) (ψ : CNF) (i j : ℕ) : List ℕ :=
  (if j ≠ fF ψ i then [posF E ψ i j] else []) ++
  (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then [2 * (litF ψ i j).1 + 1] else [])

/-- All vertex heads. -/
def vtxF (E : ℕ) (ψ : CNF) : List ℕ :=
  (List.range ψ.length).flatMap (fun i : ℕ =>
    (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => vtxI E ψ i j)) ++ [2 * E + 1, 3 * E + 2]

theorem item_heads (E k : ℕ) (ψ : CNF) (i j : ℕ) :
    (itemF E k ψ i j).map (fun l : List ℕ => l.headD 0) =
      (blkF E ψ i j).flatMap (hdF E k) ++ vtxI E ψ i j := by
  unfold itemF blkF vtxI
  simp only [List.map_append, List.flatMap_append, List.append_assoc]
  congr 1
  · split_ifs <;> simp [hdF]
  · congr 1
    · simp [hdF, List.map_flatMap, List.flatMap_map]
    · split_ifs <;> simp [hdF, hubL, varL]

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap (fun a => f a ++ g a)).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    simp only [← List.append_assoc]
    refine List.Perm.append_right _ ?_
    exact List.perm_append_comm

theorem flatMap_perm {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a, (f a).Perm (g a)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih => simpa [List.flatMap_cons] using (h a).append ih

theorem heads_perm (E k : ℕ) (ψ : CNF) :
    ((OWN' E k ψ).map (fun l : List ℕ => l.headD 0)).Perm
      ((callsF E ψ).flatMap (hdF E k) ++ vtxF E ψ) := by
  have hI : ((List.range ψ.length).flatMap (fun i : ℕ =>
      (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => itemF E k ψ i j))).map
        (fun l : List ℕ => l.headD 0) |>.Perm
      (((List.range ψ.length).flatMap (fun i : ℕ =>
        (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => blkF E ψ i j))).flatMap (hdF E k) ++
       (List.range ψ.length).flatMap (fun i : ℕ =>
        (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => vtxI E ψ i j))) := by
    simp only [List.map_flatMap, List.flatMap_assoc, item_heads]
    refine (flatMap_perm _ _ _ (fun i => flatMap_append_perm _ _ _)).trans ?_
    exact flatMap_append_perm _ _ _
  rw [List.perm_iff_count] at hI ⊢
  intro a
  have := hI a
  simp only [OWN', callsF_eq, vtxF, List.map_append, List.flatMap_append, List.count_append,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil] at this ⊢
  simp only [hdF] at *
  simp only [List.count_cons, List.count_nil, List.headD_cons] at *
  omega

end PEqualNP.MetaComplexity.Helpers.OwnerLink
