import PEqualNP.MetaComplexity.Helpers.LowMergeFacts

/-!
# Class labels along the wires

`lab t p` is the class label of point `p` after the wires below `t`: at each low wire `t` every
point whose label is a label of the alive set of `t` gets the largest such label. The number of
labels on the points of the line drops at wire `t` by at most (number of labels on its alive
set) minus one.
-/

namespace PEqualNP.MetaComplexity.LowMergeProof

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

variable {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)

/-- Class labels after the wires below `t`. -/
def lab : ℕ → Fin P → ℕ
  | 0 => fun p => p.val
  | t + 1 => fun p =>
    if IsLow P L inc C t w ∧ lab t p ∈ (aliveSet P L C t w).image (lab t) then
      ((aliveSet P L C t w).image (lab t)).sup id
    else lab t p

/-- The labels of the alive set of wire `t`. -/
def labs (t : ℕ) : Finset ℕ := (aliveSet P L C t w).image (lab inc C w t)

/-- The labels on the points of the line. -/
def lineLabs (t : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun p : Fin P => inc p w = true)).image (lab inc C w t)

/-- `s` has one label at time `t`. -/
def Const (t : ℕ) (s : Finset (Fin P)) : Prop := ∀ p ∈ s, ∀ q ∈ s, lab inc C w t p = lab inc C w t q

theorem lab_succ_eq (t : ℕ) (p q : Fin P) (h : lab inc C w t p = lab inc C w t q) :
    lab inc C w (t + 1) p = lab inc C w (t + 1) q := by
  simp only [lab]; rw [h]

theorem lab_le_eq (s t : ℕ) (hst : s ≤ t) (p q : Fin P) (h : lab inc C w s p = lab inc C w s q) :
    lab inc C w t p = lab inc C w t q := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact lab_succ_eq inc C w n p q ih

theorem const_alive (t : ℕ) (hlow : IsLow P L inc C t w) :
    Const inc C w (t + 1) (aliveSet P L C t w) := by
  intro p hp q hq
  simp only [lab]
  rw [if_pos ⟨hlow, Finset.mem_image_of_mem _ hp⟩, if_pos ⟨hlow, Finset.mem_image_of_mem _ hq⟩]

/-- F4: a low wire's alive set has one label at every later time. -/
theorem const_later (s t : ℕ) (hst : s < t) (hlow : IsLow P L inc C s w) :
    Const inc C w t (aliveSet P L C s w) := by
  intro p hp q hq
  exact lab_le_eq inc C w (s + 1) t hst p q (const_alive inc C w s hlow p hp q hq)

theorem card_image_le_one (t : ℕ) (A B : Finset (Fin P)) (hAB : A ⊆ B)
    (hB : Const inc C w t B) : (A.image (lab inc C w t)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  exact hB p (hAB hp) q (hAB hq)

theorem lab_succ_of_not_low (t : ℕ) (h : ¬ IsLow P L inc C t w) :
    lab inc C w (t + 1) = lab inc C w t := by
  funext p; simp only [lab]; rw [if_neg (fun h' => h h'.1)]

/-- The count step at one wire. -/
theorem lineLabs_step (t : ℕ) (hlow : IsLow P L inc C t w) :
    (lineLabs inc C w t).card + 1 ≤ (lineLabs inc C w (t + 1)).card + (labs inc C w t).card ∨
    (labs inc C w t).card = 0 ∧
      (lineLabs inc C w t).card ≤ (lineLabs inc C w (t + 1)).card := by
  set T := labs inc C w t with hT
  set X := lineLabs inc C w t with hX
  have hsub : aliveSet P L C t w ⊆ Finset.univ.filter (fun p : Fin P => inc p w = true) :=
    alive_sub_line inc C t w hlow
  have hTX : T ⊆ X := Finset.image_subset_image hsub
  rcases T.eq_empty_or_nonempty with hE | hne
  · right
    refine ⟨by rw [hE]; rfl, ?_⟩
    have : lab inc C w (t + 1) = lab inc C w t := by
      funext p; simp only [lab]
      rw [if_neg]
      rintro ⟨_, hm⟩
      have : lab inc C w t p ∈ T := hm
      rw [hE] at this; simp at this
    rw [hX, lineLabs, lineLabs, this]
  · left
    obtain ⟨d0, hd0, hd⟩ := Finset.exists_mem_eq_sup T hne id
    have hsupT : (aliveSet P L C t w).image (lab inc C w t) = T := rfl
    have key : insert (T.sup id) (X \ T) ⊆ lineLabs inc C w (t + 1) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [hd]
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd0
        unfold lineLabs
        refine Finset.mem_image.mpr ⟨p, hsub hp, ?_⟩
        simp only [lab]
        rw [if_pos ⟨hlow, Finset.mem_image_of_mem _ hp⟩, hsupT, hd]
      · obtain ⟨hxX, hxT⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxX
        unfold lineLabs
        refine Finset.mem_image.mpr ⟨p, hp, ?_⟩
        simp only [lab]
        rw [if_neg (fun h' => hxT h'.2)]
    have hnot : T.sup id ∉ X \ T := by
      rw [hd]; intro h; exact (Finset.mem_sdiff.mp h).2 hd0
    have h1 := Finset.card_le_card key
    rw [Finset.card_insert_of_notMem hnot] at h1
    have h2 := Finset.card_sdiff_add_card_eq_card hTX
    omega

end PEqualNP.MetaComplexity.LowMergeProof
