import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9132

-- Part 1: Projective plane combinatorics

lemma line_card {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) (l : Fin N) :
    (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
  have h := hdeg l
  rwa [Fintype.card_subtype] at h

lemma line_inter_card_le_one {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {l1 l2 : Fin N} (hne : l1 ≠ l2) :
    (Finset.univ.filter (fun p : Fin N => I p l1 ∧ I p l2)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p1 hp1 p2 hp2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
  by_contra hpne
  obtain ⟨l0, _, hu⟩ := huniq p1 p2 hpne
  have e1 := hu l1 ⟨hp1.1, hp2.1⟩
  have e2 := hu l2 ⟨hp1.2, hp2.2⟩
  exact hne (e1.trans e2.symm)

lemma exists_point_on_not_on {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {l1 l2 : Fin N} (hne : l1 ≠ l2) :
    ∃ p : Fin N, I p l1 ∧ ¬ I p l2 := by
  let P1 := Finset.univ.filter (fun p : Fin N => I p l1)
  let P12 := Finset.univ.filter (fun p : Fin N => I p l1 ∧ I p l2)
  have h1 : P1.card = q + 1 := line_card hdeg l1
  have h12 : P12.card ≤ 1 := line_inter_card_le_one huniq hne
  have hne_sdiff : (P1 \ P12).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : P1 ⊆ P12 := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp⟩ := hne_sdiff
  rw [Finset.mem_sdiff] at hp
  have hp1 : I p l1 := (Finset.mem_filter.mp hp.1).2
  have hp2 : ¬ I p l2 := fun h => hp.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp1, h⟩)
  exact ⟨p, hp1, hp2⟩

lemma exists_point_on {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) (l : Fin N) :
    ∃ p : Fin N, I p l := by
  have hc : (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := line_card hdeg l
  have hne : (Finset.univ.filter (fun p : Fin N => I p l)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (Finset.mem_filter.mp hp).2⟩

lemma point_deg {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (p : Fin N) :
    (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1 := by
  let Lp := Finset.univ.filter (fun l : Fin N => I p l)
  have hpart : Finset.univ.erase p =
      Lp.biUnion (fun l => (Finset.univ.filter (fun p' : Fin N => I p' l)).erase p) := by
    ext p'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion,
      Finset.mem_filter, Lp, true_and]
    constructor
    · intro hne
      obtain ⟨l, ⟨hpl, hp'l⟩, _⟩ := huniq p p' hne.symm
      exact ⟨l, hpl, hne, hp'l⟩
    · rintro ⟨_, _, hne, _⟩
      exact hne
  have hdisj : Set.PairwiseDisjoint (Lp : Set (Fin N))
      (fun l => (Finset.univ.filter (fun p' : Fin N => I p' l)).erase p) := by
    intro l1 hl1m l2 hl2m hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p' hp'1 hp'2
    rw [Finset.mem_erase, Finset.mem_filter] at hp'1 hp'2
    obtain ⟨l0, _, hu⟩ := huniq p p' hp'1.1.symm
    have hl1 : I p l1 := (Finset.mem_filter.mp hl1m).2
    have hl2 : I p l2 := (Finset.mem_filter.mp hl2m).2
    have e1 := hu l1 ⟨hl1, hp'1.2.2⟩
    have e2 := hu l2 ⟨hl2, hp'2.2.2⟩
    exact hne (e1.trans e2.symm)
  have hcard1 : (Finset.univ.erase p).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  have hcard2 : (Lp.biUnion (fun l => (Finset.univ.filter (fun p' : Fin N => I p' l)).erase p)).card =
      Lp.card * q := by
    rw [Finset.card_biUnion hdisj]
    have hterm : ∀ l ∈ Lp, ((Finset.univ.filter (fun p' : Fin N => I p' l)).erase p).card = q := by
      intro l hl
      have hpl : I p l := (Finset.mem_filter.mp hl).2
      have hmem : p ∈ Finset.univ.filter (fun p' : Fin N => I p' l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl⟩
      rw [Finset.card_erase_of_mem hmem, line_card hdeg l]
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have heq : Lp.card * q = (q + 1) * q := by
    have hmul : (q + 1) * q = q ^ 2 + q := by
      rw [add_mul, one_mul, sq]
    have hNsub : N - 1 = (q + 1) * q := by omega
    rw [← hcard2, ← hpart, hcard1, hNsub]
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) heq

lemma exists_line_through_not_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    {p1 p2 : Fin N} (hne : p1 ≠ p2) :
    ∃ l : Fin N, I p1 l ∧ ¬ I p2 l := by
  let L1 := Finset.univ.filter (fun l : Fin N => I p1 l)
  obtain ⟨l0, ⟨_, _⟩, hu⟩ := huniq p1 p2 hne
  have hcard : L1.card = q + 1 := point_deg hq hN hdeg huniq p1
  have hne_sdiff : (L1.erase l0).Nonempty := by
    apply Finset.card_pos.mp
    by_cases hmem : l0 ∈ L1
    · rw [Finset.card_erase_of_mem hmem]; omega
    · rw [Finset.erase_eq_of_notMem hmem]; omega
  obtain ⟨l, hl⟩ := hne_sdiff
  rw [Finset.mem_erase] at hl
  have hp1l : I p1 l := (Finset.mem_filter.mp hl.2).2
  have hnp2l : ¬ I p2 l := fun hp2l => hl.1 (hu l ⟨hp1l, hp2l⟩)
  exact ⟨l, hp1l, hnp2l⟩

lemma exists_line_through_ne {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (p l : Fin N) :
    ∃ l' : Fin N, l' ≠ l ∧ I p l' := by
  let Lp := Finset.univ.filter (fun l' : Fin N => I p l')
  have hcard : Lp.card = q + 1 := point_deg hq hN hdeg huniq p
  have hne_sdiff : (Lp.erase l).Nonempty := by
    apply Finset.card_pos.mp
    by_cases hmem : l ∈ Lp
    · rw [Finset.card_erase_of_mem hmem]; omega
    · rw [Finset.erase_eq_of_notMem hmem]; omega
  obtain ⟨l', hl'⟩ := hne_sdiff
  rw [Finset.mem_erase] at hl'
  exact ⟨l', hl'.1, (Finset.mem_filter.mp hl'.2).2⟩

lemma exists_line_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (p : Fin N) :
    ∃ l : Fin N, I p l := by
  have hcard : (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1 :=
    point_deg hq hN hdeg huniq p
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun l : Fin N => I p l)).card)
  exact ⟨l, (Finset.mem_filter.mp hl).2⟩

lemma indep_card_le {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (AP AL : Finset (Fin N))
    (hind : ∀ p ∈ AP, ∀ l ∈ AL, ¬ I p l) :
    AP.card + AL.card ≤ N := by
  let E := AP.biUnion (fun p => (Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l)))
  let B := (Finset.univ \ AL).biUnion
    (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l)))
  have hdisj : Set.PairwiseDisjoint (AP : Set (Fin N))
      (fun p => (Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l))) := by
    intro p1 _ p2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨l1, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨l2, _, heq⟩ := Finset.mem_image.mp hx2
    exact hne (Prod.mk.inj heq).1.symm
  have hEcard : E.card = AP.card * (q + 1) := by
    rw [Finset.card_biUnion hdisj]
    have hterm : ∀ p ∈ AP,
        ((Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l))).card = q + 1 := by
      intro p _
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
      exact point_deg hq hN hdeg huniq p
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hsub : E ⊆ B := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxp
    have hI : I p l := (Finset.mem_filter.mp hl).2
    have hlnot : l ∉ AL := fun hmem => hind p hp l hmem hI
    refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_sdiff.mpr ⟨Finset.mem_univ l, hlnot⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hI⟩, rfl⟩
  have hBcard : B.card ≤ (Finset.univ \ AL).card * (q + 1) := by
    calc B.card
        ≤ ∑ l ∈ Finset.univ \ AL,
            ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card :=
          Finset.card_biUnion_le
      _ = ∑ l ∈ Finset.univ \ AL, (q + 1) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
          exact line_card hdeg l
      _ = (Finset.univ \ AL).card * (q + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hle : AP.card * (q + 1) ≤ (Finset.univ \ AL).card * (q + 1) := by
    rw [← hEcard]
    exact (Finset.card_le_card hsub).trans hBcard
  have hle' : AP.card ≤ (Finset.univ \ AL).card :=
    Nat.le_of_mul_le_mul_right hle (by omega)
  have hcomp : (Finset.univ \ AL).card + AL.card = N := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ AL)
    simpa [Finset.card_univ, Fintype.card_fin] using h1
  omega

-- Part 2: Monotone Boolean circuit semantics and gate extraction

def evalX (F : ℕ → Set (Finset ℕ)) (w : ℕ) (Z : Finset ℕ) : Prop := Z ∈ F w

lemma evalX_input {m : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hin : ∀ v < m, F v = {Z | v ∈ Z}) {v : ℕ} (hv : v < m) (Z : Finset ℕ) :
    evalX F v Z ↔ v ∈ Z := by
  simp [evalX, hin v hv]

def GateSpec (F : ℕ → Set (Finset ℕ)) (m s : ℕ) : Prop :=
  ∀ g < s, ∃ a < m + g, ∃ b < m + g,
    F (m + g) = F a ∪ F b ∨ F (m + g) = F a ∨
    F (m + g) = ∅ ∨ F (m + g) = F a ∩ F b

lemma evalX_mono {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hin : ∀ v < m, F v = {Z | v ∈ Z}) (hgate : GateSpec F m s)
    {Z₁ Z₂ : Finset ℕ} (hsub : Z₁ ⊆ Z₂) :
    ∀ w < m + s, evalX F w Z₁ → evalX F w Z₂ := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h : w < m
    · simpa only [evalX_input hin h] using @hsub w
    have hwg : w = m + (w - m) := by omega
    obtain ⟨a, ha, b, hb, hs⟩ := hgate (w - m) (by omega)
    have ha' := ih a (by omega) (by omega)
    have hb' := ih b (by omega) (by omega)
    rw [hwg]
    unfold evalX at ha' hb' ⊢
    rcases hs with h₁ | h₁ | h₁ | h₁ <;> rw [h₁]
    · exact fun h => h.elim (Or.inl ∘ ha') (Or.inr ∘ hb')
    · exact ha'
    · simp
    · exact fun h => ⟨ha' h.1, hb' h.2⟩

lemma not_evalX_empty {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hin : ∀ v < m, F v = {Z | v ∈ Z}) (hgate : GateSpec F m s)
    {w : ℕ} (hw : w < m + s) : ¬ evalX F w ∅ := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w < m
    · simp [evalX_input hin h]
    have hwg : w = m + (w - m) := by omega
    obtain ⟨a, ha, b, hb, hs⟩ := hgate (w - m) (by omega)
    have ha' := ih a (by omega) (by omega)
    have hb' := ih b (by omega) (by omega)
    rw [hwg]
    unfold evalX at ha' hb' ⊢
    rcases hs with h₁ | h₁ | h₁ | h₁ <;> rw [h₁]
    · exact fun h => h.elim ha' hb'
    · exact ha'
    · simp
    · exact fun h => ha' h.1

noncomputable def gA (m s : ℕ) (F : ℕ → Set (Finset ℕ))
    (hgate : GateSpec F m s)
    (g : ℕ) : ℕ :=
  if hg : g < s then Classical.choose (hgate g hg) else 0

noncomputable def gB (m s : ℕ) (F : ℕ → Set (Finset ℕ))
    (hgate : GateSpec F m s)
    (g : ℕ) : ℕ :=
  if hg : g < s then Classical.choose (Classical.choose_spec (hgate g hg)).2 else 0

lemma gA_lt {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    {g : ℕ} (hg : g < s) : gA m s F hgate g < m + g := by
  simp only [gA, hg, dite_true]
  exact (Classical.choose_spec (hgate g hg)).1

lemma gB_lt {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    {g : ℕ} (hg : g < s) : gB m s F hgate g < m + g := by
  simp only [gB, hg, dite_true]
  exact (Classical.choose_spec (Classical.choose_spec (hgate g hg)).2).1

lemma gSpec {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    {g : ℕ} (hg : g < s) :
    F (m + g) = F (gA m s F hgate g) ∪ F (gB m s F hgate g) ∨
    F (m + g) = F (gA m s F hgate g) ∨
    F (m + g) = ∅ ∨
    F (m + g) = F (gA m s F hgate g) ∩ F (gB m s F hgate g) := by
  simp only [gA, gB, hg, dite_true]
  exact (Classical.choose_spec (Classical.choose_spec (hgate g hg)).2).2

-- 0 = CONST, 1 = COPY, 2 = OR (a ≠ b), 3 = AND (a ≠ b)
noncomputable def gKind (m s : ℕ) (F : ℕ → Set (Finset ℕ))
    (hgate : GateSpec F m s)
    (g : ℕ) : ℕ :=
  let a := gA m s F hgate g
  let b := gB m s F hgate g
  @ite ℕ (F (m + g) = ∅) (Classical.propDecidable _) 0
    (@ite ℕ (F (m + g) = F a ∨ a = b) (Classical.propDecidable _) 1
      (@ite ℕ (F (m + g) = F a ∪ F b)
        (Classical.propDecidable _) 2 3))

noncomputable def gIns (m s : ℕ) (F : ℕ → Set (Finset ℕ))
    (hgate : GateSpec F m s)
    (g : ℕ) : Finset ℕ :=
  if g < s then
    match gKind m s F hgate g with
    | 0 => ∅
    | 1 => {gA m s F hgate g}
    | _ => {gA m s F hgate g, gB m s F hgate g}
  else ∅

lemma gIns_card_le_two {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    (g : ℕ) : (gIns m s F hgate g).card ≤ 2 := by
  unfold gIns
  split_ifs
  · cases gKind m s F hgate g with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ _ => exact Finset.card_le_two
  · simp

lemma gIns_lt {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    {g : ℕ} (hg : g < s) {u : ℕ} (hu : u ∈ gIns m s F hgate g) : u < m + g := by
  unfold gIns at hu
  simp only [hg, ite_true] at hu
  cases h : gKind m s F hgate g with
  | zero => rw [h] at hu; simp at hu
  | succ n =>
    cases n with
    | zero =>
      rw [h] at hu
      simp only [Finset.mem_singleton] at hu
      subst hu
      exact gA_lt hgate hg
    | succ _ =>
      rw [h] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact gA_lt hgate hg
      · exact gB_lt hgate hg

lemma evalX_union {F : ℕ → Set (Finset ℕ)} {a b w : ℕ}
    (h : F w = F a ∪ F b) (Z : Finset ℕ) :
    evalX F w Z ↔ evalX F a Z ∨ evalX F b Z := by
  simp only [evalX, h, Set.mem_union]

lemma evalX_inter {F : ℕ → Set (Finset ℕ)} {a b w : ℕ}
    (h : F w = F a ∩ F b) (Z : Finset ℕ) :
    evalX F w Z ↔ evalX F a Z ∧ evalX F b Z := by
  simp only [evalX, h, Set.mem_inter_iff]

lemma gKind_spec {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    {g : ℕ} (hg : g < s) :
    let a := gA m s F hgate g
    let b := gB m s F hgate g
    (gKind m s F hgate g = 0 ∧ gIns m s F hgate g = ∅ ∧
      ∀ Z, ¬ evalX F (m + g) Z) ∨
    (gKind m s F hgate g = 1 ∧ gIns m s F hgate g = {a} ∧
      ∀ Z, evalX F (m + g) Z ↔ evalX F a Z) ∨
    (gKind m s F hgate g = 2 ∧ a ≠ b ∧ gIns m s F hgate g = {a, b} ∧
      ∀ Z, evalX F (m + g) Z ↔ evalX F a Z ∨ evalX F b Z) ∨
    (gKind m s F hgate g = 3 ∧ a ≠ b ∧ gIns m s F hgate g = {a, b} ∧
      ∀ Z, evalX F (m + g) Z ↔ evalX F a Z ∧ evalX F b Z) := by
  dsimp only
  set a := gA m s F hgate g
  set b := gB m s F hgate g
  by_cases h0 : F (m + g) = ∅
  · left
    have hk : gKind m s F hgate g = 0 := by unfold gKind; simp [h0]
    refine ⟨hk, by unfold gIns; simp [hg, hk], fun Z => by simp [evalX, h0]⟩
  · by_cases h1 : F (m + g) = F a ∨ a = b
    · right; left
      have hk : gKind m s F hgate g = 1 := by unfold gKind; simp [h0, h1, a, b]
      refine ⟨hk, by unfold gIns; simp [hg, hk, a], fun Z => ?_⟩
      rcases h1 with heq | hab
      · unfold evalX; rw [heq]
      · rcases gSpec hgate hg with hs | hs | hs | hs
        · rw [evalX_union hs Z]
          change evalX F a Z ∨ evalX F b Z ↔ evalX F a Z
          rw [← hab, or_self]
        · unfold evalX; rw [hs]
        · exact absurd hs h0
        · rw [evalX_inter hs Z]
          change evalX F a Z ∧ evalX F b Z ↔ evalX F a Z
          rw [← hab, and_self]
    · push Not at h1
      by_cases h2 : F (m + g) = F a ∪ F b
      · right; right; left
        have hk : gKind m s F hgate g = 2 := by
          unfold gKind
          dsimp only
          split_ifs with c1
          · exact absurd c1 (not_or.mpr h1)
          · rfl
        exact ⟨hk, h1.2, by unfold gIns; simp [hg, hk, a, b], fun Z => evalX_union h2 Z⟩
      · right; right; right
        have hk : gKind m s F hgate g = 3 := by
          unfold gKind; simp [h0, h1.1, h1.2, h2, a, b]
        have h3 : F (m + g) = F a ∩ F b := by
          rcases gSpec hgate hg with hs | hs | hs | hs
          · exact absurd hs h2
          · exact absurd hs h1.1
          · exact absurd hs h0
          · exact hs
        exact ⟨hk, h1.2, by unfold gIns; simp [hg, hk, a, b], fun Z => evalX_inter h3 Z⟩

lemma evalX_congr_ins {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    {g : ℕ} (hg : g < s) {Z1 Z2 : Finset ℕ}
    (h : ∀ u ∈ gIns m s F hgate g, evalX F u Z1 ↔ evalX F u Z2) :
    evalX F (m + g) Z1 ↔ evalX F (m + g) Z2 := by
  rcases gKind_spec hgate hg with ⟨_, _, hX⟩ | ⟨_, hi, hX⟩ | ⟨_, _, hi, hX⟩ | ⟨_, _, hi, hX⟩
  · exact ⟨fun h1 => absurd h1 (hX Z1), fun h2 => absurd h2 (hX Z2)⟩
  · rw [hX Z1, hX Z2]
    exact h (gA m s F hgate g) (by rw [hi]; simp)
  · rw [hX Z1, hX Z2]
    have ha := h (gA m s F hgate g) (by rw [hi]; simp)
    have hb := h (gB m s F hgate g) (by rw [hi]; simp)
    tauto
  · rw [hX Z1, hX Z2]
    have ha := h (gA m s F hgate g) (by rw [hi]; simp)
    have hb := h (gB m s F hgate g) (by rw [hi]; simp)
    tauto

-- Part 3: Backward reachability from output o

noncomputable def reachDown (m s : ℕ) (F : ℕ → Set (Finset ℕ))
    (hgate : GateSpec F m s) :
    ℕ → Finset ℕ → Finset ℕ
  | 0, W => W
  | n + 1, W =>
    reachDown m s F hgate n (if m + n ∈ W then W ∪ gIns m s F hgate n else W)

lemma sub_reachDown {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s) :
    ∀ (n : ℕ) (W : Finset ℕ), W ⊆ reachDown m s F hgate n W
  | 0, _ => Finset.Subset.refl _
  | n + 1, W => by
    unfold reachDown
    have h1 : W ⊆ (if m + n ∈ W then W ∪ gIns m s F hgate n else W) := by
      split_ifs
      · exact Finset.subset_union_left
      · exact Finset.Subset.refl W
    exact h1.trans (sub_reachDown hgate n _)

lemma reachDown_mem_or_lt {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s) :
    ∀ (n : ℕ), n ≤ s → ∀ (W : Finset ℕ) (w : ℕ),
      w ∈ reachDown m s F hgate n W → w ∈ W ∨ w < m + n
  | 0, _, _, _, hw => Or.inl hw
  | n + 1, hn, W, w, hw => by
    unfold reachDown at hw
    rcases reachDown_mem_or_lt hgate n (by omega) _ w hw with hw' | hlt
    · split_ifs at hw' with hmem
      · rcases Finset.mem_union.mp hw' with hW | hins
        · exact Or.inl hW
        · have hlt' : w < m + n := gIns_lt hgate (g := n) (by omega) hins
          exact Or.inr (by omega)
      · exact Or.inl hw'
    · exact Or.inr (by omega)

lemma reachDown_lt_bound {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s)
    (n : ℕ) (hn : n ≤ s) (W : Finset ℕ) (hW : ∀ w ∈ W, w < m + s)
    (w : ℕ) (hw : w ∈ reachDown m s F hgate n W) : w < m + s := by
  rcases reachDown_mem_or_lt hgate n hn W w hw with h | h
  · exact hW w h
  · omega

lemma reachDown_closed {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s) :
    ∀ (n : ℕ), n ≤ s → ∀ (W : Finset ℕ) (k : ℕ), k < n →
      m + k ∈ reachDown m s F hgate n W → gIns m s F hgate k ⊆ reachDown m s F hgate n W
  | 0, _, _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, hn, W, k, hk, hmem => by
    unfold reachDown at hmem ⊢
    set W' := if m + n ∈ W then W ∪ gIns m s F hgate n else W
    rcases (show k < n ∨ k = n by omega) with hkn | rfl
    · exact reachDown_closed hgate n (by omega) W' k hkn hmem
    · have hmW' : m + k ∈ W' := by
        rcases reachDown_mem_or_lt hgate k (by omega) W' (m + k) hmem with h | h
        · exact h
        · omega
      have hmW : m + k ∈ W := by
        dsimp only [W'] at hmW'
        split_ifs at hmW' with hm
        · exact hm
        · exact hmW'
      have hsubW' : gIns m s F hgate k ⊆ W' := by
        dsimp only [W']
        simp only [hmW, ite_true]
        exact Finset.subset_union_right
      exact hsubW'.trans (sub_reachDown hgate k W')

lemma reachDown_parent {m s : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hgate : GateSpec F m s) :
    ∀ (n : ℕ), n ≤ s → ∀ (W : Finset ℕ) (w : ℕ),
      w ∈ reachDown m s F hgate n W →
      w ∈ W ∨ ∃ k < n, m + k ∈ reachDown m s F hgate n W ∧ w ∈ gIns m s F hgate k
  | 0, _, _, _, hw => Or.inl hw
  | n + 1, hn, W, w, hw => by
    unfold reachDown at hw ⊢
    set W' := if m + n ∈ W then W ∪ gIns m s F hgate n else W
    rcases reachDown_parent hgate n (by omega) W' w hw with hw' | ⟨k, hkn, hmk, hwk⟩
    · dsimp only [W'] at hw'
      split_ifs at hw' with hmn
      · rcases Finset.mem_union.mp hw' with hW | hwg
        · exact Or.inl hW
        · refine Or.inr ⟨n, Nat.lt_succ_self n, ?_, hwg⟩
          exact sub_reachDown hgate n W' (by dsimp only [W']; simp only [hmn, ite_true]; exact Finset.mem_union_left _ hmn)
      · exact Or.inl hw'
    · exact Or.inr ⟨k, by omega, hmk, hwk⟩

-- Part 4: Generic fuel-bounded chain traversal

noncomputable def chainTerm (canStep : ℕ → Prop) (step : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, w => w
  | n + 1, w => @ite ℕ (canStep w) (Classical.propDecidable _) (chainTerm canStep step n (step w)) w

noncomputable def chainPath (canStep : ℕ → Prop) (step : ℕ → ℕ) : ℕ → ℕ → Finset ℕ
  | 0, w => {w}
  | n + 1, w =>
    @ite (Finset ℕ) (canStep w) (Classical.propDecidable _)
      (insert w (chainPath canStep step n (step w))) {w}

lemma chainTerm_mem_path (canStep : ℕ → Prop) (step : ℕ → ℕ) :
    ∀ n w, chainTerm canStep step n w ∈ chainPath canStep step n w
  | 0, w => Finset.mem_singleton_self w
  | n + 1, w => by
    unfold chainTerm chainPath
    split_ifs
    · exact Finset.mem_insert_of_mem (chainTerm_mem_path canStep step n (step w))
    · exact Finset.mem_singleton_self w

lemma self_mem_chainPath (canStep : ℕ → Prop) (step : ℕ → ℕ) :
    ∀ n w, w ∈ chainPath canStep step n w
  | 0, w => Finset.mem_singleton_self w
  | n + 1, w => by
    unfold chainPath
    split_ifs
    · exact Finset.mem_insert_self w _
    · exact Finset.mem_singleton_self w

lemma chainPath_step (canStep : ℕ → Prop) (step : ℕ → ℕ) :
    ∀ n w u, u ∈ chainPath canStep step n w → u ≠ chainTerm canStep step n w →
      canStep u ∧ step u ∈ chainPath canStep step n w
  | 0, w, u, hu, hne => by
    unfold chainPath at hu
    unfold chainTerm at hne
    rw [Finset.mem_singleton] at hu
    exact absurd hu hne
  | n + 1, w, u, hu, hne => by
    unfold chainPath at hu ⊢
    unfold chainTerm at hne
    split_ifs at hu hne ⊢ with hcs
    · rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact ⟨hcs, Finset.mem_insert_of_mem (self_mem_chainPath canStep step n (step u))⟩
      · obtain ⟨h1, h2⟩ := chainPath_step canStep step n (step w) u hu' hne
        exact ⟨h1, Finset.mem_insert_of_mem h2⟩
    · rw [Finset.mem_singleton] at hu
      exact absurd hu hne

lemma chainPath_pred (canStep : ℕ → Prop) (step : ℕ → ℕ) (P : ℕ → Prop)
    (hstep : ∀ w, canStep w → P w → P (step w)) :
    ∀ n w, P w → ∀ u ∈ chainPath canStep step n w, P u
  | 0, w, hw, u, hu => by
    unfold chainPath at hu
    rw [Finset.mem_singleton] at hu
    exact hu ▸ hw
  | n + 1, w, hw, u, hu => by
    unfold chainPath at hu
    split_ifs at hu with hcs
    · rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact hw
      · exact chainPath_pred canStep step P hstep n (step w) (hstep w hcs hw) u hu'
    · rw [Finset.mem_singleton] at hu
      exact hu ▸ hw

lemma chainPath_bounds (canStep : ℕ → Prop) (step : ℕ → ℕ)
    (hlt : ∀ w, canStep w → w < step w) :
    ∀ n w u, u ∈ chainPath canStep step n w → w ≤ u ∧ u ≤ chainTerm canStep step n w
  | 0, w, u, hu => by
    unfold chainPath at hu
    unfold chainTerm
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨le_rfl, le_rfl⟩
  | n + 1, w, u, hu => by
    unfold chainPath at hu
    unfold chainTerm
    split_ifs at hu ⊢ with hcs
    · have hltw := hlt w hcs
      have hst_le : step w ≤ chainTerm canStep step n (step w) :=
        (chainPath_bounds canStep step hlt n (step w) (step w) (self_mem_chainPath canStep step n (step w))).2
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact ⟨le_rfl, by omega⟩
      · obtain ⟨h1, h2⟩ := chainPath_bounds canStep step hlt n (step w) u hu'
        exact ⟨by omega, h2⟩
    · rw [Finset.mem_singleton] at hu
      subst hu
      exact ⟨le_rfl, le_rfl⟩

lemma chainPath_nonstart (canStep : ℕ → Prop) (step : ℕ → ℕ) (Q : ℕ → Prop)
    (hstep : ∀ w, canStep w → Q (step w)) :
    ∀ n w u, u ∈ chainPath canStep step n w → u ≠ w → Q u
  | 0, w, u, hu, hne => by
    unfold chainPath at hu
    rw [Finset.mem_singleton] at hu
    exact absurd hu hne
  | n + 1, w, u, hu, hne => by
    unfold chainPath at hu
    split_ifs at hu with hcs
    · rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact absurd rfl hne
      · by_cases hust : u = step w
        · exact hust ▸ hstep w hcs
        · exact chainPath_nonstart canStep step Q hstep n (step w) u hu' hust
    · rw [Finset.mem_singleton] at hu
      exact absurd hu hne

lemma chainTerm_stop (canStep : ℕ → Prop) (step : ℕ → ℕ) (B : ℕ)
    (hbound : ∀ w, canStep w → w < B)
    (hlt : ∀ w, canStep w → w < step w) :
    ∀ n w, B ≤ w + n → ¬ canStep (chainTerm canStep step n w)
  | 0, w, hle => by
    unfold chainTerm
    intro hcs
    have := hbound w hcs
    omega
  | n + 1, w, hle => by
    unfold chainTerm
    split_ifs with hcs
    · have := hlt w hcs
      exact chainTerm_stop canStep step B hbound hlt n (step w) (by omega)
    · exact hcs

-- Part 5: Main proof

lemma main_proof (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (s o : ℕ) (F : ℕ → Set (Finset ℕ))
    (ho : o < N + N + s)
    (hin : ∀ v < N + N, F v = {Z | v ∈ Z})
    (hgate : GateSpec F (N + N) s)
    (hpair : ∀ (p l : Fin N), I p l → evalX F o {p.val, N + l.val})
    (hX_neg : ∀ (T : Finset (Fin N)) (Z : Finset ℕ),
      T.card ≤ q →
      (∀ u ∈ Z, u < N + N) →
      (∀ p : Fin N, p.val ∈ Z → ∀ l ∈ T, ¬ I p l) →
      (∀ l : Fin N, N + l.val ∈ Z → l ∈ T) →
      ¬ evalX F o Z) :
    3 * N ≤ s + 1 := by
  classical
  have hX_pos : ∀ (p l : Fin N) (Z : Finset ℕ),
      I p l → p.val ∈ Z → N + l.val ∈ Z → evalX F o Z := by
    intro p l Z hI hp hl
    refine evalX_mono hin hgate ?_ o ho (hpair p l hI)
    exact Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hl)
  have hX_neg_pt : ∀ p : Fin N, ¬ evalX F o {p.val} := by
    intro p
    refine hX_neg ∅ {p.val} (by simp) ?_ ?_ ?_
    · intro u hu; rw [Finset.mem_singleton] at hu; subst hu; omega
    · intro _ _ _ hl; simp at hl
    · intro l hl; rw [Finset.mem_singleton] at hl; omega
  have hX_neg_ln : ∀ l : Fin N, ¬ evalX F o {N + l.val} := by
    intro l
    refine hX_neg {l} {N + l.val} (by simp; omega) ?_ ?_ ?_
    · intro u hu; rw [Finset.mem_singleton] at hu; subst hu; omega
    · intro p hp; rw [Finset.mem_singleton] at hp; omega
    · intro l' hl'; rw [Finset.mem_singleton] at hl'
      have : l' = l := Fin.ext (by omega)
      simp [this]
  have hX_neg_two_pts : ∀ p1 p2 : Fin N, ¬ evalX F o {p1.val, p2.val} := by
    intro p1 p2
    refine hX_neg ∅ {p1.val, p2.val} (by simp) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    · intro _ _ _ hl; simp at hl
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with h | h <;> omega
  have hX_neg_noninc : ∀ p l : Fin N, ¬ I p l → ¬ evalX F o {p.val, N + l.val} := by
    intro p l hnI
    refine hX_neg {l} {p.val, N + l.val} (by simp; omega) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    · intro p' hp' l' hl'
      rw [Finset.mem_singleton] at hl'
      subst hl'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
      rcases hp' with h | h
      · have : p' = p := Fin.ext h
        rwa [this]
      · omega
    · intro l' hl'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
      rcases hl' with h | h
      · omega
      · have : l' = l := Fin.ext (by omega)
        simp [this]
  have hX_neg_two_lns : ∀ l1 l2 : Fin N, ¬ evalX F o {N + l1.val, N + l2.val} := by
    intro l1 l2
    refine hX_neg {l1, l2} {N + l1.val, N + l2.val} (Finset.card_le_two.trans hq) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> omega
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h <;> omega
    · intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl ⊢
      rcases hl with h | h
      · left; exact Fin.ext (by omega)
      · right; exact Fin.ext (by omega)
  -- Reachable wires R and gates GR
  let R : Finset ℕ := reachDown (N + N) s F hgate s {o}
  have hoR : o ∈ R := sub_reachDown hgate s {o} (Finset.mem_singleton_self o)
  have hR_lt : ∀ w ∈ R, w < N + N + s := fun w hw =>
    reachDown_lt_bound hgate s le_rfl {o} (by intro u hu; rw [Finset.mem_singleton] at hu; omega) w hw
  have hR_closed : ∀ k < s, N + N + k ∈ R → gIns (N + N) s F hgate k ⊆ R :=
    fun k hk hm => reachDown_closed hgate s le_rfl {o} k hk hm
  let GR : Finset ℕ := R.filter (fun w => N + N ≤ w)
  let outs : ℕ → Finset ℕ := fun w => GR.filter (fun u => w ∈ gIns (N + N) s F hgate (u - (N + N)))
  have houts_nonempty : ∀ w ∈ R, w ≠ o → (outs w).Nonempty := by
    intro w hw hne
    rcases reachDown_parent hgate s le_rfl {o} w hw with h | ⟨k, hks, hmk, hwk⟩
    · rw [Finset.mem_singleton] at h; exact absurd h hne
    · refine ⟨N + N + k, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmk, by omega⟩, ?_⟩⟩
      have : N + N + k - (N + N) = k := by omega
      rwa [this]
  have houts_sub_GR : ∀ w u, u ∈ outs w → u ∈ GR := fun _ _ hu => (Finset.mem_filter.mp hu).1
  have houts_lt : ∀ w u, u ∈ outs w → w < u := by
    intro w u hu
    have h1 := Finset.mem_filter.mp hu
    have h2 := Finset.mem_filter.mp h1.1
    have hult : u < N + N + s := hR_lt u h2.1
    have hlt := gIns_lt hgate (g := u - (N + N)) (by omega) h1.2
    omega
  have hX_dep_R : ∀ (Z1 Z2 : Finset ℕ),
      (∀ v < N + N, v ∈ R → (v ∈ Z1 ↔ v ∈ Z2)) →
      ∀ w ∈ R, evalX F w Z1 ↔ evalX F w Z2 := by
    intro Z1 Z2 hagree w
    refine Nat.strongRecOn (motive := fun n => n ∈ R → (evalX F n Z1 ↔ evalX F n Z2)) w ?_
    intro n ih hn
    by_cases hlt : n < N + N
    · rw [evalX_input hin hlt Z1, evalX_input hin hlt Z2]
      exact hagree n hlt hn
    · set k := n - (N + N)
      have hnk : n = N + N + k := by omega
      have hks : k < s := by have := hR_lt n hn; omega
      rw [hnk]
      apply evalX_congr_ins hgate hks
      intro u hu
      have huR : u ∈ R := hR_closed k hks (hnk ▸ hn) hu
      have hult : u < n := by have := gIns_lt hgate hks hu; omega
      exact ih u hult huR
  have hrange_sub_R : Finset.range (N + N) ⊆ R := by
    intro v hv
    rw [Finset.mem_range] at hv
    by_contra hvR
    by_cases hvN : v < N
    · let p : Fin N := ⟨v, hvN⟩
      obtain ⟨l, hI⟩ := exists_line_through hq hN hdeg huniq p
      have heq := hX_dep_R {N + l.val} {p.val, N + l.val} (by
        intro u _ huR
        have hne : u ≠ p.val := by
          intro he
          rw [he] at huR
          exact hvR huR
        simp [hne]) o hoR
      have h1 : evalX F o {p.val, N + l.val} := hX_pos p l _ hI (by simp) (by simp)
      exact hX_neg_ln l (heq.mpr h1)
    · let l : Fin N := ⟨v - N, by omega⟩
      have hvl : N + l.val = v := by dsimp [l]; omega
      obtain ⟨p, hI⟩ := exists_point_on hdeg l
      have heq := hX_dep_R {p.val} {p.val, N + l.val} (by
        intro u _ huR
        have hne : u ≠ N + l.val := fun he => hvR (hvl ▸ he ▸ huR)
        simp [hne]) o hoR
      have h1 : evalX F o {p.val, N + l.val} := hX_pos p l _ hI (by simp) (by simp)
      exact hX_neg_pt p (heq.mpr h1)
  have ho_ge_m : N + N ≤ o := by
    by_contra hlt
    push Not at hlt
    have h1 : evalX F o {o} := (evalX_input hin hlt {o}).mpr (Finset.mem_singleton_self o)
    by_cases hoN : o < N
    · exact hX_neg_pt ⟨o, hoN⟩ h1
    · let l : Fin N := ⟨o - N, by omega⟩
      have : N + l.val = o := by dsimp [l]; omega
      exact hX_neg_ln l (this.symm ▸ h1)
  have hoGR : o ∈ GR := Finset.mem_filter.mpr ⟨hoR, ho_ge_m⟩
  have hGR_le_s : GR.card ≤ s := by
    let f : ℕ → ℕ := fun u => u - (N + N)
    have hinj : Set.InjOn f (GR : Set ℕ) := by
      intro u1 hu1 u2 hu2 heq
      have h1 := (Finset.mem_filter.mp hu1).2
      have h2 := (Finset.mem_filter.mp hu2).2
      dsimp only [f] at heq
      omega
    calc GR.card = (GR.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range s).card := Finset.card_le_card (by
          intro k hk
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
          have h1 := Finset.mem_filter.mp hu
          have h2 := hR_lt u h1.1
          dsimp only [f]
          exact Finset.mem_range.mpr (by omega))
      _ = s := Finset.card_range s
  -- Edge counting: N + N + Branch.card ≤ GR.card + 1
  let Branch : Finset ℕ := (R.erase o).filter (fun w => 2 ≤ (outs w).card)
  have hedge_count : N + N + Branch.card ≤ GR.card + 1 := by
    have hR_split : R = Finset.range (N + N) ∪ GR := by
      ext w
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter, GR]
      constructor
      · intro hw
        by_cases hlt : w < N + N
        · exact Or.inl hlt
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (hlt | ⟨hw, _⟩)
        · exact hrange_sub_R (Finset.mem_range.mpr hlt)
        · exact hw
    have hR_disj : Disjoint (Finset.range (N + N)) GR := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_range] at hw1
      have := (Finset.mem_filter.mp hw2).2
      omega
    have hR_card : R.card = N + N + GR.card := by
      rw [hR_split, Finset.card_union_of_disjoint hR_disj, Finset.card_range]
    have hlower : (R.erase o).card + Branch.card ≤ ∑ w ∈ R.erase o, (outs w).card := by
      have h1 : ∀ w ∈ R.erase o,
          (if 2 ≤ (outs w).card then 2 else 1) ≤ (outs w).card := by
        intro w hw
        have hmem := Finset.mem_erase.mp hw
        have hpos : 1 ≤ (outs w).card := Finset.card_pos.mpr (houts_nonempty w hmem.2 hmem.1)
        split_ifs with h2 <;> omega
      have h2 : ∑ w ∈ R.erase o, (if 2 ≤ (outs w).card then 2 else 1) =
          (R.erase o).card + Branch.card := by
        have h3 : ∀ w ∈ R.erase o,
            (if 2 ≤ (outs w).card then (2 : ℕ) else 1) =
            1 + (if 2 ≤ (outs w).card then 1 else 0) := by
          intro w _; split_ifs <;> omega
        rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
          mul_one, Finset.sum_boole]
        rfl
      rw [← h2]
      exact Finset.sum_le_sum h1
    have hupper : ∑ w ∈ R.erase o, (outs w).card ≤ 2 * GR.card := by
      calc ∑ w ∈ R.erase o, (outs w).card
          ≤ ∑ w ∈ R, (outs w).card :=
            Finset.sum_le_sum_of_subset (Finset.erase_subset o R)
        _ = ∑ w ∈ R, ∑ u ∈ GR, (if w ∈ gIns (N + N) s F hgate (u - (N + N)) then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro w _
            simp only [outs, Finset.sum_boole, Nat.cast_id]
        _ = ∑ u ∈ GR, ∑ w ∈ R, (if w ∈ gIns (N + N) s F hgate (u - (N + N)) then 1 else 0) :=
            Finset.sum_comm
        _ ≤ ∑ u ∈ GR, 2 := by
            apply Finset.sum_le_sum
            intro u _
            have hle : (R.filter (fun w => w ∈ gIns (N + N) s F hgate (u - (N + N)))).card ≤
                (gIns (N + N) s F hgate (u - (N + N))).card :=
              Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)
            simpa only [Finset.sum_boole, Nat.cast_id] using
              hle.trans (gIns_card_le_two hgate (u - (N + N)))
        _ = 2 * GR.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have herase : (R.erase o).card = N + N + GR.card - 1 := by
      rw [Finset.card_erase_of_mem hoR, hR_card]
    have hGR_pos : 1 ≤ GR.card := Finset.card_pos.mpr ⟨o, hoGR⟩
    omega
  -- OR/COPY paths and endpoints
  let canStep : ℕ → Prop := fun w =>
    w ∈ R ∧ w ≠ o ∧ (outs w).card = 1 ∧
      ∀ u ∈ outs w, gKind (N + N) s F hgate (u - (N + N)) = 1 ∨
        gKind (N + N) s F hgate (u - (N + N)) = 2
  let step : ℕ → ℕ := fun w =>
    if h : (outs w).Nonempty then Classical.choose h else 0
  have hstep_mem : ∀ w, (outs w).Nonempty → step w ∈ outs w := by
    intro w h
    simp only [step, h, dite_true]
    exact Classical.choose_spec h
  have houts_eq_singleton : ∀ w, (outs w).card = 1 → outs w = {step w} := by
    intro w hc
    have hne : (outs w).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
    have hsm : step w ∈ outs w := hstep_mem w hne
    rw [hu, Finset.mem_singleton] at hsm
    rw [hu, hsm]
  have hstep_lt : ∀ w, canStep w → w < step w := by
    intro w hcs
    have hne : (outs w).Nonempty := Finset.card_pos.mp (by omega : 0 < (outs w).card)
    exact houts_lt w _ (hstep_mem w hne)
  have hstep_R : ∀ w, canStep w → w ∈ R → step w ∈ R := by
    intro w hcs _
    have hne : (outs w).Nonempty := Finset.card_pos.mp (by omega : 0 < (outs w).card)
    exact (Finset.mem_filter.mp (houts_sub_GR w _ (hstep_mem w hne))).1
  have hstep_kind : ∀ w, canStep w →
      N + N ≤ step w ∧ (gKind (N + N) s F hgate (step w - (N + N)) = 1 ∨
        gKind (N + N) s F hgate (step w - (N + N)) = 2) := by
    intro w hcs
    have hne : (outs w).Nonempty := Finset.card_pos.mp (by omega : 0 < (outs w).card)
    have hsm := hstep_mem w hne
    exact ⟨(Finset.mem_filter.mp (houts_sub_GR w _ hsm)).2, hcs.2.2.2 _ hsm⟩
  have hstep_evalX : ∀ Z w, canStep w → evalX F w Z → evalX F (step w) Z := by
    intro Z w hcs hw
    have hne : (outs w).Nonempty := Finset.card_pos.mp (by omega : 0 < (outs w).card)
    have hsm := hstep_mem w hne
    have hstGR := houts_sub_GR w _ hsm
    have hstR : step w ∈ R := (Finset.mem_filter.mp hstGR).1
    have hst_ge : N + N ≤ step w := (Finset.mem_filter.mp hstGR).2
    have hst_lt : step w < N + N + s := hR_lt _ hstR
    set k := step w - (N + N)
    have hk : k < s := by omega
    have heq : step w = N + N + k := by omega
    have hwin : w ∈ gIns (N + N) s F hgate k := (Finset.mem_filter.mp hsm).2
    have hkind : gKind (N + N) s F hgate k = 1 ∨ gKind (N + N) s F hgate k = 2 := hcs.2.2.2 _ hsm
    rw [heq]
    rcases gKind_spec hgate hk with ⟨hk0, _, _⟩ | ⟨_, hi, hX⟩ | ⟨_, _, hi, hX⟩ | ⟨hk3, _, _, _⟩
    · rcases hkind with h | h <;> omega
    · rw [hi, Finset.mem_singleton] at hwin
      rw [hX Z, ← hwin]
      exact hw
    · rw [hi, Finset.mem_insert, Finset.mem_singleton] at hwin
      rw [hX Z]
      rcases hwin with hw1 | hw2
      · exact Or.inl (hw1 ▸ hw)
      · exact Or.inr (hw2 ▸ hw)
    · rcases hkind with h | h <;> omega
  let term : ℕ → ℕ := fun w => chainTerm canStep step (N + N + s) w
  let path : ℕ → Finset ℕ := fun w => chainPath canStep step (N + N + s) w
  have hterm_mem_R : ∀ v < N + N, term v ∈ R := fun v hv =>
    chainPath_pred canStep step (fun u => u ∈ R) hstep_R (N + N + s) v
      (hrange_sub_R (Finset.mem_range.mpr hv)) (term v) (chainTerm_mem_path canStep step (N + N + s) v)
  have hterm_stop : ∀ w, ¬ canStep (term w) := fun w =>
    chainTerm_stop canStep step (N + N + s) (fun u hcs => hR_lt u hcs.1) hstep_lt (N + N + s) w (by omega)
  have hterm_of_mem : ∀ v < N + N, ∀ Z : Finset ℕ, v ∈ Z → evalX F (term v) Z := by
    intro v hv Z hvZ
    exact chainPath_pred canStep step (fun u => evalX F u Z) (hstep_evalX Z) (N + N + s) v
      ((evalX_input hin hv Z).mpr hvZ) (term v) (chainTerm_mem_path canStep step (N + N + s) v)
  have hterm_ne_o : ∀ v < N + N, term v ≠ o := by
    intro v hv heq
    have h1 : evalX F o {v} := heq ▸ hterm_of_mem v hv {v} (Finset.mem_singleton_self v)
    by_cases hvN : v < N
    · exact hX_neg_pt ⟨v, hvN⟩ h1
    · let l : Fin N := ⟨v - N, by omega⟩
      have : N + l.val = v := by dsimp [l]; omega
      exact hX_neg_ln l (this.symm ▸ h1)
  have ho_not_mem_path : ∀ v < N + N, o ∉ path v := by
    intro v hv hoP
    by_cases heq : o = term v
    · exact hterm_ne_o v hv heq.symm
    · exact (chainPath_step canStep step (N + N + s) v o hoP heq).1.2.1 rfl
  -- Screening-off Lemma 1: at term v
  have screen_term : ∀ v < N + N, ∀ (Z1 Z2 : Finset ℕ),
      (∀ u, u ≠ v → (u ∈ Z1 ↔ u ∈ Z2)) →
      (evalX F (term v) Z1 ↔ evalX F (term v) Z2) →
      ∀ w ∈ R, w ∉ (path v).erase (term v) → (evalX F w Z1 ↔ evalX F w Z2) := by
    intro v hv Z1 Z2 hagree hterm_eq w
    refine Nat.strongRecOn (motive := fun n =>
      n ∈ R → n ∉ (path v).erase (term v) → (evalX F n Z1 ↔ evalX F n Z2)) w ?_
    intro n ih hnR hnS
    by_cases hnt : n = term v
    · exact hnt ▸ hterm_eq
    · have hnP : n ∉ path v := fun h => hnS (Finset.mem_erase.mpr ⟨hnt, h⟩)
      by_cases hlt : n < N + N
      · have hnv : n ≠ v := fun he => hnP (he ▸ self_mem_chainPath canStep step (N + N + s) v)
        rw [evalX_input hin hlt Z1, evalX_input hin hlt Z2]
        exact hagree n hnv
      · set k := n - (N + N)
        have hnk : n = N + N + k := by omega
        have hks : k < s := by have := hR_lt n hnR; omega
        rw [hnk]
        apply evalX_congr_ins hgate hks
        intro u hu
        have huR : u ∈ R := hR_closed k hks (hnk ▸ hnR) hu
        have hult : u < n := by have := gIns_lt hgate hks hu; omega
        have huS : u ∉ (path v).erase (term v) := by
          intro huE
          have hmem := Finset.mem_erase.mp huE
          obtain ⟨hcs, hstP⟩ := chainPath_step canStep step (N + N + s) v u hmem.2 hmem.1
          have hn_out : n ∈ outs u := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnR, by omega⟩, ?_⟩
            have : n - (N + N) = k := by omega
            rwa [this]
          rw [houts_eq_singleton u hcs.2.2.1, Finset.mem_singleton] at hn_out
          exact hnP (hn_out ▸ hstP)
        exact ih u hult huR huS
  -- Injectivity of term on Finset.range (N + N)
  have term_inj : ∀ v1 < N + N, ∀ v2 < N + N, v1 ≠ v2 → term v1 ≠ term v2 := by
    intro v1 hv1 v2 hv2 hne heq
    have hkill : ∀ (Z0 : Finset ℕ), v2 ∈ Z0 → v1 ∉ Z0 →
        (evalX F o Z0 ↔ evalX F o (insert v1 Z0)) := by
      intro Z0 hv2Z hv1Z
      apply screen_term v1 hv1 Z0 (insert v1 Z0)
      · intro u huv
        simp [huv]
      · have h1 : evalX F (term v1) Z0 := heq ▸ hterm_of_mem v2 hv2 Z0 hv2Z
        have h2 : evalX F (term v1) (insert v1 Z0) :=
          heq ▸ hterm_of_mem v2 hv2 (insert v1 Z0) (Finset.mem_insert_of_mem hv2Z)
        exact ⟨fun _ => h2, fun _ => h1⟩
      · exact hoR
      · intro h; exact ho_not_mem_path v1 hv1 (Finset.mem_erase.mp h).2
    by_cases h1N : v1 < N
    · by_cases h2N : v2 < N
      · let p1 : Fin N := ⟨v1, h1N⟩
        let p2 : Fin N := ⟨v2, h2N⟩
        have hpne : p1 ≠ p2 := fun h => hne (congrArg Fin.val h)
        obtain ⟨l, hp1l, hnp2l⟩ := exists_line_through_not_through hq hN hdeg huniq hpne
        have hiff := hkill {p2.val, N + l.val} (by simp [p2]) (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hne, by omega⟩)
        have hpos : evalX F o (insert v1 {p2.val, N + l.val}) :=
          hX_pos p1 l _ hp1l (by simp [p1]) (by simp)
        exact hX_neg_noninc p2 l hnp2l (hiff.mpr hpos)
      · let p1 : Fin N := ⟨v1, h1N⟩
        let l2 : Fin N := ⟨v2 - N, by omega⟩
        have hv2l : N + l2.val = v2 := by dsimp [l2]; omega
        obtain ⟨l', hl'ne, hp1l'⟩ := exists_line_through_ne hq hN hdeg huniq p1 l2
        have hiff := hkill {N + l2.val, N + l'.val} (by simp [hv2l]) (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨by omega, by omega⟩)
        have hpos : evalX F o (insert v1 {N + l2.val, N + l'.val}) :=
          hX_pos p1 l' _ hp1l' (by simp [p1]) (by simp)
        exact hX_neg_two_lns l2 l' (hiff.mpr hpos)
    · by_cases h2N : v2 < N
      · let l1 : Fin N := ⟨v1 - N, by omega⟩
        let p2 : Fin N := ⟨v2, h2N⟩
        have hv1l : N + l1.val = v1 := by dsimp [l1]; omega
        obtain ⟨p', hp'l1⟩ := exists_point_on hdeg l1
        have hiff := hkill {p2.val, p'.val} (by simp [p2]) (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨by omega, by omega⟩)
        have hpos : evalX F o (insert v1 {p2.val, p'.val}) :=
          hX_pos p' l1 _ hp'l1 (by simp) (by simp [hv1l])
        exact hX_neg_two_pts p2 p' (hiff.mpr hpos)
      · let l1 : Fin N := ⟨v1 - N, by omega⟩
        let l2 : Fin N := ⟨v2 - N, by omega⟩
        have hv1l : N + l1.val = v1 := by dsimp [l1]; omega
        have hv2l : N + l2.val = v2 := by dsimp [l2]; omega
        have hlne : l1 ≠ l2 := fun h => hne (by have := congrArg Fin.val h; omega)
        obtain ⟨p, hpl1, hnpl2⟩ := exists_point_on_not_on hq hdeg huniq hlne
        have hiff := hkill {p.val, N + l2.val} (by simp [hv2l]) (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨by omega, by omega⟩)
        have hpos : evalX F o (insert v1 {p.val, N + l2.val}) :=
          hX_pos p l1 _ hpl1 (by simp) (by simp [hv1l])
        exact hX_neg_noninc p l2 hnpl2 (hiff.mpr hpos)
  -- Helper lemmas for AND-terminated inputs
  have hand_info : ∀ v < N + N, ¬ (2 ≤ (outs (term v)).card) →
      let a := step (term v)
      a ∈ GR ∧ outs (term v) = {a} ∧ term v < a ∧
      gKind (N + N) s F hgate (a - (N + N)) = 3 ∧
      ∃ h ∈ R, h < a ∧ h ≠ term v ∧ h ∉ path v ∧
        gIns (N + N) s F hgate (a - (N + N)) = {term v, h} ∧
        (∀ Z, evalX F a Z ↔ evalX F (term v) Z ∧ evalX F h Z) := by
    intro v hv hnot2
    dsimp only
    have htR : term v ∈ R := hterm_mem_R v hv
    have htne : term v ≠ o := hterm_ne_o v hv
    have hpos : 1 ≤ (outs (term v)).card :=
      Finset.card_pos.mpr (houts_nonempty (term v) htR htne)
    have hc1 : (outs (term v)).card = 1 := by omega
    set a := step (term v)
    have houts_a : outs (term v) = {a} := houts_eq_singleton (term v) hc1
    have ha_out : a ∈ outs (term v) := by rw [houts_a]; exact Finset.mem_singleton_self a
    have haGR : a ∈ GR := houts_sub_GR (term v) a ha_out
    have haR : a ∈ R := (Finset.mem_filter.mp haGR).1
    have ha_ge : N + N ≤ a := (Finset.mem_filter.mp haGR).2
    have ha_lt : a < N + N + s := hR_lt a haR
    have hta : term v < a := houts_lt (term v) a ha_out
    set k := a - (N + N)
    have hks : k < s := by omega
    have hak : a = N + N + k := by omega
    have htin : term v ∈ gIns (N + N) s F hgate k := (Finset.mem_filter.mp ha_out).2
    have hstop : ¬ canStep (term v) := hterm_stop v
    have hkind3 : gKind (N + N) s F hgate k = 3 := by
      rcases gKind_spec hgate hks with ⟨hk0, hi, _⟩ | ⟨hk1, _, _⟩ | ⟨hk2, _, _, _⟩ | ⟨hk3, _, _, _⟩
      · rw [hi] at htin; exact absurd htin (Finset.notMem_empty _)
      · exfalso; apply hstop
        refine ⟨htR, htne, hc1, fun u hu => ?_⟩
        rw [houts_a, Finset.mem_singleton] at hu
        subst hu; exact Or.inl hk1
      · exfalso; apply hstop
        refine ⟨htR, htne, hc1, fun u hu => ?_⟩
        rw [houts_a, Finset.mem_singleton] at hu
        subst hu; exact Or.inr hk2
      · exact hk3
    rcases gKind_spec hgate hks with ⟨hk0, _, _⟩ | ⟨hk1, _, _⟩ | ⟨hk2, _, _, _⟩ | ⟨_, hab, hi, hX⟩
    · omega
    · omega
    · omega
    · have hmem_pair : term v = gA (N + N) s F hgate k ∨ term v = gB (N + N) s F hgate k := by
        rw [hi, Finset.mem_insert, Finset.mem_singleton] at htin
        exact htin
      have hsubR : gIns (N + N) s F hgate k ⊆ R := hR_closed k hks (hak ▸ haR)
      have hex_h : ∃ h, h ≠ term v ∧ gIns (N + N) s F hgate k = {term v, h} ∧
          (∀ Z, evalX F a Z ↔ evalX F (term v) Z ∧ evalX F h Z) := by
        rcases hmem_pair with heq | heq
        · refine ⟨gB (N + N) s F hgate k, by omega, by rw [hi, heq], fun Z => ?_⟩
          rw [hak, hX Z, heq]
        · refine ⟨gA (N + N) s F hgate k, by omega, ?_, fun Z => ?_⟩
          · rw [hi, heq, Finset.pair_comm]
          · rw [hak, hX Z, heq, and_comm]
      obtain ⟨h, hne_t, hi_eq, hXa⟩ := hex_h
      have hh_in : h ∈ gIns (N + N) s F hgate k := by rw [hi_eq]; simp
      have hhR : h ∈ R := hsubR hh_in
      have hha : h < a := by have := gIns_lt hgate hks hh_in; omega
      have hh_notP : h ∉ path v := by
        intro hhP
        obtain ⟨hcs, hstP⟩ := chainPath_step canStep step (N + N + s) v h hhP hne_t
        have ha_outh : a ∈ outs h := Finset.mem_filter.mpr ⟨haGR, hh_in⟩
        rw [houts_eq_singleton h hcs.2.2.1, Finset.mem_singleton] at ha_outh
        have haP : a ∈ path v := ha_outh ▸ hstP
        have hle : a ≤ term v := (chainPath_bounds canStep step hstep_lt (N + N + s) v a haP).2
        omega
      exact ⟨haGR, houts_a, hta, hkind3, h, hhR, hha, hne_t, hh_notP, hi_eq, hXa⟩
  -- Screening-off Lemmas 2 & 3 for AND-terminated inputs
  have screen_and_aux : ∀ v < N + N, ∀ a, outs (term v) = {a} →
      ∀ (Z1 Z2 : Finset ℕ),
      (∀ u, u ≠ v → (u ∈ Z1 ↔ u ∈ Z2)) →
      ∀ (P : ℕ → Prop),
      (∀ u w, u < w → P w → P u) →
      (P a → (evalX F a Z1 ↔ evalX F a Z2)) →
      ∀ w ∈ R, w ∉ path v → P w → (evalX F w Z1 ↔ evalX F w Z2) := by
    intro v hv a houts_a Z1 Z2 hagree P hPdown hPa w
    refine Nat.strongRecOn (motive := fun n =>
      n ∈ R → n ∉ path v → P n → (evalX F n Z1 ↔ evalX F n Z2)) w ?_
    intro n ih hnR hnP hPn
    by_cases hna : n = a
    · subst hna; exact hPa hPn
    · by_cases hlt : n < N + N
      · have hnv : n ≠ v := fun he => hnP (he ▸ self_mem_chainPath canStep step (N + N + s) v)
        rw [evalX_input hin hlt Z1, evalX_input hin hlt Z2]
        exact hagree n hnv
      · set k := n - (N + N)
        have hnk : n = N + N + k := by omega
        have hks : k < s := by have := hR_lt n hnR; omega
        rw [hnk]
        apply evalX_congr_ins hgate hks
        intro u hu
        have huR : u ∈ R := hR_closed k hks (hnk ▸ hnR) hu
        have hult : u < n := by have := gIns_lt hgate hks hu; omega
        have huP : u ∉ path v := by
          intro hu_in
          have hn_out : n ∈ outs u := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnR, by omega⟩, ?_⟩
            have : n - (N + N) = k := by omega
            rwa [this]
          by_cases hut : u = term v
          · rw [hut, houts_a, Finset.mem_singleton] at hn_out
            exact hna hn_out
          · obtain ⟨hcs, hstP⟩ := chainPath_step canStep step (N + N + s) v u hu_in hut
            rw [houts_eq_singleton u hcs.2.2.1, Finset.mem_singleton] at hn_out
            exact hnP (hn_out ▸ hstP)
        exact ih u hult huR huP (hPdown u n hult hPn)
  have indep_below_and : ∀ v < N + N, ∀ a, outs (term v) = {a} →
      ∀ (Z1 Z2 : Finset ℕ),
      (∀ u, u ≠ v → (u ∈ Z1 ↔ u ∈ Z2)) →
      ∀ w ∈ R, w ∉ path v → w < a → (evalX F w Z1 ↔ evalX F w Z2) := by
    intro v hv a houts_a Z1 Z2 hagree w hwR hwP hwa
    exact screen_and_aux v hv a houts_a Z1 Z2 hagree (fun n => n < a)
      (fun _ _ h1 h2 => lt_trans h1 h2) (fun h => absurd h (lt_irrefl a)) w hwR hwP hwa
  have screen_and : ∀ v < N + N, ∀ a, outs (term v) = {a} →
      ∀ (Z1 Z2 : Finset ℕ),
      (∀ u, u ≠ v → (u ∈ Z1 ↔ u ∈ Z2)) →
      (evalX F a Z1 ↔ evalX F a Z2) →
      (evalX F o Z1 ↔ evalX F o Z2) := by
    intro v hv a houts_a Z1 Z2 hagree haeq
    exact screen_and_aux v hv a houts_a Z1 Z2 hagree (fun _ => True)
      (fun _ _ _ _ => trivial) (fun _ => haeq) o hoR (ho_not_mem_path v hv) trivial
  -- No incident pair (p, l) can both be AND-terminated
  have not_both_and : ∀ (p l : Fin N), I p l →
      ¬ (¬ (2 ≤ (outs (term p.val)).card) ∧ ¬ (2 ≤ (outs (term (N + l.val))).card)) := by
    intro p l hI ⟨hpA, hlA⟩
    let v1 := p.val
    let v2 := N + l.val
    have hv1 : v1 < N + N := by dsimp [v1]; omega
    have hv2 : v2 < N + N := by dsimp [v2]; omega
    have hv12 : v1 ≠ v2 := by dsimp [v1, v2]; omega
    obtain ⟨ha1GR, houts1, _, hkind1, h1, hh1R, hh1a1, _, hh1notP1, hi1, hXa1⟩ :=
      hand_info v1 hv1 hpA
    obtain ⟨ha2GR, houts2, _, hkind2, h2, hh2R, hh2a2, _, hh2notP2, hi2, hXa2⟩ :=
      hand_info v2 hv2 hlA
    set a1 := step (term v1)
    set a2 := step (term v2)
    have hnot_in_path : ∀ v < N + N, ∀ u, u ∈ GR →
        gKind (N + N) s F hgate (u - (N + N)) = 3 → u ∉ path v := by
      intro v hv u huGR hk3 huP
      have hne : u ≠ v := by have := (Finset.mem_filter.mp huGR).2; omega
      have hk := (chainPath_nonstart canStep step
        (fun x => N + N ≤ x ∧ (gKind (N + N) s F hgate (x - (N + N)) = 1 ∨
          gKind (N + N) s F hgate (x - (N + N)) = 2))
        hstep_kind (N + N + s) v u huP hne).2
      rcases hk with h | h <;> omega
    rcases lt_trichotomy a1 a2 with hlt | heq | hgt
    · -- Case 1: a1 < a2
      have hh1_notP2 : h1 ∉ path v2 := by
        intro hh1P2
        have ha1_out : a1 ∈ outs h1 := by
          refine Finset.mem_filter.mpr ⟨ha1GR, ?_⟩
          rw [hi1]; simp
        by_cases heqt : h1 = term v2
        · rw [heqt, houts2, Finset.mem_singleton] at ha1_out
          omega
        · obtain ⟨hcs, hstP⟩ := chainPath_step canStep step (N + N + s) v2 h1 hh1P2 heqt
          rw [houts_eq_singleton h1 hcs.2.2.1, Finset.mem_singleton] at ha1_out
          exact hnot_in_path v2 hv2 a1 ha1GR hkind1 (ha1_out ▸ hstP)
      have hh1_lt2 : h1 < a2 := lt_trans hh1a1 hlt
      have hiff1 : evalX F h1 ∅ ↔ evalX F h1 {v2} :=
        indep_below_and v2 hv2 a2 houts2 ∅ {v2} (fun u huv2 => by simp [huv2]) h1 hh1R hh1_notP2 hh1_lt2
      have hn1 : ¬ evalX F h1 {v2} := fun hx =>
        not_evalX_empty hin hgate (hR_lt h1 hh1R) (hiff1.mpr hx)
      have hiff2 : evalX F h1 {v2} ↔ evalX F h1 {v1, v2} :=
        indep_below_and v1 hv1 a1 houts1 {v2} {v1, v2} (fun u huv1 => by simp [huv1]) h1 hh1R hh1notP1 hh1a1
      have hn2 : ¬ evalX F h1 {v1, v2} := fun hx => hn1 (hiff2.mpr hx)
      have ha_iff : evalX F a1 {v2} ↔ evalX F a1 {v1, v2} := by
        rw [hXa1 {v2}, hXa1 {v1, v2}]
        exact ⟨fun h => absurd h.2 hn1, fun h => absurd h.2 hn2⟩
      have ho_iff := screen_and v1 hv1 a1 houts1 {v2} {v1, v2} (fun u huv1 => by simp [huv1]) ha_iff
      have hpos : evalX F o {v1, v2} := hX_pos p l _ hI (by simp [v1]) (by simp [v2])
      exact hX_neg_ln l (ho_iff.mpr hpos)
    · -- Case 2: a1 = a2
      have htne : term v1 ≠ term v2 := term_inj v1 hv1 v2 hv2 hv12
      have ht2_in : term v2 ∈ gIns (N + N) s F hgate (a1 - (N + N)) := by
        have : a1 ∈ outs (term v2) := by rw [heq, houts2]; exact Finset.mem_singleton_self a2
        exact (Finset.mem_filter.mp this).2
      rw [hi1, Finset.mem_insert, Finset.mem_singleton] at ht2_in
      have hh1_eq : h1 = term v2 := by
        rcases ht2_in with h | h
        · exact absurd h.symm htne
        · exact h.symm
      obtain ⟨l', hl'ne, hpl'⟩ := exists_line_through_ne hq hN hdeg huniq p l
      let v' := N + l'.val
      have ht2_v' : evalX F (term v2) {v'} := by
        by_contra hnt2
        have hiff : evalX F h1 {v'} ↔ evalX F h1 {v1, v'} :=
          indep_below_and v1 hv1 a1 houts1 {v'} {v1, v'} (fun u huv1 => by simp [huv1]) h1 hh1R hh1notP1 hh1a1
        have hn1 : ¬ evalX F h1 {v'} := hh1_eq ▸ hnt2
        have hn2 : ¬ evalX F h1 {v1, v'} := fun hx => hn1 (hiff.mpr hx)
        have ha_iff : evalX F a1 {v'} ↔ evalX F a1 {v1, v'} := by
          rw [hXa1 {v'}, hXa1 {v1, v'}]
          exact ⟨fun h => absurd h.2 hn1, fun h => absurd h.2 hn2⟩
        have ho_iff := screen_and v1 hv1 a1 houts1 {v'} {v1, v'} (fun u huv1 => by simp [huv1]) ha_iff
        have hpos : evalX F o {v1, v'} := hX_pos p l' _ hpl' (by simp [v1]) (by simp [v'])
        exact hX_neg_ln l' (ho_iff.mpr hpos)
      obtain ⟨p', hp'l, hnp'l'⟩ := exists_point_on_not_on hq hdeg huniq hl'ne.symm
      let W0 : Finset ℕ := {p'.val, v'}
      let W1 : Finset ℕ := insert v2 W0
      have hW0_t2 : evalX F (term v2) W0 :=
        evalX_mono hin hgate (Finset.singleton_subset_iff.mpr (by simp [W0])) _
          (hR_lt _ (hterm_mem_R v2 hv2)) ht2_v'
      have hW1_t2 : evalX F (term v2) W1 :=
        evalX_mono hin hgate (Finset.subset_insert v2 W0) _
          (hR_lt _ (hterm_mem_R v2 hv2)) hW0_t2
      have ho_iff : evalX F o W0 ↔ evalX F o W1 := by
        apply screen_term v2 hv2 W0 W1 (fun u huv2 => by simp [W1, huv2])
        · exact ⟨fun _ => hW1_t2, fun _ => hW0_t2⟩
        · exact hoR
        · intro h; exact ho_not_mem_path v2 hv2 (Finset.mem_erase.mp h).2
      have hpos : evalX F o W1 := hX_pos p' l W1 hp'l (by simp [W1, W0]) (by simp [W1, v2])
      exact hX_neg_noninc p' l' hnp'l' (ho_iff.mpr hpos)
    · -- Case 3: a2 < a1
      have hh2_notP1 : h2 ∉ path v1 := by
        intro hh2P1
        have ha2_out : a2 ∈ outs h2 := by
          refine Finset.mem_filter.mpr ⟨ha2GR, ?_⟩
          rw [hi2]; simp
        by_cases heqt : h2 = term v1
        · rw [heqt, houts1, Finset.mem_singleton] at ha2_out
          omega
        · obtain ⟨hcs, hstP⟩ := chainPath_step canStep step (N + N + s) v1 h2 hh2P1 heqt
          rw [houts_eq_singleton h2 hcs.2.2.1, Finset.mem_singleton] at ha2_out
          exact hnot_in_path v1 hv1 a2 ha2GR hkind2 (ha2_out ▸ hstP)
      have hh2_lt1 : h2 < a1 := lt_trans hh2a2 hgt
      have hiff1 : evalX F h2 ∅ ↔ evalX F h2 {v1} :=
        indep_below_and v1 hv1 a1 houts1 ∅ {v1} (fun u huv1 => by simp [huv1]) h2 hh2R hh2_notP1 hh2_lt1
      have hn1 : ¬ evalX F h2 {v1} := fun hx =>
        not_evalX_empty hin hgate (hR_lt h2 hh2R) (hiff1.mpr hx)
      have hiff2 : evalX F h2 {v1} ↔ evalX F h2 {v1, v2} :=
        indep_below_and v2 hv2 a2 houts2 {v1} {v1, v2} (fun u huv2 => by
          simp [huv2]) h2 hh2R hh2notP2 hh2a2
      have hn2 : ¬ evalX F h2 {v1, v2} := fun hx => hn1 (hiff2.mpr hx)
      have ha_iff : evalX F a2 {v1} ↔ evalX F a2 {v1, v2} := by
        rw [hXa2 {v1}, hXa2 {v1, v2}]
        exact ⟨fun h => absurd h.2 hn1, fun h => absurd h.2 hn2⟩
      have ho_iff := screen_and v2 hv2 a2 houts2 {v1} {v1, v2} (fun u huv2 => by
        simp [huv2]) ha_iff
      have hpos : evalX F o {v1, v2} := hX_pos p l _ hI (by simp [v1]) (by simp [v2])
      exact hX_neg_pt p (ho_iff.mpr hpos)
  -- Final assembly
  let AP : Finset (Fin N) := Finset.univ.filter (fun p => ¬ (2 ≤ (outs (term p.val)).card))
  let AL : Finset (Fin N) := Finset.univ.filter (fun l => ¬ (2 ≤ (outs (term (N + l.val))).card))
  have hind : AP.card + AL.card ≤ N := by
    apply indep_card_le hq hN hdeg huniq AP AL
    intro p hp l hl hI
    exact not_both_and p l hI ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hl).2⟩
  let FP : Finset (Fin N) := Finset.univ.filter (fun p => 2 ≤ (outs (term p.val)).card)
  let FL : Finset (Fin N) := Finset.univ.filter (fun l => 2 ≤ (outs (term (N + l.val))).card)
  have hPsum : FP.card + AP.card = N := by
    have hdisj : Disjoint FP AP := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (Finset.mem_filter.mp hp2).2 (Finset.mem_filter.mp hp1).2
    have hunion : FP ∪ AP = Finset.univ := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, FP, AP, iff_true]
      exact em _
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  have hLsum : FL.card + AL.card = N := by
    have hdisj : Disjoint FL AL := by
      rw [Finset.disjoint_left]
      intro l hl1 hl2
      exact (Finset.mem_filter.mp hl2).2 (Finset.mem_filter.mp hl1).2
    have hunion : FL ∪ AL = Finset.univ := by
      ext l
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, FL, AL, iff_true]
      exact em _
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  let Fset : Finset ℕ := (Finset.range (N + N)).filter (fun v => 2 ≤ (outs (term v)).card)
  have hFset_card : FP.card + FL.card ≤ Fset.card := by
    let S1 := FP.image (fun p : Fin N => p.val)
    let S2 := FL.image (fun l : Fin N => N + l.val)
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv1
      obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hv2
      omega
    have hsub : S1 ∪ S2 ⊆ Fset := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv1 | hv2
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv1
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (Finset.mem_filter.mp hp).2⟩
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (Finset.mem_filter.mp hl).2⟩
    have hc1 : S1.card = FP.card := Finset.card_image_of_injective _ Fin.val_injective
    have hc2 : S2.card = FL.card := Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
    calc FP.card + FL.card = (S1 ∪ S2).card := by
            rw [Finset.card_union_of_disjoint hdisj, hc1, hc2]
      _ ≤ Fset.card := Finset.card_le_card hsub
  have hBranch_ge : Fset.card ≤ Branch.card := by
    have hinj : Set.InjOn term (Fset : Set ℕ) := by
      intro v1 hv1 v2 hv2 heq
      by_contra hne
      have h1 : v1 < N + N := Finset.mem_range.mp (Finset.mem_filter.mp hv1).1
      have h2 : v2 < N + N := Finset.mem_range.mp (Finset.mem_filter.mp hv2).1
      exact term_inj v1 h1 v2 h2 hne heq
    have hsub : Fset.image term ⊆ Branch := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have h1 := Finset.mem_filter.mp hv
      have hv_lt : v < N + N := Finset.mem_range.mp h1.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hterm_ne_o v hv_lt, hterm_mem_R v hv_lt⟩, h1.2⟩
    calc Fset.card = (Fset.image term).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Branch.card := Finset.card_le_card hsub
  omega

def assignment (N : ℕ) (Z : Finset ℕ) : (Fin N → Bool) × (Fin N → Bool) :=
  (fun p => decide (p.val ∈ Z), fun l => decide (N + l.val ∈ Z))

def support {N : ℕ} (A B : Fin N → Bool) : Finset ℕ :=
  ((Finset.univ.filter fun p => A p = true).image Fin.val) ∪
    ((Finset.univ.filter fun l => B l = true).image fun l => N + l.val)

lemma mem_support_point {N : ℕ} (A B : Fin N → Bool) (p : Fin N) :
    p.val ∈ support A B ↔ A p = true := by
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨a, ha, he⟩ | ⟨b, _, he⟩)
    · simpa [Fin.ext he] using ha
    · omega
  · exact fun h => Or.inl ⟨p, h, rfl⟩

lemma mem_support_line {N : ℕ} (A B : Fin N → Bool) (l : Fin N) :
    N + l.val ∈ support A B ↔ B l = true := by
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨a, _, he⟩ | ⟨b, hb, he⟩)
    · omega
    · have h : b = l := Fin.ext (by omega)
      simpa [h] using hb
  · exact fun h => Or.inr ⟨l, h, rfl⟩

lemma assignment_support {N : ℕ} (A B : Fin N → Bool) :
    assignment N (support A B) = (A, B) := by
  apply Prod.ext
  · funext p
    change decide (p.val ∈ support A B) = A p
    cases h : A p <;> simp [mem_support_point, h]
  · funext l
    change decide (N + l.val ∈ support A B) = B l
    cases h : B l <;> simp [mem_support_line, h]

lemma assignment_pair {N : ℕ} (p l : Fin N) :
    assignment N {p.val, N + l.val} =
      ((fun i : Fin N => decide (i = p)), (fun i : Fin N => decide (i = l))) := by
  apply Prod.ext
  · funext i
    have h : i.val ≠ N + l.val := by omega
    simp [assignment, h, Fin.ext_iff]
  · funext i
    have h : N + i.val ≠ p.val := by omega
    simp [assignment, h, Fin.ext_iff]

def permittedWire {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (Y : Fin N → Bool) : (Fin N → Bool) × (Fin N → Bool) :=
  (fun p => decide (¬ ∃ l : Fin N, I p l ∧ Y l = true), Y)

lemma bridge (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N = q ^ 2 + q + 1)
    (hdeg : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ p₁ p₂ : Fin N, p₁ ≠ p₂ → ∃! l : Fin N, I p₁ l ∧ I p₂ l)
    (s o : ℕ) (special : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)))
    (ho : o < N + N + s)
    (hwires : ∀ i : Fin N, W i.val = {z | z.1 i = true} ∧
      W (N + i.val) = {z | z.2 i = true})
    (hsteps : ∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
      W (N + N + g) ∈ [W a ∪ W b, W a, ∅] ∨
      W (N + N + g) = W a ∩ W b ∧
        (g ∈ special ∨ ∃ A B : Set (Fin N → Bool),
          W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B))
    (hpos : ∀ p l : Fin N, I p l →
      ((fun i : Fin N => decide (i = p)), (fun i : Fin N => decide (i = l))) ∈ W o)
    (hneg : ∀ Y : Fin N → Bool, Fintype.card {l : Fin N // Y l = true} ≤ q →
      permittedWire I Y ∉ W o) :
    3 * N ≤ s + 1 := by
  let F : ℕ → Set (Finset ℕ) := fun w => assignment N ⁻¹' (W w)
  have hin : ∀ v < N + N, F v = {Z | v ∈ Z} := by
    intro v hv
    by_cases h : v < N
    · let i : Fin N := ⟨v, h⟩
      change F i.val = _
      simp [F, (hwires i).1, assignment, i]
    · let i : Fin N := ⟨v - N, by omega⟩
      have he : N + i.val = v := by dsimp [i]; omega
      rw [← he, show F (N + i.val) = assignment N ⁻¹' W (N + i.val) from rfl, (hwires i).2]
      simp [assignment]
  have hgate : GateSpec F (N + N) s := by
    intro g hg
    obtain ⟨a, ha, b, hb, h⟩ := hsteps g hg
    refine ⟨a, ha, b, hb, ?_⟩
    rcases h with h | ⟨h, _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · left; simp [F, h, Set.preimage_union]
      · right; left; simp [F, h]
      · right; right; left; simp [F, h]
    · right; right; right; simp [F, h, Set.preimage_inter]
  refine main_proof q N I (by omega) hN hdeg huniq s o F ho hin hgate ?_ ?_
  · intro p l h
    change assignment N {p.val, N + l.val} ∈ W o
    rw [assignment_pair]
    exact hpos p l h
  · intro T Z hT hZ hp hl h
    let Y : Fin N → Bool := fun l => decide (l ∈ T)
    have hY (l : Fin N) : Y l = true ↔ l ∈ T := by simp [Y]
    have hycard : Fintype.card {l : Fin N // Y l = true} ≤ q := by
      rw [Fintype.card_subtype]
      have he : Finset.univ.filter (fun l => Y l = true) = T := by
        ext l
        simp [hY]
      rwa [he]
    let A := (permittedWire I Y).1
    have hA (p : Fin N) : A p = true ↔ ¬ ∃ l : Fin N, I p l ∧ Y l = true := by
      simp [A, permittedWire]
    have hsub : Z ⊆ support A Y := by
      intro v hv
      have hvb := hZ v hv
      by_cases hvp : v < N
      · let p : Fin N := ⟨v, hvp⟩
        change p.val ∈ support A Y
        rw [mem_support_point, hA]
        rintro ⟨l, hpl, hly⟩
        exact hp p hv l ((hY l).mp hly) hpl
      · let l : Fin N := ⟨v - N, by omega⟩
        have he : N + l.val = v := by dsimp [l]; omega
        rw [← he, mem_support_line, hY]
        exact hl l (he ▸ hv)
    have hm := evalX_mono hin hgate hsub o ho h
    change assignment N (support A Y) ∈ W o at hm
    rw [assignment_support] at hm
    exact hneg Y hycard hm

end PEqualNP.Outside.L_meta_9132

theorem PEqualNP.Outside.L_meta_9132 :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (3 : ℕ) * x2 ≤ x11 + (1 : ℕ) := by
  intro q N I inst
  dsimp
  intro hq hN hdeg huniq s o special W ho hwires hsteps hpos hneg
  exact @PEqualNP.Outside.L_meta_9132.bridge q N I inst hq hN hdeg huniq s o special W
    ho hwires hsteps hpos hneg
