import PEqualNP.CircuitLowerBounds.Helpers.Switching.Basic

/-!
# One round of the switching argument (L-lib-034)

`SwitchingSem → Round`: a union bound over the gates of level two. Conjecture until the
checker accepts the lemma that rests on it.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Round

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Switching.Plan

open scoped Classical

/-- The pointwise negation of a Boolean function. -/
def neg {V : Type} (f : BF V) : BF V := fun x => !f x

theorem cert1_neg {V : Type} {w : ℕ} {f : BF V} (h : Cert0 w f) : Cert1 w (neg f) := by
  intro x hx
  obtain ⟨S, hS, hc⟩ := h x (by simpa [neg] using hx)
  exact ⟨S, hS, fun y hy => by simp [neg, hc y hy]⟩

theorem cert0_neg {V : Type} {w : ℕ} {f : BF V} (h : Cert1 w f) : Cert0 w (neg f) := by
  intro x hx
  obtain ⟨S, hS, hc⟩ := h x (by simpa [neg] using hx)
  exact ⟨S, hS, fun y hy => by simp [neg, hc y hy]⟩

theorem neg_neg' {V : Type} (f : BF V) : neg (neg f) = f := by
  funext x; simp [neg]

theorem low_neg {V : Type} {w : ℕ} {f : BF V} (h : Low w f) : Low w (neg f) :=
  ⟨cert1_neg h.2, cert0_neg h.1⟩

theorem low_of_neg {V : Type} {w : ℕ} {f : BF V} (h : Low w (neg f)) : Low w f := by
  have := low_neg h
  rwa [neg_neg'] at this

theorem restr_neg {V : Type} (ρ : Restr V) (f : BF V) : restr ρ (neg f) = neg (restr ρ f) := rfl

theorem cert1_mono {V : Type} {w t : ℕ} (hwt : w ≤ t) {f : BF V} (h : Cert1 w f) : Cert1 t f := by
  intro x hx
  obtain ⟨S, hS, hc⟩ := h x hx
  exact ⟨S, hS.trans hwt, hc⟩

theorem cert0_mono {V : Type} {w t : ℕ} (hwt : w ≤ t) {f : BF V} (h : Cert0 w f) : Cert0 t f := by
  intro x hx
  obtain ⟨S, hS, hc⟩ := h x hx
  exact ⟨S, hS.trans hwt, hc⟩

theorem low_mono {V : Type} {w t : ℕ} (hwt : w ≤ t) {f : BF V} (h : Low w f) : Low t f :=
  ⟨cert1_mono hwt h.1, cert0_mono hwt h.2⟩

theorem fill_agree {V : Type} (ρ : Restr V) (S : Finset V) (y y' : Stars ρ → Bool)
    (h : ∀ i ∈ S.subtype (fun v => ρ v = none), y' i = y i) :
    ∀ i ∈ S, fill ρ y' i = fill ρ y i := by
  intro i hi
  unfold fill
  by_cases hρ : ρ i = none
  · rw [dif_pos hρ, dif_pos hρ]
    exact h ⟨i, hρ⟩ (by simpa [Finset.mem_subtype] using hi)
  · rw [dif_neg hρ, dif_neg hρ]

theorem card_subtype_le' {V : Type} (ρ : Restr V) (S : Finset V) :
    (S.subtype (fun v => ρ v = none)).card ≤ S.card := by
  rw [Finset.card_subtype]
  exact Finset.card_filter_le _ _

theorem cert1_restr {V : Type} {w : ℕ} (ρ : Restr V) {f : BF V} (h : Cert1 w f) :
    Cert1 w (restr ρ f) := by
  intro y hy
  obtain ⟨S, hS, hc⟩ := h (fill ρ y) hy
  exact ⟨S.subtype (fun v => ρ v = none), (card_subtype_le' ρ S).trans hS,
    fun y' hy' => hc _ (fill_agree ρ S y y' hy')⟩

theorem cert0_restr {V : Type} {w : ℕ} (ρ : Restr V) {f : BF V} (h : Cert0 w f) :
    Cert0 w (restr ρ f) := by
  intro y hy
  obtain ⟨S, hS, hc⟩ := h (fill ρ y) hy
  exact ⟨S.subtype (fun v => ρ v = none), (card_subtype_le' ρ S).trans hS,
    fun y' hy' => hc _ (fill_agree ρ S y y' hy')⟩

theorem low_restr {V : Type} {w : ℕ} (ρ : Restr V) {f : BF V} (h : Low w f) :
    Low w (restr ρ f) :=
  ⟨cert1_restr ρ h.1, cert0_restr ρ h.2⟩

/-- A function with zero-size certificates of one kind is constant, so it has both. -/
theorem low_zero_of_cert1 {V : Type} {f : BF V} (h : Cert1 0 f) : Low 0 f := by
  refine ⟨h, fun x hx => ⟨∅, le_rfl, fun y _ => ?_⟩⟩
  by_contra hy
  have hy' : f y = true := by simpa using hy
  obtain ⟨S, hS, hc⟩ := h y hy'
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
  have := hc x (by simp [hS0])
  rw [hx] at this; cases this

theorem low_zero_of_cert0 {V : Type} {f : BF V} (h : Cert0 0 f) : Low 0 f :=
  low_of_neg (low_zero_of_cert1 (cert1_neg h))

/-- On no variables every function has empty certificates. -/
theorem low_of_isEmpty {V : Type} [IsEmpty V] (t : ℕ) (f : BF V) : Low t f := by
  have key : ∀ x y : V → Bool, y = x := fun x y => funext fun v => isEmptyElim v
  exact ⟨fun x hx => ⟨∅, Nat.zero_le _, fun y _ => by rw [key x y]; exact hx⟩,
    fun x hx => ⟨∅, Nat.zero_le _, fun y _ => by rw [key x y]; exact hx⟩⟩

/-- The restriction with stars exactly on `S`. -/
noncomputable def starOn {V : Type} (S : Finset V) : Restr V := fun v => if v ∈ S then none else some false

theorem card_stars_starOn {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    Fintype.card (Stars (starOn S)) = S.card := by
  rw [Fintype.card_subtype]
  congr 1
  ext v
  simp [starOn]

theorem exists_restr_card {V : Type} [Fintype V] [DecidableEq V] {l : ℕ}
    (hl : l ≤ Fintype.card V) : ∃ ρ : Restr V, Fintype.card (Stars ρ) = l := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset V))
    (by simpa using hl)
  exact ⟨starOn S, by rw [card_stars_starOn, hS]⟩

/-- The combinatorial heart: one restriction with `l` stars is good for every gate of level
two. -/
theorem exists_good (hS : SwitchingSem) (V : Type) [Fintype V] [DecidableEq V] (w t k l : ℕ)
    (G : Finset (BF V)) (lev : BF V → ℕ) (ht : 1 ≤ t) (hwt : w ≤ t)
    (hG : IsCirc w k G lev) (hcard : G.card < 2 ^ t) (hl : l ≤ Fintype.card V)
    (hwl : 16 * w * l ≤ Fintype.card V - l) :
    ∃ ρ : Restr V, Fintype.card (Stars ρ) = l ∧
      ∀ g ∈ G, lev g ≤ 2 → Low t (restr ρ g) := by
  by_cases hN : Fintype.card V - l = 0
  · -- degenerate: `w * l = 0`
    obtain ⟨ρ, hρ⟩ := exists_restr_card (V := V) hl
    refine ⟨ρ, hρ, fun g hg h2 => ?_⟩
    have hwl0 : w * l = 0 := by
      have : 16 * w * l = 0 := Nat.le_zero.mp (hN ▸ hwl)
      have : 16 * (w * l) = 0 := by rw [← mul_assoc]; exact this
      omega
    rcases Nat.mul_eq_zero.mp hwl0 with hw | hl0
    · subst hw
      refine low_restr ρ (low_mono (Nat.zero_le t) ?_)
      rcases level_two hG hg h2 with h1 | h0
      · exact low_zero_of_cert1 h1
      · exact low_zero_of_cert0 h0
    · subst hl0
      have hV : Fintype.card V = 0 := by omega
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      haveI : IsEmpty (Stars ρ) := ⟨fun v => isEmptyElim v.1⟩
      exact low_of_isEmpty t _
  · have hNpos : 0 < Fintype.card V - l := Nat.pos_of_ne_zero hN
    set R : Finset (Restr V) :=
      Finset.univ.filter fun ρ : Restr V => Fintype.card (Stars ρ) = l with hR
    have hRpos : 0 < R.card := by
      obtain ⟨ρ, hρ⟩ := exists_restr_card (V := V) hl
      exact Finset.card_pos.mpr ⟨ρ, by simp [hR, hρ]⟩
    let G2 : Finset (BF V) := G.filter fun g => lev g ≤ 2
    let bad : BF V → Finset (Restr V) := fun g =>
      Finset.univ.filter fun ρ : Restr V => Fintype.card (Stars ρ) = l ∧ ¬ Low t (restr ρ g)
    -- each bad set is small
    have hsmall : ∀ g ∈ G2, (bad g).card * 2 ^ t ≤ R.card := by
      intro g hg
      have hgG : g ∈ G := (Finset.mem_filter.mp hg).1
      have h2 : lev g ≤ 2 := (Finset.mem_filter.mp hg).2
      -- a function with small 1-certificates and the same bad set
      obtain ⟨f, hf1, hfbad⟩ : ∃ f : BF V, Cert1 w f ∧
          ∀ ρ : Restr V, Low t (restr ρ f) ↔ Low t (restr ρ g) := by
        rcases level_two hG hgG h2 with h1 | h0
        · exact ⟨g, h1, fun _ => Iff.rfl⟩
        · refine ⟨neg g, cert1_neg h0, fun ρ => ?_⟩
          rw [restr_neg]
          exact ⟨low_of_neg, low_neg⟩
      have hsw := hS V w t l f hf1
      have hbadeq : (Finset.univ.filter fun ρ : Restr V =>
          Fintype.card (Stars ρ) = l ∧ ¬ Low t (restr ρ f)) = bad g := by
        ext ρ
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, hfbad ρ]
      have hsw' : (bad g).card * (Fintype.card V - l) ^ t ≤ R.card * (8 * w * l) ^ t := by
        rw [← hbadeq]; convert hsw using 2
      have hpow : (8 * w * l) ^ t * 2 ^ t ≤ (Fintype.card V - l) ^ t := by
        rw [← mul_pow]
        exact Nat.pow_le_pow_left (by nlinarith [hwl]) t
      by_cases h8 : 8 * w * l = 0
      · rw [h8, zero_pow (by omega), mul_zero] at hsw'
        have hb0 : (bad g).card = 0 := by
          rcases Nat.mul_eq_zero.mp (Nat.le_zero.mp hsw') with h | h
          · exact h
          · exact absurd h (by positivity)
        rw [hb0, zero_mul]; exact Nat.zero_le _
      · have hpos : 0 < (8 * w * l) ^ t := by positivity
        have : (bad g).card * 2 ^ t * (8 * w * l) ^ t ≤ R.card * (8 * w * l) ^ t := by
          calc (bad g).card * 2 ^ t * (8 * w * l) ^ t
              = (bad g).card * ((8 * w * l) ^ t * 2 ^ t) := by ring
            _ ≤ (bad g).card * (Fintype.card V - l) ^ t := Nat.mul_le_mul_left _ hpow
            _ ≤ R.card * (8 * w * l) ^ t := hsw'
        exact Nat.le_of_mul_le_mul_right this hpos
    -- union bound
    have hG2card : G2.card < 2 ^ t := lt_of_le_of_lt (Finset.card_filter_le _ _) hcard
    have hunion : (G2.biUnion bad).card < R.card := by
      have h1 : (G2.biUnion bad).card * 2 ^ t ≤ G2.card * R.card := by
        calc (G2.biUnion bad).card * 2 ^ t
            ≤ (∑ g ∈ G2, (bad g).card) * 2 ^ t :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ g ∈ G2, (bad g).card * 2 ^ t := by rw [Finset.sum_mul]
          _ ≤ ∑ _g ∈ G2, R.card := Finset.sum_le_sum hsmall
          _ = G2.card * R.card := by rw [Finset.sum_const, smul_eq_mul]
      have h2 : G2.card * R.card < 2 ^ t * R.card := Nat.mul_lt_mul_of_pos_right hG2card hRpos
      have h3 : (G2.biUnion bad).card * 2 ^ t < R.card * 2 ^ t := by
        rw [mul_comm R.card]; exact lt_of_le_of_lt h1 h2
      exact Nat.lt_of_mul_lt_mul_right h3
    obtain ⟨ρ, hρR, hρbad⟩ : ∃ ρ ∈ R, ρ ∉ G2.biUnion bad := by
      by_contra hcon
      push_neg at hcon
      exact absurd (Finset.card_le_card (fun ρ hρ => hcon ρ hρ)) (not_le.mpr hunion)
    have hρl : Fintype.card (Stars ρ) = l := by
      have := (Finset.mem_filter.mp hρR).2
      convert this
    refine ⟨ρ, hρl, fun g hg h2 => ?_⟩
    by_contra hlow
    apply hρbad
    refine Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, h2⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hlow⟩
    convert hρl

/-- `SwitchingSem → Round`. -/
theorem roundOfSwitching : RoundOfSwitching := by
  intro hS V _ _ w t k l G lev ht hwt hk hG hcard hl hwl
  obtain ⟨ρ, hρl, hgood⟩ := exists_good hS V w t k l G lev ht hwt hG hcard hl hwl
  -- the gates of level at least three, restricted
  let G3 : Finset (BF V) := G.filter fun g => 3 ≤ lev g
  let G' : Finset (BF (Stars ρ)) := G3.image (restr ρ)
  -- the least level among the gates with a given restriction
  let P : BF (Stars ρ) → ℕ → Prop := fun h n => ∃ g ∈ G, 3 ≤ lev g ∧ restr ρ g = h ∧ lev g = n
  let lev' : BF (Stars ρ) → ℕ := fun h =>
    if hh : ∃ n, P h n then Nat.find hh - 1 else 0
  have hmemG' : ∀ g ∈ G, 3 ≤ lev g → restr ρ g ∈ G' := fun g hg h3 =>
    Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, h3⟩, rfl⟩
  have hlev'le : ∀ g ∈ G, 3 ≤ lev g → lev' (restr ρ g) ≤ lev g - 1 := by
    intro g hg h3
    have hh : ∃ n, P (restr ρ g) n := ⟨lev g, g, hg, h3, rfl, rfl⟩
    have hmin : Nat.find hh ≤ lev g := Nat.find_min' hh ⟨g, hg, h3, rfl, rfl⟩
    show (if hh : ∃ n, P (restr ρ g) n then Nat.find hh - 1 else 0) ≤ lev g - 1
    rw [dif_pos hh]; omega
  have hlast : ∀ f : BF V, (f ∈ G ∨ Low w f) → (restr ρ f ∈ G' ∨ Low t (restr ρ f)) := by
    intro f hf
    rcases hf with hf | hf
    · by_cases h3 : 3 ≤ lev f
      · exact Or.inl (hmemG' f hf h3)
      · exact Or.inr (hgood f hf (by omega))
    · exact Or.inr (low_restr ρ (low_mono hwt hf))
  refine ⟨ρ, G', lev', hρl, ?_, ?_, hlast⟩
  · exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  · intro h hh'
    obtain ⟨g0, hg0, rfl⟩ := Finset.mem_image.mp hh'
    have hg0G : g0 ∈ G := (Finset.mem_filter.mp hg0).1
    have hg03 : 3 ≤ lev g0 := (Finset.mem_filter.mp hg0).2
    have hh : ∃ n, P (restr ρ g0) n := ⟨lev g0, g0, hg0G, hg03, rfl, rfl⟩
    obtain ⟨g, hgG, hg3, hgeq, hglev⟩ := Nat.find_spec hh
    have hlev'eq : lev' (restr ρ g0) = lev g - 1 := by
      show (if hh : ∃ n, P (restr ρ g0) n then Nat.find hh - 1 else 0) = lev g - 1
      rw [dif_pos hh, hglev]
    obtain ⟨-, hgk, I, hI, hform⟩ := hG g hgG
    refine ⟨by rw [hlev'eq]; omega, by rw [hlev'eq]; omega, (restr ρ) '' I, ?_, ?_⟩
    · rintro h' ⟨i, hi, rfl⟩
      rcases hI i hi with ⟨hiG, hilt⟩ | hlow
      · by_cases h3 : 3 ≤ lev i
        · left
          refine ⟨hmemG' i hiG h3, ?_⟩
          have := hlev'le i hiG h3
          rw [hlev'eq]; omega
        · exact Or.inr (hgood i hiG (by omega))
      · exact Or.inr (low_restr ρ (low_mono hwt hlow))
    · rw [← hgeq]
      rcases hform with hor | hand
      · left
        intro y
        show g (fill ρ y) = true ↔ _
        rw [hor]
        constructor
        · rintro ⟨i, hi, hix⟩
          exact ⟨restr ρ i, ⟨i, hi, rfl⟩, hix⟩
        · rintro ⟨h', ⟨i, hi, rfl⟩, hix⟩
          exact ⟨i, hi, hix⟩
      · right
        intro y
        show g (fill ρ y) = true ↔ _
        rw [hand]
        constructor
        · rintro hall h' ⟨i, hi, rfl⟩
          exact hall i hi
        · intro hall i hi
          exact hall (restr ρ i) ⟨i, hi, rfl⟩

end PEqualNP.CircuitLowerBounds.Switching.Round
