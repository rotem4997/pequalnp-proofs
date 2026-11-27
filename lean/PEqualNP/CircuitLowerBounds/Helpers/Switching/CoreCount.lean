import PEqualNP.CircuitLowerBounds.Helpers.Switching.CoreEncode

/-!
# Switching lemma: the count

The number of restrictions with `l` stars, the counting form of the switching lemma
(`card_bad`), its ratio form (`card_bad_ratio`), and the semantic fact behind it: small
canonical depth gives small certificates (`cert_of_cdt`).
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Core

variable {n : ℕ}

/-! ## Counting restrictions -/

theorem card_R (n l : ℕ) : (R n l).card = n.choose l * 2 ^ (n - l) := by
  classical
  let g : Finset (Fin n) → Fin n → Finset (Option Bool) :=
    fun S v => if v ∈ S then {none} else {some true, some false}
  have hmem : ∀ (S : Finset (Fin n)) (ρ : Restr n),
      ρ ∈ Fintype.piFinset (g S) ↔ ∀ v, ρ v = none ↔ v ∈ S := by
    intro S ρ
    rw [Fintype.mem_piFinset]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · simp [g, hv]
    · cases h : ρ v with
      | none => simp [g, hv]
      | some b => cases b <;> simp [g, hv]
  have hR : R n l = (Finset.powersetCard l (Finset.univ : Finset (Fin n))).biUnion
      fun S => Fintype.piFinset (g S) := by
    ext ρ
    rw [Finset.mem_biUnion]
    constructor
    · intro h
      have hl : stars ρ = l := by simpa [R] using h
      refine ⟨Finset.univ.filter fun v => ρ v = none, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hl⟩
      · rw [hmem]; intro v; rw [Finset.mem_filter]; simp
    · rintro ⟨S, hS, hρ⟩
      rw [Finset.mem_powersetCard] at hS
      rw [hmem] at hρ
      have : (Finset.univ.filter fun v => ρ v = none) = S := by
        ext v; rw [Finset.mem_filter]; simp [hρ v]
      have hl : stars ρ = l := by unfold stars; rw [this]; exact hS.2
      simpa [R] using hl
  have hdisj : ((Finset.powersetCard l (Finset.univ : Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint
      fun S => Fintype.piFinset (g S) := by
    intro S _ S' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ρ h1 h2
    rw [hmem] at h1 h2
    exact hne (by ext v; rw [← h1 v, ← h2 v])
  have hcard : ∀ S ∈ Finset.powersetCard l (Finset.univ : Finset (Fin n)),
      (Fintype.piFinset (g S)).card = 2 ^ (n - l) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Fintype.card_piFinset]
    have h1 : ∀ v : Fin n, (g S v).card = if v ∈ S then 1 else 2 := by
      intro v; by_cases hv : v ∈ S <;> simp [g, hv]
    simp only [h1]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have : (Finset.univ.filter fun v => v ∉ S) = Sᶜ := by
      ext v; simp
    rw [this, Finset.card_compl, hS.2, Fintype.card_fin]
  rw [hR, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard, Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem mem_R {ρ : Restr n} {l : ℕ} : ρ ∈ R n l ↔ stars ρ = l := by
  simp [R]

/-! ## The counting form -/

/-- The codes: lists of length `t` of triples whose first entry is below `w`. -/
def codes (w t : ℕ) : Finset (List (ℕ × Bool × Bool)) :=
  (Finset.univ : Finset (List.Vector (Fin w × Bool × Bool) t)).image
    fun v => v.toList.map fun e => (e.1.val, e.2)

theorem card_codes (w t : ℕ) : (codes w t).card ≤ (4 * w) ^ t := by
  unfold codes
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_univ, card_vector]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  apply le_of_eq; ring

theorem pmap_back {w : ℕ} : ∀ (c : List (ℕ × Bool × Bool)) (h : ∀ e ∈ c, e.1 < w),
    (c.pmap (fun e he => ((⟨e.1, he⟩ : Fin w), e.2)) h).map (fun e => (e.1.val, e.2)) = c
  | [], _ => rfl
  | a :: c, h => by
    simp only [List.pmap, List.map_cons, List.cons.injEq, true_and]
    exact pmap_back c (fun e he => h e (List.mem_cons_of_mem _ he))

theorem mem_codes {w t : ℕ} {c : List (ℕ × Bool × Bool)} (hl : c.length = t)
    (h : ∀ e ∈ c, e.1 < w) : c ∈ codes w t := by
  unfold codes
  rw [Finset.mem_image]
  refine ⟨⟨c.pmap (fun e he => ((⟨e.1, he⟩ : Fin w), e.2)) h, by simp [hl]⟩,
    Finset.mem_univ _, ?_⟩
  exact pmap_back c h

/-- The switching lemma, counting form, for any fuel. -/
theorem card_bad_aux (F : DNF n) (w : ℕ) (hw : ∀ T ∈ F, T.length ≤ w) (k l t : ℕ)
    (ht : 1 ≤ t) :
    ((R n l).filter fun ρ => t ≤ cdtAux k F ρ).card ≤ (R n (l - t)).card * (4 * w) ^ t := by
  have h1 : ((R n l).filter fun ρ => t ≤ cdtAux k F ρ).card ≤
      ((R n (l - t)) ×ˢ (codes w t)).card := by
    refine Finset.card_le_card_of_injOn (fun ρ => enc k t F ρ) ?_ ?_
    · intro ρ hρ
      rw [Finset.mem_coe, Finset.mem_filter] at hρ
      rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, mem_codes (enc_code_length k t F ρ hρ.2) (enc_code_lt k t F ρ hw)⟩
      rw [mem_R]
      have := enc_stars k t F ρ hρ.2
      rw [mem_R.1 hρ.1] at this
      show stars (enc k t F ρ).1 = l - t
      omega
    · intro ρ hρ ρ₂ hρ₂ he
      rw [Finset.mem_coe, Finset.mem_filter] at hρ hρ₂
      exact enc_inj k t F ρ ρ₂ ht hρ.2 hρ₂.2 he
  rw [Finset.card_product] at h1
  exact le_trans h1 (Nat.mul_le_mul_left _ (card_codes w t))

/-- **Switching lemma, counting form.** For an ordered DNF of width at most `w`, the
restrictions with `l` stars under which the canonical decision tree has depth at least `t ≥ 1`
number at most `|R(n, l - t)| (4 w)^t`. -/
theorem card_bad (F : DNF n) (w : ℕ) (hw : ∀ T ∈ F, T.length ≤ w) (l t : ℕ) (ht : 1 ≤ t) :
    (bad F l t).card ≤ (R n (l - t)).card * (4 * w) ^ t :=
  card_bad_aux F w hw n l t ht

theorem le_of_mem_bad {F : DNF n} {l t : ℕ} {ρ : Restr n} (h : ρ ∈ bad F l t) : t ≤ l := by
  unfold bad at h
  rw [Finset.mem_filter] at h
  have := enc_stars n t F ρ h.2
  rw [mem_R.1 h.1] at this
  omega

theorem choose_step (n l : ℕ) : ∀ t, t ≤ l → n.choose (l - t) * (n - l) ^ t ≤ n.choose l * l ^ t
  | 0, _ => by simp
  | t + 1, h => by
    have ih := choose_step n l t (by omega)
    have e := Nat.choose_succ_right_eq n (l - (t + 1))
    have e1 : l - (t + 1) + 1 = l - t := by omega
    rw [e1] at e
    calc n.choose (l - (t + 1)) * (n - l) ^ (t + 1)
        = n.choose (l - (t + 1)) * (n - l) * (n - l) ^ t := by ring
      _ ≤ n.choose (l - (t + 1)) * (n - (l - (t + 1))) * (n - l) ^ t := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          omega
      _ = n.choose (l - t) * (l - t) * (n - l) ^ t := by rw [e]
      _ = (n.choose (l - t) * (n - l) ^ t) * (l - t) := by ring
      _ ≤ (n.choose l * l ^ t) * l := Nat.mul_le_mul ih (by omega)
      _ = n.choose l * l ^ (t + 1) := by ring

/-- **Switching lemma, ratio form.** No division:
`card bad * (n - l)^t ≤ card (R n l) * (8 w l)^t`. -/
theorem card_bad_ratio (F : DNF n) (w : ℕ) (hw : ∀ T ∈ F, T.length ≤ w) (l t : ℕ) :
    (bad F l t).card * (n - l) ^ t ≤ (R n l).card * (8 * w * l) ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [pow_zero, mul_one]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  by_cases hne : (bad F l t).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp
  obtain ⟨ρ, hρ⟩ := hne
  have htl : t ≤ l := le_of_mem_bad hρ
  have hln : l ≤ n := by
    have h1 : ρ ∈ R n l := (Finset.mem_filter.1 hρ).1
    rw [mem_R] at h1
    rw [← h1]; exact stars_le ρ
  have h1 := card_bad F w hw l t ht
  rw [card_R] at h1
  rw [card_R]
  have h2 := choose_step n l t htl
  have e2 : n - (l - t) = n - l + t := by omega
  rw [e2, pow_add] at h1
  calc (bad F l t).card * (n - l) ^ t
      ≤ (n.choose (l - t) * (2 ^ (n - l) * 2 ^ t) * (4 * w) ^ t) * (n - l) ^ t :=
        Nat.mul_le_mul_right _ h1
    _ = (n.choose (l - t) * (n - l) ^ t) * (2 ^ (n - l) * 2 ^ t * (4 * w) ^ t) := by ring
    _ ≤ (n.choose l * l ^ t) * (2 ^ (n - l) * 2 ^ t * (4 * w) ^ t) :=
        Nat.mul_le_mul_right _ h2
    _ = n.choose l * 2 ^ (n - l) * (8 * w * l) ^ t := by
        have : (8 * w * l) ^ t = 2 ^ t * (4 * w) ^ t * l ^ t := by
          rw [← mul_pow, ← mul_pow]; congr 1; ring
        rw [this]; ring

/-! ## Small canonical depth gives small certificates -/

theorem eval_false_of_dead {T : Term n} {ρ : Restr n} {x : Fin n → Bool} (hx : Compat ρ x)
    (hd : T.Dead ρ) : T.eval x = false := by
  unfold Term.eval
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  obtain ⟨p, hp, h1 | h2⟩ := hd
  · have := hall p hp
    rw [hx _ _ h1] at this
    cases hb : p.2 <;> simp [hb] at this
  · have a := hall p hp
    have b := hall _ h2
    simp only [beq_iff_eq] at a b
    rw [a] at b
    cases hb : p.2 <;> simp [hb] at b

theorem eval_false_of_firstLive_none {F : DNF n} {ρ : Restr n} {x : Fin n → Bool}
    (hx : Compat ρ x) (h : firstLive F ρ = none) : F.eval x = false := by
  unfold DNF.eval
  rw [Bool.eq_false_iff]
  intro hany
  rw [List.any_eq_true] at hany
  obtain ⟨T, hT, hTx⟩ := hany
  have := List.find?_eq_none.1 h T hT
  simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    not_not] at this
  rw [eval_false_of_dead hx this] at hTx
  cases hTx

theorem eval_true_of_live_closed {T : Term n} {ρ : Restr n} {x : Fin n → Bool}
    (hx : Compat ρ x) (hd : ¬ T.Dead ρ) (hfree : T.free ρ = []) : T.eval x = true := by
  unfold Term.eval
  rw [List.all_eq_true]
  intro p hp
  simp only [beq_iff_eq]
  cases hρ : ρ p.1 with
  | none =>
    have : p.1 ∈ T.free ρ := mem_free.2 ⟨⟨p.2, hp⟩, hρ⟩
    rw [hfree] at this; cases this
  | some c =>
    rw [hx _ _ hρ]
    by_contra hne
    apply hd
    refine ⟨p, hp, Or.inl ?_⟩
    rw [hρ]
    cases hb : p.2 <;> cases c <;> simp_all

/-- If the canonical depth under `ρ` is at most `t` (with enough fuel), every point compatible
with `ρ` has a certificate of at most `t` starred variables for the value of `F`. -/
theorem cert_of_cdtAux : ∀ (k : ℕ) (F : DNF n) (ρ : Restr n) (t : ℕ), stars ρ ≤ k →
    cdtAux k F ρ ≤ t → ∀ x, Compat ρ x → ∃ S : Finset (Fin n), S.card ≤ t ∧
      (∀ v ∈ S, ρ v = none) ∧
      ∀ y, Compat ρ y → (∀ v ∈ S, y v = x v) → F.eval y = F.eval x := by
  intro k
  induction k with
  | zero =>
    intro F ρ t hk _ x hx
    refine ⟨∅, by simp, by simp, fun y hy _ => ?_⟩
    have hall : ∀ v, ρ v ≠ none := by
      intro v hv
      have : 0 < stars ρ := by
        unfold stars
        exact Finset.card_pos.2 ⟨v, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩⟩
      omega
    have : y = x := by
      funext v
      cases hρ : ρ v with
      | none => exact absurd hρ (hall v)
      | some b => rw [hy _ _ hρ, hx _ _ hρ]
    rw [this]
  | succ k ih =>
    intro F ρ t hk ht x hx
    cases hf : firstLive F ρ with
    | none =>
      refine ⟨∅, by simp, by simp, fun y hy _ => ?_⟩
      rw [eval_false_of_firstLive_none hy hf, eval_false_of_firstLive_none hx hf]
    | some T =>
      have hTF := firstLive_mem hf
      have hnd := firstLive_not_dead hf
      by_cases hV : T.free ρ = []
      · refine ⟨∅, by simp, by simp, fun y hy _ => ?_⟩
        have e1 : F.eval y = true := by
          unfold DNF.eval; rw [List.any_eq_true]
          exact ⟨T, hTF, eval_true_of_live_closed hy hnd hV⟩
        have e2 : F.eval x = true := by
          unfold DNF.eval; rw [List.any_eq_true]
          exact ⟨T, hTF, eval_true_of_live_closed hx hnd hV⟩
        rw [e1, e2]
      · rw [cdtAux_succ_some hf, if_neg hV] at ht
        have hsup : cdtAux k F (ext ρ (T.free ρ) x) ≤
            Finset.univ.sup fun π : Fin n → Bool => cdtAux k F (ext ρ (T.free ρ) π) :=
          Finset.le_sup (f := fun π : Fin n → Bool => cdtAux k F (ext ρ (T.free ρ) π))
            (Finset.mem_univ x)
        have hst := stars_ext (ρ := ρ) x (free_nodup T ρ) (fun v hv => free_star hv)
        have hpos : 0 < (T.free ρ).length := List.length_pos_iff.2 hV
        have hcx : Compat (ext ρ (T.free ρ) x) x := by
          intro v b hvb
          by_cases hv : v ∈ T.free ρ
          · rw [ext_of_mem hv] at hvb; exact Option.some.inj hvb
          · rw [ext_of_not_mem hv] at hvb; exact hx v b hvb
        obtain ⟨S, hS, hstar, hcert⟩ := ih F (ext ρ (T.free ρ) x) (t - (T.free ρ).length)
          (by omega) (by omega) x hcx
        classical
        refine ⟨(T.free ρ).toFinset ∪ S, ?_, ?_, ?_⟩
        · calc ((T.free ρ).toFinset ∪ S).card ≤ (T.free ρ).toFinset.card + S.card :=
              Finset.card_union_le _ _
            _ ≤ (T.free ρ).length + (t - (T.free ρ).length) :=
              Nat.add_le_add (List.toFinset_card_le _) hS
            _ ≤ t := by omega
        · intro v hv
          rcases Finset.mem_union.1 hv with hv | hv
          · exact free_star (List.mem_toFinset.1 hv)
          · have := hstar v hv
            by_cases hv' : v ∈ T.free ρ
            · rw [ext_of_mem hv'] at this; cases this
            · rwa [ext_of_not_mem hv'] at this
        · intro y hy hyx
          apply hcert y
          · intro v b hvb
            by_cases hv : v ∈ T.free ρ
            · rw [ext_of_mem hv] at hvb
              rw [hyx v (Finset.mem_union_left _ (List.mem_toFinset.2 hv))]
              exact Option.some.inj hvb
            · rw [ext_of_not_mem hv] at hvb; exact hy v b hvb
          · intro v hv; exact hyx v (Finset.mem_union_right _ hv)

/-- Small canonical depth gives small certificates, for both values of the DNF. -/
theorem cert_of_cdt (F : DNF n) (ρ : Restr n) (t : ℕ) (h : cdt F ρ ≤ t) :
    ∀ x, Compat ρ x → ∃ S : Finset (Fin n), S.card ≤ t ∧ (∀ v ∈ S, ρ v = none) ∧
      ∀ y, Compat ρ y → (∀ v ∈ S, y v = x v) → F.eval y = F.eval x :=
  cert_of_cdtAux n F ρ t (stars_le ρ) h

end PEqualNP.CircuitLowerBounds.Switching.Core
