import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4765_476
    (hNorm : ∀ (N s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let Z := (Fin N → Bool) × (Fin N → Bool)
      o < N + N + s →
      (∀ p : Fin N, W ↑p = { z : Z | z.1 p = true } ∧ W (N + ↑p) = { z : Z | z.2 p = true }) →
      (∀ g < s, ∃ a b, max a b < N + N + g ∧ W (N + N + g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      (∃ z : Z, z ∈ W o) →
      ∃ s' ≤ s, ∃ o' < N + N + s', ∃ W' : ℕ → Set Z,
        (∀ p : Fin N, W' ↑p = { z : Z | z.1 p = true } ∧ W' (N + ↑p) = { z : Z | z.2 p = true }) ∧
        (∀ g < s', ∃ a < N + N + g, ∃ b < N + N + g,
          W' (N + N + g) = W' a ∪ W' b ∨ W' (N + N + g) = W' a ∩ W' b) ∧
        ∀ z : Z, z ∈ W' o' ↔ z ∈ W o)
    (hFrontier : ∀ (N s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let Z := (Fin N → Bool) × (Fin N → Bool)
      let one := fun (p i : Fin N) => decide (i = p)
      o < N + N + s →
      (∀ p : Fin N, W ↑p = { z : Z | z.1 p = true } ∧ W (N + ↑p) = { z : Z | z.2 p = true }) →
      (∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
        W (N + N + g) = W a ∪ W b ∨ W (N + N + g) = W a ∩ W b) →
      (∀ p : Fin N, (one p, fun _ => false) ∉ W o ∧ (fun _ => false, one p) ∉ W o) →
      ∃ F : Finset ℕ,
        (∀ g ∈ F, g < s ∧ ∃ a < N + N + g, ∃ b < N + N + g, W (N + N + g) = W a ∩ W b) ∧
        ∀ z : Z, z ∈ W o ↔ ∃ g ∈ F, z ∈ W (N + N + g))
    (hFrontierBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let Z := (Fin N → Bool) × (Fin N → Bool)
      let one := fun (p i : Fin N) => decide (i = p)
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s : ℕ) (F : Finset ℕ) (W : ℕ → Set Z),
        (∀ p : Fin N, W ↑p = { z : Z | z.1 p = true } ∧ W (N + ↑p) = { z : Z | z.2 p = true }) →
        (∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
          W (N + N + g) = W a ∪ W b ∨ W (N + N + g) = W a ∩ W b) →
        (∀ g ∈ F, g < s ∧ ∃ a < N + N + g, ∃ b < N + N + g, W (N + N + g) = W a ∩ W b) →
        (∀ p l : Fin N, I p l → ∃ g ∈ F, (one p, one l) ∈ W (N + N + g)) →
        (∀ g ∈ F, ∀ z : Z, Fintype.card { l : Fin N // z.2 l = true } ≤ q →
          z ∈ W (N + N + g) → ∃ p l : Fin N, I p l ∧ z.1 p = true ∧ z.2 l = true) →
        N * q ≤ 100 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           (∀ (x9 : Finset (Fin x2)), ∀ x10 ∈ x9, x1 + (2 : ℕ) ≤ x9.card + Fintype.card { x12 : Fin x2 // x3 x12 x10 ∧ ∀ x13 ∈ x9.erase x10, ¬x3 x12 x13 }) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               have x15 : Bool → ℕ → Set (Fin x2) := fun (x15 : Bool) (x16 : ℕ) => {x17 : Fin x2 | (if x15 = Bool.true then (x14 x17, fun (x18 : Fin x2) => Bool.false) else (fun (x18 : Fin x2) => Bool.false, x14 x17)) ∈ x12 x16};               x11 < x13 + x10 → (∀ (x17 : Fin x2), x12 ↑x17 = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.1 x17 = Bool.true} ∧ x12 (x2 + ↑x17) = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.2 x17 = Bool.true}) → (∀ x18 < x10, ∃ (x20 : ℕ) (x21 : ℕ), Max.max x20 x21 < x13 + x18 ∧ x12 (x13 + x18) ∈ [x12 x20 ∪ x12 x21, x12 x20, ∅, x12 x20 ∩ x12 x21]) → (∀ (x19 : (Fin x2 → Bool) × (Fin x2 → Bool)), Fintype.card { x20 : Fin x2 // x19.2 x20 = Bool.true } ≤ x1 → (x19 ∈ x12 x11 ↔ ∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19.1 x21 = Bool.true ∧ x19.2 x22 = Bool.true)) → (∃ x20 < x10, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x15 x21 (x13 + x20) ∧ x23 ∈ x15 x21 (x13 + x20) ∧ ¬∃ x24 < x13 + x20, ∃ x25 < x13 + x20, x15 x21 (x13 + x20) = x15 x21 x24 ∪ x15 x21 x25) → x2 * x1 ≤ (100 : ℕ) * x10 := by
  intro q N I inst hq hN hdeg huniq _hpriv s o W
  dsimp only
  intro ho hin hgate hsound _hex
  let one : Fin N → Fin N → Bool := fun a b => decide (b = a)
  have hcard_one : ∀ a : Fin N, Fintype.card { x : Fin N // one a x = true } ≤ q := by
    intro a
    have hsub : Subsingleton { x : Fin N // one a x = true } := by
      refine ⟨fun u v => Subtype.ext ?_⟩
      have hu : u.1 = a := of_decide_eq_true u.property
      have hv : v.1 = a := of_decide_eq_true v.property
      exact hu.trans hv.symm
    exact le_trans (Fintype.card_le_one_iff_subsingleton.mpr hsub) (by omega)
  have hcard_zero : Fintype.card { x : Fin N // (fun _ : Fin N => false) x = true } ≤ q := by
    have hemp : IsEmpty { x : Fin N // (fun _ : Fin N => false) x = true } :=
      ⟨fun u => Bool.false_ne_true u.property⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le q
  have hpoint_deg : ∀ l : Fin N, ∃ p : Fin N, I p l := by
    intro l
    have hpos : 0 < Fintype.card { p : Fin N // I p l } := by rw [hdeg l]; omega
    obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨w.1, w.2⟩
  by_cases hsmall : q < 200
  · have hreach : ∀ (k : ℕ), k ≤ s → ∀ U : Finset ℕ, (∀ u ∈ U, u < N + N + k) →
        ∃ S : Finset ℕ, S ⊆ Finset.range (N + N) ∧ S.card ≤ U.card + k ∧
          ∀ u ∈ U, ∀ z1 z2 : (Fin N → Bool) × (Fin N → Bool),
            (∀ v ∈ S, z1 ∈ W v ↔ z2 ∈ W v) → (z1 ∈ W u ↔ z2 ∈ W u) := by
      intro k
      induction k with
      | zero =>
        intro _ U hU
        refine ⟨U, fun u hu => Finset.mem_range.mpr ?_, by omega, fun u hu z1 z2 hag => hag u hu⟩
        have hlt := hU u hu
        omega
      | succ k ih =>
        intro hk U hU
        by_cases hmem : N + N + k ∈ U
        · obtain ⟨a, b, hmax, hlaw⟩ := hgate k (by omega)
          let U' := insert a (insert b (U.erase (N + N + k)))
          have hU' : ∀ u ∈ U', u < N + N + k := by
            intro u hu
            rcases Finset.mem_insert.mp hu with hua | hu1
            · rw [hua]; exact lt_of_le_of_lt (le_max_left a b) hmax
            · rcases Finset.mem_insert.mp hu1 with hub | hu2
              · rw [hub]; exact lt_of_le_of_lt (le_max_right a b) hmax
              · have hne := (Finset.mem_erase.mp hu2).1
                have hlt := hU u (Finset.mem_erase.mp hu2).2
                omega
          obtain ⟨S, hSsub, hScard, hSag⟩ := ih (by omega) U' hU'
          have hUcard : U'.card ≤ U.card + 1 := by
            have c1 := Finset.card_insert_le a (insert b (U.erase (N + N + k)))
            have c2 := Finset.card_insert_le b (U.erase (N + N + k))
            have c3 := Finset.card_erase_add_one hmem
            dsimp [U'] at c1 c2 ⊢
            omega
          refine ⟨S, hSsub, by omega, ?_⟩
          intro u hu z1 z2 hag
          by_cases hueq : u = N + N + k
          · subst u
            have hwa := hSag a (Finset.mem_insert_self a _) z1 z2 hag
            have hwb := hSag b (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)) z1 z2 hag
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hlaw
            rcases hlaw with h1 | h1 | h1 | h1
            · rw [h1]; exact or_congr hwa hwb
            · rw [h1]; exact hwa
            · rw [h1]; exact Iff.rfl
            · rw [h1]; exact and_congr hwa hwb
          · exact hSag u (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hueq, hu⟩))) z1 z2 hag
        · have hU' : ∀ u ∈ U, u < N + N + k := by
            intro u hu
            have hlt := hU u hu
            have hne : u ≠ N + N + k := fun eq => hmem (eq ▸ hu)
            omega
          obtain ⟨S, hSsub, hScard, hSag⟩ := ih (by omega) U hU'
          exact ⟨S, hSsub, by omega, hSag⟩
    obtain ⟨S, hSsub, hScard, hSag⟩ := hreach s le_rfl {o} (by
      intro u hu
      rw [Finset.mem_singleton.mp hu]
      exact ho)
    have hNge2 : 2 ≤ N := by nlinarith [Nat.zero_le (q ^ 2)]
    have hall : Finset.range (N + N) ⊆ S := by
      intro v hv
      have hvlt := Finset.mem_range.mp hv
      by_cases hpt : v < N
      · let p : Fin N := ⟨v, hpt⟩
        let p' : Fin N := if v = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hne : p ≠ p' := by
          intro hpe
          have hval := congrArg Fin.val hpe
          by_cases hv0 : v = 0
          · simp [p, p', hv0] at hval
          · simp [p, p', hv0] at hval
        obtain ⟨l, hl, _⟩ := huniq p p' hne
        let z1 : (Fin N → Bool) × (Fin N → Bool) := (one p, one l)
        let z2 : (Fin N → Bool) × (Fin N → Bool) := (fun _ => false, one l)
        have hz1 : z1 ∈ W o := by
          apply (hsound z1 (hcard_one l)).mpr
          refine ⟨p, l, hl.1, ?_, ?_⟩
          · exact decide_eq_true rfl
          · exact decide_eq_true rfl
        have hz2 : z2 ∉ W o := by
          intro hm
          obtain ⟨a, _, _, ha, _⟩ := (hsound z2 (hcard_one l)).mp hm
          exact Bool.false_ne_true ha
        by_contra hnot
        have hag : ∀ u ∈ S, z1 ∈ W u ↔ z2 ∈ W u := by
          intro u hu
          have hult := Finset.mem_range.mp (hSsub hu)
          by_cases hup : u < N
          · let k : Fin N := ⟨u, hup⟩
            have hne' : k ≠ p := by
              intro hk
              have hval : v = u := (congrArg Fin.val hk).symm
              exact hnot (hval ▸ hu)
            have heqk : W u = { z : (Fin N → Bool) × (Fin N → Bool) | z.1 k = true } := (hin k).1
            rw [heqk]
            change one p k = true ↔ false = true
            have hfalse : one p k = false := decide_eq_false hne'
            rw [hfalse]
          · let k : Fin N := ⟨u - N, by omega⟩
            have hequ : u = N + k.val := by dsimp [k]; omega
            rw [hequ, (hin k).2]
            exact Iff.rfl
        have heq := (hSag o (Finset.mem_singleton_self o) z1 z2 hag).mp hz1
        exact hz2 heq
      · let l : Fin N := ⟨v - N, by omega⟩
        obtain ⟨p, hpl⟩ := hpoint_deg l
        let z1 : (Fin N → Bool) × (Fin N → Bool) := (one p, one l)
        let z2 : (Fin N → Bool) × (Fin N → Bool) := (one p, fun _ => false)
        have hz1 : z1 ∈ W o := by
          apply (hsound z1 (hcard_one l)).mpr
          refine ⟨p, l, hpl, ?_, ?_⟩
          · exact decide_eq_true rfl
          · exact decide_eq_true rfl
        have hz2 : z2 ∉ W o := by
          intro hm
          obtain ⟨_, b, _, _, hb⟩ := (hsound z2 hcard_zero).mp hm
          exact Bool.false_ne_true hb
        by_contra hnot
        have hag : ∀ u ∈ S, z1 ∈ W u ↔ z2 ∈ W u := by
          intro u hu
          have hult := Finset.mem_range.mp (hSsub hu)
          by_cases hup : u < N
          · let k : Fin N := ⟨u, hup⟩
            have heqk : W u = { z : (Fin N → Bool) × (Fin N → Bool) | z.1 k = true } := (hin k).1
            rw [heqk]
            exact Iff.rfl
          · let k : Fin N := ⟨u - N, by omega⟩
            have hequ : u = N + k.val := by dsimp [k]; omega
            have hne' : k ≠ l := by
              intro hk
              have hval : v = u := by
                have hkl := congrArg Fin.val hk
                dsimp [k, l] at hkl
                omega
              exact hnot (hval ▸ hu)
            rw [hequ, (hin k).2]
            change one l k = true ↔ false = true
            have hfalse : one l k = false := decide_eq_false hne'
            rw [hfalse]
        have heq := (hSag o (Finset.mem_singleton_self o) z1 z2 hag).mp hz1
        exact hz2 heq
    have hcount : N + N ≤ S.card := by
      have hc := Finset.card_le_card hall
      rw [Finset.card_range] at hc
      exact hc
    simp only [Finset.card_singleton] at hScard
    have hbound1 : N + N ≤ 1 + s := hcount.trans hScard
    have hNge100 : 100 ≤ N := by nlinarith [Nat.zero_le (q ^ 2)]
    have hqle : q ≤ 199 := by omega
    have hmul := Nat.mul_le_mul_left N hqle
    omega
  · have hlarge : 200 ≤ q := by omega
    have hl0 : 0 < N := by nlinarith [Nat.zero_le (q ^ 2)]
    obtain ⟨p0, hp0l0⟩ := hpoint_deg ⟨0, hl0⟩
    have hne : ∃ z : (Fin N → Bool) × (Fin N → Bool), z ∈ W o := by
      refine ⟨(one p0, one ⟨0, hl0⟩), (hsound (one p0, one ⟨0, hl0⟩) (hcard_one ⟨0, hl0⟩)).mpr ?_⟩
      exact ⟨p0, ⟨0, hl0⟩, hp0l0, decide_eq_true rfl, decide_eq_true rfl⟩
    obtain ⟨s', hs'le, o', ho', W', hin', hgate', heq⟩ := hNorm N s o W ho hin hgate hne
    have hone_off : ∀ p : Fin N, (one p, fun _ => false) ∉ W' o' ∧ (fun _ => false, one p) ∉ W' o' := by
      intro p
      constructor
      · intro hmem
        have hm := (heq (one p, fun _ => false)).mp hmem
        obtain ⟨_, b, _, _, hb⟩ := (hsound (one p, fun _ => false) hcard_zero).mp hm
        exact Bool.false_ne_true hb
      · intro hmem
        have hm := (heq (fun _ => false, one p)).mp hmem
        obtain ⟨a, _, _, ha, _⟩ := (hsound (fun _ => false, one p) (hcard_one p)).mp hm
        exact Bool.false_ne_true ha
    obtain ⟨F, hFand, hFcov⟩ := hFrontier N s' o' W' ho' hin' hgate' hone_off
    have hpairs : ∀ p l : Fin N, I p l → ∃ g ∈ F, (one p, one l) ∈ W' (N + N + g) := by
      intro p l hpl
      have hwo : (one p, one l) ∈ W o :=
        (hsound (one p, one l) (hcard_one l)).mpr ⟨p, l, hpl, decide_eq_true rfl, decide_eq_true rfl⟩
      exact (hFcov (one p, one l)).mp ((heq (one p, one l)).mpr hwo)
    have hfsound : ∀ g ∈ F, ∀ z : (Fin N → Bool) × (Fin N → Bool),
        Fintype.card { l : Fin N // z.2 l = true } ≤ q →
        z ∈ W' (N + N + g) → ∃ p l : Fin N, I p l ∧ z.1 p = true ∧ z.2 l = true := by
      intro g hg z hzsp hzg
      have hzwo' : z ∈ W' o' := (hFcov z).mpr ⟨g, hg, hzg⟩
      exact (hsound z hzsp).mp ((heq z).mp hzwo')
    have hres := hFrontierBound q N I hlarge hN hdeg huniq s' F W' hin' hgate' hFand hpairs hfsound
    nlinarith
