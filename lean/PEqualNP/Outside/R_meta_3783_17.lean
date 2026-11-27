import PEqualNP.Defs
import Mathlib.Data.Nat.Find

theorem PEqualNP.Outside.R_meta_3783_17
    (h1 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],
      (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
      x1 % (2 : ℕ) = (1 : ℕ) →
      ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),
        have x13 : ℕ := x2 + x2;
        have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
        x13 ≤ x11 ∧ x11 < x13 + x10 →
        (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →
        (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), x19 ≠ x20 ∧ Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19 ∩ x12 x20]) →
        (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →
        (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →
        (have x20 : ℕ → Set (Fin x2) := fun (x20 : ℕ) => {x21 : Fin x2 | (x14 x21, fun (_ : Fin x2) => Bool.false) ∈ x12 x20};
          x20 x11 = ∅ ∧
          ∃ x21 < x10,
            (∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x13 + x21 ∧ x12 (x13 + x21) = x12 x23 ∩ x12 x24) ∧
            (∀ x23 < x21, ∃ x25 < x13 + x23, ∃ x26 < x13 + x23, x20 (x13 + x23) = x20 x25 ∪ x20 x26) ∧
            (∃ (x23 x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 (x13 + x21) ∧ x24 ∈ x20 (x13 + x21)) ∧
            ¬∃ x23 < x13 + x21, ∃ x24 < x13 + x21, x20 (x13 + x21) = x20 x23 ∪ x20 x24) →
        x2 * x1 ≤ (100 : ℕ) * x10)
    (h2 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],
      (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
      x1 % (2 : ℕ) = (1 : ℕ) →
      ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),
        have x13 : ℕ := x2 + x2;
        have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
        x13 ≤ x11 ∧ x11 < x13 + x10 →
        (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →
        (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), x19 ≠ x20 ∧ Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19 ∩ x12 x20]) →
        (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →
        (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →
        (have x20 : ℕ → Set (Fin x2) := fun (x20 : ℕ) => {x21 : Fin x2 | (fun (_ : Fin x2) => Bool.false, x14 x21) ∈ x12 x20};
          x20 x11 = ∅ ∧
          ∃ x21 < x10,
            (∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x13 + x21 ∧ x12 (x13 + x21) = x12 x23 ∩ x12 x24) ∧
            (∀ x23 < x21, ∃ x25 < x13 + x23, ∃ x26 < x13 + x23, x20 (x13 + x23) = x20 x25 ∪ x20 x26) ∧
            (∃ (x23 x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 (x13 + x21) ∧ x24 ∈ x20 (x13 + x21)) ∧
            ¬∃ x23 < x13 + x21, ∃ x24 < x13 + x21, x20 (x13 + x21) = x20 x23 ∪ x20 x24) →
        x2 * x1 ≤ (100 : ℕ) * x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (1 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (_ : Fin x2) => Bool.false) else (fun (_ : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x22 : Bool) (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 x22 (x13 + x21) ∧ x24 ∈ x20 x22 (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 x22 (x13 + x21) = x20 x22 x25 ∪ x20 x22 x26) →                           x2 * x1 ≤ (100 : ℕ) * x10 := by
  classical
  intro q N I hdec hq hN hcard huniq hodd s out W _x13 _x14 hout hin hgates hright hfalse hbad
  let unit : Fin N → Fin N → Bool := fun a b => decide (b = a)
  let oh (A : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (b : Bool) (w : ℕ) : Set (Fin N) :=
    {u : Fin N | (if b = true then (unit u, fun _ => false) else (fun _ => false, unit u)) ∈ A w}
  have hoh_eq (A B : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (b : Bool) (w1 w2 : ℕ)
      (h : A w1 = B w2) : oh A b w1 = oh B b w2 := by
    ext u
    simp only [oh, Set.mem_ofPred_eq, h]
  have hoh_union (A : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (b : Bool) (w a c : ℕ)
      (h : A w = A a ∪ A c) : oh A b w = oh A b a ∪ oh A b c := by
    ext u
    simp only [oh, Set.mem_ofPred_eq, Set.mem_union, h]
  have hNpos : 0 < N := by
    have : 0 < q ^ 2 + q + 1 := Nat.succ_pos _
    omega
  have hcompress : ∀ t ≤ s,
      ∃ (m : ℕ) (W' : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (mp : ℕ → Option ℕ),
        m ≤ t ∧
        (∀ w < N + N, mp w = some w ∧ W' w = W w) ∧
        (∀ w < N + N + t, (mp w = none → W w = ∅) ∧
          ∀ w', mp w = some w' → w' < N + N + m ∧ W' w' = W w) ∧
        (∀ w' < N + N + m, ∃ w < N + N + t, W' w' = W w) ∧
        (∀ j < m, ∃ a c, a ≠ c ∧ max a c < N + N + j ∧
          W' (N + N + j) ∈ [W' a ∪ W' c, W' a ∩ W' c]) ∧
        (∀ (k : ℕ) (b : Bool), k < t →
          (∃ p1 p2 : Fin N, p1 ≠ p2 ∧ p1 ∈ oh W b (N + N + k) ∧ p2 ∈ oh W b (N + N + k)) →
          (¬∃ a < N + N + k, ∃ c < N + N + k, oh W b (N + N + k) = oh W b a ∪ oh W b c) →
          ∃ j < m, mp (N + N + k) = some (N + N + j) ∧
            ¬∃ a < N + N + j, ∃ c < N + N + j, oh W' b (N + N + j) = oh W' b a ∪ oh W' b c) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨0, W, fun w => some w, le_refl 0, ?_, ?_, ?_, ?_, ?_⟩
      · intro w _; exact ⟨rfl, rfl⟩
      · intro w hw
        refine ⟨fun h => (by cases h), fun w' h => ?_⟩
        cases h
        exact ⟨hw, rfl⟩
      · intro w' hw'; exact ⟨w', hw', rfl⟩
      · intro j hj; omega
      · intro k _ hk; omega
    | succ t ih =>
      intro ht1
      obtain ⟨m, W', mp, hm, hin', hmp, hsurj, hbin, hdirty⟩ := ih (by omega)
      have skip_step (opt : Option ℕ)
          (hopt : (opt = none → W (N + N + t) = ∅) ∧
            ∀ w', opt = some w' → w' < N + N + m ∧ W' w' = W (N + N + t)) :
          ∃ (m1 : ℕ) (W'1 : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (mp1 : ℕ → Option ℕ),
            m1 ≤ t + 1 ∧
            (∀ w < N + N, mp1 w = some w ∧ W'1 w = W w) ∧
            (∀ w < N + N + (t + 1), (mp1 w = none → W w = ∅) ∧
              ∀ w', mp1 w = some w' → w' < N + N + m1 ∧ W'1 w' = W w) ∧
            (∀ w' < N + N + m1, ∃ w < N + N + (t + 1), W'1 w' = W w) ∧
            (∀ j < m1, ∃ a c, a ≠ c ∧ max a c < N + N + j ∧
              W'1 (N + N + j) ∈ [W'1 a ∪ W'1 c, W'1 a ∩ W'1 c]) ∧
            (∀ (k : ℕ) (b : Bool), k < t + 1 →
              (∃ p1 p2 : Fin N, p1 ≠ p2 ∧ p1 ∈ oh W b (N + N + k) ∧ p2 ∈ oh W b (N + N + k)) →
              (¬∃ a < N + N + k, ∃ c < N + N + k, oh W b (N + N + k) = oh W b a ∪ oh W b c) →
              ∃ j < m1, mp1 (N + N + k) = some (N + N + j) ∧
                ¬∃ a < N + N + j, ∃ c < N + N + j, oh W'1 b (N + N + j) = oh W'1 b a ∪ oh W'1 b c) := by
        let mp1 : ℕ → Option ℕ := fun w => if w = N + N + t then opt else mp w
        refine ⟨m, W', mp1, by omega, ?_, ?_, ?_, hbin, ?_⟩
        · intro w hw
          have hne : w ≠ N + N + t := by omega
          simp only [mp1, hne, ↓reduceIte]
          exact hin' w hw
        · intro w hw
          by_cases hweq : w = N + N + t
          · subst hweq
            simp only [mp1, ↓reduceIte]
            exact hopt
          · simp only [mp1, hweq, ↓reduceIte]
            exact hmp w (by omega)
        · intro w' hw'
          obtain ⟨w, hw, heq⟩ := hsurj w' hw'
          exact ⟨w, by omega, heq⟩
        · intro k b hk htwo hnd
          by_cases hkt : k < t
          · have hne : N + N + k ≠ N + N + t := by omega
            obtain ⟨j, hj, hmpj, hndj⟩ := hdirty k b hkt htwo hnd
            refine ⟨j, hj, ?_, hndj⟩
            simp only [mp1, hne, ↓reduceIte]
            exact hmpj
          · have hkeq : k = t := by omega
            subst hkeq
            cases opt with
            | none =>
              have hempty := hopt.1 rfl
              obtain ⟨p1, _, _, hp1, _⟩ := htwo
              simp only [oh, Set.mem_ofPred_eq, hempty, Set.mem_empty_iff_false] at hp1
            | some w' =>
              obtain ⟨hw', heq'⟩ := hopt.2 w' rfl
              obtain ⟨w, hw, hWw⟩ := hsurj w' hw'
              exfalso
              apply hnd
              refine ⟨w, hw, w, hw, ?_⟩
              rw [Set.union_self]
              exact hoh_eq W W b (N + N + k) w (heq'.symm.trans hWw)
      have keep_step (a' c' : ℕ) (hne' : a' ≠ c') (hmax' : max a' c' < N + N + m)
          (hmem' : W (N + N + t) ∈ [W' a' ∪ W' c', W' a' ∩ W' c']) :
          ∃ (m1 : ℕ) (W'1 : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (mp1 : ℕ → Option ℕ),
            m1 ≤ t + 1 ∧
            (∀ w < N + N, mp1 w = some w ∧ W'1 w = W w) ∧
            (∀ w < N + N + (t + 1), (mp1 w = none → W w = ∅) ∧
              ∀ w', mp1 w = some w' → w' < N + N + m1 ∧ W'1 w' = W w) ∧
            (∀ w' < N + N + m1, ∃ w < N + N + (t + 1), W'1 w' = W w) ∧
            (∀ j < m1, ∃ a c, a ≠ c ∧ max a c < N + N + j ∧
              W'1 (N + N + j) ∈ [W'1 a ∪ W'1 c, W'1 a ∩ W'1 c]) ∧
            (∀ (k : ℕ) (b : Bool), k < t + 1 →
              (∃ p1 p2 : Fin N, p1 ≠ p2 ∧ p1 ∈ oh W b (N + N + k) ∧ p2 ∈ oh W b (N + N + k)) →
              (¬∃ a < N + N + k, ∃ c < N + N + k, oh W b (N + N + k) = oh W b a ∪ oh W b c) →
              ∃ j < m1, mp1 (N + N + k) = some (N + N + j) ∧
                ¬∃ a < N + N + j, ∃ c < N + N + j, oh W'1 b (N + N + j) = oh W'1 b a ∪ oh W'1 b c) := by
        let W'1 : ℕ → Set ((Fin N → Bool) × (Fin N → Bool)) :=
          fun w => if w = N + N + m then W (N + N + t) else W' w
        let mp1 : ℕ → Option ℕ :=
          fun w => if w = N + N + t then some (N + N + m) else mp w
        have hW'1_old (u : ℕ) (hu : u < N + N + m) : W'1 u = W' u := by
          have hne : u ≠ N + N + m := by omega
          simp only [W'1, hne, ↓reduceIte]
        have hW'1_new : W'1 (N + N + m) = W (N + N + t) := by
          simp only [W'1, ↓reduceIte]
        refine ⟨m + 1, W'1, mp1, by omega, ?_, ?_, ?_, ?_, ?_⟩
        · intro w hw
          have hne : w ≠ N + N + t := by omega
          simp only [mp1, hne, ↓reduceIte]
          rw [hW'1_old w (by omega)]
          exact hin' w hw
        · intro w hw
          by_cases hweq : w = N + N + t
          · subst hweq
            simp only [mp1, ↓reduceIte]
            refine ⟨fun h => (by cases h), fun w' h => ?_⟩
            cases h
            exact ⟨by omega, hW'1_new⟩
          · simp only [mp1, hweq, ↓reduceIte]
            have h := hmp w (by omega)
            refine ⟨h.1, fun w' hmw => ?_⟩
            obtain ⟨hw'lt, hw'eq⟩ := h.2 w' hmw
            exact ⟨by omega, (hW'1_old w' hw'lt).trans hw'eq⟩
        · intro w' hw'
          by_cases hw'm : w' < N + N + m
          · obtain ⟨w, hw, heq⟩ := hsurj w' hw'm
            exact ⟨w, by omega, (hW'1_old w' hw'm).trans heq⟩
          · have hweq : w' = N + N + m := by omega
            subst hweq
            exact ⟨N + N + t, by omega, hW'1_new⟩
        · intro j hj
          by_cases hjm : j < m
          · obtain ⟨a1, c1, hne1, hmax1, hmem1⟩ := hbin j hjm
            have ha1 : a1 < N + N + m := by omega
            have hc1 : c1 < N + N + m := by omega
            refine ⟨a1, c1, hne1, hmax1, ?_⟩
            rw [hW'1_old (N + N + j) (by omega), hW'1_old a1 ha1, hW'1_old c1 hc1]
            exact hmem1
          · have hjeq : j = m := by omega
            rw [hjeq]
            have ha' : a' < N + N + m := by omega
            have hc' : c' < N + N + m := by omega
            refine ⟨a', c', hne', hmax', ?_⟩
            rw [hW'1_new, hW'1_old a' ha', hW'1_old c' hc']
            exact hmem'
        · intro k b hk htwo hnd
          by_cases hkt : k < t
          · have hne : N + N + k ≠ N + N + t := by omega
            obtain ⟨j, hj, hmpj, hndj⟩ := hdirty k b hkt htwo hnd
            refine ⟨j, by omega, ?_, ?_⟩
            · simp only [mp1, hne, ↓reduceIte]
              exact hmpj
            · rintro ⟨a1, ha1, c1, hc1, heq⟩
              apply hndj
              refine ⟨a1, ha1, c1, hc1, ?_⟩
              rw [hoh_eq W' W'1 b (N + N + j) (N + N + j) (hW'1_old _ (by omega)).symm,
                  hoh_eq W' W'1 b a1 a1 (hW'1_old _ (by omega)).symm,
                  hoh_eq W' W'1 b c1 c1 (hW'1_old _ (by omega)).symm]
              exact heq
          · have hkeq : k = t := by omega
            subst hkeq
            refine ⟨m, by omega, ?_, ?_⟩
            · simp only [mp1, ↓reduceIte]
            · rintro ⟨a1, ha1, c1, hc1, heq⟩
              obtain ⟨wa, hwa, hWa⟩ := hsurj a1 ha1
              obtain ⟨wc, hwc, hWc⟩ := hsurj c1 hc1
              apply hnd
              refine ⟨wa, hwa, wc, hwc, ?_⟩
              rw [hoh_eq W W'1 b (N + N + k) (N + N + m) hW'1_new.symm,
                  hoh_eq W W'1 b wa a1 ((hW'1_old a1 ha1).trans hWa).symm,
                  hoh_eq W W'1 b wc c1 ((hW'1_old c1 hc1).trans hWc).symm]
              exact heq
      obtain ⟨a, c, hmax, hmem⟩ := hgates t (by omega)
      have ha : a < N + N + t := by omega
      have hc : c < N + N + t := by omega
      have hma := hmp a ha
      have hmc := hmp c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hU | hC | hE | hI
      · cases hmpa : mp a with
        | none =>
          have hWa : W a = ∅ := hma.1 hmpa
          have hWeq : W (N + N + t) = W c := by rw [hU, hWa, Set.empty_union]
          apply skip_step (mp c)
          exact ⟨fun h => hWeq.trans (hmc.1 h), fun c' h => ⟨(hmc.2 c' h).1, (hmc.2 c' h).2.trans hWeq.symm⟩⟩
        | some a' =>
          obtain ⟨ha'lt, ha'eq⟩ := hma.2 a' hmpa
          cases hmpc : mp c with
          | none =>
            have hWc : W c = ∅ := hmc.1 hmpc
            have hWeq : W (N + N + t) = W a := by rw [hU, hWc, Set.union_empty]
            apply skip_step (some a')
            refine ⟨fun h => (by cases h), fun w' h => ?_⟩
            cases h
            exact ⟨ha'lt, ha'eq.trans hWeq.symm⟩
          | some c' =>
            obtain ⟨hc'lt, hc'eq⟩ := hmc.2 c' hmpc
            by_cases hac' : a' = c'
            · apply skip_step (some a')
              refine ⟨fun h => (by cases h), fun w' h => ?_⟩
              cases h
              refine ⟨ha'lt, ?_⟩
              rw [hU, ← ha'eq, ← hc'eq, hac', Set.union_self]
            · apply keep_step a' c' hac' (max_lt ha'lt hc'lt)
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              exact Or.inl (by rw [hU, ← ha'eq, ← hc'eq])
      · apply skip_step (mp a)
        exact ⟨fun h => hC.trans (hma.1 h), fun a' h => ⟨(hma.2 a' h).1, (hma.2 a' h).2.trans hC.symm⟩⟩
      · exact skip_step none ⟨fun _ => hE, fun _ h => by cases h⟩
      · cases hmpa : mp a with
        | none =>
          have hWa : W a = ∅ := hma.1 hmpa
          exact skip_step none ⟨fun _ => by rw [hI, hWa, Set.empty_inter], fun _ h => by cases h⟩
        | some a' =>
          obtain ⟨ha'lt, ha'eq⟩ := hma.2 a' hmpa
          cases hmpc : mp c with
          | none =>
            have hWc : W c = ∅ := hmc.1 hmpc
            exact skip_step none ⟨fun _ => by rw [hI, hWc, Set.inter_empty], fun _ h => by cases h⟩
          | some c' =>
            obtain ⟨hc'lt, hc'eq⟩ := hmc.2 c' hmpc
            by_cases hac' : a' = c'
            · apply skip_step (some a')
              refine ⟨fun h => (by cases h), fun w' h => ?_⟩
              cases h
              refine ⟨ha'lt, ?_⟩
              rw [hI, ← ha'eq, ← hc'eq, hac', Set.inter_self]
            · apply keep_step a' c' hac' (max_lt ha'lt hc'lt)
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              exact Or.inr (by rw [hI, ← ha'eq, ← hc'eq])
  obtain ⟨m, W', mp, hm, hin', hmp, _, hbin, hdirty⟩ := hcompress s (le_refl s)
  have hinW' : ∀ i : Fin N,
      W' i.val = {z : (Fin N → Bool) × (Fin N → Bool) | z.1 i = true} ∧
      W' (N + i.val) = {z : (Fin N → Bool) × (Fin N → Bool) | z.2 i = true} := by
    intro i
    exact ⟨(hin' i.val (by omega)).2.trans (hin i).1,
           (hin' (N + i.val) (by omega)).2.trans (hin i).2⟩
  have hWout_ne : W out ≠ ∅ := by
    let l0 : Fin N := ⟨0, hNpos⟩
    have hc : 0 < Fintype.card { p : Fin N // I p l0 } := by rw [hcard l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hc
    intro hempty
    have hmem := hright p0 l0 hp0
    rw [hempty] at hmem
    exact hmem
  have hmpout := hmp out hout
  cases hmo : mp out with
  | none =>
    exact (hWout_ne (hmpout.1 hmo)).elim
  | some out' =>
    obtain ⟨hout'_lt, hout'_eq⟩ := hmpout.2 out' hmo
    have hmono : ∀ w < N + N + m, ∀ (p p' l l' : Fin N → Bool),
        (∀ i, p i = true → p' i = true) → (∀ i, l i = true → l' i = true) →
        (p, l) ∈ W' w → (p', l') ∈ W' w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw p p' l l' hp hl hmem
        by_cases h1w : w < N
        · have heq := (hinW' ⟨w, h1w⟩).1
          rw [heq] at hmem ⊢
          exact hp ⟨w, h1w⟩ hmem
        · by_cases h2w : w < N + N
          · have hsub : N + (w - N) = w := by omega
            have heq := (hinW' ⟨w - N, by omega⟩).2
            rw [hsub] at heq
            rw [heq] at hmem ⊢
            exact hl ⟨w - N, by omega⟩ hmem
          · have hsub : N + N + (w - (N + N)) = w := by omega
            obtain ⟨a, c, _, hmax, hgate⟩ := hbin (w - (N + N)) (by omega)
            rw [hsub] at hmax hgate
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
            rcases hgate with hU | hI
            · rw [hU] at hmem ⊢
              rcases hmem with ha | hc
              · exact Or.inl (ih a (by omega) (by omega) p p' l l' hp hl ha)
              · exact Or.inr (ih c (by omega) (by omega) p p' l l' hp hl hc)
            · rw [hI] at hmem ⊢
              exact ⟨ih a (by omega) (by omega) p p' l l' hp hl hmem.1,
                     ih c (by omega) (by omega) p p' l l' hp hl hmem.2⟩
    have hoh_out_true : oh W' true out' = ∅ := by
      ext p
      simp only [oh, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      have hcard0 : Fintype.card { l : Fin N // (fun _ : Fin N => false) l = true } ≤ q := by
        have hzero : Fintype.card { l : Fin N // (fun _ : Fin N => false) l = true } = 0 :=
          Fintype.card_eq_zero_iff.mpr ⟨fun x => Bool.noConfusion x.2⟩
        omega
      have hnf := hfalse (fun _ => false) hcard0
      rw [← hout'_eq] at hnf
      apply hnf
      refine hmono out' hout'_lt (unit p) _ (fun _ => false) (fun _ => false) ?_ (fun _ h => h) hp
      intro i _
      simp
    have hoh_out_false : oh W' false out' = ∅ := by
      ext l
      simp only [oh, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hl
      have hcard1 : Fintype.card { l' : Fin N // unit l l' = true } ≤ q := by
        have huniq_l : Fintype.card { l' : Fin N // unit l l' = true } = 1 := by
          have : Unique { l' : Fin N // unit l l' = true } := {
            default := ⟨l, by simp [unit]⟩
            uniq := fun x => Subtype.ext (by simpa [unit] using x.2)
          }
          exact Fintype.card_unique
        omega
      have hnf := hfalse (unit l) hcard1
      rw [← hout'_eq] at hnf
      apply hnf
      exact hmono out' hout'_lt (fun _ => false) _ (unit l) (unit l) (fun _ h => by cases h) (fun _ h => h) hl
    have hout'_ge : N + N ≤ out' := by
      by_contra hlt
      by_cases h1o : out' < N
      · have hmem : (⟨out', h1o⟩ : Fin N) ∈ oh W' true out' := by
          simp only [oh, ↓reduceIte, Set.mem_ofPred_eq, (hinW' ⟨out', h1o⟩).1, unit, decide_true]
        rw [hoh_out_true] at hmem
        exact hmem
      · have hsub : N + (out' - N) = out' := by omega
        have hmem : (⟨out' - N, by omega⟩ : Fin N) ∈ oh W' false out' := by
          simp only [oh, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
          have heq := (hinW' ⟨out' - N, by omega⟩).2
          rw [hsub] at heq
          rw [heq]
          simp [unit]
        rw [hoh_out_false] at hmem
        exact hmem
    have hoh_in_true_empty : oh W' true N = ∅ := by
      ext p
      simp only [oh, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have heq := (hinW' ⟨0, hNpos⟩).2
      simp only [Nat.add_zero] at heq
      rw [heq]
      simp
    have hoh_in_true_single (p : Fin N) : oh W' true p.val = {p} := by
      ext x
      simp only [oh, ↓reduceIte, Set.mem_ofPred_eq, (hinW' p).1, Set.mem_singleton_iff, unit, decide_eq_true_eq]
      exact eq_comm
    have hoh_in_false_empty : oh W' false 0 = ∅ := by
      ext l
      simp only [oh, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have heq := (hinW' ⟨0, hNpos⟩).1
      rw [heq]
      simp
    have hoh_in_false_single (l : Fin N) : oh W' false (N + l.val) = {l} := by
      ext x
      simp only [oh, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq, (hinW' l).2, Set.mem_singleton_iff, unit, decide_eq_true_eq]
      exact eq_comm
    have hright' : ∀ p l : Fin N, I p l → (unit p, unit l) ∈ W' out' := by
      intro p l hI
      rw [hout'_eq]
      exact hright p l hI
    have hfalse' : ∀ y : Fin N → Bool, Fintype.card { l : Fin N // y l = true } ≤ q →
        (fun p : Fin N => decide ¬∃ l : Fin N, I p l ∧ y l = true, y) ∉ W' out' := by
      intro y hy
      rw [hout'_eq]
      exact hfalse y hy
    obtain ⟨k0, hk0, b0, p1, p2, hne0, hp1, hp2, hnd0⟩ := hbad
    obtain ⟨j_ex, hj_ex, hmp_ex, hnd_ex⟩ :=
      hdirty k0 b0 hk0 ⟨p1, p2, hne0, hp1, hp2⟩ hnd0
    have hW_ex : W' (N + N + j_ex) = W (N + N + k0) :=
      ((hmp (N + N + k0) (by omega)).2 (N + N + j_ex) hmp_ex).2
    have htwo_ex : ∃ u1 u2 : Fin N, u1 ≠ u2 ∧ u1 ∈ oh W' b0 (N + N + j_ex) ∧ u2 ∈ oh W' b0 (N + N + j_ex) := by
      refine ⟨p1, p2, hne0, ?_, ?_⟩
      · rw [hoh_eq W' W b0 (N + N + j_ex) (N + N + k0) hW_ex]; exact hp1
      · rw [hoh_eq W' W b0 (N + N + j_ex) (N + N + k0) hW_ex]; exact hp2
    cases b0 with
    | true =>
      let Ptrue (j : ℕ) : Prop :=
        j < m ∧
        (∃ u1 u2 : Fin N, u1 ≠ u2 ∧ u1 ∈ oh W' true (N + N + j) ∧ u2 ∈ oh W' true (N + N + j)) ∧
        ¬∃ a < N + N + j, ∃ c < N + N + j, oh W' true (N + N + j) = oh W' true a ∪ oh W' true c
      have hex : ∃ j, Ptrue j := ⟨j_ex, hj_ex, htwo_ex, hnd_ex⟩
      let j0 := Nat.find hex
      have hj0 : Ptrue j0 := Nat.find_spec hex
      have hj0_min : ∀ k < j0, ¬ Ptrue k := fun k hk => Nat.find_min hex hk
      have hand0 : ∃ a c, max a c < N + N + j0 ∧ W' (N + N + j0) = W' a ∩ W' c := by
        obtain ⟨a, c, _, hmax, hgate⟩ := hbin j0 hj0.1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
        rcases hgate with hU | hI
        · exfalso
          apply hj0.2.2
          exact ⟨a, by omega, c, by omega, hoh_union W' true (N + N + j0) a c hU⟩
        · exact ⟨a, c, hmax, hI⟩
      have hclean0 : ∀ k < j0, ∃ a < N + N + k, ∃ c < N + N + k,
          oh W' true (N + N + k) = oh W' true a ∪ oh W' true c := by
        intro k hk
        by_cases htwo : ∃ u1 u2 : Fin N, u1 ≠ u2 ∧ u1 ∈ oh W' true (N + N + k) ∧ u2 ∈ oh W' true (N + N + k)
        · by_contra hno
          exact hj0_min k hk ⟨by omega, htwo, hno⟩
        · by_cases hne : ∃ u : Fin N, u ∈ oh W' true (N + N + k)
          · obtain ⟨u, hu⟩ := hne
            refine ⟨u.val, by omega, u.val, by omega, ?_⟩
            rw [Set.union_self, hoh_in_true_single u]
            ext x
            simp only [Set.mem_singleton_iff]
            constructor
            · intro hx
              by_contra hxu
              exact htwo ⟨x, u, hxu, hx, hu⟩
            · rintro rfl; exact hu
          · refine ⟨N, by omega, N, by omega, ?_⟩
            rw [Set.union_self, hoh_in_true_empty]
            ext x
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun hx => hne ⟨x, hx⟩
      have hres := h1 q N I hq hN hcard huniq hodd m out' W' ⟨hout'_ge, hout'_lt⟩ hinW' hbin hright' hfalse'
        ⟨hoh_out_true, j0, hj0.1, hand0, hclean0, hj0.2.1, hj0.2.2⟩
      omega
    | false =>
      let Pfalse (j : ℕ) : Prop :=
        j < m ∧
        (∃ u1 u2 : Fin N, u1 ≠ u2 ∧ u1 ∈ oh W' false (N + N + j) ∧ u2 ∈ oh W' false (N + N + j)) ∧
        ¬∃ a < N + N + j, ∃ c < N + N + j, oh W' false (N + N + j) = oh W' false a ∪ oh W' false c
      have hex : ∃ j, Pfalse j := ⟨j_ex, hj_ex, htwo_ex, hnd_ex⟩
      let j0 := Nat.find hex
      have hj0 : Pfalse j0 := Nat.find_spec hex
      have hj0_min : ∀ k < j0, ¬ Pfalse k := fun k hk => Nat.find_min hex hk
      have hand0 : ∃ a c, max a c < N + N + j0 ∧ W' (N + N + j0) = W' a ∩ W' c := by
        obtain ⟨a, c, _, hmax, hgate⟩ := hbin j0 hj0.1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
        rcases hgate with hU | hI
        · exfalso
          apply hj0.2.2
          exact ⟨a, by omega, c, by omega, hoh_union W' false (N + N + j0) a c hU⟩
        · exact ⟨a, c, hmax, hI⟩
      have hclean0 : ∀ k < j0, ∃ a < N + N + k, ∃ c < N + N + k,
          oh W' false (N + N + k) = oh W' false a ∪ oh W' false c := by
        intro k hk
        by_cases htwo : ∃ u1 u2 : Fin N, u1 ≠ u2 ∧ u1 ∈ oh W' false (N + N + k) ∧ u2 ∈ oh W' false (N + N + k)
        · by_contra hno
          exact hj0_min k hk ⟨by omega, htwo, hno⟩
        · by_cases hne : ∃ u : Fin N, u ∈ oh W' false (N + N + k)
          · obtain ⟨u, hu⟩ := hne
            refine ⟨N + u.val, by omega, N + u.val, by omega, ?_⟩
            rw [Set.union_self, hoh_in_false_single u]
            ext x
            simp only [Set.mem_singleton_iff]
            constructor
            · intro hx
              by_contra hxu
              exact htwo ⟨x, u, hxu, hx, hu⟩
            · rintro rfl; exact hu
          · refine ⟨0, by omega, 0, by omega, ?_⟩
            rw [Set.union_self, hoh_in_false_empty]
            ext x
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun hx => hne ⟨x, hx⟩
      have hres := h2 q N I hq hN hcard huniq hodd m out' W' ⟨hout'_ge, hout'_lt⟩ hinW' hbin hright' hfalse'
        ⟨hoh_out_false, j0, hj0.1, hand0, hclean0, hj0.2.1, hj0.2.2⟩
      omega
