import PEqualNP.Defs

-- The overlapping OR gate is not used: the bound holds for every such circuit.
-- One choice bit per gate suffices to realize every minimal sparse-line cover
-- (proved here by induction on the number of gates; the cover is minimal by counting).
-- Orient those bits so that the all-false setting gives exactly the line inputs.
-- The pair tests already cost three times the number of points minus one gates.
set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4476_1
    (linear : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N+N+s →
      (∀ v < N+N, F v = {{v}}) → (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
        F (N+N+j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
        F (N+N+j) = F a ∨ F (N+N+j) = {∅} ∨ F (N+N+j) = F a ∪ F b) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N+l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N, (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) → 3*N ≤ s+1)
    (network : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 300 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ),
      o < N+N+s → 3*N ≤ s+1 → (∀ z v, v < N+N → D z v = {v}) →
      (∀ j : Fin s, ∃ a < N+N+j.val, ∃ b < N+N+j.val,
        (∀ z, D z (N+N+j.val) = D z a ∪ D z b) ∨
        (∀ z, D z (N+N+j.val) = if z j then D z a else D z b) ∨
        ∀ z, D z (N+N+j.val) = ∅) →
      (∀ z, ∀ p l : Fin N, I p l → p.val ∈ D z o ∨ N+l.val ∈ D z o) →
      (∀ p : Fin N, p.val ∉ D (fun _ => false) o ∧ N+p.val ∈ D (fun _ => false) o) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ z, ∀ p : Fin N, (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ D z o ↔ p ∉ T)) →
      N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∃ x15 < x9, ∃ x16 < x2 + x2 + x15, ∃ x17 < x2 + x2 + x15, x11 (x2 + x2 + x15) = x11 x16 ∪ x11 x17 ∧ ∃ x18 ∈ x11 x16, ∃ x19 ∈ x11 x17, ¬Disjoint x18 x19) → (∀ x16 ∈ x11 x10, ∀ (x18 x19 : Fin x2), x3 x18 x19 → ↑x18 ∈ x16 ∨ x2 + ↑x19 ∈ x16) → (∀ (x17 : Finset (Fin x2)), x17.card ≤ x1 → ∃ x19 ∈ x11 x10, ∀ (x20 : Fin x2), (↑x20 ∈ x19 ↔ ∃ x21 ∈ x17, x3 x20 x21) ∧ (x2 + ↑x20 ∈ x19 ↔ x20 ∉ x17)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI q200 order degree unique s o F room inputs gates _overlap safe saturated
  have count := linear q N I (by omega) order degree unique s o F room inputs gates safe saturated
  by_cases modest : q ≤ 299
  · have product := Nat.mul_le_mul_left N modest
    omega
  · have choices : ∀ t : ℕ, (∀ j < t, ∃ a < N+N+j, ∃ b < N+N+j,
          F (N+N+j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
          F (N+N+j) = F a ∨ F (N+N+j) = {∅} ∨ F (N+N+j) = F a ∪ F b) →
        ∃ D : (Fin t → Bool) → ℕ → Finset ℕ,
          (∀ z v, v < N+N → D z v = {v}) ∧ (∀ j : Fin t, ∃ a < N+N+j.val, ∃ b < N+N+j.val,
          (∀ z, D z (N+N+j.val) = D z a ∪ D z b) ∨
          (∀ z, D z (N+N+j.val) = if z j then D z a else D z b) ∨
          ∀ z, D z (N+N+j.val) = ∅) ∧
          (∀ z, ∀ v < N+N+t, D z v ∈ F v) ∧
          ∀ A : Finset ℕ, ∃ z, ∀ v < N+N+t, (∃ B ∈ F v, B ⊆ A) → D z v ⊆ A := by
      intro t
      induction t with
      | zero =>
        intro _
        refine ⟨fun _ v => {v}, fun _ _ _ => rfl, fun j => j.elim0, ?_, ?_⟩
        · intro z v hv
          rw [inputs v (by omega)]
          exact Set.mem_singleton _
        · intro A
          refine ⟨fun j => j.elim0, ?_⟩
          rintro v hv ⟨B, hB, hBA⟩
          rw [inputs v (by omega), Set.mem_singleton_iff] at hB
          subst hB
          exact hBA
      | succ t ih =>
        intro hg
        obtain ⟨D, bits, steps, sound, realize⟩ := ih (fun j hj => hg j (by omega))
        obtain ⟨a, ha, b, hb, hk⟩ : ∃ a < N+N+t, ∃ b < N+N+t,
            F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
            F (N+N+t) = F a ∪ F b ∨ F (N+N+t) = {∅} := by
          obtain ⟨a, ha, b, hb, h | h | h | h⟩ := hg t (by omega)
          · exact ⟨a, ha, b, hb, Or.inl h⟩
          · exact ⟨a, ha, a, ha, Or.inr (Or.inl (by rw [h, Set.union_self]))⟩
          · exact ⟨a, ha, b, hb, Or.inr (Or.inr h)⟩
          · exact ⟨a, ha, b, hb, Or.inr (Or.inl h)⟩
        let r : (Fin (t+1) → Bool) → Fin t → Bool := fun z j => z j.castSucc
        let G : (Fin (t+1) → Bool) → Finset ℕ := fun z =>
          if F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) then
            D (r z) a ∪ D (r z) b
          else if F (N+N+t) = F a ∪ F b then (if z (Fin.last t) then D (r z) a else D (r z) b)
          else ∅
        let D' : (Fin (t+1) → Bool) → ℕ → Finset ℕ := fun z v =>
          if v = N+N+t then G z else D (r z) v
        have old : ∀ z v, v < N+N+t → D' z v = D (r z) v := by
          intro z v hv
          change (if v = N+N+t then G z else D (r z) v) = D (r z) v
          rw [if_neg (by omega)]
        have new : ∀ z, D' z (N+N+t) = G z := by
          intro z
          change (if N+N+t = N+N+t then G z else D (r z) (N+N+t)) = G z
          rw [if_pos rfl]
        refine ⟨D', ?_, ?_, ?_, ?_⟩
        · intro z v hv
          rw [old z v (by omega)]
          exact bits _ v hv
        · intro j
          by_cases hj : j.val < t
          · obtain ⟨a', ha', b', hb', h | h | h⟩ := steps ⟨j.val, hj⟩
            · refine ⟨a', ha', b', hb', Or.inl (fun z => ?_)⟩
              rw [old z _ (by omega), old z a' (by omega), old z b' (by omega)]
              exact h (r z)
            · refine ⟨a', ha', b', hb', Or.inr (Or.inl (fun z => ?_))⟩
              rw [old z _ (by omega), old z a' (by omega), old z b' (by omega)]
              exact h (r z)
            · refine ⟨a', ha', b', hb', Or.inr (Or.inr (fun z => ?_))⟩
              rw [old z _ (by omega)]
              exact h (r z)
          · have hjt : j = Fin.last t := Fin.ext (by rw [Fin.val_last]; omega)
            subst hjt
            refine ⟨a, by rw [Fin.val_last]; exact ha, b, by rw [Fin.val_last]; exact hb, ?_⟩
            by_cases hJ : F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b)
            · refine Or.inl (fun z => ?_)
              rw [Fin.val_last, new, old z a ha, old z b hb]
              change (if F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) then
                D (r z) a ∪ D (r z) b
                else if F (N+N+t) = F a ∪ F b then (if z (Fin.last t) then D (r z) a else D (r z) b)
                else ∅) = _
              rw [if_pos hJ]
            · by_cases hO : F (N+N+t) = F a ∪ F b
              · refine Or.inr (Or.inl (fun z => ?_))
                rw [Fin.val_last, new, old z a ha, old z b hb]
                change (if F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) then
                  D (r z) a ∪ D (r z) b
                  else if F (N+N+t) = F a ∪ F b then (if z (Fin.last t) then D (r z) a else D (r z) b)
                  else ∅) = _
                rw [if_neg hJ, if_pos hO]
              · refine Or.inr (Or.inr (fun z => ?_))
                rw [Fin.val_last, new]
                change (if F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) then
                  D (r z) a ∪ D (r z) b
                  else if F (N+N+t) = F a ∪ F b then (if z (Fin.last t) then D (r z) a else D (r z) b)
                  else ∅) = _
                rw [if_neg hJ, if_neg hO]
        · intro z v hv
          by_cases hvt : v = N+N+t
          · subst hvt
            rw [new]
            change (if F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) then
                D (r z) a ∪ D (r z) b
                else if F (N+N+t) = F a ∪ F b then (if z (Fin.last t) then D (r z) a else D (r z) b)
                else ∅) ∈ _
            split_ifs with hJ hO hc
            · rw [hJ]
              exact Set.mem_image2_of_mem (sound _ a ha) (sound _ b hb)
            · rw [hO]
              exact Or.inl (sound _ a ha)
            · rw [hO]
              exact Or.inr (sound _ b hb)
            · rcases hk with h | h | h
              · exact absurd h hJ
              · exact absurd h hO
              · rw [h]
                exact Set.mem_singleton _
          · rw [old z v (by omega)]
            exact sound _ v (by omega)
        · intro A
          obtain ⟨z0, hz0⟩ := realize A
          let z' : Fin (t+1) → Bool := fun j =>
            if h : j.val < t then z0 ⟨j.val, h⟩ else decide (∃ B ∈ F a, B ⊆ A)
          have hr : r z' = z0 := by
            funext j
            change (if h : j.castSucc.val < t then z0 ⟨j.castSucc.val, h⟩
              else decide (∃ B ∈ F a, B ⊆ A)) = z0 j
            rw [dif_pos (by simp)]
            rfl
          have hlast : z' (Fin.last t) = decide (∃ B ∈ F a, B ⊆ A) := by
            change (if h : (Fin.last t).val < t then z0 ⟨(Fin.last t).val, h⟩
              else decide (∃ B ∈ F a, B ⊆ A)) = _
            rw [dif_neg (by simp)]
          refine ⟨z', ?_⟩
          rintro v hv ⟨B, hB, hBA⟩
          by_cases hvt : v = N+N+t
          · subst hvt
            rw [new]
            change (if F (N+N+t) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) then
                D (r z') a ∪ D (r z') b
                else if F (N+N+t) = F a ∪ F b then (if z' (Fin.last t) then D (r z') a else D (r z') b)
                else ∅) ⊆ _
            rw [hr, hlast]
            split_ifs with hJ hO hc
            · rw [hJ] at hB
              obtain ⟨Ba, hBa, Bb, hBb, rfl⟩ := hB
              exact Finset.union_subset
                (hz0 a ha ⟨Ba, hBa, subset_trans Finset.subset_union_left hBA⟩)
                (hz0 b hb ⟨Bb, hBb, subset_trans Finset.subset_union_right hBA⟩)
            · exact hz0 a ha (of_decide_eq_true hc)
            · have hn : ¬ ∃ B ∈ F a, B ⊆ A := fun hx => hc (decide_eq_true hx)
              rw [hO] at hB
              rcases hB with h | h
              · exact absurd ⟨B, h, hBA⟩ hn
              · exact hz0 b hb ⟨B, h, hBA⟩
            · exact Finset.empty_subset _
          · rw [old z' v (by omega), hr]
            exact hz0 v (by omega) ⟨B, hB, hBA⟩
    have minimal : ∀ (T : Finset (Fin N)) (A B : Finset ℕ), T.card ≤ q → B ⊆ A →
        (∀ p l : Fin N, I p l → p.val ∈ B ∨ N+l.val ∈ B) →
        (∀ p : Fin N, (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) →
        ∀ p : Fin N, (p.val ∈ B ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ B ↔ p ∉ T) := by
      intro T A B hT hBA hcov hA p
      have uncovered : ∀ l : Fin N, l ∉ T → ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k := by
        intro l hl
        by_contra hcon
        have hcv : ∀ p : Fin N, I p l → ∃ k ∈ T, I p k := by
          intro p hp
          by_contra hno
          exact hcon ⟨p, hp, fun k hk hpk => hno ⟨k, hk, hpk⟩⟩
        have h1 : (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
          rw [← Fintype.card_subtype]
          exact degree l
        have h2 : Finset.univ.filter (fun p : Fin N => I p l)
            ⊆ T.biUnion (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨k, hk, hpk⟩ := hcv p hp.2
          rw [Finset.mem_biUnion]
          exact ⟨k, hk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2, hpk⟩⟩
        have h3 : ∀ k ∈ T, (Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)).card ≤ 1 := by
          intro k hk
          rw [Finset.card_le_one]
          intro a ha b hb
          rw [Finset.mem_filter] at ha hb
          by_contra hab
          obtain ⟨l0, _, hl0⟩ := unique a b hab
          have e1 : l = l0 := hl0 l ⟨ha.2.1, hb.2.1⟩
          have e2 : k = l0 := hl0 k ⟨ha.2.2, hb.2.2⟩
          exact hl (by rw [e1, ← e2]; exact hk)
        have h4 := Finset.card_le_card h2
        have h5 := Finset.card_biUnion_le_card_mul T
          (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)) 1 h3
        omega
      refine ⟨⟨fun hpB => (hA p).1.mp (hBA hpB), ?_⟩, ⟨fun hB => (hA p).2.mp (hBA hB), ?_⟩⟩
      · intro hex
        obtain ⟨l, hlT, hpl⟩ := hex
        rcases hcov p l hpl with h | h
        · exact h
        · exact absurd hlT ((hA l).2.mp (hBA h))
      · intro hpT
        obtain ⟨p0, hp0, hno⟩ := uncovered p hpT
        rcases hcov p0 p hp0 with h | h
        · exfalso
          obtain ⟨k, hk, hIk⟩ := (hA p0).1.mp (hBA h)
          exact hno k hk hIk
        · exact h
    obtain ⟨D, bits, steps, sound0, realize0⟩ := choices s gates
    have sound : ∀ z, D z o ∈ F o := fun z => sound0 z o room
    have realize : ∀ A ∈ F o, ∃ z, D z o ⊆ A := by
      intro A hA
      obtain ⟨z, hz⟩ := realize0 A
      exact ⟨z, hz o room ⟨A, hA, subset_refl A⟩⟩
    have chosen (T : Finset (Fin N)) (small : T.card ≤ q) : ∃ z, ∀ p : Fin N,
        (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ D z o ↔ p ∉ T) := by
      obtain ⟨A,inA,spec⟩ := saturated T small
      obtain ⟨z,sub⟩ := realize A inA
      exact ⟨z,minimal T A (D z o) small sub (safe _ (sound z)) spec⟩
    obtain ⟨base, empty⟩ := chosen ∅ (by simp)
    let flip := fun (z : Fin s → Bool) (j : Fin s) => if base j then !z j else z j
    let norm := fun (z : Fin s → Bool) => D (flip z)
    have twice (z : Fin s → Bool) : flip (flip z) = z := by
      funext j
      cases hb : base j <;> simp [flip,hb]
    have zero : flip (fun _ => false) = base := by
      funext j
      cases hb : base j <;> simp [flip,hb]
    apply network q N I (by omega) order degree unique s o norm room count
    · exact fun z v hv => bits (flip z) v hv
    · intro j
      obtain ⟨a,ha,b,hb,join | choice | unit⟩ := steps j
      · exact ⟨a,ha,b,hb,Or.inl (fun z => join (flip z))⟩
      · cases baseBit : base j with
        | false =>
          refine ⟨a,ha,b,hb,Or.inr (Or.inl (fun z => ?_))⟩
          simpa only [norm,flip,baseBit,Bool.false_eq_true,if_false] using choice (flip z)
        | true =>
          refine ⟨b,hb,a,ha,Or.inr (Or.inl (fun z => ?_))⟩
          have h := choice (flip z)
          change D (flip z) (N + N + j.val) = if z j then D (flip z) b else D (flip z) a
          rw [h]
          have sj : flip z j = !z j := by simp [flip,baseBit]
          cases v : z j <;> simp [sj,v]
      · exact ⟨a,ha,b,hb,Or.inr (Or.inr (fun z => unit (flip z)))⟩
    · exact fun z p l pl => safe _ (sound (flip z)) p l pl
    · intro p
      change p.val ∉ D (flip (fun _ => false)) o ∧ N+p.val ∈ D (flip (fun _ => false)) o
      rw [zero]
      have h := empty p
      simpa using h
    · intro T small
      obtain ⟨z,hz⟩ := chosen T small
      refine ⟨flip z, fun p => ?_⟩
      simpa only [norm, twice] using hz p
