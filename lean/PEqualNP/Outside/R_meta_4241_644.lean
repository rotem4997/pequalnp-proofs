import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_4241_644
    (compile : ∀ (N : ℕ) (C : Circuit) (K : Set (Finset (Fin N))), K.Nonempty → Monotone2 C →
      let F : Type := Set (Finset (Fin N))
      have allowed : Finset (Fin N) → Prop := fun (t : Finset (Fin N)) => ∃ k ∈ K, t ⊆ k
      have base : F → Prop := fun (A : F) =>
        A = ∅ ∨ A = {∅} ∨ ∃ i : Fin N, A = {t : Finset (Fin N) | t = {i} ∧ allowed t}
      have make : F → F → Set (Finset (Fin N)) := fun (A B : F) =>
        {t : Finset (Fin N) | allowed t ∧ ∃ a ∈ A, ∃ b ∈ B, t = a ∪ b}
      have avail : List F → F → Prop := fun (L : List F) (A : F) => base A ∨ A ∈ L
      have trim : F → Set (Finset (Fin N)) := fun (s : F) =>
        {t : Finset (Fin N) | Minimal (fun u : Finset (Fin N) => u ∈ s) t}
      have valid : List F → Prop := fun (L : List F) =>
        ∀ (H : List F) (A : F) (T : List F), L = H ++ A :: T → ¬ avail H A ∧
          ∃ u : F, avail H u ∧ ∃ v : F, avail H v ∧ (A = trim (u ∪ v) ∨ A = trim (make u v))
      ∃ L : List F, valid L ∧ L.length ≤ C.size ∧ ∀ i : ℕ, ∃ A : F, avail L A ∧
        (∀ t ∈ A, allowed t ∧ ∀ x : Fin N → Bool, (∀ j ∈ t, x j = false) →
          (C.wires (List.ofFn x)).getD i false = false) ∧
        ∀ k ∈ K, (C.wires (List.ofFn fun (j : Fin N) => decide (j ∉ k))).getD i false = false →
          ∃ t ∈ A, t ⊆ k)
    (coverCost :
      have lines : Fin 13 → Finset (Fin 13) := singerLines3
      have missed : Finset (Fin 13) → Finset (Fin 13) := missLines lines
      have K : Set (Finset (Fin 26)) := {z : Finset (Fin 26) | ∃ P : Finset (Fin 13),
        ((∀ p ∉ P, ∃ l ∈ missed P, p ∈ lines l) ∧
        (P.card ≤ 2 ∨ (missed P).card ≤ 2 ∨ P.card = 3 ∧ ∃ l : Fin 13, P ⊆ lines l)) ∧
        z = {i : Fin (13 + 13) | Fin.addCases (fun p : Fin 13 => decide (p ∉ P))
          (fun l : Fin 13 => decide (l ∉ missed P)) i = true}}
      let F : Type := Set (Finset (Fin 26))
      have allowed : Finset (Fin 26) → Prop := fun (t : Finset (Fin 26)) => ∃ k ∈ K, t ⊆ k
      have base : F → Prop := fun (A : F) =>
        A = ∅ ∨ A = {∅} ∨ ∃ i : Fin 26, A = {t : Finset (Fin 26) | t = {i} ∧ allowed t}
      have make : F → F → Set (Finset (Fin 26)) := fun (A B : F) =>
        {t : Finset (Fin 26) | allowed t ∧ ∃ a ∈ A, ∃ b ∈ B, t = a ∪ b}
      have avail : List F → F → Prop := fun (L : List F) (A : F) => base A ∨ A ∈ L
      have trim : F → Set (Finset (Fin 26)) := fun (s : F) =>
        {t : Finset (Fin 26) | Minimal (fun u : Finset (Fin 26) => u ∈ s) t}
      have valid : List F → Prop := fun (L : List F) =>
        ∀ (H : List F) (A : F) (T : List F), L = H ++ A :: T → ¬ avail H A ∧
          ∃ u : F, avail H u ∧ ∃ v : F, avail H v ∧ (A = trim (u ∪ v) ∨ A = trim (make u v))
      ∀ L : List F, valid L → ∀ A B : F, avail L A → avail L B → A ∪ B = K → 63 ≤ L.length) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → ∀ (x9 x10 : Fin ((26 : ℕ) + x7.size)), x9 ≠ x10 → (∀ (x12 x13 : Fin (13 : ℕ)), x2 x12 x13 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x4 x12 x13), x6 x7 (↑x10) (x4 x12 x13)] = Bool.true) → (∀ (x13 : Finset (Fin (13 : ℕ))), (∀ x14 ∉ x13, ∃ (x16 : Fin (13 : ℕ)), x3 x13 x16 ∧ x2 x14 x16) → (x13.card ≤ (2 : ℕ) ∨ Nat.card { x15 : Fin (13 : ℕ) // x3 x13 x15 } ≤ (2 : ℕ) ∨ x13.card = (3 : ℕ) ∧ ∃ (x15 : Fin (13 : ℕ)), ∀ x16 ∈ x13, x2 x16 x15) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x9) (x5 x13), x6 x7 (↑x10) (x5 x13)] = Bool.false) → (63 : ℕ) ≤ x7.size := by
  intro offsets inc off pos neg read C mono a b _ yes no
  classical
  let lines := singerLines3
  let missed := missLines lines
  let mask (P : Finset (Fin 13)) : Finset (Fin 26) :=
    Finset.univ.filter (fun i => Fin.addCases (motive := fun _ => Bool)
          (fun p : Fin 13 => decide (p ∉ P)) (fun l : Fin 13 => decide (l ∉ missed P)) i = true)
  let good (P : Finset (Fin 13)) :=
    (∀ p ∉ P, ∃ l ∈ missed P, p ∈ lines l) ∧
    (P.card ≤ 2 ∨ (missed P).card ≤ 2 ∨ P.card = 3 ∧ ∃ l, P ⊆ lines l)
  let K : Set (Finset (Fin 26)) := {k | ∃ P, good P ∧ k = mask P}
  have incidence (p l : Fin 13) : inc p l ↔ p ∈ lines l := by
    revert p l
    decide +kernel
  have misses (P : Finset (Fin 13)) (l : Fin 13) : l ∈ missed P ↔ off P l := by
    change l ∈ (Finset.univ.filter fun w => Disjoint (lines w) P) ↔ off P l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.disjoint_right]
    exact forall₂_congr fun p _ => not_congr (incidence p l).symm
  have leftMask (P : Finset (Fin 13)) (p : Fin 13) : Fin.castAdd 13 p ∈ mask P ↔ p ∉ P := by
    simp [mask]
  have rightMask (P : Finset (Fin 13)) (l : Fin 13) : Fin.natAdd 13 l ∈ mask P ↔ l ∉ missed P := by
    simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and, Fin.addCases_right, decide_eq_true_eq]
  have emptyGood : good ∅ := by
    refine ⟨fun p _ => ⟨p, (misses ∅ p).mpr (by simp [off]), (incidence p p).mp ?_⟩, Or.inl (by simp)⟩
    exact ⟨0, by decide, by simp⟩
  obtain ⟨L, hL, len, describe⟩ := compile 26 C K ⟨_, ∅, emptyGood, rfl⟩ mono
  obtain ⟨A, ha, soundA, completeA⟩ := describe a
  obtain ⟨B, hb, soundB, completeB⟩ := describe b
  have andEval (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by
    cases u <;> cases v <;> rfl
  have covers (t : Finset (Fin 26)) (ht : t ∈ A ∪ B) (p l : Fin 13) (h : inc p l) :
      Fin.castAdd 13 p ∈ t ∨ Fin.natAdd 13 l ∈ t := by
    by_contra! hn
    have dark (j : Fin 26) (hj : j ∈ t) : pos p l j = false := by
      change decide (_ ∨ _) = false
      simp only [decide_eq_false_iff_not, not_or]
      exact ⟨fun e => hn.1 (e ▸ hj), fun e => hn.2 (e ▸ hj)⟩
    have hit := yes p l h
    rw [andEval] at hit
    rcases ht with ht | ht
    · have hz := (soundA t ht).2 _ dark
      change read C a (pos p l) = false at hz
      simp [hz] at hit
    · have hz := (soundB t ht).2 _ dark
      change read C b (pos p l) = false at hz
      simp [hz] at hit
  have tight (t : Finset (Fin 26)) (ht : t ∈ A ∪ B) (P : Finset (Fin 13))
      (g : good P) (sub : t ⊆ mask P) : t = mask P := by
    apply Finset.Subset.antisymm sub
    intro i
    refine Fin.addCases (m := 13) (n := 13) (motive := fun j => j ∈ mask P → j ∈ t) (fun p hp => ?_) (fun l hl => ?_) i
    · obtain ⟨l, hl, edge⟩ := g.1 p ((leftMask P p).mp hp)
      exact (covers t ht p l ((incidence p l).mpr edge)).resolve_right
        (fun h => (rightMask P l).mp (sub h) hl)
    · have meet : ¬ off P l := fun h => (rightMask P l).mp hl ((misses P l).mpr h)
      change ¬ (∀ p ∈ P, ¬ inc p l) at meet
      push Not at meet
      obtain ⟨p, hp, edge⟩ := meet
      exact (covers t ht p l edge).resolve_left (fun h => (leftMask P p).mp (sub h) hp)
  have exactFamily : A ∪ B = K := by
    ext t
    constructor
    · intro ht
      have al := ht.elim (fun h => (soundA t h).1) (fun h => (soundB t h).1)
      obtain ⟨_, ⟨P, g, rfl⟩, sub⟩ := al
      exact ⟨P, g, tight t ht P g sub⟩
    · rintro ⟨P, g, rfl⟩
      have sameP (p q : Fin 13) : Fin.castAdd 13 p = Fin.castAdd 13 q ↔ p = q :=
        ⟨fun h => Fin.ext (congrArg (fun i : Fin 26 => i.val) h), congrArg (Fin.castAdd 13)⟩
      have sameL (l w : Fin 13) : Fin.natAdd 13 l = Fin.natAdd 13 w ↔ l = w := by
        refine ⟨fun h => Fin.ext ?_, congrArg (Fin.natAdd 13)⟩
        exact Nat.add_left_cancel (show 13 + l.val = 13 + w.val from congrArg Fin.val h)
      have apart (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
        intro h
        have he : p.val = 13 + l.val := congrArg Fin.val h
        omega
      have apart' (l p : Fin 13) : Fin.natAdd 13 l ≠ Fin.castAdd 13 p := (apart p l).symm
      have eqx : (fun j => decide (j ∉ mask P)) = neg P := by
        funext j
        refine Fin.addCases (m := 13) (n := 13) (motive := fun i => decide (i ∉ mask P) = neg P i) (fun p => ?_) (fun l => ?_) j
        · change decide (Fin.castAdd 13 p ∉ mask P) = decide
            ((∃ q ∈ P, Fin.castAdd 13 p = Fin.castAdd 13 q) ∨
              ∃ w, Fin.castAdd 13 p = Fin.natAdd 13 w ∧ off P w)
          apply decide_eq_decide.mpr
          simp only [leftMask, not_not, sameP, apart]
          simp
        · change decide (Fin.natAdd 13 l ∉ mask P) = decide
            ((∃ q ∈ P, Fin.natAdd 13 l = Fin.castAdd 13 q) ∨
              ∃ w, Fin.natAdd 13 l = Fin.natAdd 13 w ∧ off P w)
          apply decide_eq_decide.mpr
          simp only [rightMask, not_not, sameL, apart', misses]
          simp
      have card : Nat.card {l : Fin 13 // off P l} = (missed P).card := by
        have eq : (Finset.univ.filter fun l => off P l) = missed P := by
          ext l
          simp [misses]
        rw [← eq, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
      have hfalse := no P (fun p hp => by
        obtain ⟨l, hl, edge⟩ := g.1 p hp
        exact ⟨l, (misses P l).mp hl, (incidence p l).mpr edge⟩) (by
        rcases g.2 with h | h | ⟨h, l, hl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl (card ▸ h))
        · exact Or.inr (Or.inr ⟨h,l,fun p hp => (incidence p l).mpr (hl hp)⟩))
      rw [andEval] at hfalse
      have hk : mask P ∈ K := ⟨P,g,rfl⟩
      rcases Bool.and_eq_false_iff.mp hfalse with h | h
      · obtain ⟨t, ht, sub⟩ := completeA _ hk (eqx.symm ▸ h)
        exact (tight t (Or.inl ht) P g sub) ▸ Or.inl ht
      · obtain ⟨t, ht, sub⟩ := completeB _ hk (eqx.symm ▸ h)
        exact (tight t (Or.inr ht) P g sub) ▸ Or.inr ht
  let targets : Set (Finset (Fin 26)) := {z | ∃ P, good P ∧
    (z : Set (Fin 26)) = {i : Fin (13 + 13) | Fin.addCases (fun p : Fin 13 => decide (p ∉ P))
      (fun l : Fin 13 => decide (l ∉ missed P)) i = true}}
  have maskSet (P : Finset (Fin 13)) : (mask P : Set (Fin 26)) =
      {i : Fin (13 + 13) | Fin.addCases (fun p : Fin 13 => decide (p ∉ P))
        (fun l : Fin 13 => decide (l ∉ missed P)) i = true} := by
    ext i
    simp only [mask, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  have sameTargets : K = targets := by
    ext z
    constructor
    · rintro ⟨P, g, rfl⟩
      exact ⟨P, g, maskSet P⟩
    · rintro ⟨P, g, hz⟩
      exact ⟨P, g, Finset.coe_injective (hz.trans (maskSet P).symm)⟩
  rw [sameTargets] at hL ha hb exactFamily
  exact (coverCost L hL A B ha hb exactFamily).trans len
