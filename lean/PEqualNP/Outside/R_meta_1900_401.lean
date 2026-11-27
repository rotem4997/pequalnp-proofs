import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1900_401
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n), (∃ w : Fin n, G.Adj v w) → (∀ a b : Fin n, G.Adj a b → a = v ∨ b = v) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) → Set.ncard {w : Fin n | G.Adj v w} ≤ C.size)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) → (∀ v : Fin n, ∃ a b : Fin n, G.Adj a b ∧ a ≠ v ∧ b ≠ v) → ∃ v : Fin n, (∃ w : Fin n, G.Adj v w) ∧ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ a b : Fin n, G.Adj a b ∧ a ≠ v ∧ b ≠ v ∧ x a = true ∧ x b = true) ∧ D.size + Set.ncard {w : Fin n | G.Adj v w} + 1 ≤ C.size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  intro n G0 C0 hE0 hC40 hM0 hcomp0
  classical
  -- the star at v, as a block, and its cost
  have star : ∀ (G : SimpleGraph (Fin n)) (v : Fin n), (∃ w, G.Adj v w) →
      PEqualNP.BicliqueBlockCost.IsBlock G (({v} : Finset (Fin n)), Finset.univ.filter (fun w => G.Adj v w)) ∧
      PEqualNP.BicliqueBlockCost.blockCost (({v} : Finset (Fin n)), Finset.univ.filter (fun w => G.Adj v w)) = Set.ncard {w : Fin n | G.Adj v w} := by
    intro G v hv
    obtain ⟨w, hw⟩ := hv
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [Finset.disjoint_singleton_left, Finset.mem_filter, Finset.mem_univ, true_and]
      exact G.loopless.irrefl v
    · exact Finset.singleton_nonempty v
    · exact ⟨w, by simpa using hw⟩
    · intro a ha b hb
      simp only [Finset.mem_singleton] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      subst ha; exact hb
    · unfold PEqualNP.BicliqueBlockCost.blockCost
      have : (↑(Finset.univ.filter (fun w => G.Adj v w)) : Set (Fin n)) = {w : Fin n | G.Adj v w} := by
        ext w; simp
      rw [← this, Set.ncard_coe_finset, Finset.card_singleton]
      dsimp only
      omega
  have key : ∀ m : ℕ, ∀ (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (Finset.univ.filter (fun u => ∃ w, G.Adj u w)).card ≤ m →
      (∃ u w : Fin n, G.Adj u w) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) →
      PEqualNP.BicliqueBlockCost.HasBlockCost G C.size := by
    intro m
    induction m with
    | zero =>
      intro G C hm hE _ _ _
      obtain ⟨u, w, huw⟩ := hE
      have : u ∈ Finset.univ.filter (fun u => ∃ w, G.Adj u w) := by simp; exact ⟨w, huw⟩
      have := Finset.card_pos.mpr ⟨u, this⟩
      omega
    | succ m ih =>
      intro G C hm hE hC4 hM hcomp
      by_cases hs : ∃ v, ∀ a b, G.Adj a b → a = v ∨ b = v
      · obtain ⟨v, hv⟩ := hs
        have hvw : ∃ w, G.Adj v w := by
          obtain ⟨a, b, hab⟩ := hE
          rcases hv a b hab with h | h
          · subst h; exact ⟨b, hab⟩
          · subst h; exact ⟨a, hab.symm⟩
        obtain ⟨hB, hcost⟩ := star G v hvw
        refine ⟨{(({v} : Finset (Fin n)), Finset.univ.filter (fun w => G.Adj v w))}, ⟨?_, ?_⟩, ?_⟩
        · intro p hp
          rw [Finset.mem_singleton] at hp
          subst hp; exact hB
        · intro a b hab
          refine ⟨_, Finset.mem_singleton_self _, ?_⟩
          unfold PEqualNP.BicliqueBlockCost.BlockCovers
          rcases hv a b hab with h | h
          · subst h; left; simp [hab]
          · subst h; right; simp [hab.symm]
        · unfold PEqualNP.BicliqueBlockCost.familyCost
          rw [Finset.sum_singleton, Finset.card_singleton, hcost]
          have := h1 n G C v hvw hv hM hcomp
          omega
      · push Not at hs
        obtain ⟨v, hvw, D, hMD, hD, hsz⟩ := h2 n G C hC4 hM hcomp hs
        let G' : SimpleGraph (Fin n) :=
          { Adj := fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v
            symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
            loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
        have hG'adj : ∀ a b, G'.Adj a b ↔ (G.Adj a b ∧ a ≠ v ∧ b ≠ v) := fun a b => Iff.rfl
        have hm' : (Finset.univ.filter (fun u => ∃ w, G'.Adj u w)).card ≤ m := by
          have hsub : Finset.univ.filter (fun u => ∃ w, G'.Adj u w) ⊆
              (Finset.univ.filter (fun u => ∃ w, G.Adj u w)).erase v := by
            intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hG'adj] at hu
            obtain ⟨w, hw, hu1, _⟩ := hu
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hu1, w, hw⟩
          have hvmem : v ∈ Finset.univ.filter (fun u => ∃ w, G.Adj u w) := by simpa using hvw
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hvmem] at this
          omega
        have hE' : ∃ u w : Fin n, G'.Adj u w := by
          obtain ⟨a, b, hab, ha, hb⟩ := hs v
          exact ⟨a, b, hab, ha, hb⟩
        have hC4' : ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G'.Adj a b → G'.Adj b c → G'.Adj c d → ¬ G'.Adj d a := by
          intro a b c d h1 h2 h3 h4 h5 h6 hab hbc hcd hda
          exact hC4 a b c d h1 h2 h3 h4 h5 h6 hab.1 hbc.1 hcd.1 hda.1
        have hD' : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ a b : Fin n, G'.Adj a b ∧ x a = true ∧ x b = true := by
          intro x
          rw [hD x]
          constructor
          · rintro ⟨a, b, hab, ha, hb, hxa, hxb⟩
            exact ⟨a, b, ⟨hab, ha, hb⟩, hxa, hxb⟩
          · rintro ⟨a, b, ⟨hab, ha, hb⟩, hxa, hxb⟩
            exact ⟨a, b, hab, ha, hb, hxa, hxb⟩
        obtain ⟨F', ⟨hFb, hFc⟩, hFcost⟩ := ih G' D (by convert hm') hE' hC4' hMD hD'
        obtain ⟨hB, hcost⟩ := star G v hvw
        set p : PEqualNP.BicliqueBlockCost.Block n := (({v} : Finset (Fin n)), Finset.univ.filter (fun w => G.Adj v w)) with hp
        have hpF : p ∉ F' := by
          intro hpF
          obtain ⟨_, _, ⟨b, hb⟩, hadj⟩ := hFb p hpF
          have := hadj v (by simp [p]) b hb
          exact this.2.1 rfl
        refine ⟨insert p F', ⟨?_, ?_⟩, ?_⟩
        · intro q hq
          rw [Finset.mem_insert] at hq
          rcases hq with hq | hq
          · subst hq; exact hB
          · obtain ⟨hq1, hq2, hq3, hq4⟩ := hFb q hq
            exact ⟨hq1, hq2, hq3, fun a ha b hb => (hq4 a ha b hb).1⟩
        · intro a b hab
          by_cases ha : a = v
          · subst ha
            refine ⟨p, Finset.mem_insert_self _ _, ?_⟩
            left; simp [p, hab]
          · by_cases hb : b = v
            · subst hb
              refine ⟨p, Finset.mem_insert_self _ _, ?_⟩
              right; simp [p, hab.symm]
            · obtain ⟨q, hq, hcov⟩ := hFc a b ⟨hab, ha, hb⟩
              exact ⟨q, Finset.mem_insert_of_mem hq, hcov⟩
        · unfold PEqualNP.BicliqueBlockCost.familyCost at hFcost ⊢
          rw [Finset.sum_insert hpF, Finset.card_insert_of_notMem hpF, hcost]
          omega
  exact key _ G0 C0 le_rfl hE0 hC40 hM0 hcomp0
