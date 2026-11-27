import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9000

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem cntq {α : Type} (p : α → Bool) (l : List α) : ∃ S : Finset ℕ, S.card = (l.filter p).length ∧ (∀ j ∈ S, j < l.length) ∧ ∀ j (h : j < l.length), p l[j] = true → j ∈ S := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨∅, by simp, by simp, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨S, h1, h0, h2⟩ := ih
    by_cases ha : p a = true
    · refine ⟨insert l.length S, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem (fun h => by have := h0 _ h; omega), h1]
        simp [ha]
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp
        · have := h0 j hj; simp; omega
      · intro j h hp
        by_cases hj : j < l.length
        · rw [List.getElem_append_left hj] at hp
          exact Finset.mem_insert_of_mem (h2 j hj hp)
        · have : j = l.length := by simp at h; omega
          rw [this]; exact Finset.mem_insert_self _ _
    · refine ⟨S, by rw [h1]; simp [ha], fun j hj => by have := h0 j hj; simp; omega, ?_⟩
      intro j h hp
      by_cases hj : j < l.length
      · rw [List.getElem_append_left hj] at hp
        exact h2 j hj hp
      · have : j = l.length := by simp at h; omega
        subst this
        rw [List.getElem_append_right le_rfl] at hp
        simp at hp
        exact absurd hp ha

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9000

theorem PEqualNP.Outside.L_meta_9000 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x6 : Fin x1 → Fin x2) (x7 : Fin x1 → Fin x2), ∀ (x8 x9 : Fin x1), x3 (x6 x8) (x7 x9) ↔ x8 = x9) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x8 x9 : Fin x2), x3 x8 x9 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x8 ∨ x11 = Fin.natAdd x2 x9)) = Bool.true) → (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) → x1 ≤ (2 : ℕ) * (List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => !x10.op.eval [Bool.true, Bool.false]) x5.gates).length + (1 : ℕ) := by
  intro k n R _ C hM hC hacc hrej
  classical
  obtain ⟨u, v, huv⟩ := hM
  let W : (Fin (n + n) → Bool) → ℕ → Bool := fun x w => (PEqualNP.Outside.L_meta_9000.run C.gates (List.ofFn x)).getD w false
  let ed : Fin k → Fin (n + n) → Bool := fun j i => decide (i = Fin.castAdd n (u j) ∨ i = Fin.natAdd n (v j))
  let bs : Fin k → Fin (n + n) → Bool := fun j => Fin.append (fun p => decide (¬ R p (v j))) (fun l => decide (l = v j))
  have bsP : ∀ j p, bs j (Fin.castAdd n p) = decide (¬ R p (v j)) := fun j p => Fin.append_left _ _ p
  have bsL : ∀ j l, bs j (Fin.natAdd n l) = decide (l = v j) := fun j l => Fin.append_right _ _ l
  have hed : ∀ j, W (ed j) C.output = true := fun j => hacc (u j) (v j) ((huv j j).2 rfl)
  have hbs : ∀ j, W (bs j) C.output = false := by
    intro j
    refine hrej (bs j) ?_ ?_
    · have : Fintype.card { x10 : Fin n // bs j (Fin.natAdd n x10) = true } = Fintype.card { x10 : Fin n // x10 = v j } := by
        refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
        rw [bsL]; simp
      rw [this, Fintype.card_subtype_eq]
    · rintro ⟨p, l, h1, h2, h3⟩
      have h2 : ¬ R p (v j) := by rw [bsP] at h2; simpa using h2
      have h3 : l = v j := by rw [bsL] at h3; simpa using h3
      rw [h3] at h1
      exact h2 h1
  let Pr : ℕ → Fin k → Prop := fun w j => W (bs j) w = false ∧ ∀ x : Fin (n + n) → Bool, x (Fin.castAdd n (u j)) = true → W x w = true
  have hdist : ∀ w i j, Pr w i → Pr w j → i = j := by
    intro w i j hi hj
    by_contra hne
    have h1 : bs j (Fin.castAdd n (u i)) = true := by
      have : ¬ R (u i) (v j) := fun h => hne ((huv i j).1 h)
      rw [bsP]; simp [this]
    have := hi.2 (bs j) h1
    rw [hj.1] at this
    cases this
  have wg : ∀ x j (hj : j < C.gates.length), W x (n + n + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + n + j then W x i else false) := by
    intro x j hj
    have := PEqualNP.Outside.L_meta_9000.run_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at this
    exact this
  have wi : ∀ (x : Fin (n + n) → Bool) (i : Fin (n + n)), W x i = x i := by
    intro x i
    simp only [W]
    rw [PEqualNP.Outside.L_meta_9000.run_input _ _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  -- the roots
  let Sl : ℕ → ℕ × Fin 2 → Prop := fun w s => ∃ hj : s.1 < C.gates.length, C.gates[s.1].op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ C.gates[s.1].inputs[(s.2 : ℕ)]? = some w
  have desc : ∀ j w, W (ed j) w = true → W (bs j) w = false → Pr w j ∨ ∃ s r, Sl r s ∧ Pr r j := by
    intro j w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h1 h2
      by_cases hw : w < n + n
      · left
        have e1 := wi (ed j) ⟨w, hw⟩
        have e2 := wi (bs j) ⟨w, hw⟩
        have h1 : ed j ⟨w, hw⟩ = true := e1.symm.trans h1
        have h2' : bs j ⟨w, hw⟩ = false := e2.symm.trans h2
        simp only [ed, decide_eq_true_eq] at h1
        rcases h1 with h1 | h1
        · refine ⟨h2, fun x hx => ?_⟩
          have e3 := wi x ⟨w, hw⟩
          rw [h1] at e3
          have e4 : w = ((Fin.castAdd n (u j) : Fin (n + n)) : ℕ) := congrArg Fin.val h1
          rw [e4]
          exact e3.trans hx
        · rw [h1, bsL] at h2'
          simp at h2'
      · obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hw)
        by_cases hg : g < C.gates.length
        swap
        · simp only [W] at h1
          rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_9000.run_length, List.length_ofFn]; omega)] at h1
          cases h1
        have hop : C.gates[g].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[g].op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using (hC _ (List.getElem_mem hg)).1
        have hl2 := (hC _ (List.getElem_mem hg)).2
        have g1 := wg (ed j) g hg
        have g2 := wg (bs j) g hg
        rw [h1] at g1
        rw [h2] at g2
        rcases hop with ho | ho
        · rw [ho] at g1 g2
          have g1 := g1.symm
          have g2 := g2.symm
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false, Function.comp, id] at g1 g2
          obtain ⟨i, hi, g2⟩ := g2
          have g1 := g1 i hi
          by_cases hlt : i < n + n + g
          · rw [if_pos hlt] at g1 g2
            have g2 : W (bs j) i = false := by simpa using g2
            rcases ih i hlt g1 g2 with h | h
            · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hi
              exact Or.inr ⟨(g, ⟨t, by omega⟩), _, ⟨hg, ho, List.getElem?_eq_getElem ht⟩, h⟩
            · exact Or.inr h
          · rw [if_neg hlt] at g1
            cases g1
        · rw [ho] at g1 g2
          have g1 := g1.symm
          have g2 := g2.symm
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false, Function.comp, id] at g1 g2
          obtain ⟨i, hi, g1⟩ := g1
          have g2 := g2 i hi
          by_cases hlt : i < n + n + g
          · rw [if_pos hlt] at g1 g2
            have g2 : W (bs j) i = false := by simpa using g2
            rcases ih i hlt g1 g2 with h | h
            · left
              refine ⟨h2, fun x hx => ?_⟩
              rw [wg x g hg, ho]
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
              exact ⟨i, hi, by rw [if_pos hlt]; exact h.2 x hx⟩
            · exact Or.inr h
          · rw [if_neg hlt] at g1
            cases g1
  have hroot : ∀ j, ∃ s : Option (ℕ × Fin 2), (s = none ∧ Pr C.output j) ∨ ∃ s' r, s = some s' ∧ Sl r s' ∧ Pr r j := by
    intro j
    rcases desc j C.output (hed j) (hbs j) with h | ⟨s, r, h1, h2⟩
    · exact ⟨none, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨some s, Or.inr ⟨s, r, rfl, h1, h2⟩⟩
  choose φ hφ using hroot
  have hinj : Function.Injective φ := by
    intro i j hij
    rcases hφ i with ⟨a1, a2⟩ | ⟨s, r, a1, a2, a3⟩ <;> rcases hφ j with ⟨b1, b2⟩ | ⟨s', r', b1, b2, b3⟩
    · exact hdist _ i j a2 b2
    · rw [hij, b1] at a1; cases a1
    · rw [hij, b1] at a1; cases a1
    · rw [hij, b1] at a1
      have e := Option.some.inj a1
      subst e
      obtain ⟨hj1, _, e1⟩ := a2
      obtain ⟨hj2, _, e2⟩ := b2
      rw [e1] at e2
      have e2 := Option.some.inj e2
      subst e2
      exact hdist _ i j a3 b3
  obtain ⟨A, hA1, _, hA2⟩ := PEqualNP.Outside.L_meta_9000.cntq (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [true, false]) C.gates
  have hmem : ∀ j, φ j ∈ insert none ((A ×ˢ (Finset.univ : Finset (Fin 2))).map Function.Embedding.some) := by
    intro j
    rcases hφ j with ⟨a1, _⟩ | ⟨s, r, a1, ⟨hj, ho, _⟩, _⟩
    · rw [a1]; exact Finset.mem_insert_self _ _
    · rw [a1]
      refine Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨s, Finset.mem_product.2 ⟨hA2 _ hj ?_, Finset.mem_univ _⟩, rfl⟩)
      rw [ho]; rfl
  have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k))) φ (fun j _ => Finset.mem_coe.2 (hmem j)) (fun i _ j _ h => hinj h)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := Finset.card_insert_le (none : Option (ℕ × Fin 2)) ((A ×ˢ (Finset.univ : Finset (Fin 2))).map Function.Embedding.some)
  rw [Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
  omega
