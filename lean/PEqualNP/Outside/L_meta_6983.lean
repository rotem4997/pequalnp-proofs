import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6983

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




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6983

theorem PEqualNP.Outside.L_meta_6983 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool), (∀ (x4 : Fin (13 : ℕ) × Fin (4 : ℕ)), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 (x3 x4) = Bool.true) → ∃ (x5 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))), x5.length ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x6 = Bool.false → List.foldl (fun (x8 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x9 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x8 x10 ∨ x10 ⊆ x9.1 ∪ x9.2 ∧ x8 x9.1 ∧ x8 x9.2) (fun (x8 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x8 = ∅ ∨ ∃ (x9 : Fin (26 : ℕ)), x6 x9 = Bool.false ∧ ∀ x10 ∈ x8, x3 x10 x9 = Bool.true) x5 Finset.univ := by
  intro C hC X hX
  classical
  let val : (Fin 26 → Bool) → ℕ → Bool := fun x w => (PEqualNP.Outside.L_meta_6983.run C.gates (List.ofFn x)).getD w false
  let rd : (Fin 26 → Bool) → ℕ → ℕ → Bool := fun x j t => if t < 26 + j then val x t else false
  let S : ℕ → Finset (Fin 13 × Fin 4) := fun w => Finset.univ.filter fun e => val (X e) w = true
  let R : ℕ → ℕ → Finset (Fin 13 × Fin 4) := fun j t => Finset.univ.filter fun e => rd (X e) j t = true
  let gi : ℕ → List ℕ := fun j => (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs
  let big := 26 + C.gates.length + 1
  let pr : ℕ → Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4) := fun j => (R j ((gi j).getD 0 big), R j ((gi j).getD 1 big))
  let isOr : ℕ → Prop := fun j => ∃ h : j < C.gates.length, C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or
  let PL : ℕ → List (Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4)) := fun k => ((List.range k).filter fun j => decide (isOr j)).map pr
  refine ⟨PL C.gates.length, ?_, fun x hx => ?_⟩
  · simp only [PL, List.length_map]
    have e : ((List.range C.gates.length).filter fun j => decide (isOr j)).length = ((Finset.range C.gates.length).filter isOr).card := by
      rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)]
      congr 1
      ext j
      simp
    rw [e, ← Set.ncard_coe_finset, ← Set.ncard_image_of_injective {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} Fin.val_injective]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj
    obtain ⟨_, h, ho⟩ := hj
    exact ⟨⟨j, h⟩, ho, rfl⟩
  · let st : (Finset (Fin 13 × Fin 4) → Prop) → Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4) → Finset (Fin 13 × Fin 4) → Prop := fun Q p T => Q T ∨ T ⊆ p.1 ∪ p.2 ∧ Q p.1 ∧ Q p.2
    let Q0 : Finset (Fin 13 × Fin 4) → Prop := fun T => T = ∅ ∨ ∃ i : Fin 26, x i = false ∧ ∀ e ∈ T, X e i = true
    change List.foldl st Q0 (PL C.gates.length) Finset.univ
    have key : ∀ k ≤ C.gates.length, (∀ T T', T' ⊆ T → List.foldl st Q0 (PL k) T → List.foldl st Q0 (PL k) T') ∧ List.foldl st Q0 (PL k) ∅ ∧
        ∀ w < 26 + k, val x w = false → List.foldl st Q0 (PL k) (S w) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨?_, Or.inl rfl, ?_⟩
        · rintro T T' hT (rfl | ⟨i, h1, h2⟩)
          · exact Or.inl (Finset.subset_empty.1 hT)
          · exact Or.inr ⟨i, h1, fun e he => h2 e (hT he)⟩
        · intro w hw hv
          have hw' : w < 26 := by omega
          have iv : ∀ y : Fin 26 → Bool, val y w = y ⟨w, hw'⟩ := by
            intro y
            simp only [val]
            rw [PEqualNP.Outside.L_meta_6983.run_input _ _ _ (by simpa using hw'), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw']
            rfl
          refine Or.inr ⟨⟨w, hw'⟩, (iv x).symm.trans hv, fun e he => (iv (X e)).symm.trans ?_⟩
          simpa [S] using he
      | succ k ih =>
        intro hk
        obtain ⟨i1, i2, i3⟩ := ih (by omega)
        have hk' : k < C.gates.length := by omega
        have hgk : C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hk'
        have rg := fun y : Fin 26 → Bool => PEqualNP.Outside.L_meta_6983.run_gate C.gates (List.ofFn y) k hk'
        simp only [List.length_ofFn] at rg
        have rg' : ∀ y : Fin 26 → Bool, val y (26 + k) = C.gates[k].op.eval (C.gates[k].inputs.map fun t => rd y k t) := rg
        -- a wire read as false is in the family
        have rdQ : ∀ t, rd x k t = false → List.foldl st Q0 (PL k) (R k t) := by
          intro t ht
          by_cases h : t < 26 + k
          · have e : R k t = S t := by
              simp only [R, S, rd, if_pos h]
            rw [e]
            refine i3 t h ?_
            simpa [rd, h] using ht
          · have e : R k t = ∅ := by
              simp only [R, rd, if_neg h]
              simp
            rw [e]; exact i2
        obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hk')
        have hop' : C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hop
        rcases hop' with ho | ho
        · have hPL : PL (k + 1) = PL k := by
            simp only [PL, List.range_succ, List.filter_append, List.map_append]
            have : ¬ isOr k := by
              rintro ⟨h, h2⟩
              rw [ho] at h2; cases h2
            simp [this]
          rw [hPL]
          refine ⟨i1, i2, fun w hw hv => ?_⟩
          by_cases hwk : w = 26 + k
          · subst hwk
            rw [rg' x, ho] at hv
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_false, Function.comp, id] at hv
            obtain ⟨t, ht, hvt⟩ := hv
            refine i1 (R k t) _ ?_ (rdQ t (by simpa using hvt))
            intro e he
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at he
            rw [rg' (X e), ho] at he
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at he
            simpa [R] using he t ht
          · exact i3 w (by omega) hv
        · have hPL : PL (k + 1) = PL k ++ [pr k] := by
            simp only [PL, List.range_succ, List.filter_append, List.map_append]
            have : isOr k := ⟨hk', ho⟩
            simp [this]
          rw [hPL, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          refine ⟨?_, Or.inl i2, fun w hw hv => ?_⟩
          · rintro T T' hT (h | ⟨h1, h2, h3⟩)
            · exact Or.inl (i1 T T' hT h)
            · exact Or.inr ⟨hT.trans h1, h2, h3⟩
          · by_cases hwk : w = 26 + k
            · subst hwk
              rw [rg' x, ho] at hv
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_false, Function.comp, id] at hv
              have hbig : ∀ y : Fin 26 → Bool, rd y k big = false := by
                intro y
                simp only [rd, big]
                rw [if_neg (by omega)]
              have opd : ∀ m, rd x k (C.gates[k].inputs.getD m big) = false := by
                intro m
                by_cases hm : m < C.gates[k].inputs.length
                · rw [List.getD_eq_getElem _ _ hm]
                  have := hv _ (List.getElem_mem hm)
                  simpa using this
                · rw [List.getD_eq_default _ _ (by omega)]; exact hbig x
              refine Or.inr ⟨?_, ?_, ?_⟩
              · intro e he
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at he
                rw [rg' (X e), ho] at he
                simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at he
                obtain ⟨t, ht, hvt⟩ := he
                obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ht
                have hm2 : m < 2 := by omega
                simp only [pr, gi, hgk, Finset.mem_union]
                interval_cases m
                · left
                  rw [List.getD_eq_getElem _ _ hm]
                  simpa [R] using hvt
                · right
                  rw [List.getD_eq_getElem _ _ hm]
                  simpa [R] using hvt
              · simp only [pr, gi, hgk]; exact rdQ _ (opd 0)
              · simp only [pr, gi, hgk]; exact rdQ _ (opd 1)
            · exact Or.inl (i3 w (by omega) hv)
    obtain ⟨k1, k2, k3⟩ := key C.gates.length le_rfl
    have huniv : (Finset.univ : Finset (Fin 13 × Fin 4)) = S C.output := by
      ext e
      simp only [Finset.mem_univ, true_iff, S, Finset.mem_filter, true_and]
      exact hX e
    have ho : C.output < 26 + C.gates.length := by
      by_contra h
      have h1 := hX (0, 0)
      change (PEqualNP.Outside.L_meta_6983.run C.gates (List.ofFn (X (0, 0)))).getD C.output false = true at h1
      rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6983.run_length]; simp; omega)] at h1
      cases h1
    rw [huniv]
    exact k3 _ ho hx
