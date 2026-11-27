import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7724

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



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7724

theorem PEqualNP.Outside.L_meta_7724 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Bool),   have x4 : (Fin x1 → Bool) → Fin x1 → Bool := fun (x4 : Fin x1 → Bool) (x5 : Fin x1) => x3 x5 && x4 x5;   have x5 : List Bool := x2.wires (List.ofFn x3);   PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 (x4 x7) ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (x4 x8)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size + List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.inputs.any fun (x10 : ℕ) => !x5.getD x10 Bool.false) x2.gates ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x8 x9 = PEqualNP.MetaComplexity.circuitFun x1 x2 (x4 x9) := by
  intro n C S mk W hC hne
  classical
  have hW : ∀ w, W.getD w false = (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn S)).getD w false := fun w => rfl
  have gd : ∀ (f : Fin n → Bool) (i : ℕ) (hi : i < n), (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
    intro f i hi
    simp [List.getD_eq_getElem?_getD, hi]
  have hmono : ∀ x w, (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn (mk x))).getD w false = true → W.getD w false = true := by
    intro x w h
    refine PEqualNP.Outside.L_meta_7724.mono C.gates (List.ofFn (mk x)) (List.ofFn S) (by simp) (fun i hi => ?_) hC.1 w h
    by_cases hin : i < n
    · rw [gd _ _ hin] at hi ⊢
      simp only [mk, Bool.and_eq_true] at hi
      exact hi.1
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
  have hfalse : ∀ x w, W.getD w false = false → (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn (mk x))).getD w false = false := by
    intro x w h
    cases e : (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn (mk x))).getD w false with
    | false => rfl
    | true => rw [hmono x w e] at h; cases h
  let P : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g => g.inputs.any fun i => !W.getD i false
  have key : ∀ k ≤ C.gates.length, ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → ℕ),
      (∀ g ∈ hs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j (hj : j < hs.length), ∀ i ∈ hs[j].inputs, i < n + j) ∧
      hs.length + ((C.gates.take k).filter P).length = k ∧ (∀ w, w < n + k → W.getD w false = true → m w < n + hs.length) ∧
      ∀ x, ∀ w < n + k, W.getD w false = true → (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn (mk x))).getD w false = (PEqualNP.Outside.L_meta_7724.run hs (List.ofFn x)).getD (m w) false := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => w, by simp, by simp, by simp, ?_, ?_⟩
      · intro w hw _
        simpa using hw
      · intro x w hw hWw
        have hw' : w < n := by omega
        rw [PEqualNP.Outside.L_meta_7724.run_input _ _ _ (by simpa using hw'), PEqualNP.Outside.L_meta_7724.run_input _ _ _ (by simpa using hw'), gd _ _ hw', gd _ _ hw']
        rw [hW, PEqualNP.Outside.L_meta_7724.run_input _ _ _ (by simpa using hw'), gd _ _ hw'] at hWw
        simp only [mk, hWw, Bool.true_and]
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, hb, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have hop := hC.1 _ (List.getElem_mem hk')
      have hlen := hC.2.2 _ (List.getElem_mem hk')
      have hback : ∀ i ∈ C.gates[k].inputs, i < n + k := by
        intro i hi
        refine hC.2.1 k hk' i ?_
        have e : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk'
        rw [e]; exact hi
      obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
      have ha : a < n + k := hback a (by rw [hab]; simp)
      have hb' : b < n + k := hback b (by rw [hab]; simp)
      have rg : ∀ y : Fin n → Bool, (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn y)).getD (n + k) false = C.gates[k].op.eval [(PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn y)).getD a false, (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn y)).getD b false] := by
        intro y
        have := PEqualNP.Outside.L_meta_7724.run_gate C.gates (List.ofFn y) k hk'
        rw [List.length_ofFn] at this
        rw [this, hab]
        simp [ha, hb']
      have hWk : W.getD (n + k) false = C.gates[k].op.eval [W.getD a false, W.getD b false] := by
        rw [hW, hW, hW]; exact rg S
      have hfil : ((C.gates.take (k + 1)).filter P).length = ((C.gates.take k).filter P).length + if P C.gates[k] = true then 1 else 0 := by
        rw [List.take_succ_eq_append_getElem hk', List.filter_append, List.length_append]
        congr 1
        split_ifs with h <;> simp [h]
      have hPe : P C.gates[k] = (!W.getD a false || !W.getD b false) := by
        simp only [P, hab, List.any_cons, List.any_nil, Bool.or_false]
      by_cases hP : P C.gates[k] = true
      · have fin : ∀ r : ℕ, (W.getD (n + k) false = true → r < n + hs.length ∧ ∀ x, (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn (mk x))).getD (n + k) false = (PEqualNP.Outside.L_meta_7724.run hs (List.ofFn x)).getD r false) →
            ∃ (hs : List PEqualNP.CircuitLowerBounds.Gate) (m : ℕ → ℕ),
      (∀ g ∈ hs, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j (hj : j < hs.length), ∀ i ∈ hs[j].inputs, i < n + j) ∧
      hs.length + ((C.gates.take (k + 1)).filter P).length = k + 1 ∧ (∀ w, w < n + (k + 1) → W.getD w false = true → m w < n + hs.length) ∧
      ∀ x, ∀ w < n + (k + 1), W.getD w false = true → (PEqualNP.Outside.L_meta_7724.run C.gates (List.ofFn (mk x))).getD w false = (PEqualNP.Outside.L_meta_7724.run hs (List.ofFn x)).getD (m w) false := by
          intro r hr
          refine ⟨hs, Function.update m (n + k) r, h1, hb, by rw [hfil, if_pos hP]; omega, ?_, ?_⟩
          · intro w hw ht
            by_cases hwe : w = n + k
            · subst hwe; rw [Function.update_self]; exact (hr ht).1
            · rw [Function.update_of_ne hwe]; exact h3 w (by omega) ht
          · intro x w hw ht
            by_cases hwe : w = n + k
            · subst hwe; rw [Function.update_self]; exact (hr ht).2 x
            · rw [Function.update_of_ne hwe]; exact h4 x w (by omega) ht
        rw [hPe] at hP
        rcases hop with ho | ho
        · refine fin 0 fun ht => ?_
          rw [hWk, ho] at ht
          exfalso
          revert ht hP
          cases W.getD a false <;> cases W.getD b false <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        · by_cases hWa : W.getD a false = true
          · have hWb : W.getD b false = false := by
              rw [hWa] at hP; simpa using hP
            refine fin (m a) fun _ => ⟨h3 a ha hWa, fun x => ?_⟩
            rw [rg, ho, hfalse x b hWb, ← h4 x a ha hWa]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          · have hWa' := Bool.eq_false_iff.2 hWa
            refine fin (m b) fun ht => ?_
            have hWb : W.getD b false = true := by
              rw [hWk, ho, hWa'] at ht
              simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using ht
            refine ⟨h3 b hb' hWb, fun x => ?_⟩
            rw [rg, ho, hfalse x a hWa', ← h4 x b hb' hWb]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      · have hP' := hP
        rw [hPe] at hP'
        have hWa : W.getD a false = true := by
          revert hP'; cases W.getD a false <;> simp
        have hWb : W.getD b false = true := by
          revert hP'; cases W.getD b false <;> simp
        refine ⟨hs ++ [⟨C.gates[k].op, [m a, m b]⟩], Function.update m (n + k) (n + hs.length), ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · have : g = ⟨C.gates[k].op, [m a, m b]⟩ := by simpa using hg
            subst this
            exact ⟨hop, rfl⟩
        · intro j hj i hi
          rw [List.length_append, List.length_singleton] at hj
          rcases Nat.lt_or_ge j hs.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have : j = hs.length := by omega
            subst this
            have hi' : i = m a ∨ i = m b := by simpa using hi
            rcases hi' with rfl | rfl
            · exact h3 a ha hWa
            · exact h3 b hb' hWb
        · rw [hfil, if_neg hP, List.length_append]
          simp only [List.length_singleton]
          omega
        · intro w hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; simp
          · rw [Function.update_of_ne hwe]
            have := h3 w (by omega) ht
            omega
        · intro x w hw ht
          by_cases hwe : w = n + k
          · subst hwe
            rw [Function.update_self]
            have hl : n + hs.length = (PEqualNP.Outside.L_meta_7724.run hs (List.ofFn x)).length := by rw [PEqualNP.Outside.L_meta_7724.run_length, List.length_ofFn]
            rw [PEqualNP.Outside.L_meta_7724.run_snoc, hl, PEqualNP.Outside.L_meta_7724.getD_at, rg, h4 x a ha hWa, h4 x b hb' hWb]
            rfl
          · rw [Function.update_of_ne hwe, h4 x w (by omega) ht, PEqualNP.Outside.L_meta_7724.run_prefix _ _ _ _ (by rw [List.length_ofFn]; exact h3 w (by omega) ht)]
  obtain ⟨hs, m, h1, hb, h2, h3, h4⟩ := key C.gates.length le_rfl
  rw [List.take_length] at h2
  have hout : W.getD C.output false = true := by
    by_contra h
    have h' := Bool.eq_false_iff.2 h
    obtain ⟨x, y, hxy⟩ := hne
    exact hxy ((hfalse x _ h').trans (hfalse y _ h').symm)
  have holt : C.output < n + C.gates.length := by
    by_contra h
    rw [hW, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_7724.run_length, List.length_ofFn]; omega)] at hout
    cases hout
  refine ⟨⟨hs, m C.output⟩, ⟨fun g hg => (h1 g hg).1, ?_, fun g hg => (h1 g hg).2⟩, ?_, fun x => (h4 x _ holt hout).symm⟩
  · intro j hj i hi
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨hs, m C.output⟩ j = hs[j] := List.getD_eq_getElem _ _ hj
    rw [e] at hi
    exact hb j hj i hi
  · rw [List.countP_eq_length_filter]
    exact le_of_eq h2
