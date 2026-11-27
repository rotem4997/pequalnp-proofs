import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5910

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

end PEqualNP.Outside.L_meta_5910

theorem PEqualNP.Outside.L_meta_5910 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ), PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output = x2 + x2 + x5 → x4.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x13 ∧ x13.size + (1 : ℕ) ≤ x4.size ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x3 { gates := x13.gates, output := x6 : PEqualNP.CircuitLowerBounds.Circuit } ∧ PEqualNP.GenericRejection.RightOnIncidentPairs x3 { gates := x13.gates, output := x7 : PEqualNP.CircuitLowerBounds.Circuit } ∧ ∀ (x14 : Finset (Fin x2)), x14.card ≤ x1 → ∃ x16 ∈ [x6, x7], ∀ (x17 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x13 (PEqualNP.GenericRejection.incidenceInput x17 x14) x16 = PEqualNP.GenericRejection.incidenceFun x3 x17 x14 := by
  intro q N S C k a b hC ho hk hR hF
  classical
  have hkl : k < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hk
    cases hk
  have hgk : C.gates[k] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ := by
    rw [List.getElem?_eq_getElem hkl] at hk
    exact Option.some.inj hk
  have hback := hC.2.1 k hkl
  have hgk' : PEqualNP.MetaComplexity.NestedCover.gateAt C k = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ := by
    rw [← hgk]; exact List.getD_eq_getElem _ _ hkl
  rw [hgk'] at hback
  have ha : a < N + N + k := hback a (by simp)
  have hb : b < N + N + k := hback b (by simp)
  let gs := C.gates.take k
  have hgl : gs.length = k := by simp [gs]; omega
  let I := fun X Y : Finset (Fin N) => PEqualNP.GenericRejection.incidenceInput X Y
  have hIl : ∀ X Y, (I X Y).length = N + N := by intro X Y; simp [I, PEqualNP.GenericRejection.incidenceInput]
  let V := fun (X Y : Finset (Fin N)) (w : ℕ) => (PEqualNP.Outside.L_meta_5910.run gs (I X Y)).getD w false
  have hpre : ∀ X Y w, w < N + N + k → (PEqualNP.Outside.L_meta_5910.run C.gates (I X Y)).getD w false = V X Y w := by
    intro X Y w hw
    have e : C.gates = gs ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    conv_lhs => rw [e]
    exact PEqualNP.Outside.L_meta_5910.run_prefix gs _ _ w (by rw [hIl, hgl]; exact hw)
  have hev : ∀ X Y, C.eval (I X Y) = (V X Y a && V X Y b) := by
    intro X Y
    change (PEqualNP.Outside.L_meta_5910.run C.gates (I X Y)).getD C.output false = _
    have h := PEqualNP.Outside.L_meta_5910.run_gate C.gates (I X Y) k hkl
    rw [hIl, hgk] at h
    rw [ho, h]
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, hpre X Y a ha, hpre X Y b hb,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
  have hmono : ∀ X X' Y Y' w, X ⊆ X' → Y ⊆ Y' → V X Y w = true → V X' Y' w = true := by
    intro X X' Y Y' w hX hY
    refine PEqualNP.Outside.L_meta_5910.mono gs (I X Y) (I X' Y') (by rw [hIl, hIl]) ?_ ?_ w
    · intro i hi
      simp only [I, PEqualNP.GenericRejection.incidenceInput] at hi ⊢
      rcases Nat.lt_or_ge i N with h1 | h1
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1), List.getElem?_ofFn, dif_pos h1] at hi ⊢
        simp only [Option.getD_some, decide_eq_true_eq] at hi ⊢
        exact hX hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using h1), List.length_ofFn, List.getElem?_ofFn] at hi ⊢
        split_ifs at hi ⊢ with h2
        · simp only [Option.getD_some, decide_eq_true_eq] at hi ⊢
          exact hY hi
        · simp at hi
    · intro g hg
      exact hC.1 g (List.mem_of_mem_take hg)
  have hpair : ∀ l : Fin N, ∀ p ∈ S l, V {p} {l} a = true ∧ V {p} {l} b = true := by
    intro l p hp
    have := hR l p hp
    rw [show C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = C.eval (I {p} {l}) from rfl, hev, Bool.and_eq_true] at this
    exact this
  refine ⟨⟨gs, C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact hC.1 g (List.mem_of_mem_take hg)
  · intro j hj i hi
    have hj' : j < k := by
      have : j < gs.length := hj
      omega
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, C.output⟩ j = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, gs, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj']
    rw [e] at hi
    exact hC.2.1 j (by omega) i hi
  · intro g hg
    exact hC.2.2 g (List.mem_of_mem_take hg)
  · change gs.length + 1 ≤ C.gates.length
    omega
  · intro l p hp
    exact (hpair l p hp).1
  · intro l p hp
    exact (hpair l p hp).2
  · intro Y hY
    let P : Finset (Fin N) := Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l
    have hPF : PEqualNP.GenericRejection.IsFalseInput S P Y := by
      intro l hl
      rw [Finset.disjoint_left]
      intro p hp hpP
      exact (Finset.mem_filter.1 hpP).2 l hl hp
    have h0 := hF P Y hY hPF
    rw [show C.eval (PEqualNP.GenericRejection.incidenceInput P Y) = C.eval (I P Y) from rfl, hev, Bool.and_eq_false_iff] at h0
    have main : ∀ w, V P Y w = false → (∀ l : Fin N, ∀ p ∈ S l, V {p} {l} w = true) → ∀ X : Finset (Fin N),
        V X Y w = PEqualNP.GenericRejection.incidenceFun S X Y := by
      intro w hw hp X
      rw [Bool.eq_iff_iff]
      simp only [PEqualNP.GenericRejection.incidenceFun, decide_eq_true_eq]
      constructor
      · intro hX
        by_contra hcon
        have hsub : X ⊆ P := by
          intro p hpX
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun l hl hpl => hcon ⟨p, hpX, l, hl, hpl⟩⟩
        have := hmono X P Y Y w hsub (Finset.Subset.refl _) hX
        rw [hw] at this
        cases this
      · rintro ⟨p, hpX, l, hl, hpl⟩
        exact hmono {p} X {l} Y w (Finset.singleton_subset_iff.2 hpX) (Finset.singleton_subset_iff.2 hl) (hp l p hpl)
    rcases h0 with h0 | h0
    · exact ⟨a, by simp, main a h0 fun l p hp => (hpair l p hp).1⟩
    · exact ⟨b, by simp, main b h0 fun l p hp => (hpair l p hp).2⟩
