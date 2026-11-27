import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8996

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc (l : List ℕ) (v i : ℕ) :
    (l ++ [v]).getD i 0 = if i < l.length then l.getD i 0 else if i = l.length then v else 0 := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem ld_snoc (gs : List Gate) (g : Gate) (n : ℕ) (m : Finset ℕ) :
    (Circuit.mk (gs ++ [g]) 0).lineDegrees n m =
      (Circuit.mk gs 0).lineDegrees n m ++ [g.lineDegree ((Circuit.mk gs 0).lineDegrees n m)] := by
  simp only [Circuit.lineDegrees, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ld_len (gs : List Gate) (n : ℕ) (m : Finset ℕ) :
    ((Circuit.mk gs 0).lineDegrees n m).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.lineDegrees]
  | append_singleton gs g ih =>
    rw [ld_snoc, List.length_append, ih]
    simp only [List.length_append, List.length_singleton]
    omega

theorem w_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x =
      (Circuit.mk gs 0).wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fmax_le (l : List ℕ) (c : ℕ) (h : ∀ v ∈ l, v ≤ c) : l.foldr max 0 ≤ c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun v hv => h v (by simp [hv]))

theorem fmax_mono (l : List ℕ) (f g : ℕ → ℕ) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).foldr max 0 ≤ (l.map g).foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sum_mono (l : List ℕ) (f g : ℕ → ℕ) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem gate_eta (g : Gate) (h1 : g.op = GateOp.and) (h2 : g.inputs.length = 2) :
    g = ⟨GateOp.and, [g.inputs.getD 0 0, g.inputs.getD 1 0]⟩ := by
  rcases g with ⟨op, ins⟩
  simp only at h1 h2
  subst h1
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h2
  rfl

theorem or_ne_and : GateOp.or ≠ GateOp.and := by intro h; cases h

theorem ld_or (ins : List ℕ) (d : List ℕ) :
    (Gate.mk GateOp.or ins).lineDegree d = (ins.map fun i => d.getD i 0).foldr max 0 := by
  unfold Gate.lineDegree
  rw [if_neg or_ne_and]

theorem ld_and (ins : List ℕ) (d : List ℕ) :
    (Gate.mk GateOp.and ins).lineDegree d = (ins.map fun i => d.getD i 0).sum := by
  unfold Gate.lineDegree
  rw [if_pos rfl]

theorem main (n : ℕ) (m : Finset ℕ) (S : Set (Fin n → Bool)) (C : Circuit) (hM : Monotone2 C)
    (hR : ∀ i a b : ℕ, C.gates[i]? = some ⟨GateOp.and, [a, b]⟩ →
      0 < ((Circuit.mk (C.gates.take i) 0).lineDegrees n m).getD a 0 →
      0 < ((Circuit.mk (C.gates.take i) 0).lineDegrees n m).getD b 0 →
      ∃ p : List ℕ, p.length ≤ 2 ∧ ∀ x ∈ S,
        ((((Circuit.mk (C.gates.take i) 0).wires (List.ofFn x)).getD a false &&
          ((Circuit.mk (C.gates.take i) 0).wires (List.ofFn x)).getD b false) =
          p.any fun j => ((Circuit.mk (C.gates.take i) 0).wires (List.ofFn x)).getD j false)) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ HasLineDegree n m C' 1 ∧
      ∀ x ∈ S, circuitFun n C' x = circuitFun n C x := by
  classical
  let D : ℕ → List ℕ := fun i => (Circuit.mk (C.gates.take i) 0).lineDegrees n m
  let W : ℕ → (Fin n → Bool) → List Bool :=
    fun i x => (Circuit.mk (C.gates.take i) 0).wires (List.ofFn x)
  let dg : ℕ → Gate := fun i => C.gates.getD i ⟨GateOp.and, []⟩
  let ia : ℕ → ℕ := fun i => (dg i).inputs.getD 0 0
  let ib : ℕ → ℕ := fun i => (dg i).inputs.getD 1 0
  let cond : ℕ → Prop := fun i => i < C.gates.length ∧ (dg i).op = GateOp.and ∧
    (dg i).inputs.length = 2 ∧ 0 < (D i).getD (ia i) 0 ∧ 0 < (D i).getD (ib i) 0
  have hdg : ∀ i (hi : i < C.gates.length), dg i = C.gates[i] := by
    intro i hi
    simp [dg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hgate : ∀ i, cond i → dg i = ⟨GateOp.and, [ia i, ib i]⟩ := by
    intro i hc
    exact gate_eta (dg i) hc.2.1 hc.2.2.1
  have hc' : ∀ i, ∃ p : List ℕ, cond i → (p.length ≤ 2 ∧ ∀ x ∈ S,
      (((W i x).getD (ia i) false && (W i x).getD (ib i) false) =
        p.any fun j => (W i x).getD j false)) := by
    intro i
    by_cases hc : cond i
    · have hsome : C.gates[i]? = some ⟨GateOp.and, [ia i, ib i]⟩ := by
        rw [List.getElem?_eq_getElem hc.1, ← hdg i hc.1, hgate i hc]
      obtain ⟨p, hp⟩ := hR i (ia i) (ib i) hsome hc.2.2.2.1 hc.2.2.2.2
      exact ⟨p, fun _ => hp⟩
    · exact ⟨[], fun h => absurd h hc⟩
  choose pk hpk using hc'
  let F : ℕ → Gate := fun i => if cond i then ⟨GateOp.or, pk i⟩ else dg i
  -- wires agree on S
  have hW : ∀ k, k ≤ C.gates.length → ∀ x ∈ S,
      (Circuit.mk ((List.range k).map F) 0).wires (List.ofFn x) = W k x := by
    intro k
    induction k with
    | zero =>
      intro _ x _
      simp [W, Circuit.wires]
    | succ k ih =>
      intro hk x hx
      have hkl : k < C.gates.length := hk
      have e1 : (List.range (k + 1)).map F = (List.range k).map F ++ [F k] := by
        rw [List.range_succ, List.map_append, List.map_singleton]
      have e2 : C.gates.take (k + 1) = C.gates.take k ++ [dg k] := by
        rw [List.take_succ, List.getElem?_eq_getElem hkl, hdg k hkl]
        rfl
      show (Circuit.mk ((List.range (k + 1)).map F) 0).wires (List.ofFn x) =
        (Circuit.mk (C.gates.take (k + 1)) 0).wires (List.ofFn x)
      rw [e1, e2, w_snoc, w_snoc, ih (by omega) x hx]
      have hv : (F k).op.eval ((F k).inputs.map fun i => (W k x).getD i false) =
          (dg k).op.eval ((dg k).inputs.map fun i => (W k x).getD i false) := by
        by_cases hc : cond k
        · have hF : F k = ⟨GateOp.or, pk k⟩ := if_pos hc
          rw [hF, hgate k hc]
          have := ((hpk k hc).2 x hx)
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id, Bool.and_true, List.any_map]
          rw [this]
          rfl
        · have hF : F k = dg k := if_neg hc
          rw [hF]
      rw [hv]
  -- degrees
  have hD : ∀ k, k ≤ C.gates.length → ∀ i,
      ((Circuit.mk ((List.range k).map F) 0).lineDegrees n m).getD i 0 ≤ 1 ∧
      ((Circuit.mk ((List.range k).map F) 0).lineDegrees n m).getD i 0 ≤ (D k).getD i 0 := by
    intro k
    induction k with
    | zero =>
      intro _ i
      have e : ((Circuit.mk ((List.range 0).map F) 0).lineDegrees n m) = D 0 := by
        simp [D, Circuit.lineDegrees]
      rw [e]
      refine ⟨?_, le_rfl⟩
      simp only [D, List.take_zero, Circuit.lineDegrees, List.foldl_nil,
        List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases h : (List.range n)[i]? with _ | v
      · simp
      · simp only [Option.map_some, Option.getD_some]
        split_ifs <;> omega
    | succ k ih =>
      intro hk i
      have hkl : k < C.gates.length := hk
      have e1 : (List.range (k + 1)).map F = (List.range k).map F ++ [F k] := by
        rw [List.range_succ, List.map_append, List.map_singleton]
      have e2 : C.gates.take (k + 1) = C.gates.take k ++ [dg k] := by
        rw [List.take_succ, List.getElem?_eq_getElem hkl, hdg k hkl]
        rfl
      have ih' := ih (by omega)
      set d' := (Circuit.mk ((List.range k).map F) 0).lineDegrees n m with hd'
      have hl1 : d'.length = n + k := by rw [hd', ld_len]; simp
      have hl2 : (D k).length = n + k := by
        simp only [D]; rw [ld_len]; simp; omega
      show ((Circuit.mk ((List.range (k + 1)).map F) 0).lineDegrees n m).getD i 0 ≤ 1 ∧
        ((Circuit.mk ((List.range (k + 1)).map F) 0).lineDegrees n m).getD i 0 ≤
          ((Circuit.mk (C.gates.take (k + 1)) 0).lineDegrees n m).getD i 0
      rw [e1, e2, ld_snoc, ld_snoc, ← hd', getD_snoc, getD_snoc]
      change _ ∧ _ ≤ if i < (D k).length then (D k).getD i 0 else
        if i = (D k).length then (dg k).lineDegree (D k) else 0
      rw [hl1, hl2]
      by_cases h1 : i < n + k
      · rw [if_pos h1, if_pos h1]
        exact ih' i
      rw [if_neg h1, if_neg h1]
      by_cases h2 : i = n + k
      · rw [if_pos h2, if_pos h2]
        -- the new gate
        have hall : ∀ j, d'.getD j 0 ≤ 1 := fun j => (ih' j).1
        have hle : ∀ j, d'.getD j 0 ≤ (D k).getD j 0 := fun j => (ih' j).2
        have hmem : dg k ∈ C.gates := by rw [hdg k hkl]; exact List.getElem_mem hkl
        obtain ⟨hop, hlen⟩ := hM _ hmem
        by_cases hc : cond k
        · have hF : F k = ⟨GateOp.or, pk k⟩ := if_pos hc
          rw [hF, ld_or, hgate k hc, ld_and]
          have hnew : ((pk k).map fun i => d'.getD i 0).foldr max 0 ≤ 1 :=
            fmax_le _ _ (by
              intro v hv
              obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
              exact hall j)
          refine ⟨hnew, ?_⟩
          have ha := hc.2.2.2.1
          have hb := hc.2.2.2.2
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          omega
        · have hF : F k = dg k := if_neg hc
          rw [hF]
          rcases hdk : dg k with ⟨op, ins⟩
          rw [hdk] at hop hlen
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with rfl | rfl
          · rw [ld_and, ld_and]
            refine ⟨?_, sum_mono _ _ _ (fun j _ => hle j)⟩
            simp only at hlen
            rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
            · simp
            · simpa using hall a
            · have hnc : ¬ (0 < (D k).getD a 0 ∧ 0 < (D k).getD b 0) := by
                intro hab
                apply hc
                refine ⟨hkl, ?_, ?_, ?_, ?_⟩
                · rw [hdk]
                · rw [hdk]; rfl
                · simp only [ia]; rw [hdk]; exact hab.1
                · simp only [ib]; rw [hdk]; exact hab.2
              have ha := hle a
              have hb := hle b
              have ha1 := hall a
              have hb1 := hall b
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
              omega
            · simp at hlen
          · rw [ld_or, ld_or]
            refine ⟨?_, fmax_mono _ _ _ (fun j _ => hle j)⟩
            exact fmax_le _ _ (by
              intro v hv
              obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
              exact hall j)
      · rw [if_neg h2, if_neg h2]
        omega
  refine ⟨⟨(List.range C.gates.length).map F, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_range] at hi
    by_cases hc : cond i
    · have hF : F i = ⟨GateOp.or, pk i⟩ := if_pos hc
      rw [hF]
      exact ⟨by simp, (hpk i hc).1⟩
    · have hF : F i = dg i := if_neg hc
      rw [hF, hdg i hi]
      exact hM _ (List.getElem_mem hi)
  · simp [Circuit.size]
  · exact (hD C.gates.length le_rfl C.output).1
  · intro x hx
    have h := hW C.gates.length le_rfl x hx
    simp only [W, List.take_length] at h
    show ((Circuit.mk ((List.range C.gates.length).map F) 0).wires (List.ofFn x)).getD
        C.output false = (C.wires (List.ofFn x)).getD C.output false
    rw [h]
    rfl

end PEqualNP.Outside.L_meta_8996

theorem PEqualNP.Outside.L_meta_8996 : ∀ (x1 : ℕ) (x2 : Finset ℕ) (x3 : Set (Fin x1 → Bool)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     (∀ (x6 x7 x8 : ℕ),         x4.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } →           have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.take x6 x4.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };           (0 : ℕ) < (x10.lineDegrees x1 x2).getD x7 (0 : ℕ) →             (0 : ℕ) < (x10.lineDegrees x1 x2).getD x8 (0 : ℕ) →               ∃ (x13 : List ℕ),                 x13.length ≤ (2 : ℕ) ∧                   ∀ x14 ∈ x3,                     have x16 : List Bool := x10.wires (List.ofFn x14);                     (x16.getD x7 Bool.false && x16.getD x8 Bool.false) = x13.any fun (x17 : ℕ) => x16.getD x17 Bool.false) →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x4.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree x1 x2 x7 (1 : ℕ) ∧ ∀ x8 ∈ x3, PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x4 x8 := by
  intro n m S C hM hR
  exact PEqualNP.Outside.L_meta_8996.main n m S C hM (fun i a b h1 h2 h3 => hR i a b h1 h2 h3)

