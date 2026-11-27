import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8553

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




def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · exact add ⟨GateOp.not, [t]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · exact add ⟨GateOp.not, [t]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (F : Finset ℕ) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ i : Fin n, (∃ b, ∀ x, ρ x i = b) ∨ ∀ x, ρ x i = x i)
    (hne : ∃ x y, C.eval (List.ofFn (ρ x)) ≠ C.eval (List.ofFn (ρ y)))
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (C.wires (List.ofFn (ρ x))).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (C.wires (List.ofFn (ρ x))).getD (n + j) false = (C.wires (List.ofFn (ρ x))).getD w false)) :
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (ρ x))) (C.size - F.card) := by
  classical
  have hwires : ∀ x, C.wires (List.ofFn (ρ x)) = run C.gates (List.ofFn (ρ x)) := fun x => rfl
  have hpre : ∀ (k : ℕ) (x : Fin n → Bool) (w : ℕ), k ≤ C.gates.length → w < n + k → (run (C.gates.take k) (List.ofFn (ρ x))).getD w false = (run C.gates (List.ofFn (ρ x))).getD w false := by
    intro k x w hk hw
    have := run_prefix (C.gates.take k) (C.gates.drop k) (List.ofFn (ρ x)) w (by rw [List.length_take]; simp; omega)
    rw [List.take_append_drop] at this
    exact this.symm
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < n + hs.length) ∧
      ∀ x : Fin n → Bool, ∀ w < n + k, (run C.gates (List.ofFn (ρ x))).getD w false = rv (run hs (List.ofFn x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : w < n then (if hb : ∃ b, ∀ x, ρ x ⟨w, h⟩ = b then .inl hb.choose else .inr w) else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        simp only [Nat.add_zero] at hw
        beta_reduce at ht
        rw [dif_pos hw] at ht
        split_ifs at ht
        cases ht
        simpa using hw
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by simpa using hw), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw]
        beta_reduce
        rw [dif_pos hw]
        simp only [Option.getD_some]
        split_ifs with hb
        · exact hb.choose_spec x
        · simp only [rv, run, List.foldl_nil]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw]
          exact (h0 ⟨w, hw⟩).resolve_left hb x
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      -- extend with a value for wire `n + k`
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < n + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : Fin n → Bool, (run C.gates (List.ofFn (ρ x))).getD (n + k) false = rv (run (hs ++ e) (List.ofFn x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < n + hs.length) ∧
      ∀ x : Fin n → Bool, ∀ w < n + (k + 1), (run C.gates (List.ofFn (ρ x))).getD w false = rv (run hs (List.ofFn x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (List.ofFn x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            simpa using this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit n hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (by simp)]
        have rg := run_gate C.gates (List.ofFn (ρ x)) k hk'
        rw [List.length_ofFn] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, y, hxy⟩ := hne
    refine hxy ?_
    change (run C.gates (List.ofFn (ρ x))).getD C.output false = (run C.gates (List.ofFn (ρ y))).getD C.output false
    rw [List.getD_eq_default _ _ (by rw [run_length]; simp; omega), List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  have hev : ∀ x, C.eval (List.ofFn (ρ x)) = rv (run hs (List.ofFn x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · obtain ⟨x, y, hxy⟩ := hne
    rw [hev, hev, hm] at hxy
    exact absurd rfl hxy
  · refine ⟨⟨hs, t⟩, ?_, ?_, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have e1 : C.size = C.gates.length := rfl
      have e2 : PEqualNP.CircuitLowerBounds.Circuit.size ⟨hs, t⟩ = hs.length := rfl
      omega
    · have := hev x
      rw [hm] at this
      exact this.symm


def Wv (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (x : Fin n → Bool) (w : ℕ) : Bool := (run C.gates (List.ofFn (ρ x))).getD w false

def Cst (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (w : ℕ) : Prop := ∃ b, ∀ x, Wv n C ρ x w = b

def Red (n : ℕ) (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (j : ℕ) : Prop :=
  Cst n C ρ (n + j) ∨ ∃ w < n + j, ∀ x, Wv n C ρ x (n + j) = Wv n C ρ x w

def Shp (n : ℕ) (C : Circuit) : Prop := PEqualNP.MetaComplexity.FanInTwo C ∧ (∀ j (h : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j) ∧
  ∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = if g.op.eval [false] = true then 1 else 2

def Res (n : ℕ) (i0 : Fin n) : (Fin n → Bool) → Fin n → Bool := fun x => Function.update x i0 false

theorem mkShp (n : ℕ) (C : Circuit) (h1 : PEqualNP.MetaComplexity.FanInTwo C) (h2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (h3 : ∀ g ∈ C.gates, g.inputs.Nodup ∧ g.inputs.length = if g.op.eval [false] = true then 1 else 2) : Shp n C := by
  refine ⟨h1, fun j h i hi => ?_, h3⟩
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ h
  exact h2 j h i (by rw [e]; exact hi)

theorem Wg {n : ℕ} {C : Circuit} (h : Shp n C) (ρ : (Fin n → Bool) → Fin n → Bool) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    Wv n C ρ x (n + j) = C.gates[j].op.eval (C.gates[j].inputs.map (Wv n C ρ x)) := by
  have := run_gate C.gates (List.ofFn (ρ x)) j hj
  rw [List.length_ofFn] at this
  rw [Wv, this]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [if_pos (h.2.1 j hj i hi)]
  rfl

theorem Wi {n : ℕ} (C : Circuit) (ρ : (Fin n → Bool) → Fin n → Bool) (x : Fin n → Bool) (i : Fin n) : Wv n C ρ x i = ρ x i := by
  rw [Wv, run_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem Wz {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) : Wv n C (Res n i) x i = false := by
  rw [Wi]; simp [Res]

theorem sem {n : ℕ} {C : Circuit} (h : Shp n C) (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j].inputs) :
    (C.gates[j].op = GateOp.not ∧ (∀ u ∈ C.gates[j].inputs, u = w) ∧ ∀ ρ x, Wv n C ρ x (n + j) = !Wv n C ρ x w) ∨
    ∃ v ∈ C.gates[j].inputs, (∀ u ∈ C.gates[j].inputs, u = w ∨ u = v) ∧
      ((C.gates[j].op = GateOp.and ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w && Wv n C ρ x v)) ∨
       (C.gates[j].op = GateOp.or ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w || Wv n C ρ x v))) := by
  obtain ⟨h1, h2⟩ := h.2.2 _ (List.getElem_mem hj)
  have hop := (h.1 _ (List.getElem_mem hj)).1
  have hg := fun ρ x => Wg h ρ x j hj
  generalize hl : C.gates[j].inputs = l at *
  have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or ∨ C.gates[j].op = GateOp.not := by simpa using hop
  rcases hop' with ho | ho | ho
  · rw [ho] at h2
    have h2' : l.length = 2 := by simpa [GateOp.eval] using h2
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h2'
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨b, by simp, by simp, Or.inl ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval]⟩⟩
    · exact ⟨a, by simp, by simp; , Or.inl ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval, Bool.and_comm]⟩⟩
  · rw [ho] at h2
    have h2' : l.length = 2 := by simpa [GateOp.eval] using h2
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h2'
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨b, by simp, by simp, Or.inr ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval]⟩⟩
    · exact ⟨a, by simp, by simp; , Or.inr ⟨ho, fun ρ x => by rw [hg, ho]; simp [GateOp.eval, Bool.or_comm]⟩⟩
  · rw [ho] at h2
    have h2' : l.length = 1 := by simpa [GateOp.eval] using h2
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h2'
    left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    exact ⟨ho, by simp, fun ρ x => by rw [hg, ho]; simp [GateOp.eval]⟩

theorem sem2 {n : ℕ} {C : Circuit} (h : Shp n C) (j : ℕ) (hj : j < C.gates.length) (w w' : ℕ) (hw : w ∈ C.gates[j].inputs) (hw' : w' ∈ C.gates[j].inputs) (hne : w' ≠ w) :
      (C.gates[j].op = GateOp.and ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w && Wv n C ρ x w')) ∨
       (C.gates[j].op = GateOp.or ∧ ∀ ρ x, Wv n C ρ x (n + j) = (Wv n C ρ x w || Wv n C ρ x w')) := by
  rcases sem h j hj w hw with ⟨_, h2, _⟩ | ⟨v, _, h2, h3⟩
  · exact absurd (h2 _ hw') hne
  · rcases h2 _ hw' with e | e
    · exact absurd e hne
    · rw [e]; exact h3

theorem redc {n : ℕ} {C : Circuit} (h : Shp n C) (ρ : (Fin n → Bool) → Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j].inputs)
    (hc : Cst n C ρ w) : Cst n C ρ (n + j) ∨ ∃ v ∈ C.gates[j].inputs, ∀ x, Wv n C ρ x (n + j) = Wv n C ρ x v := by
  obtain ⟨b, hb⟩ := hc
  rcases sem h j hj w hw with ⟨_, _, h3⟩ | ⟨v, hv, _, ⟨_, h3⟩ | ⟨_, h3⟩⟩
  · exact Or.inl ⟨!b, fun x => by rw [h3, hb]⟩
  · cases b
    · exact Or.inl ⟨false, fun x => by rw [h3, hb]; rfl⟩
    · exact Or.inr ⟨v, hv, fun x => by rw [h3, hb]; simp⟩
  · cases b
    · exact Or.inr ⟨v, hv, fun x => by rw [h3, hb]; simp⟩
    · exact Or.inl ⟨true, fun x => by rw [h3, hb]; simp⟩

theorem redR {n : ℕ} {C : Circuit} (h : Shp n C) (ρ : (Fin n → Bool) → Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w ∈ C.gates[j].inputs)
    (hc : Cst n C ρ w) : Red n C ρ j := by
  rcases redc h ρ j hj w hw hc with h1 | ⟨v, hv, h1⟩
  · exact Or.inl h1
  · exact Or.inr ⟨v, h.2.1 j hj v hv, h1⟩

theorem setrun (n : ℕ) (gs : List Gate) (t : ℕ) (ht : t < gs.length) (y : List Bool) (hy : y.length = n)
    (H : ∀ k (hk : k < gs.length), k ≠ t → gs[k].op.eval (gs[k].inputs.map fun i => if i < n + k then (if i = n + t then false else (run gs y).getD i false) else false) = (run gs y).getD (n + k) false) :
    ∀ w < n + gs.length, (run (gs.set t ⟨GateOp.or, []⟩) y).getD w false = if w = n + t then false else (run gs y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [if_neg (by omega), run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hwn)
      have hk : k < gs.length := by omega
      have e := run_gate (gs.set t ⟨GateOp.or, []⟩) y k (by rw [List.length_set]; exact hk)
      rw [hy] at e
      rw [e]
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos rfl, List.getElem_set_self]
        rfl
      · rw [if_neg (by omega), List.getElem_set_ne (fun h => hkt h.symm), ← H k hk hkt]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with h1 h2
        · rw [ih i (by omega) (by omega), if_pos h2]
        · rw [ih i (by omega) (by omega), if_neg h2]
        · rfl

theorem fanset (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (t o : ℕ) : PEqualNP.MetaComplexity.FanInTwo ⟨C.gates.set t ⟨GateOp.or, []⟩, o⟩ := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with h | rfl
  · exact hC g h
  · exact ⟨by simp, by simp⟩

theorem nored {n : ℕ} {C : Circuit} (hm : PEqualNP.MetaComplexity.IsMinimalCircuit n C) (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (j : ℕ) (hj : j < C.gates.length) : ¬Red n C (fun x => x) j := by
  intro hr
  obtain ⟨D, d1, d2, d3⟩ := engine n C (fun x => x) {j} hm.1 (fun i => Or.inr fun x => rfl) hnc (by
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨hj, hr⟩)
  have := hm.2 D d1 (by funext x; exact d3 x)
  have hs : C.size = C.gates.length := rfl
  rw [Finset.card_singleton] at d2
  omega

theorem reader {n : ℕ} {C : Circuit} (h : Shp n C) (hm : PEqualNP.MetaComplexity.IsMinimalCircuit n C) (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (j : ℕ) (hj : j < C.gates.length) (ho : n + j ≠ C.output) : ∃ k, ∃ hk : k < C.gates.length, j < k ∧ n + j ∈ C.gates[k].inputs := by
  by_contra hcon
  have hno : ∀ k (hk : k < C.gates.length), n + j ∉ C.gates[k].inputs := by
    intro k hk hmem
    have := h.2.1 k hk _ hmem
    exact hcon ⟨k, hk, by omega, hmem⟩
  let C' : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hrun : ∀ x : Fin n → Bool, ∀ w < n + C.gates.length, (run C'.gates (List.ofFn x)).getD w false = if w = n + j then false else (run C.gates (List.ofFn x)).getD w false := by
    intro x
    refine setrun n C.gates j hj _ (by simp) ?_
    intro k hk hkj
    have e := run_gate C.gates (List.ofFn x) k hk
    rw [List.length_ofFn] at e
    rw [e]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hh : ¬ i = n + j := fun hh => hno k hk (by rw [← hh]; exact hi)
    simp only [if_neg hh, List.length_ofFn]
  have hlen : C'.gates.length = C.gates.length := List.length_set
  have hev : ∀ x : Fin n → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    change (run C'.gates (List.ofFn x)).getD C.output false = (run C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n + C.gates.length
    · rw [hrun x _ hlt, if_neg (fun hh => ho hh.symm)]
    · rw [List.getD_eq_default _ _ (by rw [run_length, hlen]; simp; omega), List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  obtain ⟨D, d1, d2, d3⟩ := engine n C' (fun x => x) {j} (fanset C hm.1 j C.output) (fun i => Or.inr fun x => rfl) (by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨x, y, by rw [hev, hev]; exact hxy⟩) (by
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    refine ⟨by rw [hlen]; exact hj, Or.inl ⟨false, fun x => ?_⟩⟩
    have := hrun x (n + k) (by omega)
    rw [if_pos rfl] at this
    exact this)
  have := hm.2 D d1 (by funext x; exact (d3 x).trans (hev x))
  have hs : C.size = C.gates.length := rfl
  have hs' : C'.size = C.gates.length := hlen
  rw [Finset.card_singleton] at d2
  omega

theorem nout {n : ℕ} {C : Circuit} {ρ : (Fin n → Bool) → Fin n → Bool} (hne : ∃ x y, C.eval (List.ofFn (ρ x)) ≠ C.eval (List.ofFn (ρ y))) (w : ℕ) (hc : Cst n C ρ w) : w ≠ C.output := by
  rintro rfl
  obtain ⟨x, y, hxy⟩ := hne
  obtain ⟨b, hb⟩ := hc
  exact hxy ((hb x).trans (hb y).symm)

theorem resne {n : ℕ} {C : Circuit} {i0 : Fin n} (hne : ∃ x y, C.eval (List.ofFn (Res n i0 x)) ≠ C.eval (List.ofFn (Res n i0 y))) :
    ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
  obtain ⟨x, y, h⟩ := hne
  exact ⟨_, _, h⟩

theorem fin4 {n : ℕ} {C : Circuit} (h : Shp n C) {i0 : Fin n} (hne : ∃ x y, C.eval (List.ofFn (Res n i0 x)) ≠ C.eval (List.ofFn (Res n i0 y)))
    (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a < C.gates.length ∧ Red n C (Res n i0) a) (hb : b < C.gates.length ∧ Red n C (Res n i0) b)
    (hc : c < C.gates.length ∧ Red n C (Res n i0) c) (hd : d < C.gates.length ∧ Red n C (Res n i0) d) :
    ∃ s, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (Res n i0 x))) s := by
  classical
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]), Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hF : ∀ j ∈ ({a, b, c, d} : Finset ℕ), j < C.gates.length ∧ Red n C (Res n i0) j := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hle : 4 ≤ C.size := by
    rw [← hcard]
    refine (Finset.card_le_card (fun j hj => Finset.mem_range.2 (hF j hj).1)).trans ?_
    rw [Finset.card_range]
    exact le_rfl
  have := engine n C (Res n i0) {a, b, c, d} h.1 (by
      intro i
      by_cases hi : i = i0
      · subst hi; exact Or.inl ⟨false, fun x => by simp [Res]⟩
      · exact Or.inr fun x => by simp [Res, Function.update_of_ne hi]) hne hF
  rw [hcard] at this
  exact ⟨C.size - 4, by omega, this⟩

theorem filt (gs : List Gate) (P : Gate → Bool) (r : ℕ) (hr : r < gs.length) (hP : P gs[r] = true) :
    gs.filter P = (gs.take r).filter P ++ gs[r] :: (gs.drop (r + 1)).filter P := by
  conv_lhs => rw [← List.take_append_drop r gs, List.drop_eq_getElem_cons hr]
  rw [List.filter_append, List.filter_cons_of_pos hP]

theorem filt1 (gs : List Gate) (P : Gate → Bool) (r : ℕ) (hr : r < gs.length) (hP : P gs[r] = true) (hu : ∀ k (hk : k < gs.length), P gs[k] = true → k = r) :
    gs.filter P = [gs[r]] := by
  have h1 : (gs.take r).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg hPg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_take] at hk
    rw [List.getElem_take] at hPg
    have := hu k (by omega) hPg
    omega
  have h2 : (gs.drop (r + 1)).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg hPg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_drop] at hk
    rw [List.getElem_drop] at hPg
    have := hu _ (by omega) hPg
    omega
  rw [filt gs P r hr hP, h1, h2]
  rfl

theorem filt2 (gs : List Gate) (P : Gate → Bool) (g : Gate) (h : gs.filter P = [g]) : ∃ r, ∃ hr : r < gs.length, gs[r] = g ∧ P gs[r] = true ∧ ∀ k (hk : k < gs.length), P gs[k] = true → k = r := by
  have hmem : g ∈ gs.filter P := by rw [h]; simp
  rw [List.mem_filter] at hmem
  obtain ⟨r, hr, e⟩ := List.getElem_of_mem hmem.1
  have hP : P gs[r] = true := by rw [e]; exact hmem.2
  refine ⟨r, hr, e, hP, ?_⟩
  intro k hk hPk
  have hlen : (gs.filter P).length = 1 := by rw [h]; rfl
  by_contra hne
  have e1 := filt gs P r hr hP
  have e2 := congrArg List.length e1
  rw [hlen, List.length_append, List.length_cons] at e2
  have h1 : (gs.take r).filter P = [] := List.length_eq_zero_iff.1 (by omega)
  have h2 : (gs.drop (r + 1)).filter P = [] := List.length_eq_zero_iff.1 (by omega)
  rw [List.filter_eq_nil_iff] at h1 h2
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · refine h1 gs[k] ?_ hPk
    rw [List.mem_take_iff_getElem]
    exact ⟨k, by omega, rfl⟩
  · refine h2 gs[k] ?_ hPk
    rw [List.mem_iff_getElem]
    refine ⟨k - (r + 1), by rw [List.length_drop]; omega, ?_⟩
    rw [List.getElem_drop]
    congr 1
    omega

theorem engine2 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card ≤ C.size ∧ (∀ x, D.eval (tgt x) = C.eval (src x)) ∧ ∀ w < n + C.gates.length, ∃ r : Bool ⊕ ℕ, ∀ x, (run C.gates (src x)).getD w false = rv (run D.gates (tgt x)) r := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      -- extend with a value for wire `n + k`
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_, fun w hw => ⟨m w, fun x => h4 x w hw⟩⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm


theorem prop {N : ℕ} {C : Circuit} (h : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j) (B : ℕ → Prop) (x y : Fin N → Bool)
    (hi : ∀ i : Fin N, ¬B i → x i = y i)
    (hg : ∀ k (hk : k < C.gates.length), ¬B (N + k) → (∃ w ∈ C.gates[k].inputs, B w) → Wv N C (fun x => x) x (N + k) = Wv N C (fun x => x) y (N + k)) :
    ∀ w, ¬B w → Wv N C (fun x => x) x w = Wv N C (fun x => x) y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · have e1 := Wi C (fun x => x) x ⟨w, h1⟩
      have e2 := Wi C (fun x => x) y ⟨w, h1⟩
      simp only at e1 e2
      rw [e1, e2]; exact hi ⟨w, h1⟩ hw
    · by_cases h2 : w < N + C.gates.length
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h1)
        have hk : k < C.gates.length := by omega
        by_cases hb : ∃ u ∈ C.gates[k].inputs, B u
        · exact hg k hk hw hb
        · have r1 := run_gate C.gates (List.ofFn x) k hk
          have r2 := run_gate C.gates (List.ofFn y) k hk
          rw [List.length_ofFn] at r1 r2
          simp only [Wv]
          rw [r1, r2]
          congr 1
          refine List.map_congr_left fun i hi' => ?_
          rw [if_pos (h k hk i hi'), if_pos (h k hk i hi')]
          exact ih i (h k hk i hi') (fun hB => hb ⟨i, hi', hB⟩)
      · simp only [Wv]
        rw [List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega), List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]

def nm (g : Gate) : Gate := ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩

theorem nm_run (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (d : List Bool) : run (gs.map nm) d = run gs d := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    have e : (nm g).op.eval ((nm g).inputs.map fun i => d.getD i false) = g.op.eval (g.inputs.map fun i => d.getD i false) := by
      obtain ⟨o, l⟩ := g
      rcases hop _ List.mem_cons_self with rfl | rfl | rfl
      · simp [nm, GateOp.eval]
      · simp [nm, GateOp.eval]
      · rcases l with _ | ⟨a, l⟩ <;> simp [nm, GateOp.eval]
    simp only [run, List.map_cons, List.foldl_cons]
    rw [e]
    exact ih (fun g' h' => hop g' (List.mem_cons_of_mem _ h')) _

theorem shp {N : ℕ} {C : Circuit} (hm : PEqualNP.MetaComplexity.IsMinimalCircuit N C) (hnc : ∃ x y : Fin N → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hb : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j) (hl : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) : Shp N C := by
  refine ⟨hm.1, hb, fun g hg => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or ∨ C.gates[j].op = GateOp.not := by simpa using (hm.1 _ hg).1
  have h2 := (hm.1 _ hg).2
  have hl' := hl _ hg
  have hr := nored hm hnc j hj
  have hbj := hb j hj
  have wg : ∀ x, Wv N C (fun x => x) x (N + j) = C.gates[j].op.eval (C.gates[j].inputs.map fun i => Wv N C (fun x => x) x i) := by
    intro x
    have r1 := run_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at r1
    simp only [Wv]
    rw [r1]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [if_pos (hbj i hi)]
  generalize C.gates[j].inputs = l at h2 hl' hbj wg
  generalize C.gates[j].op = o at hop hl' wg
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact absurd (Or.inl ⟨o.eval [], fun x => by rw [wg]; rfl⟩) hr
  · rcases hop with rfl | rfl | rfl
    · exact absurd (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩) hr
    · exact absurd (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩) hr
    · simp [GateOp.eval]
  · have hab : a ≠ b := by
      rintro rfl
      rcases hop with rfl | rfl | rfl
      · exact hr (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩)
      · exact hr (Or.inr ⟨a, hbj a (by simp), fun x => by rw [wg]; simp [GateOp.eval]⟩)
      · have := hl' rfl; simp at this
    rcases hop with rfl | rfl | rfl
    · simp [GateOp.eval, hab]
    · simp [GateOp.eval, hab]
    · have := hl' rfl; simp at this
  · simp at h2

theorem main {n : ℕ} {C : Circuit} (i0 : Fin (n + 1)) (g : ℕ) (hm : PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C)
    (hb : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + 1 + j) (hl : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hrd : ∀ k (hk : k < C.gates.length), (i0 : ℕ) ∈ C.gates[k].inputs → k = g ∧ C.gates[k].op ≠ GateOp.or)
    (hne : ∃ x y : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) false x)) ≠ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) false y)))
    (hd : ∃ x : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) false x)) = false ∧ C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) true x)) = true) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ x, D.eval (List.ofFn x) = C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) false x))) ∧ D.size + 2 ≤ C.size ∧
      (D.size + 3 ≤ C.size ∨ ∃ t : ℕ, ∀ x : Fin n → Bool, C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) false x)) = false → C.eval (List.ofFn (i0.insertNth (α := fun _ => Bool) true x)) = true → (D.wires (List.ofFn x)).getD t false = true) := by
  classical
  let N := n + 1
  let I : Bool → (Fin n → Bool) → Fin N → Bool := fun b x => i0.insertNth (α := fun _ => Bool) b x
  let ρ := Res N i0
  have hρ : ∀ x, ρ (I false x) = I false x := by
    intro x
    simp only [ρ, Res, I]
    rw [Fin.update_insertNth]
  have hρ2 : ∀ y : Fin N → Bool, ρ y = I false (i0.removeNth y) := by
    intro y
    simp only [ρ, Res, I]
    rw [Fin.insertNth_removeNth]
  have hIo : ∀ b b' x (i : Fin N), i ≠ i0 → I b x i = I b' x i := by
    intro b b' x i hi
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [I, Fin.insertNth_apply_succAbove]
  have hnc : ∃ x y : Fin N → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨x, y, h⟩ := hne; exact ⟨_, _, h⟩
  have hneR : ∃ x y, C.eval (List.ofFn (ρ x)) ≠ C.eval (List.ofFn (ρ y)) := by
    obtain ⟨x, y, h⟩ := hne
    exact ⟨I false x, I false y, by rw [hρ, hρ]; exact h⟩
  have hS := shp hm hnc hb hl
  have hi0 := i0.isLt
  obtain ⟨x0, hx0, hx1⟩ := hd
  have ki : Cst N C ρ i0 := ⟨false, fun x => Wz C i0 x⟩
  have oi : (i0 : ℕ) ≠ C.output := nout hneR _ ki
  -- some gate reads i0
  have hex : ∃ k, ∃ hk : k < C.gates.length, (i0 : ℕ) ∈ C.gates[k].inputs := by
    by_contra hcon
    have := prop hb (fun w => w = (i0 : ℕ)) (I false x0) (I true x0) (fun i hi => hIo _ _ _ _ (fun e => hi (congrArg Fin.val e))) (by
      rintro k hk _ ⟨w, hw, rfl⟩
      exact absurd ⟨k, hk, hw⟩ hcon) C.output (fun e => oi e.symm)
    have h' : C.eval (List.ofFn (I false x0)) = C.eval (List.ofFn (I true x0)) := this
    have e1 : C.eval (List.ofFn (I false x0)) = false := hx0
    have e2 : C.eval (List.ofFn (I true x0)) = true := hx1
    rw [e1, e2] at h'; cases h'
  obtain ⟨g', hg, mg⟩ := hex
  obtain ⟨rfl, og⟩ := hrd g' hg mg
  -- engine with a set F
  have eng : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ Red N C ρ j) → ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card ≤ C.size ∧ (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (I false x))) ∧
      ∀ w < N + C.gates.length, ∃ r : Bool ⊕ ℕ, ∀ x : Fin n → Bool, Wv N C (fun x => x) (I false x) w = rv (run D.gates (List.ofFn x)) r := by
    intro F hF
    obtain ⟨D, d1, d2, d3, d4⟩ := engine2 N n C (fun x : Fin n → Bool => List.ofFn (I false x)) (fun x => List.ofFn x) (fun x => List.length_ofFn) (fun x => List.length_ofFn) F hm.1 (by
      intro w hw
      have ew : ∀ x : Fin n → Bool, (List.ofFn (I false x)).getD w false = I false x ⟨w, hw⟩ := fun x => by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw), List.getElem_ofFn]
      by_cases he : (⟨w, hw⟩ : Fin N) = i0
      · refine Or.inl ⟨false, fun x => ?_⟩
        rw [ew, he]
        simp [I]
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq he
        refine Or.inr ⟨k, k.isLt, fun x => ?_⟩
        rw [ew, ← hk, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        simp [I]) (by
      rintro ⟨b, hb'⟩
      obtain ⟨x, y, h⟩ := hne
      exact h ((hb' x).trans (hb' y).symm)) (by
      intro j hj
      obtain ⟨h1, h2⟩ := hF j hj
      refine ⟨h1, ?_⟩
      rcases h2 with ⟨b, hb'⟩ | ⟨w, hw, h2⟩
      · refine Or.inl ⟨b, fun x => ?_⟩
        have := hb' (I false x)
        simp only [Wv] at this
        rw [hρ] at this
        exact this
      · refine Or.inr ⟨w, hw, fun x => ?_⟩
        have := h2 (I false x)
        simp only [Wv] at this
        rw [hρ] at this
        exact this)
    exact ⟨D, d1, d2, d3, d4⟩
  have kg : Cst N C ρ (N + g') := by
    rcases sem hS g' hg _ mg with ⟨_, _, h3⟩ | ⟨v, _, _, ⟨_, h3⟩ | ⟨h4, _⟩⟩
    · exact ⟨true, fun x => by rw [h3, Wz]; rfl⟩
    · exact ⟨false, fun x => by rw [h3, Wz]; rfl⟩
    · exact absurd h4 og
  have og' := nout hneR _ kg
  obtain ⟨r, hr, hgr, mr⟩ := reader hS hm hnc g' hg og'
  have Rr := redR hS ρ r hr _ mr kg
  have done3 : ∀ s, s < C.gates.length → Red N C ρ s → s ≠ g' → s ≠ r → ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ x, D.eval (List.ofFn x) = C.eval (List.ofFn (I false x))) ∧ D.size + 2 ≤ C.size ∧
      (D.size + 3 ≤ C.size ∨ ∃ t : ℕ, ∀ x : Fin n → Bool, C.eval (List.ofFn (I false x)) = false → C.eval (List.ofFn (I true x)) = true → (D.wires (List.ofFn x)).getD t false = true) := by
    intro s hs Rs h1 h2
    obtain ⟨D, d1, d2, d3, _⟩ := eng {g', r, s} (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨hg, Or.inl kg⟩
      · exact ⟨hr, Rr⟩
      · exact ⟨hs, Rs⟩)
    have hc : ({g', r, s} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    rw [hc] at d2
    exact ⟨D, d1, d3, by omega, Or.inl d2⟩
  by_cases h2 : ∃ k, ∃ hk : k < C.gates.length, k ≠ r ∧ N + g' ∈ C.gates[k].inputs
  · obtain ⟨k, hk, hkr, mk⟩ := h2
    have := hb k hk _ mk
    exact done3 k hk (redR hS ρ k hk _ mk kg) (by omega) hkr
  have honly : ∀ k (hk : k < C.gates.length), N + g' ∈ C.gates[k].inputs → k = r := by
    intro k hk h
    by_contra hkr
    exact h2 ⟨k, hk, hkr, h⟩
  by_cases kr : Cst N C ρ (N + r)
  · obtain ⟨s, hs, hrs, ms⟩ := reader hS hm hnc r hr (nout hneR _ kr)
    exact done3 s hs (redR hS ρ s hs _ ms kr) (by omega) (by omega)
  -- exactly one reader, and it becomes a copy
  have indG : ∀ (x y : Fin N → Bool), (∀ i, i ≠ i0 → x i = y i) → ∀ w, w < N + g' → w ≠ (i0 : ℕ) → Wv N C (fun x => x) x w = Wv N C (fun x => x) y w := by
    intro x y hxy w hw hwi
    refine prop hb (fun w => w = (i0 : ℕ) ∨ N + g' ≤ w) x y (fun i hi => hxy i (fun e => hi (Or.inl (congrArg Fin.val e)))) ?_ w (by omega)
    rintro k hk hk2 ⟨u, hu, rfl | hu2⟩
    · have := (hrd k hk hu).1
      exact absurd (Or.inr (by omega)) hk2
    · have := hb k hk u hu
      exact absurd (Or.inr (by omega)) hk2
  have indR : ∀ (x y : Fin N → Bool), (∀ i, i ≠ i0 → x i = y i) → ∀ w, w < N + r → w ≠ (i0 : ℕ) → w ≠ N + g' → Wv N C (fun x => x) x w = Wv N C (fun x => x) y w := by
    intro x y hxy w hw hwi hwg
    refine prop hb (fun w => w = (i0 : ℕ) ∨ w = N + g' ∨ N + r ≤ w) x y (fun i hi => hxy i (fun e => hi (Or.inl (congrArg Fin.val e)))) ?_ w (by omega)
    rintro k hk hk2 ⟨u, hu, rfl | rfl | hu2⟩
    · have := (hrd k hk hu).1
      exact absurd (Or.inr (Or.inl (by omega))) hk2
    · have := honly k hk hu
      exact absurd (Or.inr (Or.inr (by omega))) hk2
    · have := hb k hk u hu
      exact absurd (Or.inr (Or.inr (by omega))) hk2
  have indO : ∀ (x y : Fin N → Bool), (∀ i, i ≠ i0 → x i = y i) → Wv N C (fun x => x) x (N + r) = Wv N C (fun x => x) y (N + r) → C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
    intro x y hxy hrr
    refine prop hb (fun w => w = (i0 : ℕ) ∨ w = N + g') x y (fun i hi => hxy i (fun e => hi (Or.inl (congrArg Fin.val e)))) ?_ C.output (by rintro (e | e); exacts [oi e.symm, og' e.symm])
    rintro k hk hk2 ⟨u, hu, rfl | rfl⟩
    · have := (hrd k hk hu).1
      exact absurd (Or.inr (by omega)) hk2
    · have := honly k hk hu
      subst this
      exact hrr
  have hRes : ∀ y : Fin N → Bool, ∀ i, i ≠ i0 → y i = ρ y i := by
    intro y i hi
    simp only [ρ, Res]
    rw [Function.update_of_ne hi]
  -- the finishing step: a wire z, independent of i0, not constant, whose value false makes r equal
  have fin : ∀ z, z < N + C.gates.length → (∀ x y : Fin N → Bool, (∀ i, i ≠ i0 → x i = y i) → Wv N C (fun x => x) x z = Wv N C (fun x => x) y z) → ¬Cst N C (fun x => x) z →
      (∀ x : Fin n → Bool, Wv N C (fun x => x) (I false x) z = false → Wv N C (fun x => x) (I false x) (N + r) = Wv N C (fun x => x) (I true x) (N + r)) →
      ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ x, D.eval (List.ofFn x) = C.eval (List.ofFn (I false x))) ∧ D.size + 2 ≤ C.size ∧
      (D.size + 3 ≤ C.size ∨ ∃ t : ℕ, ∀ x : Fin n → Bool, C.eval (List.ofFn (I false x)) = false → C.eval (List.ofFn (I true x)) = true → (D.wires (List.ofFn x)).getD t false = true) := by
    intro z hz hind hnz hzr
    obtain ⟨D, d1, d2, d3, d4⟩ := eng {g', r} (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact ⟨hg, Or.inl kg⟩
      · exact ⟨hr, Rr⟩)
    rw [Finset.card_pair (by omega)] at d2
    obtain ⟨q, hq⟩ := d4 z hz
    refine ⟨D, d1, d3, d2, Or.inr ?_⟩
    rcases q with b | t
    · exfalso
      refine hnz ⟨b, fun y => ?_⟩
      rw [hind y (ρ y) (hRes y), hρ2, hq]
      rfl
    · refine ⟨t, fun x hx hx' => ?_⟩
      have e : (D.wires (List.ofFn x)).getD t false = Wv N C (fun x => x) (I false x) z := (hq x).symm
      rw [e]
      by_contra hzf
      have := indO (I false x) (I true x) (fun i hi => hIo _ _ _ _ hi) (hzr x (by simpa using hzf))
      rw [hx, hx'] at this; cases this
  have hrg : r ≠ g' := by omega
  have hri : ∀ u ∈ C.gates[r].inputs, u ≠ (i0 : ℕ) := by
    rintro u hu rfl
    exact hrg (hrd r hr hu).1
  rcases sem hS g' hg _ mg with ⟨_, _, hgn⟩ | ⟨v, hv, _, ⟨_, hga⟩ | ⟨h4, _⟩⟩
  · -- NOT
    have kt : ∀ x, Wv N C ρ x (N + g') = true := fun x => by rw [hgn, Wz]; rfl
    rcases sem hS r hr _ mr with ⟨_, _, h3⟩ | ⟨u, hu, _, ⟨_, h3⟩ | ⟨_, h3⟩⟩
    · exact absurd ⟨false, fun x => by rw [h3, kt]; rfl⟩ kr
    · have hug : u ≠ N + g' := by
        rintro rfl
        exact kr ⟨true, fun x => by rw [h3, kt]; rfl⟩
      have hul := hb r hr u hu
      refine fin u (by omega) (fun x y hxy => indR x y hxy u hul (hri u hu) hug) ?_ ?_
      · rintro ⟨b, hb'⟩
        refine nored hm hnc r hr ?_
        cases b
        · exact Or.inl ⟨false, fun x => by rw [h3, hb']; first | (simp; done) | (simp; rfl)⟩
        · exact Or.inr ⟨N + g', by omega, fun x => by rw [h3, hb']; first | (simp; done) | (simp; rfl)⟩
      · intro x hx
        have e := indR (I false x) (I true x) (fun i hi => hIo _ _ _ _ hi) u hul (hri u hu) hug
        rw [h3, h3, ← e, hx]; first | (simp; done) | (simp; rfl)
    · exact absurd ⟨true, fun x => by rw [h3, kt]; rfl⟩ kr
  · -- AND
    have kf : ∀ x, Wv N C ρ x (N + g') = false := fun x => by rw [hga, Wz]; rfl
    have hvi : v ≠ (i0 : ℕ) := by
      rintro rfl
      exact nored hm hnc g' hg (Or.inr ⟨i0, by omega, fun x => by rw [hga]; simp⟩)
    have hvl := hb g' hg v hv
    rcases sem hS r hr _ mr with ⟨_, _, h3⟩ | ⟨u, hu, _, ⟨_, h3⟩ | ⟨_, h3⟩⟩
    · exact absurd ⟨true, fun x => by rw [h3, kf]; rfl⟩ kr
    · exact absurd ⟨false, fun x => by rw [h3, kf]; rfl⟩ kr
    · have hug : u ≠ N + g' := by
        rintro rfl
        exact kr ⟨false, fun x => by rw [h3, kf]; rfl⟩
      have hul := hb r hr u hu
      refine fin v (by omega) (fun x y hxy => indG x y hxy v hvl hvi) ?_ ?_
      · rintro ⟨b, hb'⟩
        refine nored hm hnc g' hg ?_
        cases b
        · exact Or.inl ⟨false, fun x => by rw [hga, hb']; first | (simp; done) | (simp; rfl)⟩
        · exact Or.inr ⟨i0, by omega, fun x => by rw [hga, hb']; first | (simp; done) | (simp; rfl)⟩
      · intro x hx
        have e := indR (I false x) (I true x) (fun i hi => hIo _ _ _ _ hi) u hul (hri u hu) hug
        have e2 := indG (I false x) (I true x) (fun i hi => hIo _ _ _ _ hi) v hvl hvi
        rw [h3, h3, hga, hga, ← e, ← e2, hx]; first | (simp; done) | (simp; rfl)
  · exact absurd h4 og

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8553

theorem PEqualNP.Outside.L_meta_8553 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (x1 + (1 : ℕ))) (x4 : Fin x2.size),   have x5 : Bool → (Fin x1 → Bool) → Bool := fun (x5 : Bool) (x6 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun (x1 + (1 : ℕ)) x2 (x3.insertNth x5 x6);   PEqualNP.MetaComplexity.IsMinimalCircuit (x1 + (1 : ℕ)) x2 → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false, Bool.false]) x2.gates ≤ (2 : ℕ) → (∀ (x8 : Fin x2.size), ∀ x9 ∈ (x2.gates.get x8).inputs, x9 < x1 + (1 : ℕ) + ↑x8) → (∀ (x9 : Fin x2.size), ↑x3 ∈ (x2.gates.get x9).inputs ↔ x9 = x4) → (x2.gates.get x4).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∃ (x11 : Fin x1 → Bool) (x12 : Fin x1 → Bool), x5 Bool.false x11 ≠ x5 Bool.false x12) → (∃ (x12 : Fin x1 → Bool), x5 Bool.false x12 = Bool.false ∧ x5 Bool.true x12 = Bool.true) → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = x5 Bool.false ∧ x13.size + (2 : ℕ) ≤ x2.size ∧ (x13.size + (3 : ℕ) ≤ x2.size ∨ ∃ (x14 : ℕ), ∀ (x15 : Fin x1 → Bool), x5 Bool.false x15 = Bool.false → x5 Bool.true x15 = Bool.true → (x13.wires (List.ofFn x15)).getD x14 Bool.false = Bool.true) := by
  intro n C i0 g f hm _ hb hrd hop hne hd
  have hops : ∀ q ∈ C.gates, q.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ q.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ q.op = PEqualNP.CircuitLowerBounds.GateOp.not := fun q hq => by simpa using (hm.1 q hq).1
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map PEqualNP.Outside.L_meta_8553.nm, C.output⟩
  have hev : ∀ y, C'.eval y = C.eval y := by
    intro y
    have := PEqualNP.Outside.L_meta_8553.nm_run C.gates hops y
    change (PEqualNP.Outside.L_meta_8553.run (C.gates.map PEqualNP.Outside.L_meta_8553.nm) y).getD C.output false = _
    rw [this]; rfl
  have hsub : ∀ q : PEqualNP.CircuitLowerBounds.Gate, ∀ i ∈ (PEqualNP.Outside.L_meta_8553.nm q).inputs, i ∈ q.inputs := by
    intro q i hi
    simp only [PEqualNP.Outside.L_meta_8553.nm] at hi
    split_ifs at hi
    · exact List.mem_of_mem_take hi
    · exact hi
  have hlen : C'.gates.length = C.gates.length := by simp [C']
  have hfun : PEqualNP.MetaComplexity.circuitFun (n + 1) C' = PEqualNP.MetaComplexity.circuitFun (n + 1) C := by
    funext x; exact hev _
  have hm' : PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C' := by
    refine ⟨?_, fun D hD hfD => ?_⟩
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2⟩ := hm.1 q' hq'
      refine ⟨h1, ?_⟩
      simp only [PEqualNP.Outside.L_meta_8553.nm]
      split_ifs
      · rw [List.length_take]; omega
      · exact h2
    · have := hm.2 D hD (hfD.trans hfun)
      have e : C'.size = C.size := hlen
      rw [e]; exact this
  obtain ⟨D, d1, d2, d3, d4⟩ := PEqualNP.Outside.L_meta_8553.main (C := C') i0 g hm' (by
    intro j hj i hi
    have hj' : j < C.gates.length := by rw [← hlen]; exact hj
    simp only [C', List.getElem_map] at hi
    exact hb ⟨j, hj'⟩ i (hsub _ i hi)) (by
    intro q hq hqo
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    have hqo' : q'.op = PEqualNP.CircuitLowerBounds.GateOp.not := hqo
    simp only [PEqualNP.Outside.L_meta_8553.nm]
    rw [if_pos (by rw [hqo']; rfl), List.length_take]
    omega) (by
    intro k hk hi
    have hk' : k < C.gates.length := by rw [← hlen]; exact hk
    simp only [C', List.getElem_map] at hi ⊢
    have h1 := (hrd ⟨k, hk'⟩).1 (hsub _ _ hi)
    refine ⟨congrArg Fin.val h1, ?_⟩
    have h2 : C.gates[k] = C.gates.get g := by rw [← h1]; rfl
    intro h3
    exact hop (by rw [← h2]; exact h3)) (by
    obtain ⟨x, y, h⟩ := hne
    exact ⟨x, y, by rw [hev, hev]; exact h⟩) (by
    obtain ⟨x, h1, h2⟩ := hd
    exact ⟨x, by rw [hev]; exact h1, by rw [hev]; exact h2⟩)
  have e : C'.size = C.size := hlen
  rw [e] at d3 d4
  refine ⟨D, d1, ?_, d3, ?_⟩
  · funext x
    exact (d2 x).trans (hev _)
  · rcases d4 with h | ⟨t, ht⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, fun x h0 h1 => ht x (by rw [hev]; exact h0) (by rw [hev]; exact h1)⟩
