import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7087

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

theorem main {n : ℕ} {C : Circuit} (h : Shp n C) (i0 : Fin n) (hm : PEqualNP.MetaComplexity.IsMinimalCircuit n C) (hne : ∃ x y, C.eval (List.ofFn (Res n i0 x)) ≠ C.eval (List.ofFn (Res n i0 y)))
    (t o : ℕ) (ht : t < C.gates.length) (ho : o < C.gates.length) (rt : (i0 : ℕ) ∈ C.gates[t].inputs) (ro : (i0 : ℕ) ∈ C.gates[o].inputs)
    (ot : C.gates[t].op = GateOp.not) (oo : C.gates[o].op = GateOp.or)
    (hno : ¬∃ g, (C.gates.filter fun g => g.inputs.contains (n + t)) = [g] ∧ g.op = GateOp.and) :
    ∃ s, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => C.eval (List.ofFn (Res n i0 x))) s := by
  have hnc := resne hne
  have hi0 := i0.isLt
  have st : ∀ ρ x, Wv n C ρ x (n + t) = !Wv n C ρ x i0 := by
    rcases sem h t ht _ rt with ⟨_, _, h3⟩ | ⟨v, _, _, ⟨h4, _⟩ | ⟨h4, _⟩⟩
    · exact h3
    · rw [ot] at h4; cases h4
    · rw [ot] at h4; cases h4
  have so2 : ∀ w ∈ C.gates[o].inputs, w ≠ i0 → ∀ ρ x, Wv n C ρ x (n + o) = (Wv n C ρ x i0 || Wv n C ρ x w) := by
    intro w hw hne'
    rcases sem2 h o ho _ _ ro hw hne' with ⟨h4, _⟩ | ⟨_, h4⟩
    · rw [oo] at h4; cases h4
    · exact h4
  have kt : Cst n C (Res n i0) (n + t) := ⟨true, fun x => by rw [st, Wz]; rfl⟩
  have Ro : Red n C (Res n i0) o := redR h _ o ho _ ro ⟨false, fun x => Wz C i0 x⟩
  have hto : t ≠ o := by rintro rfl; rw [ot] at oo; cases oo
  have hor : n + t ∉ C.gates[o].inputs := by
    intro hh
    refine nored hm hnc o ho (Or.inl ⟨true, fun x => ?_⟩)
    rw [so2 _ hh (by omega), st]; simp
  obtain ⟨r, hr, htr, mr⟩ := reader h hm hnc t ht (nout hne _ kt)
  have hro : r ≠ o := by rintro rfl; exact hor mr
  have Rr := redR h _ r hr _ mr kt
  by_cases h2 : ∃ k, ∃ hk : k < C.gates.length, k ≠ r ∧ n + t ∈ C.gates[k].inputs
  · obtain ⟨k, hk, hkr, mk⟩ := h2
    have := h.2.1 k hk _ mk
    exact fin4 h hne t o r k hto (by omega) (by omega) (fun e => hro e.symm) (by rintro rfl; exact hor mk) (fun e => hkr e.symm) ⟨ht, Or.inl kt⟩ ⟨ho, Ro⟩ ⟨hr, Rr⟩ ⟨hk, redR h _ k hk _ mk kt⟩
  · have hf := filt1 C.gates (fun g => g.inputs.contains (n + t)) r hr (by simpa using mr) (by
      intro k hk hP
      by_contra hkr
      exact h2 ⟨k, hk, hkr, by simpa using hP⟩)
    have ona : C.gates[r].op ≠ GateOp.and := fun e => hno ⟨_, hf, e⟩
    have hsr := sem h r hr _ mr
    have kr : Cst n C (Res n i0) (n + r) := by
      rcases hsr with ⟨_, _, h3⟩ | ⟨v, _, _, ⟨h4, _⟩ | ⟨_, h3⟩⟩
      · exact ⟨false, fun x => by rw [h3, st, Wz]; rfl⟩
      · exact absurd h4 ona
      · exact ⟨true, fun x => by rw [h3, st, Wz]; rfl⟩
    obtain ⟨s, hs, hrs, ms⟩ := reader h hm hnc r hr (nout hne _ kr)
    have hso : s ≠ o := by
      rintro rfl
      refine nored hm hnc s hs ?_
      have e := so2 _ ms (by omega)
      rcases hsr with ⟨_, _, h3⟩ | ⟨v, _, _, ⟨h4, _⟩ | ⟨_, h3⟩⟩
      · exact Or.inr ⟨i0, by omega, fun x => by rw [e, h3, st]; simp⟩
      · exact absurd h4 ona
      · refine Or.inl ⟨true, fun x => ?_⟩
        rw [e, h3, st]
        cases Wv n C (fun x => x) x i0 <;> simp
    exact fin4 h hne t o r s hto (by omega) (by omega) (fun e => hro e.symm) (fun e => hso e.symm) (by omega) ⟨ht, Or.inl kt⟩ ⟨ho, Ro⟩ ⟨hr, Rr⟩ ⟨hs, redR h _ s hs _ ms kr⟩

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7087

theorem PEqualNP.Outside.L_meta_7087 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : ℕ),   have x5 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x5 : ℕ) => List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains x5) x2.gates;   PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → (∀ x8 ∈ x2.gates, x8.inputs.Nodup ∧ x8.inputs.length = if x8.op.eval [Bool.false] = Bool.true then (1 : ℕ) else (2 : ℕ)) → (∃ (x9 : Fin x1 → Bool) (x10 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x9 x3 Bool.false) ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x10 x3 Bool.false)) → (x5 ↑x3).length = (2 : ℕ) → (∃ x11 ∈ x5 ↑x3, x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) → x4 < x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → ↑x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).inputs → (¬∃ (x15 : PEqualNP.CircuitLowerBounds.Gate), x5 (x1 + x4) = [x15] ∧ x15.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x17 x3 Bool.false)) x16 := by
  intro n C i0 t rd hm hb hs hne _ hor ht ot rt hno
  have h := PEqualNP.Outside.L_meta_7087.mkShp n C hm.1 hb hs
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C t = C.gates[t] := List.getD_eq_getElem _ _ ht
  rw [e] at ot rt
  obtain ⟨g, hg, og⟩ := hor
  have hg' := List.mem_filter.1 hg
  obtain ⟨o, ho, rfl⟩ := List.getElem_of_mem hg'.1
  exact PEqualNP.Outside.L_meta_7087.main h i0 hm hne t o ht ho rt (by simpa using hg'.2) ot og hno
