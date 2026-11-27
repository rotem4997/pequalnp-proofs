import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6198

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


theorem engine2 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
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
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem cntp {α : Type} (p : α → Bool) (l : List α) : ∃ S : Finset ℕ, S.card = (l.filter p).length ∧ ∀ j ∈ S, ∃ h : j < l.length, p l[j] = true := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨∅, by simp, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨S, h1, h2⟩ := ih
    have h3 : ∀ j ∈ S, ∃ h : j < (l ++ [a]).length, p (l ++ [a])[j] = true := by
      intro j hj
      obtain ⟨h, hp⟩ := h2 j hj
      exact ⟨by simp; omega, by rw [List.getElem_append_left h]; exact hp⟩
    by_cases ha : p a = true
    · refine ⟨insert l.length S, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem, h1]
        · simp [ha]
        · intro hm
          obtain ⟨h, _⟩ := h2 _ hm
          omega
      · intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact ⟨by simp, by simpa using ha⟩
        · exact h3 j hj
    · exact ⟨S, by rw [h1]; simp [ha], h3⟩

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6198

theorem PEqualNP.Outside.L_meta_6198 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x4 : Bool), ∀ (x5 : Fin (10 : ℕ) → Bool), x5 (0 : Fin (10 : ℕ)) = Bool.false → x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) = x4) ∨ ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => (if x5.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x5.inputs else x5.inputs).any fun (x6 : ℕ) => (List.ofFn x2).getD x6 (1 : Fin (10 : ℕ)) == (0 : Fin (10 : ℕ))) x1.gates).length ≤ x1.size ∧ ∀ (x5 : Fin (10 : ℕ) → Bool), x5 (0 : Fin (10 : ℕ)) = Bool.false → x4.eval ((List.ofFn fun (x7 : Fin (9 : ℕ)) => x5 ([(2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))].getD ↑x7 (0 : Fin (10 : ℕ)))) ++ [Bool.false]) = x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) := by
  intro C σ hC
  classical
  by_cases hne : ∃ b, ∀ y : {y : Fin 10 → Bool // y 0 = false}, C.eval (List.ofFn (y.1 ∘ σ) ++ [y.1 0 || y.1 2]) = b
  · obtain ⟨b, hb⟩ := hne
    exact Or.inl ⟨b, fun y hy => hb ⟨y, hy⟩⟩
  right
  let X := {y : Fin 10 → Bool // y 0 = false}
  let src : X → List Bool := fun y => List.ofFn (y.1 ∘ σ) ++ [y.1 0 || y.1 2]
  let pi : List (Fin 10) := [2, 3, 8, 6, 1, 7, 4, 5, 9]
  let tgt : X → List Bool := fun y => (List.ofFn fun k : Fin 9 => y.1 (pi.getD k 0)) ++ [false]
  let P : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g => (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs).any fun i => (List.ofFn σ).getD i 1 == 0
  obtain ⟨F, hF1, hF2⟩ := PEqualNP.Outside.L_meta_6198.cntp P C.gates
  have hsrc : ∀ y, (src y).length = 11 := by intro y; simp [src]
  have htgt : ∀ y, (tgt y).length = 10 := by intro y; simp [tgt]
  have s1 : ∀ (y : X) (i : ℕ) (hi : i < 10), (src y).getD i false = y.1 (σ ⟨i, hi⟩) := by
    intro y i hi
    simp only [src]
    rw [PEqualNP.Outside.L_meta_6198.getD_lt _ _ _ (by simpa using hi), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
    rfl
  have s2 : ∀ y : X, (src y).getD 10 false = y.1 2 := by
    intro y
    have := PEqualNP.Outside.L_meta_6198.getD_at (List.ofFn (y.1 ∘ σ)) (y.1 0 || y.1 2)
    rw [List.length_ofFn] at this
    simp only [src]
    rw [this, y.2]; rfl
  have t1 : ∀ (y : X) (k : ℕ) (hk : k < 9), (tgt y).getD k false = y.1 (pi.getD k 0) := by
    intro y k hk
    simp only [tgt]
    rw [PEqualNP.Outside.L_meta_6198.getD_lt _ _ _ (by simpa using hk), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk]
    rfl
  have cov : ∀ a : Fin 10, a ≠ 0 → ∃ k, k < 9 ∧ pi.getD k 0 = a := by
    decide
  have zero : ∀ i, (List.ofFn σ).getD i 1 = 0 → i < 11 ∧ ∀ y : X, (src y).getD i false = false := by
    intro i hi
    by_cases h : i < 10
    · refine ⟨by omega, fun y => ?_⟩
      rw [s1 y i h]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h] at hi
      simp only [Option.getD_some] at hi
      rw [hi]; exact y.2
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by decide)
  obtain ⟨D, hD1, hD2, hD3⟩ := PEqualNP.Outside.L_meta_6198.engine2 11 10 C src tgt hsrc htgt F hC (by
    intro w hw
    by_cases h : w < 10
    · by_cases h2 : σ ⟨w, h⟩ = 0
      · exact Or.inl ⟨false, fun y => by rw [s1 y w h, h2]; exact y.2⟩
      · obtain ⟨k, hk, e⟩ := cov _ h2
        exact Or.inr ⟨k, by omega, fun y => by rw [s1 y w h, t1 y k hk, e]⟩
    · have : w = 10 := by omega
      subst this
      exact Or.inr ⟨0, by omega, fun y => by rw [s2 y, t1 y 0 (by omega)]; rfl⟩) hne (by
    intro j hj
    obtain ⟨hjl, hP⟩ := hF2 j hj
    refine ⟨hjl, ?_⟩
    have hg := hC _ (List.getElem_mem hjl)
    have hop : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hg.1
    have rg := fun y : X => PEqualNP.Outside.L_meta_6198.run_gate C.gates (src y) j hjl
    simp only [hsrc] at rg
    have z : ∀ i, (List.ofFn σ).getD i 1 = 0 → ∀ y : X, (if i < 11 + j then (PEqualNP.Outside.L_meta_6198.run C.gates (src y)).getD i false else false) = false := by
      intro i hi y
      obtain ⟨h1, h2⟩ := zero i hi
      rw [PEqualNP.Outside.L_meta_6198.run_input _ _ _ (by rw [hsrc]; exact h1), h2 y]; simp
    obtain ⟨op, l, hgate⟩ : ∃ op l, C.gates[j] = ⟨op, l⟩ := ⟨_, _, rfl⟩
    rw [hgate] at hop hg hP
    simp only [hgate] at rg
    simp only at hop
    have hl : l.length ≤ 2 := hg.2
    rcases hop with rfl | rfl | rfl
    · left
      refine ⟨false, fun x => ?_⟩
      rw [rg x]
      have hm : ∃ i ∈ l, (List.ofFn σ).getD i 1 = 0 := by simpa [P, PEqualNP.CircuitLowerBounds.GateOp.eval] using hP
      obtain ⟨i, hi, hi0⟩ := hm
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_false, Function.comp, id]
      exact ⟨i, hi, by rw [z i hi0 x]; simp⟩
    · have hm : ∃ i ∈ l, (List.ofFn σ).getD i 1 = 0 := by simpa [P, PEqualNP.CircuitLowerBounds.GateOp.eval] using hP
      obtain ⟨i, hi, hi0⟩ := hm
      have other : ∃ q, ∀ x, (PEqualNP.Outside.L_meta_6198.run C.gates (src x)).getD (11 + j) false = (if q < 11 + j then (PEqualNP.Outside.L_meta_6198.run C.gates (src x)).getD q false else false) := by
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · cases hi
        · refine ⟨a, fun x => ?_⟩
          rw [rg x]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · refine ⟨b, fun x => ?_⟩
            rw [rg x]
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, z _ hi0 x, Bool.false_or, Bool.or_false]
          · refine ⟨a, fun x => ?_⟩
            rw [rg x]
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, z _ hi0 x, Bool.or_false]
        · simp at hl
      obtain ⟨q, hq⟩ := other
      by_cases hqj : q < 11 + j
      · exact Or.inr ⟨q, hqj, fun x => by rw [hq x, if_pos hqj]⟩
      · exact Or.inl ⟨false, fun x => by rw [hq x, if_neg hqj]⟩
    · left
      refine ⟨true, fun x => ?_⟩
      rw [rg x]
      have hm : ∃ i ∈ l.take 1, (List.ofFn σ).getD i 1 = 0 := by simpa [P, PEqualNP.CircuitLowerBounds.GateOp.eval] using hP
      rcases l with _ | ⟨a, l⟩
      · simp at hm
      · have ha : (List.ofFn σ).getD a 1 = 0 := by
          obtain ⟨i, hi, hi0⟩ := hm
          have : i = a := by simpa using hi
          rw [← this]; exact hi0
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.headD_cons, z a ha x, Bool.not_false])
  refine ⟨D, hD1, ?_, fun y hy => hD3 ⟨y, hy⟩⟩
  rw [← hF1]
  exact hD2
