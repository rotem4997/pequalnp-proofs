import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8241

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

end PEqualNP.Outside.L_meta_8241

theorem PEqualNP.Outside.L_meta_8241 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ)) (x3 : Fin (10 : ℕ) → ℕ) (x4 : Finset ℕ),   have x5 : (Fin (9 : ℕ) → Bool) → Fin (10 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ) → Bool) (x6 : Fin (10 : ℕ)) => (List.ofFn x5).getD (x3 x6) Bool.false;   have x6 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x6 : Fin (9 : ℕ) → Bool) => List.ofFn (x5 x6) ++ [!x5 x6 (0 : Fin (10 : ℕ))];   have x7 : ℕ → (Fin (9 : ℕ) → Bool) → Bool := fun (x7 : ℕ) (x8 : Fin (9 : ℕ) → Bool) => (x1.wires (x6 x8)).getD x7 Bool.false;   PEqualNP.MetaComplexity.FanInTwo x1 → x3 (0 : Fin (10 : ℕ)) = ↑x2 ∨ (9 : ℕ) ≤ x3 (0 : Fin (10 : ℕ)) → (∀ x10 ∈ x4, (11 : ℕ) ≤ x10 ∧ x10 < (11 : ℕ) + x1.size ∧ ((∃ (x12 : Bool), ∀ (x13 : Fin (9 : ℕ) → Bool), x7 x10 x13 = x12) ∨ ∃ x12 < x10, ∀ (x13 : Fin (9 : ℕ) → Bool), x7 x10 x13 = x7 x12 x13)) → (∃ (x11 : Bool), ∀ (x12 : Fin (9 : ℕ) → Bool), x1.eval (x6 x12) = x11) ∨ ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + x4.card ≤ x1.size + (1 : ℕ) ∧ (∀ (x12 : Fin (9 : ℕ) → Bool), (x11.wires (List.ofFn x12)).getD (9 : ℕ) Bool.false = !x12 x2) ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (x6 x12) := by
  intro C v m F y src V hC hm0 hF
  classical
  have hsrc : ∀ x, (src x).length = 11 := by intro x; simp [src]
  have gx : ∀ (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9), (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have gy : ∀ (x : Fin 9 → Bool) (i : Fin 10), (src x).getD (i : ℕ) false = y x i := by
    intro x i
    simp only [src]
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have g10 : ∀ (x : Fin 9 → Bool), (src x).getD 10 false = !y x 0 := by
    intro x
    simp only [src]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  by_cases hne : ∃ b, ∀ x, C.eval (src x) = b
  · exact Or.inl hne
  right
  let tgt : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [!x v]
  have t9 : ∀ x : Fin 9 → Bool, (tgt x).getD 9 false = !x v := by
    intro x
    simp only [tgt]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have tl : ∀ (x : Fin 9 → Bool) (i : ℕ), i < 9 → (tgt x).getD i false = (List.ofFn x).getD i false := by
    intro x i hi
    simp only [tgt]
    rw [List.getD_append _ _ _ _ (by simpa using hi)]
  let F' : Finset ℕ := F.image fun w => w - 11
  have hcard : F'.card = F.card := by
    refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
    have h1 := (hF a ha).1
    have h2 := (hF b hb).1
    have hab : a - 11 = b - 11 := hab
    omega
  obtain ⟨D, d1, d2, d3⟩ := PEqualNP.Outside.L_meta_8241.engine2 11 10 C src tgt hsrc (by intro x; simp [tgt]) F' hC (by
    intro w hw
    by_cases h10 : w < 10
    · have e := fun x => gy x ⟨w, h10⟩
      simp only at e
      by_cases h9 : m ⟨w, h10⟩ < 9
      · refine Or.inr ⟨m ⟨w, h10⟩, by omega, fun x => ?_⟩
        rw [e, tl x _ h9]
      · refine Or.inl ⟨false, fun x => ?_⟩
        rw [e]
        exact List.getD_eq_default _ _ (by simp; omega)
    · have : w = 10 := by omega
      subst this
      rcases hm0 with h | h
      · refine Or.inr ⟨9, by omega, fun x => ?_⟩
        rw [g10, t9]
        congr 1
        have hv := v.isLt
        simp only [y]
        rw [h, gx x v hv]
      · refine Or.inl ⟨true, fun x => ?_⟩
        rw [g10]
        have : y x 0 = false := List.getD_eq_default _ _ (by simp; omega)
        rw [this]; rfl) hne (by
    intro j hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨h1, h2, h3⟩ := hF w hw
    have e : 11 + (w - 11) = w := by omega
    have hs : C.size = C.gates.length := rfl
    refine ⟨by omega, ?_⟩
    rw [e]
    exact h3)
  rw [hcard] at d2
  refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.not, [(v : ℕ)]⟩ :: D.gates, D.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.1 hg with rfl | h
    · exact ⟨by simp, by simp⟩
    · exact d1 g h
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_cons] at d2 ⊢
    omega
  · intro x
    have e : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.not, [(v : ℕ)]⟩ :: D.gates, D.output⟩ (List.ofFn x) = PEqualNP.Outside.L_meta_8241.run D.gates (tgt x) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, PEqualNP.Outside.L_meta_8241.run, tgt, List.map_cons, List.map_nil, gx x v v.isLt, PEqualNP.CircuitLowerBounds.GateOp.eval, List.headD_cons]
    rw [e, PEqualNP.Outside.L_meta_8241.run_input _ _ _ (by simp [tgt]), t9]
  · intro x
    have e : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.not, [(v : ℕ)]⟩ :: D.gates, D.output⟩ (List.ofFn x) = PEqualNP.Outside.L_meta_8241.run D.gates (tgt x) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, PEqualNP.Outside.L_meta_8241.run, tgt, List.map_cons, List.map_nil, gx x v v.isLt, PEqualNP.CircuitLowerBounds.GateOp.eval, List.headD_cons]
    rw [← d3 x]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
    rw [e]
    rfl
