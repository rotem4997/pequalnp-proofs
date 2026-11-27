import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6917

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




def cst : Gate := ⟨GateOp.or, []⟩

def wv (hs : List Gate) (x : List Bool) : Option ℕ → Bool
  | none => false
  | some t => (run hs x).getD t false

def ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), (gs[i].op = GateOp.and ∨ gs[i].op = GateOp.or) ∧ ∃ a b, gs[i].inputs = [a, b] ∧ a < n + i ∧ b < n + i

theorem ok_pre {n : ℕ} {gs : List Gate} {g : Gate} (h : ok n (gs ++ [g])) : ok n gs := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

theorem ok_last {n : ℕ} {gs : List Gate} {g : Gate} (h : ok n (gs ++ [g])) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n + gs.length ∧ b < n + gs.length := by
  have := h gs.length (by simp)
  simpa using this

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : ok n gs) (g : Gate) (h1 : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : ℕ) (h2 : g.inputs = [a, b]) (ha : a < n + gs.length) (hb : b < n + gs.length) : ok n (gs ++ [g]) := by
  intro i hi
  rcases Nat.lt_or_ge i gs.length with h3 | h3
  · rw [List.getElem_append_left h3]; exact h i h3
  · have : i = gs.length := by simp at hi; omega
    subst this
    simpa using ⟨h1, a, b, h2, ha, hb⟩

theorem set_ne (gs : List Gate) (g c : Gate) (j : ℕ) (h : j ≠ gs.length) : (gs ++ [g]).set j c = gs.set j c ++ [g] := by
  rcases Nat.lt_or_ge j gs.length with h1 | h1
  · rw [List.set_append_left _ _ h1]
  · rw [List.set_eq_of_length_le (by simp; omega), List.set_eq_of_length_le (by omega)]

theorem set_eq (gs : List Gate) (g c : Gate) : (gs ++ [g]).set gs.length c = gs ++ [c] := by simp

theorem build (n j : ℕ) : ∀ gs : List Gate, ok n gs → ∃ (hs : List Gate) (m : ℕ → Option ℕ), ok n hs ∧ hs.length ≤ gs.length ∧
    (j < gs.length → hs.length < gs.length) ∧ (∀ w t, m w = some t → w < n + gs.length → t < n + hs.length) ∧
    ∀ x : List Bool, x.length = n → ∀ w < n + gs.length, (run (gs.set j cst) x).getD w false = wv hs x (m w) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], some, by intro i hi; simp at hi, le_rfl, by simp, by intro w t h hw; cases h; exact hw, ?_⟩
    intro x hx w hw
    simp [wv, run]
  | append_singleton gs g ih =>
    intro h
    obtain ⟨hs, m, i1, i2, i3, i4, i5⟩ := ih (ok_pre h)
    obtain ⟨hop, a, b, hab, ha, hb⟩ := ok_last h
    -- generic finish without a new gate
    have fin0 : ∀ v : Option ℕ, (∀ t, v = some t → t < n + hs.length) → (j < gs.length → True) →
        (∀ x : List Bool, x.length = n → (run ((gs ++ [g]).set j cst) x).getD (n + gs.length) false = wv hs x v) →
        ∃ (hs' : List Gate) (m' : ℕ → Option ℕ), ok n hs' ∧ hs'.length ≤ (gs ++ [g]).length ∧
    (j < (gs ++ [g]).length → hs'.length < (gs ++ [g]).length) ∧ (∀ w t, m' w = some t → w < n + (gs ++ [g]).length → t < n + hs'.length) ∧
    ∀ x : List Bool, x.length = n → ∀ w < n + (gs ++ [g]).length, (run ((gs ++ [g]).set j cst) x).getD w false = wv hs' x (m' w) := by
      intro v hv _ hx0
      refine ⟨hs, Function.update m (n + gs.length) v, i1, by simp; omega, by intro _; simp; omega, ?_, ?_⟩
      · intro w t hw hlt
        by_cases hwe : w = n + gs.length
        · subst hwe; rw [Function.update_self] at hw; exact hv t hw
        · rw [Function.update_of_ne hwe] at hw
          exact i4 w t hw (by simp at hlt; omega)
      · intro x hx w hw
        by_cases hwe : w = n + gs.length
        · subst hwe; rw [Function.update_self]; exact hx0 x hx
        · rw [Function.update_of_ne hwe, ← i5 x hx w (by simp at hw; omega)]
          have hw' : w < n + gs.length := by simp at hw; omega
          by_cases hj : j = gs.length
          · rw [hj, set_eq, List.set_eq_of_length_le (le_refl _), run_prefix _ _ _ _ (by omega)]
          · rw [set_ne _ _ _ _ hj, run_prefix _ _ _ _ (by simp; omega)]
    by_cases hj : j = gs.length
    · refine fin0 none (by intro t h; cases h) (fun _ => trivial) ?_
      intro x hx
      rw [hj, set_eq, run_snoc]
      have : n + gs.length = (run gs x).length := by rw [run_length, hx]
      rw [this, getD_at]
      simp [wv, cst, GateOp.eval]
    have val : ∀ x : List Bool, x.length = n → (run ((gs ++ [g]).set j cst) x).getD (n + gs.length) false = g.op.eval [wv hs x (m a), wv hs x (m b)] := by
      intro x hx
      rw [set_ne _ _ _ _ hj, run_snoc]
      have : n + gs.length = (run (gs.set j cst) x).length := by rw [run_length, hx]; simp
      rw [this, getD_at, hab]
      simp only [List.map_cons, List.map_nil]
      rw [i5 x hx a ha, i5 x hx b hb]
    have lt1 : hs.length < (gs ++ [g]).length := by simp; omega
    rcases hma : m a with _ | s
    · rcases hop with ho | ho
      · refine fin0 none (by intro t h; cases h) (fun _ => trivial) fun x hx => ?_
        rw [val x hx, hma, ho]; simp [wv, GateOp.eval]
      · refine fin0 (m b) (fun t ht => i4 b t ht hb) (fun _ => trivial) fun x hx => ?_
        rw [val x hx, hma, ho]; simp [wv, GateOp.eval]
    rcases hmb : m b with _ | t
    · rcases hop with ho | ho
      · refine fin0 none (by intro t h; cases h) (fun _ => trivial) fun x hx => ?_
        rw [val x hx, hmb, ho]; simp [wv, GateOp.eval]
      · refine fin0 (m a) (fun t ht => i4 a t ht ha) (fun _ => trivial) fun x hx => ?_
        rw [val x hx, hmb, ho]; simp [wv, GateOp.eval]
    have hs1 := i4 a s hma ha
    have ht1 := i4 b t hmb hb
    refine ⟨hs ++ [⟨g.op, [s, t]⟩], Function.update m (n + gs.length) (some (n + hs.length)), ok_snoc i1 _ hop s t rfl hs1 ht1, by simp; omega, ?_, ?_, ?_⟩
    · intro hlt
      have : j < gs.length := by simp at hlt; omega
      have := i3 this
      simp; omega
    · intro w r hw hlt
      by_cases hwe : w = n + gs.length
      · subst hwe; rw [Function.update_self] at hw; cases hw; simp
      · rw [Function.update_of_ne hwe] at hw
        have := i4 w r hw (by simp at hlt; omega)
        simp; omega
    · intro x hx w hw
      by_cases hwe : w = n + gs.length
      · subst hwe
        rw [Function.update_self, val x hx, hma, hmb]
        have : n + hs.length = (run hs x).length := by rw [run_length, hx]
        simp only [wv]
        rw [this, run_snoc, getD_at]
        simp
      · have hw' : w < n + gs.length := by simp at hw; omega
        rw [Function.update_of_ne hwe, set_ne _ _ _ _ hj, run_prefix _ _ _ _ (by simp; omega), i5 x hx w hw']
        rcases hmw : m w with _ | r
        · rfl
        · have := i4 w r hmw hw'
          simp only [wv]
          rw [run_prefix _ _ _ _ (by omega)]

theorem cutle (j : ℕ) (x : List Bool) : ∀ gs : List Gate, (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → ∀ i,
    (run (gs.set j cst) x).getD i false = true → (run gs x).getD i false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ i h; simpa using h
  | append_singleton gs g ih =>
    intro hop i h
    have ih' := ih fun g hg => hop g (by simp [hg])
    have l1 : (run gs x).length = x.length + gs.length := run_length gs x
    have l2 : (run (gs.set j cst) x).length = x.length + gs.length := by rw [run_length]; simp
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hi | hi | hi
    · rw [run_prefix _ _ _ _ hi]
      refine ih' i ?_
      by_cases hj : j = gs.length
      · rw [hj, set_eq, run_prefix _ _ _ _ hi] at h
        rw [hj, List.set_eq_of_length_le (le_refl _)]; exact h
      · rw [set_ne _ _ _ _ hj, run_prefix _ _ _ _ (by simpa using hi)] at h
        exact h
    · by_cases hj : j = gs.length
      · rw [hj, set_eq, run_snoc, hi, ← l1, getD_at] at h
        simp [cst, GateOp.eval] at h
      · rw [set_ne _ _ _ _ hj, run_snoc, hi, ← l2, getD_at] at h
        rw [run_snoc, hi, ← l1, getD_at]
        rcases hop g (by simp) with ho | ho
        · rw [ho] at h ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at h ⊢
          exact fun k hk => ih' k (h k hk)
        · rw [ho] at h ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at h ⊢
          obtain ⟨k, hk, hk2⟩ := h
          exact ⟨k, hk, ih' k hk2⟩
    · rw [List.getD_eq_default _ _ (by
        have := run_length ((gs ++ [g]).set j cst) x
        simp at this ⊢; omega)] at h
      cases h

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6917

theorem PEqualNP.Outside.L_meta_6917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x2.size),   PEqualNP.TopForm.IsAO2 x1 x2 →     have x5 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates.set ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x6 ∧ x6.size < x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧ ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x6 x7 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x7 = Bool.true := by
  intro n C j hC C1
  have hok : PEqualNP.Outside.L_meta_6917.ok n C.gates := by
    intro i hi
    refine ⟨hC.1 _ (List.getElem_mem hi), ?_⟩
    have h2 := hC.2.2 _ (List.getElem_mem hi)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 h2
    have h3 := hC.2.1 i hi
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ hi
    rw [e, hab] at h3
    exact ⟨a, b, hab, h3 a (by simp), h3 b (by simp)⟩
  obtain ⟨hs, m, i1, i2, i3, i4, i5⟩ := PEqualNP.Outside.L_meta_6917.build n j C.gates hok
  have hj : (j : ℕ) < C.gates.length := j.isLt
  have le1 : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C1 y = true → PEqualNP.MetaComplexity.circuitFun n C y = true := by
    intro y hy
    exact PEqualNP.Outside.L_meta_6917.cutle j (List.ofFn y) C.gates hC.1 C.output hy
  have ao : ∀ hs o, PEqualNP.Outside.L_meta_6917.ok n hs → PEqualNP.TopForm.IsAO2 n ⟨hs, o⟩ := by
    intro hs o h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (h i hi).1
    · intro i hi k hk
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨hs, o⟩ i = hs[i] := List.getD_eq_getElem _ _ hi
      rw [e] at hk
      obtain ⟨_, a, b, hab, ha, hb⟩ := h i hi
      rw [hab] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨_, a, b, hab, _, _⟩ := h i hi
      rw [hab]; rfl
  have zero : (∀ y, PEqualNP.MetaComplexity.circuitFun n C1 y = false) → ∃ D, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C1 ∧ ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D y = true → PEqualNP.MetaComplexity.circuitFun n C y = true := by
    intro hz
    have hD : ∀ y, PEqualNP.MetaComplexity.circuitFun n ⟨[], n⟩ y = false := by
      intro y
      simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    refine ⟨⟨[], n⟩, ao _ _ (by intro i hi; simp at hi), by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using Nat.zero_lt_of_lt hj, ?_, ?_⟩
    · funext y; rw [hD, hz]
    · intro y hy; rw [hD] at hy; cases hy
  by_cases ho : C.output < n + C.gates.length
  · have hv : ∀ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C1 y = PEqualNP.Outside.L_meta_6917.wv hs (List.ofFn y) (m C.output) := by
      intro y
      exact i5 (List.ofFn y) (by simp) C.output ho
    rcases hm : m C.output with _ | t
    · refine zero fun y => ?_
      rw [hv, hm]; rfl
    · refine ⟨⟨hs, t⟩, ao _ _ i1, i3 hj, ?_, ?_⟩
      · funext y
        rw [hv, hm]; rfl
      · intro y hy
        refine le1 y ?_
        rw [hv, hm]; exact hy
  · refine zero fun y => ?_
    change (PEqualNP.Outside.L_meta_6917.run (C.gates.set j PEqualNP.Outside.L_meta_6917.cst) (List.ofFn y)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6917.run_length]; simp; omega)]
