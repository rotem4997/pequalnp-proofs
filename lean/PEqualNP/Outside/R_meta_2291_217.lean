import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first selected output may be replaced by false in every later gate.
-- Both selected gates can then be evaluated separately on the same eleven-gate core.
-- Wire 21 supplies the default false bit for a missing or removed wire.
theorem PEqualNP.Outside.R_meta_2291_217
    (positive :
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (gs : List Gate) (a b : Gate), gs.length ≤ 11 →
        FanInTwo ⟨gs ++ [a,b], 0⟩ →
        (∀ g ∈ gs ++ [a,b], ∀ i ∈ g.inputs, i ≤ 21) →
        a.op ≠ .not → b.op ≠ .not →
        ∃ x : Fin 9 → Bool,
          let w := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 && x 6])
          let read := fun (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)
          (read a || read b) ≠ f x)
    (negative :
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (gs : List Gate) (g : Gate) (i : ℕ), gs.length ≤ 11 → i ≤ 21 →
        FanInTwo ⟨gs ++ [g], 0⟩ →
        (∀ h ∈ gs ++ [g], ∀ j ∈ h.inputs, j ≤ 21) →
        let w := fun x : Fin 9 → Bool => (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 && x 6])
        let read := fun x => g.op.eval (g.inputs.map fun j => (w x).getD j false)
        (∀ x, f x = false → read x = false ∧ (w x).getD i false = true) →
        ∃ x, f x = true ∧ read x = false ∧ (w x).getD i false = true) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length → (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) := by
  let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let input := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 && x 6]
  have ninput (x) : (input x).length = 10 := by simp [input]
  let val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := w ++ [val g w]
  let rewire (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
  have transport (r : ℕ → ℕ) (g : Gate) (old new : List Bool)
      (h : ∀ i, new.getD (r i) false = old.getD i false) :
      val (rewire r g) new = val g old := by
    unfold val rewire
    simp only [List.map_map]
    exact congrArg g.op.eval (List.map_congr_left (fun i _ => h i))
  have lengthRun (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp [ih, step, Nat.add_comm, Nat.add_left_comm]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have produced (pre : List Gate) (g : Gate) (post : List Gate) (w : List Bool) :
      ((pre ++ g :: post).foldl step w).getD (w.length + pre.length) false =
        val g (pre.foldl step w) := by
    rw [List.foldl_append, List.foldl_cons, ← lengthRun pre w,
      keep _ _ _ (by simp [step])]
    simp [step]
  have splitAtWire (gs : List Gate) (i : ℕ) (h : i < gs.length) :
      ∃ p a q, gs = p ++ a :: q ∧ p.length = i := by
    refine ⟨gs.take i, gs[i], gs.drop (i + 1), ?_, by simp [Nat.le_of_lt h]⟩
    rw [← List.drop_eq_getElem_cons h, List.take_append_drop]
  let cap := fun i : ℕ => min i 21
  have capRead (w : List Bool) (hw : w.length ≤ 21) (i : ℕ) :
      w.getD (cap i) false = w.getD i false := by
    by_cases h : i ≤ 21
    · simp [cap, h]
    · rw [show cap i = 21 from Nat.min_eq_right (by omega),
        List.getD_eq_default _ _ hw, List.getD_eq_default _ _ (by omega)]
  have capRun (gs : List Gate) (w : List Bool) (hw : w.length + gs.length ≤ 21) :
      (gs.map (rewire cap)).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.length_cons] at hw
      have eq : step w (rewire cap g) = step w g := by
        simp only [step, transport cap g w w (capRead w (by omega))]
      simp only [List.map_cons, List.foldl_cons, eq]
      apply ih
      simp only [step, List.length_append, List.length_singleton]
      omega
  let skip := fun (k i : ℕ) => if i < k then i else if i = k then 21 else i - 1
  have skipRead (w t : List Bool) (k : ℕ) (hk : w.length = k)
      (size : (w ++ t).length ≤ 21) (i : ℕ) :
      (w ++ t).getD (skip k i) false = (w ++ false :: t).getD i false := by
    by_cases h : i < k
    · simp only [skip, ite_eq_left h, List.getD_append _ _ _ _ (show i < w.length by omega)]
    · by_cases e : i = k
      · subst i
        rw [show skip k k = 21 by simp [skip], List.getD_eq_default _ _ size,
          List.getD_append_right _ _ _ _ (by omega), hk, Nat.sub_self]
        rfl
      · rw [show skip k i = i - 1 by simp [skip, h, e],
          List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),
          show i - w.length = (i - 1 - w.length) + 1 by omega, List.getD_cons_succ]
  have removeSlot (w : List Bool) (k : ℕ) (hk : w.length = k)
      (gs : List Gate) (t : List Bool) (size : (w ++ t).length + gs.length ≤ 21) :
      ∃ u : List Bool,
        gs.foldl step (w ++ false :: t) = w ++ false :: u ∧
        (gs.map (rewire (skip k))).foldl step (w ++ t) = w ++ u := by
    induction gs generalizing t with
    | nil => exact ⟨t, rfl, rfl⟩
    | cons g gs ih =>
      simp only [List.length_cons] at size
      let b := val g (w ++ false :: t)
      have moved := transport (skip k) g _ _ (skipRead w t k hk (by omega))
      have left : step (w ++ false :: t) g = w ++ false :: (t ++ [b]) := by
        simp [step, b, List.append_assoc]
      have right : step (w ++ t) (rewire (skip k) g) = w ++ (t ++ [b]) := by
        simp only [step, moved, List.append_assoc, b]
      simp only [List.map_cons, List.foldl_cons, left, right]
      apply ih
      simp only [List.length_append, List.length_singleton] at *
      omega
  let edges := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) ||
    (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
    (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  have graphEq : edges = f := by decide +kernel
  have witness : ∀ k : Fin 10,
      let x : Fin 9 → Bool := fun j =>
        if k.val = 9 then decide (j = 0 ∨ j = 6) else decide (j.val = k.val)
      (input x).getD k.val false = true ∧ f x = false := by decide +kernel
  intro gs i j fan size ij jbound eq
  have original (x) :
      ((gs.foldl step (input x)).getD i false || (gs.foldl step (input x)).getD j false) =
        f x := (congrFun eq x).trans (congrFun graphEq x)
  have ilo : 10 ≤ i := by
    by_contra! small
    let k : Fin 10 := ⟨i, small⟩
    let x : Fin 9 → Bool := fun v =>
      if k.val = 9 then decide (v = 0 ∨ v = 6) else decide (v.val = k.val)
    obtain ⟨on, off⟩ := witness k
    change (input x).getD i false = true at on
    change f x = false at off
    have h := original x
    rw [keep _ _ _ (by simpa only [ninput] using small), on, Bool.true_or, off] at h
    contradiction
  obtain ⟨pre, a, tail, rfl, plen⟩ := splitAtWire gs (i - 10) (by omega)
  simp only [List.length_append, List.length_cons] at size jbound
  obtain ⟨mid, b, post, rfl, mlen⟩ := splitAtWire tail (j - i - 1) (by omega)
  simp only [List.length_append, List.length_cons] at size
  have pi : 10 + pre.length = i := by omega
  have mj : 10 + (pre.length + (mid.length + 1)) = j := by omega
  let trim := fun t : ℕ => if t < i then t else 21
  let core := pre ++ mid.map (rewire (skip i))
  let T := core.map (rewire cap)
  let A := rewire cap (rewire trim a)
  let B := rewire cap (rewire (skip i) b)
  have smallCore : core.length ≤ 11 := by simp only [core, List.length_append, List.length_map]; omega
  have smallT : T.length ≤ 11 := by simpa [T] using smallCore
  let ok := fun g : Gate =>
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  have rewireOK (r) (g : Gate) : ok (rewire r g) ↔ ok g := by simp [ok, rewire]
  have bounded (g : Gate) : ∀ t ∈ (rewire cap g).inputs, t ≤ 21 := by
    intro t ht
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    exact Nat.min_le_right _ _
  have okA : ok A := (rewireOK _ _).mpr ((rewireOK _ _).mpr (fan a (by simp)))
  have okB : ok B := (rewireOK _ _).mpr ((rewireOK _ _).mpr (fan b (by simp)))
  have okT (g) (hg : g ∈ T) : ok g ∧ ∀ t ∈ g.inputs, t ≤ 21 := by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    refine ⟨(rewireOK _ _).mpr ?_, bounded v⟩
    rcases List.mem_append.mp hv with hp | hm
    · exact fan v (List.mem_append_left _ hp)
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
      exact (rewireOK _ _).mpr (fan u (by simp [hu]))
  let wires := fun x => T.foldl step (input x)
  have fits (x) : (wires x).length ≤ 21 := by
    simp only [wires, lengthRun, ninput]
    omega
  have independent (x) : (val A (wires x) || val B (wires x)) = f x := by
    let w := pre.foldl step (input x)
    have hw : w.length = i := by simp only [w, lengthRun, ninput, pi]
    have readA := produced pre a (mid ++ b :: post) (input x)
    have readB := produced (pre ++ a :: mid) b post (input x)
    simp only [ninput, pi] at readA
    simp only [ninput, List.length_append, List.length_cons, mj, List.append_assoc,
      List.cons_append, List.foldl_append, List.foldl_cons] at readB
    have orig : (val a w || val b (mid.foldl step (w ++ [val a w]))) = f x := by
      have h := original x
      rw [readA] at h
      convert h using 2
      simpa only [List.foldl_append, List.foldl_cons] using readB.symm
    obtain ⟨t, pinned, shortened⟩ := removeSlot w i hw mid [] (by
      simp only [List.append_nil]; omega)
    simp only [List.append_nil] at shortened
    have wc : wires x = w ++ t := by
      dsimp only [wires, T]
      rw [capRun _ _ (by rw [ninput]; omega)]
      exact (List.foldl_append ..).trans shortened
    have ht : (w ++ t).length ≤ 21 := wc ▸ fits x
    have early : val (rewire trim a) (w ++ t) = val a w := by
      apply transport
      intro v
      by_cases h : v < i
      · simp only [trim, ite_eq_left h]
        exact List.getD_append _ _ _ _ (by omega)
      · simp only [trim, ite_eq_right h]
        rw [List.getD_eq_default _ _ ht, List.getD_eq_default _ _ (by omega)]
    rw [wc]
    change (val (rewire cap (rewire trim a)) (w ++ t) ||
      val (rewire cap (rewire (skip i) b)) (w ++ t)) = f x
    rw [transport cap _ _ _ (capRead _ ht), transport cap _ _ _ (capRead _ ht), early,
      transport (skip i) b _ _ (skipRead w t i hw ht), ← pinned]
    cases hb : val a w <;> simpa only [hb, Bool.true_or, Bool.false_or] using orig
  have withNeg (neg other : Gate) (hop : neg.op = .not) (hok : ok other)
      (npins : ∀ k ∈ neg.inputs, k ≤ 21) (opins : ∀ k ∈ other.inputs, k ≤ 21)
      (compute : ∀ x, (val neg (wires x) || val other (wires x)) = f x) : False := by
    let pin := neg.inputs.headD 21
    have pinBound : pin ≤ 21 := by
      cases hg : neg.inputs with
      | nil => simp [pin, hg]
      | cons a as => simpa [pin, hg] using npins a (by simp [hg])
    have negEval (x) : val neg (wires x) = !(wires x).getD pin false := by
      change neg.op.eval (neg.inputs.map fun j => (wires x).getD j false) = _
      rw [hop]
      change (!((neg.inputs.map fun j => (wires x).getD j false).headD false)) = _
      cases hg : neg.inputs with
      | nil => simp only [pin, hg, List.map_nil, List.headD_nil,
          List.getD_eq_default _ _ (fits x)]
      | cons a as => simp [pin, hg]
    have oneFan : FanInTwo ⟨T ++ [other], 0⟩ := by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact (okT v h).1
      · simpa only [List.mem_singleton.mp h] using hok
    have onePins : ∀ v ∈ T ++ [other], ∀ k ∈ v.inputs, k ≤ 21 := by
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact (okT v h).2
      · simpa only [List.mem_singleton.mp h] using opins
    have row (x) : ((!(wires x).getD pin false) || val other (wires x)) = f x := by
      rw [← negEval]; exact compute x
    obtain ⟨x, on, off, hit⟩ := negative T other pin smallT pinBound oneFan onePins (by
      intro x hx
      change val other (wires x) = false ∧ (wires x).getD pin false = true
      have zero := Bool.or_eq_false_iff.mp ((row x).trans hx)
      exact ⟨zero.2, by simpa using zero.1⟩)
    change f x = true at on
    change val other (wires x) = false at off
    change (wires x).getD pin false = true at hit
    have h := row x
    rw [hit, off, on] at h
    contradiction
  by_cases hn : A.op = .not
  · exact withNeg A B hn okB (bounded _) (bounded _) independent
  by_cases hm : B.op = .not
  · exact withNeg B A hm okA (bounded _) (bounded _) (fun x => (Bool.or_comm ..).trans (independent x))
  have pairFan : FanInTwo ⟨T ++ [A,B], 0⟩ := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact (okT v h).1
    · rcases (show v = A ∨ v = B by simpa using h) with rfl | rfl
      · exact okA
      · exact okB
  have pairPins : ∀ v ∈ T ++ [A,B], ∀ k ∈ v.inputs, k ≤ 21 := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact (okT v h).2
    · rcases (show v = A ∨ v = B by simpa using h) with rfl | rfl
      · exact bounded _
      · exact bounded _
  obtain ⟨x, hx⟩ := positive T A B smallT pairFan pairPins hn hm
  exact hx (independent x)
