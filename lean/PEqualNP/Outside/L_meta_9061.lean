import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9061

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

end PEqualNP.Outside.L_meta_9061

theorem PEqualNP.Outside.L_meta_9061 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (400 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → (¬∃ (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[(1 : ℕ)]? = Option.some x17) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R inst C hq hn hcard _ hM h1 h2 hand hin hedge _ hno
  exfalso
  have hlen : C.gates.length ≤ 1 := by
    by_contra h
    exact hno ⟨C.gates[1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hsz : C.size = C.gates.length := rfl
  have ho : C.output = n + n := by omega
  obtain ⟨g, hg, hop⟩ := hand
  rw [ho, Nat.sub_self] at hg
  obtain ⟨a, b, hab, hlt, hb⟩ := hin 0 g hg
  have hg0 : 0 < C.gates.length := by omega
  have hgg : C.gates[0] = g := by
    rw [List.getElem?_eq_getElem hg0] at hg; simpa using hg
  have hval : ∀ x : Fin (n + n) → Bool, C.eval (List.ofFn x) = true → (List.ofFn x).getD a false = true := by
    intro x hx
    have h := PEqualNP.Outside.L_meta_9061.run_gate C.gates (List.ofFn x) 0 hg0
    have he : C.eval (List.ofFn x) = (PEqualNP.Outside.L_meta_9061.run C.gates (List.ofFn x)).getD (n + n + 0) false := by
      show (PEqualNP.Outside.L_meta_9061.run C.gates (List.ofFn x)).getD C.output false = _
      rw [ho]; rfl
    rw [List.length_ofFn] at h
    rw [he, h, hgg, hop, hab] at hx
    simp only [List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true] at hx
    have := hx.1
    rw [if_pos (by omega), PEqualNP.Outside.L_meta_9061.run_input _ _ _ (by rw [List.length_ofFn]; omega)] at this
    exact this
  have hn2 : 2 ≤ n := by nlinarith
  obtain ⟨v, hv⟩ : ∃ v : Fin n, (Fin.natAdd n v : Fin (n + n)).val ≠ a := by
    by_contra hcon
    push Not at hcon
    have e0 := hcon ⟨0, by omega⟩
    have e1 := hcon ⟨1, by omega⟩
    simp only [Fin.val_natAdd] at e0 e1
    omega
  obtain ⟨u, hu, hua⟩ : ∃ u : Fin n, R u v ∧ u.val ≠ a := by
    have hc := hcard v
    have h1lt : 1 < Fintype.card { x // R x v } := by rw [hc]; omega
    obtain ⟨⟨p, hp⟩, ⟨r, hr⟩, hne⟩ := Fintype.one_lt_card_iff.mp h1lt
    by_cases hpa : p.val = a
    · refine ⟨r, hr, fun hra => hne ?_⟩
      apply Subtype.ext
      apply Fin.ext
      show p.val = r.val
      omega
    · exact ⟨p, hp, hpa⟩
  have key := hval _ (hedge u v hu)
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn] at key
  simp only [decide_eq_true_eq] at key
  rcases key with h | h
  · exact hua (by have := congrArg Fin.val h; simpa using this.symm)
  · exact hv (by have := congrArg Fin.val h; simpa using this.symm)
