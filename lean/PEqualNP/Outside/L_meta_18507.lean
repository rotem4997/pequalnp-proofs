import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18507
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def push (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def higher (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (k + ·)⟩

lemma after (pre w : List Bool) (gs : List Gate) :
    (gs.map (higher pre.length)).foldl push (pre ++ w) = pre ++ gs.foldl push w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tail ih =>
    simp only [List.map_cons, List.foldl_cons]
    have h (i : ℕ) : (pre ++ w).getD (pre.length + i) false = w.getD i false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append]
    have eq : push (pre ++ w) (higher pre.length g) = pre ++ push w g := by
      simp only [push, higher, List.map_map, Function.comp_def, h, List.append_assoc]
    rw [eq, ih]

def pairing {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : Gate :=
  ⟨GateOp.or, [i.val, n + (p i).val]⟩

lemma earlier {n : ℕ} (p : Equiv.Perm (Fin n)) (u v : Fin n) (l : List (Fin n)) (extra : List Bool) :
    (l.map (pairing p)).foldl push (oneEach u v ++ extra) =
      oneEach u v ++ (extra ++ l.map fun i => decide (i = u ∨ i = p.symm v)) := by
  induction l generalizing extra with
  | nil => simp
  | cons i rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    have val1 : (oneEach u v ++ extra).getD i.val false = decide (i = u) := by
      simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, i.isLt, show i.val < n+n by omega]
    have val2 : (oneEach u v ++ extra).getD (n + (p i).val) false = decide (p i = v) := by
      simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, (p i).isLt]
    have eq : push (oneEach u v ++ extra) (pairing p i) =
        oneEach u v ++ (extra ++ [decide (i = u ∨ i = p.symm v)]) := by
      simp only [push, pairing, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, List.append_assoc, val1, val2]
      simp [Equiv.apply_eq_iff_eq_symm_apply]
    rw [eq, ih]
    simp

def liftC {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨(List.finRange n).map (pairing p) ++ C.gates.map (higher (n+n)), n+n+C.output⟩

lemma liftEval {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (u v : Fin n) :
    (liftC p C).eval (oneEach u v) =
    C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = p.symm v)) := by
  have h := earlier p u v (List.finRange n) []
  simp only [List.append_nil, List.nil_append] at h
  have hl : (oneEach u v).length = n+n := by simp [oneEach]
  change (((List.finRange n).map (pairing p) ++ C.gates.map (higher (n+n))).foldl push (oneEach u v)).getD (n+n+C.output) false = _
  rw [List.foldl_append, h, ← hl, after]
  rw [← List.ofFn_eq_map]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, Circuit.eval, Circuit.wires]
  <;> rfl

lemma liftMono {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (hc : Monotone2 C) : Monotone2 (liftC p C) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
    simp [pairing]
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    simpa [higher] using hc q hq

end PEqualNP.Outside.L_meta_18507
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_meta_18507

theorem PEqualNP.Outside.L_meta_18507 : (∀ (n s : ℕ) (H : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)), (∀ a b, H a b = H b a) → (∀ a, H a a = false) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ (∀ a : Fin n, C.eval (List.ofFn fun i : Fin n => decide (i = a)) = false) ∧ (∀ a b : Fin n, a ≠ b → C.eval (List.ofFn fun i : Fin n => decide (i = a ∨ i = b)) = H a b)) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => H u (π.symm v)) (n + s)) := by
  intro n s H p _ diag hc
  obtain ⟨C, hm, hs, one, two⟩ := hc
  refine ⟨liftC p C, liftMono p C hm, ?_, ?_⟩
  · simpa [liftC, Circuit.size] using Nat.add_le_add_left hs n
  · intro u v
    change (liftC p C).eval (oneEach u v) = H u (p.symm v)
    rw [liftEval]
    by_cases h : u = p.symm v
    · rw [← h, diag]
      simpa using one u
    · exact two u _ h
