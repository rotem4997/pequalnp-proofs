import PEqualNP.MetaComplexity.Helpers.PadOr

/-!
# A rigid AND term: `(x AND y) OR g` costs exactly two gates more than `g`

Helper for `L-meta-153` (proofs only, no statement may use it). For a non-constant `g` on `k`
inputs, `(x 0 && x 1) || g (inputs 2 ..)` on `2 + k` inputs has a circuit with at most `s + 2`
gates exactly when `g` has one with at most `s`.

* Upward: rename the inputs of a circuit for `g` along `Fin.natAdd 2`, then add an AND gate on
  wires `0, 1` and an OR gate on that AND and the old output.
* Downward: rename to arity `k + 1 + 1`, one-gate elimination at input `0` with value `true`
  (`one_gate_at`), rename down to `x last || g` on `k + 1` inputs, then `pad_down`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RigidAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.PadOr

/-- Add an AND gate on wires `0, 1` and an OR gate reading it and the old output. -/
def addAndOr (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [m + C.gates.length, C.output]⟩],
    m + C.gates.length + 1⟩

theorem addAndOr_eval (C : Circuit) (x : List Bool) (h2 : 2 ≤ x.length)
    (hout : C.output < x.length + C.gates.length) :
    (addAndOr C x.length).eval x = ((x.getD 0 false && x.getD 1 false) || C.eval x) := by
  obtain ⟨t, ht, hl⟩ := fold_prefix C.gates x
  have hw : C.wires x = x ++ t := ht
  have hlen : (C.wires x).length = x.length + C.gates.length := by
    rw [hw, List.length_append, hl]
  set a := GateOp.and.eval ([0, 1].map fun i => (C.wires x).getD i false) with ha
  have hw2 : (addAndOr C x.length).wires x =
      (C.wires x ++ [a]) ++ [GateOp.or.eval ([x.length + C.gates.length, C.output].map
        fun i => (C.wires x ++ [a]).getD i false)] := by
    simp [addAndOr, Circuit.wires, List.foldl_append, ha]
  unfold Circuit.eval
  rw [hw2]
  have hl2 : (C.wires x ++ [a]).length = x.length + C.gates.length + 1 := by
    simp [hlen]
  have ho : (addAndOr C x.length).output = (C.wires x ++ [a]).length := by
    simp [addAndOr, hl2]
  rw [ho, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  have hA : (C.wires x ++ [a]).getD (x.length + C.gates.length) false = a := by
    rw [← hlen]; exact getD_snoc_eq _ _ _
  have hB : (C.wires x ++ [a]).getD C.output false = (C.wires x).getD C.output false := by
    rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hout)]
  have h0 : (C.wires x).getD 0 false = x.getD 0 false := by
    rw [hw, List.getD_append _ _ _ _ (by omega)]
  have h1 : (C.wires x).getD 1 false = x.getD 1 false := by
    rw [hw, List.getD_append _ _ _ _ (by omega)]
  simp only [List.map_cons, List.map_nil, hA, hB]
  simp only [ha, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id, h0, h1, Bool.or_false, Bool.and_true, List.getD_cons_zero]

/-- The target function: `(x 0 && x 1) || g (inputs 2 ..)`. -/
def andOr (k : ℕ) (g : (Fin k → Bool) → Bool) : (Fin (2 + k) → Bool) → Bool :=
  fun x => (x (Fin.castAdd k 0) && x (Fin.castAdd k 1)) || g (fun j : Fin k => x (Fin.natAdd 2 j))

/-- Upward: two more gates pay for the AND term. -/
theorem rigid_up (k s : ℕ) (g : (Fin k → Bool) → Bool) (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (h : HasCircuitSize k g s) : HasCircuitSize (2 + k) (andOr k g) (s + 2) := by
  obtain ⟨C, ok, hsz, hev⟩ := relabel_size (Fin.natAdd 2 : Fin k → Fin (2 + k)) g s h
  have hsz' : C.gates.length ≤ s := hsz
  have happ : ∀ y : Fin k → Bool,
      (Fin.append (fun _ : Fin 2 => false) y : Fin (2 + k) → Bool) ∘ Fin.natAdd 2 = y := by
    intro y; funext j; simp [Fin.append_right]
  have hout : C.output < 2 + k + C.gates.length := by
    by_contra hc
    obtain ⟨y, y', hyy⟩ := hnc
    have hfalse : ∀ x : Fin (2 + k) → Bool, C.eval (List.ofFn x) = false := by
      intro x
      obtain ⟨t, ht, hl⟩ := fold_prefix C.gates (List.ofFn x)
      unfold Circuit.eval
      apply List.getD_eq_default
      have : (C.wires (List.ofFn x)).length = 2 + k + C.gates.length := by
        have hw : C.wires (List.ofFn x) = List.ofFn x ++ t := ht
        rw [hw, List.length_append, hl, List.length_ofFn]
      omega
    apply hyy
    have e1 := hev (Fin.append (fun _ : Fin 2 => false) y)
    have e2 := hev (Fin.append (fun _ : Fin 2 => false) y')
    rw [hfalse] at e1 e2
    beta_reduce at e1 e2
    rw [happ] at e1 e2
    rw [← e1, ← e2]
  refine ⟨addAndOr C (2 + k), ?_, ?_, ?_⟩
  · intro gt hg
    simp only [addAndOr, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with hg | hg | hg
    · exact ok gt hg
    · subst hg; simp
    · subst hg; simp
  · simp [addAndOr, Circuit.size]; omega
  · intro x
    have hl : (List.ofFn x).length = 2 + k := List.length_ofFn
    have e := addAndOr_eval C (List.ofFn x) (by rw [hl]; omega) (by rw [hl]; exact hout)
    rw [hl] at e
    rw [e, hev x]
    have h0 : (List.ofFn x).getD 0 false = x (Fin.castAdd k 0) := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getElem_ofFn]; rfl
    have h1 : (List.ofFn x).getD 1 false = x (Fin.castAdd k 1) := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getElem_ofFn]; rfl
    rw [h0, h1]; rfl

/-- Downward: the AND term costs at least two gates. -/
theorem rigid_down (k s : ℕ) (g : (Fin k → Bool) → Bool) (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (h : HasCircuitSize (2 + k) (andOr k g) (s + 2)) : HasCircuitSize k g s := by
  have hk : k + 1 + 1 = 2 + k := by omega
  have hH := relabel_size (Fin.cast hk.symm : Fin (2 + k) → Fin (k + 1 + 1)) (andOr k g) _ h
  set H : (Fin (k + 1 + 1) → Bool) → Bool :=
    fun z => andOr k g (z ∘ Fin.cast hk.symm) with hHdef
  set p : Fin (k + 1 + 1) := ⟨0, by omega⟩ with hp
  set q : Fin (k + 1 + 1) := ⟨1, by omega⟩ with hq
  set r : Fin k → Fin (k + 1 + 1) := fun j => ⟨2 + j, by omega⟩ with hr
  have hHval : ∀ z, H z = ((z p && z q) || g (fun j => z (r j))) := by
    intro z; rfl
  obtain ⟨y, y', hyy⟩ := hnc
  obtain ⟨w, hw⟩ : ∃ w : Fin k → Bool, g w = false := by
    cases h1 : g y
    · exact ⟨y, h1⟩
    · cases h2 : g y'
      · exact ⟨y', h2⟩
      · exact absurd (h1.trans h2.symm) hyy
  -- a point built from the values at p, q and the rest
  let mk : Bool → Bool → (Fin k → Bool) → Fin (k + 1 + 1) → Bool :=
    fun a b v i => if i.val = 0 then a else if i.val = 1 then b else
      if hi : i.val - 2 < k then v ⟨i.val - 2, hi⟩ else false
  have mk_p : ∀ a b v, mk a b v p = a := by intro a b v; simp [mk, hp]
  have mk_q : ∀ a b v, mk a b v q = b := by intro a b v; simp [mk, hq]
  have mk_r : ∀ a b v, (fun j => mk a b v (r j)) = v := by
    intro a b v; funext j; simp [mk, hr]; omega
  have up_p : ∀ (z : Fin (k + 1 + 1) → Bool) (c : Bool), Function.update z p c p = c := by
    intro z c; simp
  have up_q : ∀ (z : Fin (k + 1 + 1) → Bool) (c : Bool), Function.update z p c q = z q := by
    intro z c; apply Function.update_of_ne; simp [hp, hq, Fin.ext_iff]
  have up_r : ∀ (z : Fin (k + 1 + 1) → Bool) (c : Bool),
      (fun j => Function.update z p c (r j)) = fun j => z (r j) := by
    intro z c; funext j; apply Function.update_of_ne; simp [hp, hr, Fin.ext_iff]
  have hdep : ∃ x : Fin (k + 1 + 1) → Bool, H (Function.update x p (!x p)) ≠ H x := by
    refine ⟨mk false true w, ?_⟩
    rw [hHval, hHval, up_p, up_q, up_r, mk_p, mk_q, mk_r, hw]; simp
  have hnc' : ∃ x x' : Fin (k + 1 + 1) → Bool,
      H (Function.update x p true) ≠ H (Function.update x' p true) := by
    refine ⟨mk false true w, mk false false w, ?_⟩
    rw [hHval, hHval, up_p, up_p, up_q, up_q, up_r, up_r, mk_q, mk_q, mk_r, mk_r, hw]; simp
  have h1 := PEqualNP.MetaComplexity.Helpers.Forest.one_gate_at (k + 1) H p true (s + 1) hdep hnc' hH
  let π : Fin (k + 1 + 1) → Fin (k + 1) :=
    fun i => if hi : 2 ≤ i.val then ⟨i.val - 2, by omega⟩ else Fin.last k
  have h2 := relabel_size π _ (s + 1) h1
  have e : (fun x : Fin (k + 1) → Bool => H (Function.update (x ∘ π) p true))
      = fun x : Fin (k + 1) → Bool => x (Fin.last k) || g (fun i : Fin k => x i.castSucc) := by
    funext x
    rw [hHval, up_p, up_q, up_r]
    have hq' : (x ∘ π) q = x (Fin.last k) := by simp [π, hq]
    have hr' : (fun j => (x ∘ π) (r j)) = fun i : Fin k => x i.castSucc := by
      funext j; simp only [Function.comp, π, hr]
      rw [dif_pos (by omega)]; congr 1; ext; simp
    rw [hq', hr']; simp
  rw [e] at h2
  exact pad_down k s g ⟨y, y', hyy⟩ h2

theorem rigid_and (k s : ℕ) (g : (Fin k → Bool) → Bool) (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    HasCircuitSize (2 + k) (andOr k g) (s + 2) ↔ HasCircuitSize k g s :=
  ⟨rigid_down k s g hnc, rigid_up k s g hnc⟩

end PEqualNP.MetaComplexity.Helpers.RigidAnd
