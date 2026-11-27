import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_735

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def reindex (phi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map phi }

private lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases lt : i < w.length
  · simp [List.getD, List.getElem?_append_left lt, Nat.ne_of_lt lt]
  · rw [List.getD, List.getElem?_append_right (by omega)]
    by_cases eq : i = w.length
    · simp [eq]
    · have a : w.length ≤ i := by omega
      have b : [b].length ≤ i - w.length := by simp; omega
      simp [eq, List.getD, List.getElem?_eq_none a, List.getElem?_eq_none b]

private lemma fold_preserves (phi : ℕ → ℕ) (n n' m : ℕ)
    (pin : ∀ t : ℕ, t < m → ∀ i : ℕ, phi i = n' + t ↔ i = n + t)
    (gs : List Gate) (t : ℕ) (w w' : List Bool)
    (ht : t + gs.length ≤ m) (hw : w.length = n + t) (hw' : w'.length = n' + t)
    (same : ∀ i, w'.getD (phi i) false = w.getD i false) :
    ∀ i, ((gs.map (reindex phi)).foldl extend w').getD (phi i) false =
      (gs.foldl extend w).getD i false := by
  induction gs generalizing t w w' with
  | nil => exact same
  | cons g rest ih =>
    have htm : t < m := by simp at ht; omega
    have hin :
        (g.inputs.map phi).map (fun j => w'.getD j false) =
          g.inputs.map (fun j => w.getD j false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => same i)
    apply ih (t + 1) (extend w g) (extend w' (reindex phi g))
    · simp at ht
      omega
    · simp [extend, hw]; omega
    · simp [extend, hw']; omega
    · intro i
      simp only [extend, reindex, getD_snoc, hw, hw', hin, pin t htm i, same i]

end PEqualNP.Outside.L_meta_735

theorem PEqualNP.Outside.L_meta_735 : ∀ (n n' : ℕ) (Z : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ Z ↔ ∃ j : Fin n', e j = k) → n' + Z.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ phi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ Z, x.getD (k : ℕ) false = false) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := 0 } x').getD (phi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := gates.map (fun g => { op := g.op, inputs := g.inputs.map phi }), output := phi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  classical
  open PEqualNP.Outside.L_meta_735 in
  open PEqualNP.CircuitLowerBounds in
  intro n n' Z e _ image _ gates
  let m := gates.length
  let onInput (i : ℕ) := ∃ j : Fin n', (e j).val = i
  let phi (i : ℕ) : ℕ :=
    if h : onInput i then h.choose.val
    else if n ≤ i ∧ i < n + m then n' + (i - n) else n' + m
  have pin (t : ℕ) (ht : t < m) (i : ℕ) : phi i = n' + t ↔ i = n + t := by
    unfold phi
    split
    next he =>
      have hj := he.choose.isLt
      have hi : i < n := he.choose_spec ▸ (e he.choose).isLt
      omega
    next _ =>
      split
      next hi => omega
      next hn =>
        constructor
        · omega
        · intro h
          exact (hn (by omega)).elim
  refine ⟨phi, ?_⟩
  intro x x' hx hx' hZ he
  have base (i : ℕ) : x'.getD (phi i) false = x.getD i false := by
    by_cases himage : onInput i
    · rw [show phi i = himage.choose.val by exact dite_eq_left himage]
      simpa only [himage.choose_spec] using (he himage.choose).symm
    · have hphi : n' ≤ phi i := by
        rw [show phi i = _ by exact dite_eq_right himage]
        split <;> omega
      have miss : x'.getD (phi i) false = false := by
        simp [List.getD, List.getElem?_eq_none (hx'.symm ▸ hphi)]
      rw [miss]
      by_cases iold : i < n
      · let k : Fin n := ⟨i, iold⟩
        have hk : k ∈ Z := by
          by_contra hn
          obtain ⟨j, hj⟩ := (image k).mp hn
          exact himage ⟨j, congrArg Fin.val hj⟩
        exact (hZ k hk).symm
      · symm
        simp [List.getD, List.getElem?_eq_none (show x.length ≤ i by omega)]
  have output := fold_preserves phi n n' m pin gates 0 x x'
    (by simp [m]) (by simpa using hx) (by simpa using hx') base
  constructor
  · exact output
  · intro o
    exact output o
