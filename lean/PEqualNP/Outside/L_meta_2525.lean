import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2525

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne (L : List Bool) (S : Bool) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j false = L.getD j false := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len (L : List Bool) (S : Bool) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k false = S := by
  subst h; simp

theorem getD_ofFn {m : ℕ} (f : Fin m → Bool) (j : Fin m) :
    (List.ofFn f).getD j.val false = f j := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ofFn' (f : Fin 9 → Bool) (j : Fin 9) : (List.ofFn f).getD j.val false = f j :=
  getD_ofFn f j

-- Two runs that agree off wire v still agree off wire v when no gate reads v.
theorem agree_off (v : ℕ) (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length →
    (∀ i, i ≠ v → w.getD i false = w'.getD i false) → (∀ g ∈ gs, v ∉ g.inputs) →
    ∀ i, i ≠ v → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ h _; exact h
  | cons g gs ih =>
    intro w w' hl h hr
    have hg : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (fun e => hr g List.mem_cons_self (e ▸ ha))
    refine ih (w ++ [_]) (w' ++ [_]) (by simp [hl]) ?_
      (fun g' hg' => hr g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    rw [hg]
    by_cases hil : i = w.length
    · rw [getD_snoc_len _ _ _ hil.symm, getD_snoc_len _ _ _ (hl.symm.trans hil.symm)]
    · rw [getD_snoc_ne _ _ _ hil, getD_snoc_ne _ _ _ (by omega), h i hi]

def F9 (x : Fin 9 → Bool) : Bool :=
  [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
    (5, 7), (6, 8), (8, 5)].any fun e => x e.1 && x e.2

def pt (l : List (Fin 9)) : Fin 9 → Bool := fun i => decide (i ∈ l)

theorem reads (C : Circuit)
    (hw : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4))
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = F9 x) (v u : Fin 9)
    (hv : (pt [v] 0 || pt [v] 4) = true) (hvu : (pt [v, u] 0 || pt [v, u] 4) = true)
    (hu : (pt [u] 0 || pt [u] 4) = true)
    (hT : F9 (pt [v, u]) = true) (hF : F9 (pt [u]) = false) (hs : F9 (pt [v]) = false) :
    ∃ g ∈ List.drop 1 C.gates, v.val ∈ g.inputs := by
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil =>
    exfalso
    have h := hw (pt [v])
    rw [hv] at h
    have e : (Circuit.wires ⟨[], out⟩ (List.ofFn (pt [v]))).getD 9 false = false :=
      List.getD_eq_default _ _ (by simp [Circuit.wires])
    rw [e] at h; exact absurd h (by decide)
  | cons g rest =>
    by_contra hno
    have hnone : ∀ g' ∈ rest, v.val ∉ g'.inputs := fun g' hg' hm => hno ⟨g', hg', hm⟩
    have hw' : ∀ x : Fin 9 → Bool,
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
      intro x
      rw [← hw x]
      show _ = (wiresFrom rest (List.ofFn x ++ [_])).getD 9 false
      rw [getD_wiresFrom _ _ _ (by simp)]
      exact (getD_snoc_len _ _ 9 (by simp)).symm
    have hgo : out ≠ v.val := by
      intro h
      have e := he (pt [v])
      rw [hs] at e
      have e2 : (wiresFrom (g :: rest) (List.ofFn (pt [v]))).getD out false = false := e
      rw [h, getD_wiresFrom _ _ _ (by simp), getD_ofFn'] at e2
      simp [pt] at e2
    have key := agree_off v.val rest (List.ofFn (pt [v, u]) ++ [true])
      (List.ofFn (pt [u]) ++ [true]) (by simp)
      (by
        intro i hi
        by_cases h9 : i = 9
        · rw [h9, getD_snoc_len _ _ 9 (by simp), getD_snoc_len _ _ 9 (by simp)]
        · rw [getD_snoc_ne _ _ _ (by simpa using h9), getD_snoc_ne _ _ _ (by simpa using h9)]
          by_cases h8 : i < 9
          · have a1 := getD_ofFn' (pt [v, u]) ⟨i, h8⟩
            have a2 := getD_ofFn' (pt [u]) ⟨i, h8⟩
            rw [show i = (⟨i, h8⟩ : Fin 9).val from rfl, a1, a2]
            have hne : (⟨i, h8⟩ : Fin 9) ≠ v := fun e => hi (congrArg Fin.val e)
            simp [pt, hne]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      hnone out hgo
    have r1 : (wiresFrom (g :: rest) (List.ofFn (pt [v, u]))).getD out false
        = F9 (pt [v, u]) := he _
    have r2 : (wiresFrom (g :: rest) (List.ofFn (pt [u]))).getD out false
        = F9 (pt [u]) := he _
    have s1 : wiresFrom (g :: rest) (List.ofFn (pt [v, u]))
        = wiresFrom rest (List.ofFn (pt [v, u]) ++ [true]) := by
      show wiresFrom rest (_ ++ [_]) = _
      rw [hw', hvu]
    have s2 : wiresFrom (g :: rest) (List.ofFn (pt [u]))
        = wiresFrom rest (List.ofFn (pt [u]) ++ [true]) := by
      show wiresFrom rest (_ ++ [_]) = _
      rw [hw', hu]
    rw [s1, hT] at r1
    rw [s2, hF] at r2
    rw [r1, r2] at key
    exact absurd key (by decide)

theorem both (C : Circuit)
    (hw : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4))
    (he : circuitFun 9 C = F9) :
    (∃ g ∈ List.drop 1 C.gates, 0 ∈ g.inputs) ∧ ∃ g ∈ List.drop 1 C.gates, 4 ∈ g.inputs :=
  ⟨reads C hw (fun x => congrFun he x) 0 4 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    reads C hw (fun x => congrFun he x) 4 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

end PEqualNP.Outside.L_meta_2525

theorem PEqualNP.Outside.L_meta_2525 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → (∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x5.inputs) ∧ ∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x5.inputs := by
  exact PEqualNP.Outside.L_meta_2525.both
