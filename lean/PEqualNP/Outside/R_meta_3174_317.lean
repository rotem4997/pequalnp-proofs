import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The relabelling proof follows the parent reduction R_meta_2762_612.
-- Reflection fixing vertex zero leaves three mixed pairs up to order.
theorem PEqualNP.Outside.R_meta_3174_317
    (pair12 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, x 1 || x 2]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (pair13 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, x 1 || x 3]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (pair18 : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, x 1 || x 8]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro ops hlen allowed mixed C hf hs
  obtain ⟨a, b, rfl⟩ : ∃ a b, ops = [a,b] := by
    cases ops with
    | nil => simp at hlen
    | cons a t =>
      cases t with
      | nil => simp at hlen
      | cons b t =>
        cases t with
        | nil => exact ⟨_, _, rfl⟩
        | cons => simp at hlen
  have ha := allowed a (by simp)
  have hb := allowed b (by simp)
  let A : Fin 9 := ⟨a, by omega⟩
  let B : Fin 9 := ⟨b, by omega⟩
  let f := fun (x : Fin 9 → Bool) =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let w := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0, x A || x B]
  have read (x : Fin 9 → Bool) (extra : List Bool) (i : Fin 9) :
      (List.ofFn x ++ extra).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  by_contra! agree
  have correct (x : Fin 9 → Bool) : C.eval (w x) = f x := by
    have e := Classical.not_not.mp (agree x)
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [((List.ofFn x ++ [!x 0]).getD A.val false || ((List.ofFn x ++ [!x 0]).getD B.val false || false))]) = _ at e
    simpa only [w, read, Bool.or_false, List.append_assoc, List.cons_append, List.nil_append] using e
  let move := fun (r : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map r)
  let relabel := fun (r : ℕ → ℕ) => Circuit.mk (C.gates.map (move r)) (r C.output)
  have fan (r : ℕ → ℕ) : FanInTwo (relabel r) := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hf t ht).1, by simpa [move] using (hf t ht).2⟩
  have transport (r : ℕ → ℕ) (low : ∀ i < 11, r i < 11) (high : ∀ i, 11 ≤ i → r i = i)
      (u v : List Bool) (hu : u.length = 11) (hv : v.length = 11)
      (h : ∀ i, v.getD (r i) false = u.getD i false) : (relabel r).eval v = C.eval u := by
    let step := fun (t : List Bool) (g : Gate) => t ++ [g.op.eval (g.inputs.map fun j => t.getD j false)]
    have loop (gs : List Gate) (u v : List Bool) (heq : v.length = u.length) (large : 11 ≤ u.length)
        (inv : ∀ i, v.getD (r i) false = u.getD i false) (i : ℕ) :
        ((gs.map (move r)).foldl step v).getD (r i) false = (gs.foldl step u).getD i false := by
      induction gs generalizing u v with
      | nil => exact inv i
      | cons g gs ih =>
        change ((gs.map (move r)).foldl step (step v (move r g))).getD (r i) false =
          (gs.foldl step (step u g)).getD i false
        have ins : ((move r g).inputs.map fun j => v.getD j false) = (g.inputs.map fun j => u.getD j false) := by
          simp only [move, List.map_map, Function.comp_def, inv]
        apply ih _ _ (by simp [step, heq]) (by simp [step]; omega)
        intro j
        by_cases jl : j < u.length
        · have rj : r j < v.length := by
            by_cases hh : j < 11
            · have hh' := low j hh
              omega
            · rw [high j (by omega), heq]
              exact jl
          exact (List.getD_append _ _ _ _ rj).trans ((inv j).trans (List.getD_append _ _ _ _ jl).symm)
        · rw [high j (by omega)]
          simp only [step, move, List.getD, List.getElem?_append, heq, ite_eq_right jl]
          change ([g.op.eval ((move r g).inputs.map fun j => v.getD j false)][j-u.length]?).getD false = _
          rw [ins]
          rfl
    exact loop C.gates u v (hv.trans hu.symm) hu.ge h C.output
  let perm := fun (s : Bool) (i : Fin 9) => if s then (![0,5,8,3,4,1,7,6,2] : Fin 9 → Fin 9) i else i
  let V := ([1,2,3,5,8] : List (Fin 9))
  let codes := ([12,13,18] : List ℕ)
  have reps : ∀ a ∈ V, ∀ b ∈ V, (¬∀ i ∈ [a,b], i = 1 ∨ i = 5) → (¬∀ i ∈ [a,b], i = 2 ∨ i = 3 ∨ i = 8) →
      ∃ k ∈ codes, ∃ s : Bool,
        ((perm s a, perm s b) = (Fin.ofNat 9 (k / 10), Fin.ofNat 9 (k % 10)) ∨
         (perm s b, perm s a) = (Fin.ofNat 9 (k / 10), Fin.ofNat 9 (k % 10))) := by
    decide +kernel
  have aV : A ∈ V := by simpa [V, A, Fin.ext_iff] using ha
  have bV : B ∈ V := by simpa [V, B, Fin.ext_iff] using hb
  have m1 : ¬∀ i ∈ [A,B], i = 1 ∨ i = 5 := by
    intro h
    apply mixed.1
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simpa [A, Fin.ext_iff] using h A (by simp)
    · simpa [B, Fin.ext_iff] using h B (by simp)
  have m2 : ¬∀ i ∈ [A,B], i = 2 ∨ i = 3 ∨ i = 8 := by
    intro h
    apply mixed.2
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simpa [A, Fin.ext_iff] using h A (by simp)
    · simpa [B, Fin.ext_iff] using h B (by simp)
  obtain ⟨k, hk, s, hab⟩ := reps A aV B bV m1 m2
  let r := fun i : ℕ => if h : i < 9 then (perm s ⟨i,h⟩).val else i
  have fixes : perm s 0 = 0 := by cases s <;> decide
  have symm : ∀ s : Bool, ∀ x : Fin 9 → Bool, f (x ∘ perm s) = f x := by decide +kernel
  have sz : (relabel r).size ≤ 13 := by
    change (C.gates.map (move r)).length ≤ 13
    rw [List.length_map]
    exact hs
  have fixed : ∃ x : Fin 9 → Bool, (relabel r).eval
      (List.ofFn x ++ [!x 0, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]) ≠ f x := by
    simp only [codes, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact pair12 (relabel r) (fan r) sz
    · exact pair13 (relabel r) (fan r) sz
    · exact pair18 (relabel r) (fan r) sz
  obtain ⟨x, hx⟩ := fixed
  let y := x ∘ perm s
  let v := List.ofFn x ++ [!x 0, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]
  have hor : (y A || y B) = (x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))) := by
    rcases hab with h | h
    · cases Prod.mk.inj h with | intro h1 h2 => simp [y, Function.comp_def, h1, h2]
    · cases Prod.mk.inj h with | intro h1 h2 => simp [y, Function.comp_def, h1, h2, Bool.or_comm]
  have tr := transport r (by
    intro i hi
    by_cases h : i < 9
    · simpa [r,h] using (show (perm s ⟨i,h⟩).val < 11 by have := (perm s ⟨i,h⟩).isLt; omega)
    · simpa [r,h] using hi)
    (by intro i hi; simp [r, show ¬i < 9 by omega]) (w y) v (by simp [w]) (by simp [v]) (by
    intro i
    by_cases h : i < 9
    · rw [show r i = (perm s ⟨i,h⟩).val by simp [r,h]]
      exact (read x _ (perm s ⟨i,h⟩)).trans (read y _ ⟨i,h⟩).symm
    · simp only [v, w, r, dite_eq_right h, List.getD, List.getElem?_append, List.length_ofFn, ite_eq_right h, hor, show y 0 = x 0 by simp [y, fixes]])
  exact hx (tr.trans ((correct y).trans (symm s x)))
