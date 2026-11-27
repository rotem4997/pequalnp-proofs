import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1747

open PEqualNP.CircuitLowerBounds

def enc : List Bool → ℕ
  | [] => 0
  | b :: t => Nat.bit b (enc t)

theorem enc_testBit (w : List Bool) (i : ℕ) : (enc w).testBit i = w.getD i false := by
  induction w generalizing i with
  | nil => simp [enc]
  | cons b t ih =>
    cases i with
    | zero => simp [enc]
    | succ i => simp [enc, Nat.testBit_bit_succ, ih]

def run : List Gate → ℕ → ℕ → ℕ
  | [], _, W => W
  | g :: gs, k, W =>
    run gs (k + 1) (W ||| (bif g.op.eval (g.inputs.map fun i => W.testBit i) then 2 ^ k else 0))

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (w.getD i false || (b && decide (w.length = i))) := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne']
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨d, rfl⟩ : ∃ d, i = w.length + (d + 1) := ⟨i - w.length - 1, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem run_rep (gs : List Gate) (w : List Bool) (W : ℕ)
    (h : ∀ i, W.testBit i = w.getD i false) (i : ℕ) :
    (run gs w.length W).testBit i =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs generalizing w W i with
  | nil => simpa [run] using h i
  | cons g gs ih =>
    have hv : (g.inputs.map fun i => W.testBit i) = (g.inputs.map fun i => w.getD i false) := by
      congr 1
      funext j
      exact h j
    have hrep : ∀ j, (W ||| (bif g.op.eval (g.inputs.map fun i => w.getD i false) then 2 ^ w.length
        else 0)).testBit j
        = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD j false := by
      intro j
      rw [getD_snoc, Nat.testBit_lor, h j]
      cases g.op.eval (g.inputs.map fun i => w.getD i false) <;> simp [Nat.testBit_two_pow]
    have key := ih _ _ hrep i
    simp only [List.length_append, List.length_singleton] at key
    simp only [run, List.foldl_cons, hv]
    exact key

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run C.gates x.length (enc x)).testBit C.output := by
  unfold Circuit.eval Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) C.output).symm

theorem eval26 (G : List Gate) (o : ℕ) (x : List Bool) (hx : x.length = 26) :
    Circuit.eval ⟨G, o⟩ x = (run G 26 (enc x)).testBit o := by
  rw [eval_eq, hx]

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem isAO_iff (o : GateOp) (h : isAO o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp [isAO] at h ⊢

theorem ao2_of (gs : List Gate)
    (h : gs.all (fun g => isAO g.op && decide (g.inputs.length = 2)) = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  rw [Bool.and_eq_true] at h1
  exact ⟨isAO_iff _ h1.1, of_decide_eq_true h1.2⟩

def nl (u l : Fin 13) : Bool :=
  !(decide (u - l = 0) || decide (u - l = 1) || decide (u - l = 3) || decide (u - l = 9))

def row (a b c d : Fin 13) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u = a) || decide (u = b) || decide (u = c) || decide (u = d)) ++
    List.ofFn (fun v : Fin 13 => nl a v && nl b v && nl c v && nl d v)

theorem row_len (a b c d : Fin 13) : (row a b c d).length = 26 := by
  simp [row]

theorem row_eq (a b c d : Fin 13) :
    (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ ({a, b, c, d} : Finset (Fin 13))))
      ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ ({a, b, c, d} : Finset (Fin 13)),
        r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = row a b c d := by
  have e1 : (fun u2 : Fin 13 => decide (u2 ∈ ({a, b, c, d} : Finset (Fin 13)))) =
      (fun u : Fin 13 => decide (u = a) || decide (u = b) || decide (u = c) || decide (u = d)) := by
    funext u
    rw [Bool.eq_iff_iff]
    simp
    tauto
  have e2 : (fun v2 : Fin 13 => decide (∀ r ∈ ({a, b, c, d} : Finset (Fin 13)),
      r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) =
      (fun v : Fin 13 => nl a v && nl b v && nl c v && nl d v) := by
    funext v
    rw [Bool.eq_iff_iff]
    simp [nl]
    tauto
  unfold row
  rw [e1, e2]

theorem min_split (Q : Finset (Fin 13)) (n : ℕ) (h : Q.card = n + 1) :
    ∃ a t, Q = insert a t ∧ t.card = n ∧ ∀ x ∈ t, a < x := by
  have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨Q.min' hne, Q.erase (Q.min' hne), ?_, ?_, ?_⟩
  · exact (Finset.insert_erase (Finset.min'_mem Q hne)).symm
  · rw [Finset.card_erase_of_mem (Finset.min'_mem Q hne), h]
    rfl
  · intro x hx
    exact lt_of_le_of_ne (Finset.min'_le Q x (Finset.mem_of_mem_erase hx))
      (Finset.ne_of_mem_erase hx).symm

theorem neg_of (G : List Gate) (o : ℕ)
    (h : ∀ a b : Fin 13, a < b → ∀ c : Fin 13, b < c → ∀ d : Fin 13, c < d →
      (run G 26 (enc (row a b c d))).testBit o = false) :
    ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      Circuit.eval ⟨G, o⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
        ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q,
          r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false := by
  intro Q hQ _
  obtain ⟨a, t1, rfl, h1, ha⟩ := min_split Q 3 hQ
  obtain ⟨b, t2, rfl, h2, hb⟩ := min_split t1 2 h1
  obtain ⟨c, t3, rfl, h3, hc⟩ := min_split t2 1 h2
  obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp h3
  rw [row_eq, eval26 G o _ (row_len a b c d)]
  exact h a b (ha b (by simp)) c (hb c (by simp)) d (hc d (by simp))

theorem fin13 (P : Fin 13 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

end PEqualNP.Outside.L_meta_1747

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1747 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 23 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)))
       = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ)))) ∧
  (∀ Q : Finset (Fin 13), Q.card = 4 →
     (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
     C.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
             ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · refine PEqualNP.Outside.L_meta_1747.ao2_of _ ?_
    decide +kernel
  · intro p l h
    refine (PEqualNP.Outside.L_meta_1747.eval_eq _ _).trans ?_
    revert p l
    decide +kernel
  · refine PEqualNP.Outside.L_meta_1747.neg_of _ _ ?_
    refine PEqualNP.Outside.L_meta_1747.fin13 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
