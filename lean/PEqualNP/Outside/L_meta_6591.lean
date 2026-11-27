import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6591

open PEqualNP.CircuitLowerBounds

theorem foldSet (gs : List Gate) : ∀ (w : List Bool) (p : ℕ) (v : Bool), p < w.length →
    (∀ g ∈ gs, p ∉ g.inputs) →
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.set p v)
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).set p v := by
  induction gs with
  | nil => intro w p v _ _; rfl
  | cons g gs ih =>
    intro w p v hp hg
    simp only [List.foldl_cons]
    have h1 : (g.inputs.map fun i => (w.set p v).getD i false)
        = (g.inputs.map fun i => w.getD i false) := by
      apply List.map_congr_left
      intro i hi
      have hne : p ≠ i := fun h => hg g List.mem_cons_self (h ▸ hi)
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
    rw [h1, ← List.set_append_left p v hp]
    exact ih _ p v (by simp; omega) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem foldPrefix (gs : List Gate) : ∀ (w : List Bool) (p : ℕ), p < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)[p]?
      = w[p]? := by
  induction gs with
  | nil => intro w p _; rfl
  | cons g gs ih =>
    intro w p hp
    simp only [List.foldl_cons]
    rw [ih _ p (by simp; omega)]
    exact List.getElem?_append_left hp

def E (x2 : Fin 42) (x7 : Fin 42 → Bool) : Fin 43 → Bool :=
  fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x7 0 || x7 x2) x7 x8

def L (x2 : Fin 42) (x3 x4 : Fin 43) (x7 : Fin 42 → Bool) : List Bool :=
  List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) =>
    Fin.lastCases (E x2 x7 x3 || E x2 x7 x4) (E x2 x7) x9

def adjP (u v : Fin 42) : Prop :=
  (u : ℕ) < (21 : ℕ) ∧ (21 : ℕ) ≤ (v : ℕ) ∧
    ((v : ℕ) + (21 : ℕ) - (u : ℕ)) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]

def P (x1 : Fin 42 → Bool) : Prop :=
  ∃ (x2 : Fin 42) (x3 : Fin 42), adjP x2 x3 ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true

theorem ofFnE (x2 : Fin 42) (x7 : Fin 42 → Bool) :
    List.ofFn (E x2 x7) = List.ofFn x7 ++ [x7 0 || x7 x2] := by
  unfold E
  rw [List.ofFn_succ_last]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

theorem L_eq (x2 : Fin 42) (x3 x4 : Fin 43) (x7 : Fin 42 → Bool) :
    L x2 x3 x4 x7 = (List.ofFn x7 ++ [x7 0 || x7 x2]) ++ [E x2 x7 x3 || E x2 x7 x4] := by
  unfold L
  rw [List.ofFn_succ_last]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [ofFnE]

theorem L_len (x2 : Fin 42) (x3 x4 : Fin 43) (x7 : Fin 42 → Bool) :
    (L x2 x3 x4 x7).length = 44 := by
  simp [L]

theorem L_get (x2 : Fin 42) (x3 x4 : Fin 43) (x7 : Fin 42 → Bool) (a : Fin 42) :
    (L x2 x3 x4 x7)[(a : ℕ)]? = some (x7 a) := by
  have ha := a.isLt
  rw [L_eq, List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp)]
  rw [List.getElem?_ofFn, dif_pos ha]

theorem ofFn_set (a : Fin 42) (S : Fin 42 → Bool) :
    List.ofFn (fun i => decide (i = a) || S i) = (List.ofFn S).set a true := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_ofFn]
  by_cases h : (a : ℕ) = i
  · subst h
    simp
  · have hne : (⟨i, by simpa using h1⟩ : Fin 42) ≠ a := by
      intro e
      apply h
      rw [← e]
    simp [h, hne]

theorem L_set (x2 a : Fin 42) (x3 x4 : Fin 43) (S S' : Fin 42 → Bool)
    (hofn : List.ofFn S' = (List.ofFn S).set a true)
    (t1 : (S' 0 || S' x2) = (S 0 || S x2))
    (t2 : (E x2 S' x3 || E x2 S' x4) = (E x2 S x3 || E x2 S x4)) :
    L x2 x3 x4 S' = (L x2 x3 x4 S).set a true := by
  rw [L_eq, L_eq, hofn, t1, t2]
  simp only [List.append_assoc]
  rw [List.set_append_left (s := List.ofFn S) (a : ℕ) true (by simp)]

theorem tails (x2 a : Fin 42) (x3 x4 : Fin 43) (h34 : x3 < x4)
    (hc : List.count (a : ℕ) [(0 : ℕ), (x2 : ℕ), (x3 : ℕ), (x4 : ℕ)] = 1) :
    ∃ b : Fin 42, (b : ℕ) ≠ (a : ℕ) ∧ ∀ S S' : Fin 42 → Bool,
      (∀ i : Fin 42, (i : ℕ) ≠ (a : ℕ) → S' i = S i) → S b = true → S' b = true →
      (S' 0 || S' x2) = (S 0 || S x2) ∧
      (E x2 S' x3 || E x2 S' x4) = (E x2 S x3 || E x2 S x4) := by
  have ha := a.isLt
  rcases Fin.eq_castSucc_or_eq_last x3 with ⟨j3, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last x4 with ⟨j4, rfl⟩ | rfl
    · have h34' : (j3 : ℕ) < (j4 : ℕ) := h34
      simp only [E, Fin.lastCases_castSucc]
      simp only [List.count_cons, List.count_nil, beq_iff_eq, Fin.val_castSucc, zero_add] at hc
      split_ifs at hc
      any_goals omega
      · refine ⟨j3, by omega, fun S S' hS hb hb' => ?_⟩
        simp [hb, hb', hS 0 (show (0 : ℕ) ≠ (a : ℕ) by omega), hS x2 (by omega)]
      · refine ⟨j4, by omega, fun S S' hS hb hb' => ?_⟩
        simp [hb, hb', hS 0 (show (0 : ℕ) ≠ (a : ℕ) by omega), hS x2 (by omega)]
      · refine ⟨0, (show (0 : ℕ) ≠ (a : ℕ) by omega), fun S S' hS hb hb' => ?_⟩
        simp [hb, hb', hS j3 (by omega), hS j4 (by omega)]
      · refine ⟨x2, by omega, fun S S' hS hb hb' => ?_⟩
        simp [hb, hb', hS j3 (by omega), hS j4 (by omega)]
    · simp only [E, Fin.lastCases_castSucc, Fin.lastCases_last]
      simp only [List.count_cons, List.count_nil, beq_iff_eq, Fin.val_castSucc, Fin.val_last,
        zero_add] at hc
      split_ifs at hc
      any_goals omega
      · exact ⟨0, (show (0 : ℕ) ≠ (a : ℕ) by omega), fun S S' hS hb hb' => by simp [hb, hb']⟩
      · exact ⟨0, (show (0 : ℕ) ≠ (a : ℕ) by omega), fun S S' hS hb hb' => by simp [hb, hb']⟩
      · exact ⟨x2, by omega, fun S S' hS hb hb' => by simp [hb, hb']⟩
  · exact absurd h34 (not_lt.mpr (Fin.le_last _))

def adjN (u v : ℕ) : Bool :=
  Nat.blt u 21 && Nat.ble 21 v && [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)].contains ((v + 21 - u) % 21)

def chk : Bool :=
  (List.range 42).all fun a => (List.range 42).all fun b =>
    Nat.beq a b || (List.range 42).any fun c =>
      (adjN a c || adjN c a) && !(adjN b c) && !(adjN c b)

theorem chk_true : chk = true := by decide +kernel

theorem adjN_iff (u v : Fin 42) : adjN (u : ℕ) (v : ℕ) = true ↔ adjP u v := by
  simp [adjN, adjP, and_assoc]

theorem G (a b : Fin 42) (hab : a ≠ b) :
    ∃ c : Fin 42, (adjP a c ∨ adjP c a) ∧ ¬ adjP b c ∧ ¬ adjP c b := by
  have h := chk_true
  unfold chk at h
  rw [List.all_eq_true] at h
  have h1 := h a (List.mem_range.mpr a.isLt)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.mpr b.isLt)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true h2)) hab
  · rw [List.any_eq_true] at h2
    obtain ⟨c, hc, hcc⟩ := h2
    have hc' := List.mem_range.mp hc
    refine ⟨⟨c, hc'⟩, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hcc
    obtain ⟨⟨h3, h4⟩, h5⟩ := hcc
    refine ⟨?_, ?_, ?_⟩
    · rcases h3 with h3 | h3
      · exact Or.inl ((adjN_iff a ⟨c, hc'⟩).mp h3)
      · exact Or.inr ((adjN_iff ⟨c, hc'⟩ a).mp h3)
    · intro hh
      have := (adjN_iff b ⟨c, hc'⟩).mpr hh
      simp_all
    · intro hh
      have := (adjN_iff ⟨c, hc'⟩ b).mpr hh
      simp_all

theorem core (x2 : Fin 42) (x3 x4 : Fin 43) (x5 : Circuit) (h34 : x3 < x4)
    (h : ∀ x7 : Fin 42 → Bool, x5.eval (L x2 x3 x4 x7) = true ↔ P x7) (a : Fin 42)
    (hc : List.count (a : ℕ) [(0 : ℕ), (x2 : ℕ), (x3 : ℕ), (x4 : ℕ)] = 1) :
    ∃ g ∈ x5.gates, (a : ℕ) ∈ g.inputs := by
  by_contra hcon
  have hno : ∀ g ∈ x5.gates, (a : ℕ) ∉ g.inputs := fun g hg hin => hcon ⟨g, hg, hin⟩
  have ha := a.isLt
  by_cases hout : x5.output = (a : ℕ)
  · have hev : x5.eval (L x2 x3 x4 fun i => decide (i = a)) = true := by
      unfold Circuit.eval Circuit.wires
      rw [hout, List.getD_eq_getElem?_getD, foldPrefix _ _ _ (by rw [L_len]; omega), L_get]
      simp
    obtain ⟨u, v, huv, h1, h2⟩ := (h _).mp hev
    simp only [decide_eq_true_eq] at h1 h2
    subst h1
    subst h2
    obtain ⟨p, q, _⟩ := huv
    omega
  · obtain ⟨b, hba, htail⟩ := tails x2 a x3 x4 h34 hc
    have hab : a ≠ b := fun e => hba (by rw [e])
    obtain ⟨c, hac, hbc⟩ := G a b hab
    have hca : c ≠ a := by
      rintro rfl
      rcases hac with ⟨p, q, _⟩ | ⟨p, q, _⟩ <;> omega
    have ht := htail (fun i => decide (i = b) || decide (i = c))
      (fun i => decide (i = a) || (decide (i = b) || decide (i = c)))
      (fun i hi => by
        have : i ≠ a := fun e => hi (by rw [e])
        simp [this])
      (by simp) (by simp)
    have hset := L_set x2 a x3 x4 (fun i => decide (i = b) || decide (i = c))
      (fun i => decide (i = a) || (decide (i = b) || decide (i = c)))
      (ofFn_set a _) ht.1 ht.2
    have hP' : P (fun i => decide (i = a) || (decide (i = b) || decide (i = c))) := by
      rcases hac with hh | hh
      · exact ⟨a, c, hh, by simp, by simp⟩
      · exact ⟨c, a, hh, by simp, by simp⟩
    have hPn : ¬ P (fun i => decide (i = b) || decide (i = c)) := by
      rintro ⟨u, v, huv, h1, h2⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> first
        | exact hbc.1 huv
        | exact hbc.2 huv
        | (obtain ⟨p, q, _⟩ := huv; omega)
    have e1 := (h _).mpr hP'
    apply hPn
    apply (h _).mp
    rw [← e1, hset]
    unfold Circuit.eval Circuit.wires
    rw [foldSet _ _ _ _ (by rw [L_len]; omega) hno]
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (fun e => hout e.symm)]

end PEqualNP.Outside.L_meta_6591

theorem PEqualNP.Outside.L_meta_6591 : have x1 : (Fin (42 : ℕ) → Bool) → Prop := fun (x1 : Fin (42 : ℕ) → Bool) => ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (42 : ℕ)), (↑x2 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3 ∧ (↑x3 + (21 : ℕ) - ↑x2) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∀ (x2 : Fin (42 : ℕ)) (x3 x4 : Fin (43 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x3 < x4 →     (∀ (x7 : Fin (42 : ℕ) → Bool),         have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x2) x7 x8;         x5.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x3 || x8 x4) x8 x9) = Bool.true ↔ x1 x7) →       ∀ (x8 : Fin (42 : ℕ)), List.count ↑x8 [(0 : ℕ), ↑x2, ↑x3, ↑x4] = (1 : ℕ) → ∃ x10 ∈ x5.gates, ↑x8 ∈ x10.inputs := by
  intro x1 x2 x3 x4 x5 h34 h x8 hc
  exact PEqualNP.Outside.L_meta_6591.core x2 x3 x4 x5 h34 h x8 hc
