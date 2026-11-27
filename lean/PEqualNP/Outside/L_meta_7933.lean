import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7933

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



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7933

theorem PEqualNP.Outside.L_meta_7933 : have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ)); have x3 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x3 x4 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x3 x4 x5; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) => Decidable.decide (x5 = x4); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 → (∀ (x7 x8 : Fin (13 : ℕ)), x2 x7 x8 → x5.eval (x3 (x4 x7) (x4 x8)) = Bool.true) → (∀ (x8 : Fin (13 : ℕ) → Bool), (∀ (x9 : Fin (13 : ℕ)), x8 x9 = Bool.false → ∃ (x11 : Fin (13 : ℕ)), x2 x9 x11 ∧ x1 x8 x11 = Bool.false) → x5.eval (x3 x8 fun (x10 : Fin (13 : ℕ)) => !x1 x8 x10) = Bool.false) → ∀ (x9 x10 : Fin (13 : ℕ) → Bool), x5.eval (x3 x9 x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)), x10 x11 = Bool.true ∧ x1 x9 x11 = Bool.true := by
  intro N I inp e C hC hpos hneg x y
  have gD : ∀ (f : Fin 26 → Bool) (i : ℕ) (hi : i < 26), (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
    intro f i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have hmono : ∀ a b a' b' : Fin 13 → Bool, (∀ p, a p = true → a' p = true) → (∀ p, b p = true → b' p = true) → C.eval (inp a b) = true → C.eval (inp a' b') = true := by
    intro a b a' b' ha hb h
    refine PEqualNP.Outside.L_meta_7933.mono C.gates (inp a b) (inp a' b') (by simp [inp]) (fun i hi => ?_) hC.1 C.output h
    by_cases hin : i < 26
    · have e1 := gD (fun x5 : Fin (13 + 13) => Fin.addCases a b x5) i hin
      have e2 := gD (fun x5 : Fin (13 + 13) => Fin.addCases a' b' x5) i hin
      have hi' : (Fin.addCases (motive := fun _ => Bool) a b (⟨i, hin⟩ : Fin (13 + 13))) = true := e1.symm.trans hi
      refine e2.trans ?_
      revert hi'
      refine Fin.addCases (m := 13) (n := 13) (motive := fun k => Fin.addCases (motive := fun _ => Bool) a b k = true → Fin.addCases (motive := fun _ => Bool) a' b' k = true) (fun p => ?_) (fun p => ?_) (⟨i, hin⟩ : Fin (13 + 13))
      · simp only [Fin.addCases_left]; exact ha p
      · simp only [Fin.addCases_right]; exact hb p
    · rw [List.getD_eq_default _ _ (by simp [inp]; omega)] at hi; cases hi
  have hNI : ∀ (a : Fin 13 → Bool) (l : Fin 13), N a l = true ↔ ∃ p, I p l ∧ a p = true := by
    intro a l
    simp only [N, I, Bool.or_eq_true]
    constructor
    · rintro (((h | h) | h) | h)
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr (Or.inl rfl), h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), h⟩
    · rintro ⟨p, rfl | rfl | rfl | rfl, h⟩
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    classical
    let z : Fin 13 → Bool := fun p => decide (∀ l, y l = true → ¬I p l)
    have hxz : ∀ p, x p = true → z p = true := by
      intro p hp
      simp only [z, decide_eq_true_eq]
      intro l hl hI
      exact hcon l hl ((hNI x l).2 ⟨p, hI, hp⟩)
    have hyz : ∀ l, y l = true → (!N z l) = true := by
      intro l hl
      rw [Bool.not_eq_true']
      by_contra hN
      obtain ⟨p, hI, hp⟩ := (hNI z l).1 (by simpa using hN)
      simp only [z, decide_eq_true_eq] at hp
      exact hp l hl hI
    have h1 := hneg z (by
      intro p hp
      simp only [z, decide_eq_false_iff_not, not_forall, not_not] at hp
      obtain ⟨l, hl, hI⟩ := hp
      exact ⟨l, hI, by have := hyz l hl; simpa using this⟩)
    have h2 := hmono x y z (fun l => !N z l) hxz hyz h
    rw [h1] at h2; cases h2
  · rintro ⟨l, hl, hN⟩
    obtain ⟨p, hI, hp⟩ := (hNI x l).1 hN
    refine hmono (e p) (e l) x y ?_ ?_ (hpos p l hI)
    · intro q hq
      simp only [e, decide_eq_true_eq] at hq
      rw [hq]; exact hp
    · intro q hq
      simp only [e, decide_eq_true_eq] at hq
      rw [hq]; exact hl
