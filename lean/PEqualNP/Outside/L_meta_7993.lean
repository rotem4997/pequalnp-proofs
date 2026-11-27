import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7993

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem gates_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
  simp only [eraseGate, if_pos hm]

theorem out_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  simp only [eraseGate, if_pos hm]

theorem len_erase (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length + 1 = C.gates.length := by
  rw [gates_erase n C m p hm]
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem pref (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i < n + m) :
    ((eraseGate n C m p).wires x).getD i false = (C.wires x).getD i false := by
  have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
    rw [fold_len, hx, List.length_take]; omega
  have key : C.gates.foldl step x = (C.gates.drop m).foldl step
      ((C.gates.take m).foldl step x) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [wires_eq, wires_eq, gates_erase n C m p hm, List.foldl_append,
    fold_stab _ (List.foldl step x (List.take m C.gates)) _ (by omega), key,
    fold_stab _ (List.foldl step x (List.take m C.gates)) _ (by omega)]


def F (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (k : ℕ) : Circuit :=
  Nat.rec (motive := fun _ => Circuit) C (fun k D => eraseGate n D (f k) (g k)) k

theorem F_succ (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (k : ℕ) :
    F n C f g (k + 1) = eraseGate n (F n C f g k) (f k) (g k) := rfl

def Unr (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (j : ℕ) : Prop :=
  C.output ≠ n + f j ∧ (∀ t < j, g t ≠ n + f j) ∧
    ∀ (q : ℕ) (G : Gate), f j < q → C.gates[q]? = some G → n + f j ∈ G.inputs →
      ∃ t < j, f t = q

def Inv (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (M k : ℕ) : Prop :=
  ∀ j, k ≤ j → j < M → f j < (F n C f g k).gates.length ∧
    (∀ x : List Bool, x.length = n → ∀ i ≤ n + f j,
      ((F n C f g k).wires x).getD i false = (C.wires x).getD i false) ∧
    (Unr n C f g j → (F n C f g k).output ≠ n + f j ∧
      ∀ (q : ℕ) (G : Gate), f j < q → (F n C f g k).gates[q]? = some G →
        n + f j ∈ G.inputs → ∃ t, k ≤ t ∧ t < j ∧ f t = q)

theorem inv_zero (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (M : ℕ)
    (hlt : ∀ j < M, f j < C.gates.length) : Inv n C f g M 0 := by
  intro j _ hj
  refine ⟨hlt j hj, fun x _ i _ => rfl, ?_⟩
  intro hU
  refine ⟨hU.1, ?_⟩
  intro q G hq hg hin
  obtain ⟨t, ht, he⟩ := hU.2.2 q G hq hg hin
  exact ⟨t, Nat.zero_le _, ht, he⟩

theorem inv_succ (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (M k : ℕ)
    (hdec : ∀ j < M, ∀ t < j, f j < f t) (hkM : k < M)
    (I : Inv n C f g M k) : Inv n C f g M (k + 1) := by
  intro j hkj hjM
  obtain ⟨hmk, _, _⟩ := I k le_rfl hkM
  obtain ⟨h1, h2, h3⟩ := I j (by omega) hjM
  have hfj : f j < f k := hdec j hjM k (by omega)
  have hlen := len_erase n (F n C f g k) (f k) (g k) hmk
  rw [F_succ]
  refine ⟨by omega, ?_, ?_⟩
  · intro x hx i hi
    rw [pref n _ (f k) (g k) hmk x hx i (by omega)]
    exact h2 x hx i hi
  · intro hU
    obtain ⟨ho, hr⟩ := h3 hU
    have hp : g k ≠ n + f j := hU.2.1 k (by omega)
    have hred : ∀ i, eraseRedirect n (f k) (g k) i = n + f j → i = n + f j := by
      intro i hi
      unfold eraseRedirect at hi
      split_ifs at hi
      · exact absurd hi hp
      · omega
      · exact hi
    refine ⟨?_, ?_⟩
    · rw [out_erase n _ (f k) (g k) hmk]
      intro h; exact ho (hred _ h)
    · intro q G hq hg hin
      rw [gates_erase n _ (f k) (g k) hmk, List.getElem?_append] at hg
      by_cases hqm : q < f k
      · rw [if_pos (by rw [List.length_take]; omega), List.getElem?_take, if_pos hqm] at hg
        obtain ⟨t, ht1, ht2, ht3⟩ := hr q G hq hg hin
        refine ⟨t, ?_, ht2, ht3⟩
        by_contra hc
        have : t = k := by omega
        subst this
        omega
      · rw [if_neg (by rw [List.length_take]; omega), List.getElem?_map, List.getElem?_drop] at hg
        rw [List.length_take, Nat.min_eq_left (by omega)] at hg
        rcases hg' : (F n C f g k).gates[f k + 1 + (q - f k)]? with _ | G'
        · rw [hg'] at hg; simp at hg
        · rw [hg'] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          subst hg
          simp only [List.mem_map] at hin
          obtain ⟨i, hi, hie⟩ := hin
          have := hred i hie
          subst this
          obtain ⟨t, ht1, ht2, ht3⟩ := hr _ G' (by omega) hg' hi
          exfalso
          by_cases htk : t = k
          · subst htk; omega
          · have := hdec t (by omega) k (by omega)
            omega

theorem inv_all (n : ℕ) (C : Circuit) (f g : ℕ → ℕ) (M : ℕ)
    (hlt : ∀ j < M, f j < C.gates.length)
    (hdec : ∀ j < M, ∀ t < j, f j < f t) : ∀ k ≤ M, Inv n C f g M k := by
  intro k
  induction k with
  | zero => intro _; exact inv_zero n C f g M hlt
  | succ k ih => intro hk; exact inv_succ n C f g M k hdec (by omega) (ih (by omega))

end PEqualNP.Outside.L_meta_7993

open PEqualNP.Outside.L_meta_7993 PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves in
theorem PEqualNP.Outside.L_meta_7993 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Set (Fin x1 → Bool)) (x5 x6 : ℕ → ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ) =>     ∀ x9 ∈ x4,       have x11 : List Bool := x7.wires (List.ofFn x9);       x11.getD (x1 + x5 x8) Bool.false = x11.getD (x6 x8) Bool.false;   (∀ x8 < x2, x5 x8 < x3.size ∧ x6 x8 < x1 + x5 x8 ∧ (∀ x10 < x8, x5 x8 < x5 x10) ∧ (x7 x3 x8 ∨ x3.output ≠ x1 + x5 x8 ∧ (∀ x10 < x8, x6 x10 ≠ x1 + x5 x8) ∧ ∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x5 x8 < x10 → x3.gates[x10]? = Option.some x11 → x1 + x5 x8 ∈ x11.inputs → ∃ x15 < x8, x5 x15 = x10)) → ∃ (x9 : ℕ → PEqualNP.CircuitLowerBounds.Circuit), x9 (0 : ℕ) = x3 ∧ ∀ x10 < x2, x5 x10 < (x9 x10).size ∧ x9 (x10 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x9 x10) (x5 x10) (x6 x10) ∧ (x7 (x9 x10) x10 ∨ (x9 x10).output ≠ x1 + x5 x10 ∧ ∀ x12 ∈ List.drop (x5 x10 + (1 : ℕ)) (x9 x10).gates, x1 + x5 x10 ∉ x12.inputs) := by
  intro n M C X f g
  intro P H
  have hlt : ∀ j < M, f j < C.gates.length := fun j hj => (H j hj).1
  have hdec : ∀ j < M, ∀ t < j, f j < f t := fun j hj => (H j hj).2.2.1
  refine ⟨F n C f g, rfl, ?_⟩
  intro j hj
  obtain ⟨h1, h2, h3⟩ := inv_all n C f g M hlt hdec j (le_of_lt hj) j le_rfl hj
  refine ⟨h1, rfl, ?_⟩
  have hg : g j < n + f j := (H j hj).2.1
  rcases (H j hj).2.2.2 with hE | hU
  · left
    intro a ha
    have e := hE a ha
    dsimp only at e ⊢
    rw [h2 _ (by simp) _ le_rfl, h2 _ (by simp) _ (by omega)]
    exact e
  · right
    have hU' : Unr n C f g j := hU
    refine ⟨(h3 hU').1, ?_⟩
    intro G hG hin
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hG
    rw [List.getElem?_drop] at hi
    obtain ⟨t, ht1, ht2, _⟩ := (h3 hU').2 _ G (by omega) hi hin
    omega
