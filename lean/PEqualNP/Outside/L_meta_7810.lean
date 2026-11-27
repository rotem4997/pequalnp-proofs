import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7810

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

def Inv (n : ℕ) {ι : Type} (xs : ι → List Bool) (C : Circuit) (S : Finset ℕ) : Prop :=
  ∀ j ∈ S, j < C.gates.length ∧
    ((∃ p, ((p < n + j ∧ (p < n ∨ p - n ∉ S)) ∨ n + C.gates.length ≤ p) ∧
        ∀ a, (C.wires (xs a)).getD (n + j) false = (C.wires (xs a)).getD p false) ∨
     (C.output ≠ n + j ∧ ∀ k, k ∉ S → ∀ g, C.gates[k]? = some g → n + j ∉ g.inputs))

def Stp (n : ℕ) {ι : Type} (xs : ι → List Bool) (C D : Circuit) : Prop :=
  ∃ m p, m < C.size ∧ (p < n + m ∨ n + C.size ≤ p) ∧ D = eraseGate n C m p ∧
    ((∀ a, (C.wires (xs a)).getD (n + m) false = (C.wires (xs a)).getD p false) ∨
     (C.output ≠ n + m ∧ ∀ g ∈ List.drop (m + 1) C.gates, n + m ∉ g.inputs))

theorem pres (n : ℕ) {ι : Type} (xs : ι → List Bool) (hxs : ∀ a, (xs a).length = n)
    (C : Circuit) (S : Finset ℕ) (m p : ℕ) (hm : m < C.gates.length)
    (hmax : ∀ j ∈ S, j ≤ m) (hp : ∀ j ∈ S, j ≠ m → p ≠ n + j) (H : Inv n xs C S) :
    Inv n xs (eraseGate n C m p) (S.erase m) := by
  intro j hj
  have hjS := Finset.mem_of_mem_erase hj
  have hjne := Finset.ne_of_mem_erase hj
  have hjm : j < m := by have := hmax j hjS; omega
  have hlen := len_erase n C m p hm
  obtain ⟨_, H2⟩ := H j hjS
  refine ⟨by omega, ?_⟩
  rcases H2 with ⟨q, hq, he⟩ | ⟨ho, hr⟩
  · left
    refine ⟨q, ?_, ?_⟩
    · rcases hq with ⟨h1, h2⟩ | h2
      · refine Or.inl ⟨h1, ?_⟩
        rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (fun h => h2 (Finset.mem_of_mem_erase h))
      · exact Or.inr (by omega)
    · intro a
      rw [pref n C m p hm _ (hxs a) _ (by omega), he a]
      rcases hq with ⟨h1, _⟩ | h2
      · rw [pref n C m p hm _ (hxs a) _ (by omega)]
      · rw [getD_big _ _ (by rw [wires_eq, fold_len, hxs a]; omega),
          getD_big _ _ (by rw [wires_eq, fold_len, hxs a]; omega)]
  · right
    have hred : ∀ i, eraseRedirect n m p i = n + j → i = n + j := by
      intro i hi
      unfold eraseRedirect at hi
      split_ifs at hi
      · exact absurd hi (hp j hjS hjne)
      · omega
      · exact hi
    refine ⟨?_, ?_⟩
    · rw [out_erase n C m p hm]
      intro h; exact ho (hred _ h)
    · intro k hk g hg
      rw [gates_erase n C m p hm, List.getElem?_append] at hg
      by_cases hkm : k < m
      · rw [if_pos (by rw [List.length_take]; omega), List.getElem?_take, if_pos hkm] at hg
        refine hr k (fun h => hk (Finset.mem_erase.2 ⟨by omega, h⟩)) g hg
      · rw [if_neg (by rw [List.length_take]; omega), List.getElem?_map, List.getElem?_drop] at hg
        rw [List.length_take, Nat.min_eq_left (by omega)] at hg
        rcases hg' : C.gates[m + 1 + (k - m)]? with _ | g'
        · rw [hg'] at hg; simp at hg
        · rw [hg'] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          subst hg
          simp only [List.mem_map, not_exists, not_and]
          intro i hi hie
          have := hred i hie
          subst this
          exact hr (m + 1 + (k - m)) (fun h => by have := hmax _ h; omega) g' hg' hi

theorem multi (n : ℕ) {ι : Type} (xs : ι → List Bool) (hxs : ∀ a, (xs a).length = n) :
    ∀ (k : ℕ) (C : Circuit) (S : Finset ℕ), S.card = k → Inv n xs C S →
    ∃ f : ℕ → Circuit, f 0 = C ∧ ∀ t < k, Stp n xs (f t) (f (t + 1)) := by
  intro k
  induction k with
  | zero => intro C S _ _; exact ⟨fun _ => C, rfl, fun t ht => absurd ht (by omega)⟩
  | succ k ih =>
    intro C S hS H
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    have hmS := S.max'_mem hne
    have hmax : ∀ j ∈ S, j ≤ S.max' hne := fun j hj => S.le_max' j hj
    generalize S.max' hne = m at hmS hmax
    obtain ⟨hm, H2⟩ := H m hmS
    have hcard : (S.erase m).card = k := by
      rw [Finset.card_erase_of_mem hmS]; omega
    have fin : ∀ p, Inv n xs (eraseGate n C m p) (S.erase m) →
        Stp n xs C (eraseGate n C m p) →
        ∃ f : ℕ → Circuit, f 0 = C ∧ ∀ t < k + 1, Stp n xs (f t) (f (t + 1)) := by
      intro p hI hSt
      obtain ⟨f, hf0, hf⟩ := ih _ _ hcard hI
      refine ⟨fun t => if t = 0 then C else f (t - 1), rfl, ?_⟩
      intro t ht
      rcases t with _ | t
      · simp only [if_true, Nat.zero_add, if_neg (Nat.one_ne_zero), Nat.sub_self, hf0]
        exact hSt
      · simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
        exact hf t (by omega)
    rcases H2 with ⟨p, hp, he⟩ | ⟨ho, hr⟩
    · apply fin p
      · apply pres n xs hxs C S m p hm hmax _ H
        intro j hjS hjne
        have := hmax j hjS
        rcases hp with ⟨h1, h2 | h2⟩ | h2
        · omega
        · intro h; apply h2; rw [h]; simpa using hjS
        · omega
      · refine ⟨m, p, hm, ?_, rfl, Or.inl he⟩
        rcases hp with ⟨h1, _⟩ | h2
        · exact Or.inl h1
        · exact Or.inr h2
    · apply fin (n + C.gates.length)
      · apply pres n xs hxs C S m _ hm hmax _ H
        intro j hjS hjne
        have := hmax j hjS
        omega
      · refine ⟨m, _, hm, Or.inr (le_refl _), rfl, Or.inr ⟨ho, ?_⟩⟩
        intro g hg
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
        rw [List.getElem?_drop] at hi
        exact hr _ (fun h => by have := hmax _ h; omega) g hi

end PEqualNP.Outside.L_meta_7810

open PEqualNP.Outside.L_meta_7810 PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves in
theorem PEqualNP.Outside.L_meta_7810 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),   (∀ x6 ∈ x5, x6 < x4.size) →     (∀ x7 ∈ x5,         (∃ (x9 : ℕ),             (x9 < x1 + x7 ∧ (x9 < x1 ∨ x9 - x1 ∉ x5) ∨ x1 + x4.size ≤ x9) ∧               ∀ (x10 : Fin x1 → Bool),                 have x11 : List Bool := x4.wires (List.ofFn (Function.update (Function.update x10 x2 Bool.false) x3 Bool.false));                 x11.getD (x1 + x7) Bool.false = x11.getD x9 Bool.false) ∨           x4.output ≠ x1 + x7 ∧ PEqualNP.MetaComplexity.NestedCover.readsIn x4 (Finset.range x4.size \ x5) (x1 + x7) = (0 : ℕ)) →       ∃ (x8 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),         x8 (0 : ℕ) = x4 ∧           ∀ x9 < x5.card,             ∃ (x11 : ℕ) (x12 : ℕ),               x11 < (x8 x9).size ∧                 (x12 < x1 + x11 ∨ x1 + (x8 x9).size ≤ x12) ∧                   x8 (x9 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x8 x9) x11 x12 ∧                     ((∀ (x13 : Fin x1 → Bool),                         have x14 : List Bool := (x8 x9).wires (List.ofFn (Function.update (Function.update x13 x2 Bool.false) x3 Bool.false));                         x14.getD (x1 + x11) Bool.false = x14.getD x12 Bool.false) ∨                       (x8 x9).output ≠ x1 + x11 ∧ ∀ x13 ∈ List.drop (x11 + (1 : ℕ)) (x8 x9).gates, x1 + x11 ∉ x13.inputs) := by
  intro n i1 i2 C S hlt H
  have hI : Inv n (fun f : Fin n → Bool =>
      List.ofFn (Function.update (Function.update f i1 Bool.false) i2 Bool.false)) C S := by
    intro j hj
    refine ⟨hlt j hj, ?_⟩
    rcases H j hj with ⟨p, hp, he⟩ | ⟨ho, hr⟩
    · exact Or.inl ⟨p, hp, he⟩
    · refine Or.inr ⟨ho, ?_⟩
      intro k hk g hg
      unfold PEqualNP.MetaComplexity.NestedCover.readsIn at hr
      rw [Finset.sum_eq_zero_iff] at hr
      have hkl : k < C.gates.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hg
        exact absurd hg (by simp)
      have := hr k (Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hkl, hk⟩)
      rw [List.count_eq_zero] at this
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, hg]; rfl
      rw [e] at this
      exact this
  obtain ⟨f, hf0, hf⟩ := multi n _ (by intro a; simp) S.card C S rfl hI
  refine ⟨f, hf0, ?_⟩
  intro t ht
  obtain ⟨m, p, h1, h2, h3, h4⟩ := hf t ht
  exact ⟨m, p, h1, h2, h3, h4⟩
