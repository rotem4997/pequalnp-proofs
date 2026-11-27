import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2986
open PEqualNP.CircuitLowerBounds

section
open PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem dsn_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dsn_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [dsn_eq] at hj
      rw [h1, dsn_eq, h2, dsn_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [dsn_ne _ _ _ _ hjl] at hj
      rw [dsn_ne _ _ _ _ (by omega), dsn_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [dsn_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [dsn_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact dsn_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega
end

end PEqualNP.Outside.L_meta_2986

open PEqualNP.Outside.L_meta_2986 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2986 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (x2 + x2) x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → (2 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  intro q N I _ C hq hN hl hu hC _ htrue hfalse
  have hne : ∀ a b : Fin N, Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    omega
  have hinj : ∀ a b : Fin N, Fin.natAdd N a = Fin.natAdd N b → a = b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    exact Fin.ext this
  have hsize : PEqualNP.MetaComplexity.HasCircuitSize (N + N)
      (PEqualNP.MetaComplexity.circuitFun (N + N) C) C.size := by
    refine ⟨C, ?_, le_refl _, fun x => rfl⟩
    intro g hg
    refine ⟨?_, (hC g hg).2⟩
    rcases (hC g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hN1 : 1 < N := by nlinarith
  have hdep : ∀ i : Fin (N + N), ∃ x : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Function.update x i (!x i))
        ≠ PEqualNP.MetaComplexity.circuitFun (N + N) C x := by
    intro i
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · obtain ⟨p', hp'⟩ : ∃ p' : Fin N, p ≠ p' := by
        by_cases h0 : p = ⟨0, by omega⟩
        · exact ⟨⟨1, hN1⟩, by rw [h0]; simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, by omega⟩, h0⟩
      obtain ⟨l, ⟨hl1, _⟩, _⟩ := hu p p' hp'
      refine ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l), ?_⟩
      rw [htrue p l hl1]
      have A : ∀ p0 : Fin N, Function.update (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) (Fin.castAdd N p) (!decide (Fin.castAdd N p = Fin.castAdd N p ∨ Fin.castAdd N p = Fin.natAdd N l)) (Fin.castAdd N p0) = false := by
        intro p0
        by_cases h : Fin.castAdd N p0 = Fin.castAdd N p
        · rw [h, Function.update_self]; simp
        · rw [Function.update_of_ne h]
          refine decide_eq_false ?_
          rintro (h' | h')
          · exact h h'
          · exact hne p0 l h'
      have B : ∀ a : Fin N, Function.update (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) (Fin.castAdd N p) (!decide (Fin.castAdd N p = Fin.castAdd N p ∨ Fin.castAdd N p = Fin.natAdd N l)) (Fin.natAdd N a) = true → a = l := by
        intro a h
        rw [Function.update_of_ne (Ne.symm (hne p a))] at h
        simp only [decide_eq_true_eq] at h
        rcases h with h | h
        · exact absurd h.symm (hne p a)
        · exact hinj a l h
      have := hfalse _ (le_trans (Fintype.card_le_one_iff_subsingleton.mpr
          ⟨fun a b => Subtype.ext ((B a.1 a.2).trans (B b.1 b.2).symm)⟩) (by omega)) (by
        rintro ⟨p0, l0, _, h1, _⟩
        rw [A p0] at h1
        exact absurd h1 (by simp))
      rw [this]
      simp
    · have hpos : 0 < Fintype.card { x9 : Fin N // I x9 l } := by rw [hl l]; omega
      obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
      refine ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l), ?_⟩
      rw [htrue p l hp]
      have A : ∀ a : Fin N, Function.update (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) (Fin.natAdd N l) (!decide (Fin.natAdd N l = Fin.castAdd N p ∨ Fin.natAdd N l = Fin.natAdd N l)) (Fin.natAdd N a) = false := by
        intro a
        by_cases h : Fin.natAdd N a = Fin.natAdd N l
        · rw [h, Function.update_self]; simp
        · rw [Function.update_of_ne h]
          refine decide_eq_false ?_
          rintro (h' | h')
          · exact hne p a h'.symm
          · exact h h'
      refine ne_of_eq_of_ne (hfalse _ ?_ ?_) (by simp)
      · exact le_trans (Fintype.card_le_one_iff_subsingleton.mpr
          ⟨fun a b => absurd a.2 (by rw [A a.1]; simp)⟩) (by omega)
      · rintro ⟨p0, l0, _, _, h2⟩
        rw [A l0] at h2
        exact absurd h2 (by simp)
  have hd := dep_lower (N + N) _ hdep C.size hsize
  omega
