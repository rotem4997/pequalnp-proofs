import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2274

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def AO (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def sval (a : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr i => a.getD i false

def lk (m : List (Bool ⊕ ℕ)) (k : ℕ) : Bool ⊕ ℕ := m.getD k (Sum.inl false)

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem bne {b : Bool} (h : ¬ b = false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem bnt {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

theorem gd_snoc {α : Type} (l : List α) (s d : α) (k : ℕ) :
    (l ++ [s]).getD k d = if k < l.length then l.getD k d else if k = l.length then s else d := by
  by_cases h1 : k < l.length
  · rw [ifp h1]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · rw [ifn h1]
    by_cases h2 : k = l.length
    · rw [ifp h2]
      subst h2
      simp [List.getD_eq_getElem?_getD]
    · rw [ifn h2, List.getD_eq_default]
      rw [List.length_append, List.length_singleton]
      omega

theorem sval_app (a w : List Bool) (s : Bool ⊕ ℕ) (hs : ∀ i, s = Sum.inr i → i < a.length) :
    sval (a ++ w) s = sval a s := by
  cases s with
  | inl c => rfl
  | inr i =>
    have h := hs i rfl
    show (a ++ w).getD i false = a.getD i false
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem and_abs (a : List Bool) : ∀ syms : List (Bool ⊕ ℕ), Sum.inl false ∈ syms →
    (syms.map (sval a)).all id = false
  | [], h => by simp at h
  | s :: t, h => by
      rcases List.mem_cons.1 h with h' | h'
      · subst h'
        rfl
      · rw [List.map_cons, List.all_cons, and_abs a t h', Bool.and_false]

theorem or_abs (a : List Bool) : ∀ syms : List (Bool ⊕ ℕ), Sum.inl true ∈ syms →
    (syms.map (sval a)).any id = true
  | [], h => by simp at h
  | s :: t, h => by
      rcases List.mem_cons.1 h with h' | h'
      · subst h'
        rfl
      · rw [List.map_cons, List.any_cons, or_abs a t h', Bool.or_true]

theorem and_red (a : List Bool) : ∀ syms : List (Bool ⊕ ℕ), Sum.inl false ∉ syms →
    (syms.map (sval a)).all id =
      ((syms.filterMap Sum.getRight?).map (fun i => a.getD i false)).all id
  | [], _ => rfl
  | Sum.inl c :: t, h => by
      have ht : Sum.inl false ∉ t := fun h' => h (List.mem_cons_of_mem _ h')
      have hc : c = true := by
        cases c
        · exact absurd List.mem_cons_self h
        · rfl
      subst hc
      rw [List.map_cons, List.all_cons, and_red a t ht]
      rfl
  | Sum.inr i :: t, h => by
      have ht : Sum.inl false ∉ t := fun h' => h (List.mem_cons_of_mem _ h')
      rw [List.map_cons, List.all_cons, and_red a t ht]
      rfl

theorem or_red (a : List Bool) : ∀ syms : List (Bool ⊕ ℕ), Sum.inl true ∉ syms →
    (syms.map (sval a)).any id =
      ((syms.filterMap Sum.getRight?).map (fun i => a.getD i false)).any id
  | [], _ => rfl
  | Sum.inl c :: t, h => by
      have ht : Sum.inl true ∉ t := fun h' => h (List.mem_cons_of_mem _ h')
      have hc : c = false := by
        cases c
        · rfl
        · exact absurd List.mem_cons_self h
      subst hc
      rw [List.map_cons, List.any_cons, or_red a t ht]
      rfl
  | Sum.inr i :: t, h => by
      have ht : Sum.inl true ∉ t := fun h' => h (List.mem_cons_of_mem _ h')
      rw [List.map_cons, List.any_cons, or_red a t ht]
      rfl

theorem fm_mem (syms : List (Bool ⊕ ℕ)) (i : ℕ) (h : i ∈ syms.filterMap Sum.getRight?) :
    Sum.inr i ∈ syms := by
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.1 h
  cases s with
  | inl c => simp at he
  | inr j =>
    simp at he
    subst he
    exact hs

theorem fm_lt (c : Bool) : ∀ syms : List (Bool ⊕ ℕ), Sum.inl c ∈ syms →
    (syms.filterMap Sum.getRight?).length < syms.length
  | [], h => by simp at h
  | s :: t, h => by
      have hle := List.length_filterMap_le (Sum.getRight? (α := Bool) (β := ℕ)) t
      rcases List.mem_cons.1 h with h' | h'
      · subst h'
        simp only [List.filterMap_cons, Sum.getRight?_inl, List.length_cons]
        omega
      · have := fm_lt c t h'
        cases s with
        | inl d =>
          simp only [List.filterMap_cons, Sum.getRight?_inl, List.length_cons]
          omega
        | inr j =>
          simp only [List.filterMap_cons, Sum.getRight?_inr, List.length_cons]
          omega

theorem step_ex (g : Gate) (hg : AO g) (m : List (Bool ⊕ ℕ)) (L : ℕ)
    (hb : ∀ k i, lk m k = Sum.inr i → i < L) (z : ℕ) :
    (∃ s : Bool ⊕ ℕ, (∀ i, s = Sum.inr i → i < L) ∧ ∀ a b : List Bool,
        (∀ k, sval a (lk m k) = b.getD k false) →
        sval a s = g.op.eval (g.inputs.map fun i => b.getD i false)) ∨
    (∃ l : List ℕ, l.length ≤ 2 ∧ (∀ i ∈ l, i < L) ∧ (lk m z = Sum.inl false → z ∉ g.inputs) ∧
      ∀ a b : List Bool, (∀ k, sval a (lk m k) = b.getD k false) →
        g.op.eval (l.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  obtain ⟨hop, hlen⟩ := hg
  have key : ∀ a b : List Bool, (∀ k, sval a (lk m k) = b.getD k false) →
      (g.inputs.map fun i => b.getD i false) = (g.inputs.map (lk m)).map (sval a) := by
    intro a b h
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => (h i).symm)
  have hslen : (g.inputs.map (lk m)).length ≤ 2 := by
    rw [List.length_map]
    exact hlen
  have hbr : ∀ i ∈ (g.inputs.map (lk m)).filterMap Sum.getRight?, i < L := by
    intro i hi
    obtain ⟨k, _, hk⟩ := List.mem_map.1 (fm_mem _ _ hi)
    exact hb k i hk
  have hfl := List.length_filterMap_le (Sum.getRight? (α := Bool) (β := ℕ)) (g.inputs.map (lk m))
  rcases hop with hop | hop
  · by_cases h0 : Sum.inl false ∈ g.inputs.map (lk m)
    · left
      refine ⟨Sum.inl false, fun i h => (by cases h), fun a b h => ?_⟩
      rw [key a b h, hop]
      exact (and_abs a _ h0).symm
    · have red : ∀ a b : List Bool, (∀ k, sval a (lk m k) = b.getD k false) →
          g.op.eval (g.inputs.map fun i => b.getD i false) =
          (((g.inputs.map (lk m)).filterMap Sum.getRight?).map fun i => a.getD i false).all id := by
        intro a b h
        rw [key a b h, hop]
        exact and_red a _ h0
      rcases hr : (g.inputs.map (lk m)).filterMap Sum.getRight? with _ | ⟨i, _ | ⟨j, t⟩⟩
      · left
        refine ⟨Sum.inl true, fun i h => (by cases h), fun a b h => ?_⟩
        rw [red a b h, hr]
        rfl
      · left
        refine ⟨Sum.inr i, fun i' h => ?_, fun a b h => ?_⟩
        · cases h
          exact hbr i (by rw [hr]; exact List.mem_cons_self)
        · rw [red a b h, hr]
          show a.getD i false = (a.getD i false && true)
          rw [Bool.and_true]
      · right
        refine ⟨i :: j :: t, ?_, ?_, ?_, fun a b h => ?_⟩
        · rw [← hr]
          omega
        · rw [← hr]
          exact hbr
        · intro hz hzin
          exact h0 (List.mem_map.2 ⟨z, hzin, hz⟩)
        · rw [red a b h, hr, hop]
          rfl
  · by_cases h1 : Sum.inl true ∈ g.inputs.map (lk m)
    · left
      refine ⟨Sum.inl true, fun i h => (by cases h), fun a b h => ?_⟩
      rw [key a b h, hop]
      exact (or_abs a _ h1).symm
    · have red : ∀ a b : List Bool, (∀ k, sval a (lk m k) = b.getD k false) →
          g.op.eval (g.inputs.map fun i => b.getD i false) =
          (((g.inputs.map (lk m)).filterMap Sum.getRight?).map fun i => a.getD i false).any id := by
        intro a b h
        rw [key a b h, hop]
        exact or_red a _ h1
      rcases hr : (g.inputs.map (lk m)).filterMap Sum.getRight? with _ | ⟨i, _ | ⟨j, t⟩⟩
      · left
        refine ⟨Sum.inl false, fun i h => (by cases h), fun a b h => ?_⟩
        rw [red a b h, hr]
        rfl
      · left
        refine ⟨Sum.inr i, fun i' h => ?_, fun a b h => ?_⟩
        · cases h
          exact hbr i (by rw [hr]; exact List.mem_cons_self)
        · rw [red a b h, hr]
          show a.getD i false = (a.getD i false || false)
          rw [Bool.or_false]
      · right
        refine ⟨i :: j :: t, ?_, ?_, ?_, fun a b h => ?_⟩
        · rw [← hr]
          omega
        · rw [← hr]
          exact hbr
        · intro hz hzin
          have hmem : Sum.inl false ∈ g.inputs.map (lk m) := List.mem_map.2 ⟨z, hzin, hz⟩
          have hlt := fm_lt false _ hmem
          rw [hr] at hlt
          simp only [List.length_cons] at hlt
          omega
        · rw [red a b h, hr, hop]
          rfl

theorem sim (z : ℕ) : ∀ (gs : List Gate) (m : List (Bool ⊕ ℕ)) (L : ℕ),
    (∀ g ∈ gs, AO g) → (∀ k i, lk m k = Sum.inr i → i < L) →
    ∃ (ng : List Gate) (m' : List (Bool ⊕ ℕ)), (∀ g ∈ ng, AO g) ∧ ng.length ≤ gs.length ∧
      (z < m.length → lk m z = Sum.inl false → ∀ g ∈ gs, z ∈ g.inputs →
        ng.length + 1 ≤ gs.length) ∧
      ∀ (a b : List Bool), a.length = L → b.length = m.length →
        (∀ k, sval a (lk m k) = b.getD k false) →
        ∀ o, sval (ng.foldl stp a) (lk m' o) = (gs.foldl stp b).getD o false := by
  intro gs
  induction gs with
  | nil =>
    intro m L _ _
    exact ⟨[], m, fun g h => by simp at h, le_refl _, fun _ _ g h => by simp at h,
      fun a b _ _ h o => h o⟩
  | cons g gs ih =>
    intro m L hAO hb
    have hg := hAO g List.mem_cons_self
    have hAO' : ∀ g' ∈ gs, AO g' := fun g' h => hAO g' (List.mem_cons_of_mem _ h)
    rcases step_ex g hg m L hb z with ⟨s, hs, hval⟩ | ⟨l, hl2, hlL, hz, hval⟩
    · have hb' : ∀ k i, lk (m ++ [s]) k = Sum.inr i → i < L := by
        intro k i h
        unfold lk at h
        rw [gd_snoc] at h
        by_cases h1 : k < m.length
        · rw [ifp h1] at h
          exact hb k i h
        · rw [ifn h1] at h
          by_cases h2 : k = m.length
          · rw [ifp h2] at h
            exact hs i h
          · rw [ifn h2] at h
            cases h
      obtain ⟨ng, m', h1, h2, h3, h4⟩ := ih (m ++ [s]) L hAO' hb'
      refine ⟨ng, m', h1, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro _ _ g0 _ _
        simp only [List.length_cons]
        omega
      · intro a b ha hbl hinv o
        have hinv' : ∀ k, sval a (lk (m ++ [s]) k) = (stp b g).getD k false := by
          intro k
          unfold lk stp
          rw [gd_snoc, gd_snoc, hbl]
          by_cases c1 : k < m.length
          · rw [ifp c1, ifp c1]
            exact hinv k
          · rw [ifn c1, ifn c1]
            by_cases c2 : k = m.length
            · rw [ifp c2, ifp c2]
              exact hval a b hinv
            · rw [ifn c2, ifn c2]; rfl
        exact h4 a (stp b g) ha (by simp [stp, hbl]) hinv' o
    · have hb' : ∀ k i, lk (m ++ [Sum.inr L]) k = Sum.inr i → i < L + 1 := by
        intro k i h
        unfold lk at h
        rw [gd_snoc] at h
        by_cases h1 : k < m.length
        · rw [ifp h1] at h
          exact Nat.lt_succ_of_lt (hb k i h)
        · rw [ifn h1] at h
          by_cases h2 : k = m.length
          · rw [ifp h2] at h
            cases h
            exact Nat.lt_succ_self _
          · rw [ifn h2] at h
            cases h
      obtain ⟨ng, m', h1, h2, h3, h4⟩ := ih (m ++ [Sum.inr L]) (L + 1) hAO' hb'
      refine ⟨⟨g.op, l⟩ :: ng, m', ?_, ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_cons.1 hg' with h' | h'
        · subst h'
          exact ⟨hg.1, hl2⟩
        · exact h1 g' h'
      · simp only [List.length_cons]
        omega
      · intro hzm hzf g0 hg0 hzg
        rcases List.mem_cons.1 hg0 with h' | h'
        · subst h'
          exact absurd hzg (hz hzf)
        · have hzf' : lk (m ++ [Sum.inr L]) z = Sum.inl false := by
            unfold lk
            rw [gd_snoc, ifp hzm]
            exact hzf
          have hzm' : z < (m ++ [Sum.inr L]).length := by
            rw [List.length_append]
            omega
          have := h3 hzm' hzf' g0 h' hzg
          simp only [List.length_cons]
          omega
      · intro a b ha hbl hinv o
        have hinv' : ∀ k, sval (stp a ⟨g.op, l⟩) (lk (m ++ [Sum.inr L]) k) =
            (stp b g).getD k false := by
          intro k
          unfold lk
          rw [gd_snoc]
          unfold stp
          rw [gd_snoc, hbl]
          by_cases c1 : k < m.length
          · rw [ifp c1, ifp c1, ← hinv k]
            exact sval_app a _ _ (fun i hi => by rw [ha]; exact hb k i hi)
          · rw [ifn c1, ifn c1]
            by_cases c2 : k = m.length
            · rw [ifp c2, ifp c2]
              have hL : ¬ L < a.length := by omega
              show (a ++ [_]).getD L false = _
              rw [gd_snoc, ifn hL, ifp ha.symm]
              exact hval a b hinv
            · rw [ifn c2, ifn c2]; rfl
        exact h4 (stp a ⟨g.op, l⟩) (stp b g) (by simp [stp, ha]) (by simp [stp, hbl]) hinv' o

theorem ev_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (a b : List Bool) (h : ∀ k, a.getD k false = true → b.getD k false = true) :
    op.eval (ins.map fun i => a.getD i false) = true →
    op.eval (ins.map fun i => b.getD i false) = true := by
  rcases hop with rfl | rfl
  · intro H
    have H' : (ins.map fun i => a.getD i false).all id = true := H
    show (ins.map fun i => b.getD i false).all id = true
    rw [List.all_eq_true] at H' ⊢
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact h i (H' _ (List.mem_map.2 ⟨i, hi, rfl⟩))
  · intro H
    have H' : (ins.map fun i => a.getD i false).any id = true := H
    show (ins.map fun i => b.getD i false).any id = true
    rw [List.any_eq_true] at H' ⊢
    obtain ⟨v, hv, hvt⟩ := H'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, h i hvt⟩

theorem mono : ∀ (gs : List Gate) (a b : List Bool), (∀ g ∈ gs, AO g) → a.length = b.length →
    (∀ k, a.getD k false = true → b.getD k false = true) →
    ∀ k, (gs.foldl stp a).getD k false = true → (gs.foldl stp b).getD k false = true := by
  intro gs
  induction gs with
  | nil =>
    intro a b _ _ h
    exact h
  | cons g gs ih =>
    intro a b hAO hl h
    refine ih (stp a g) (stp b g) (fun g' h' => hAO g' (List.mem_cons_of_mem _ h'))
      (by simp [stp, hl]) ?_
    intro k
    unfold stp
    rw [gd_snoc, gd_snoc, hl]
    by_cases c1 : k < b.length
    · rw [ifp c1, ifp c1]
      exact h k
    · rw [ifn c1, ifn c1]
      by_cases c2 : k = b.length
      · rw [ifp c2, ifp c2]
        exact ev_mono g.op (hAO g List.mem_cons_self).1 g.inputs a b h
      · rw [ifn c2, ifn c2]
        exact id

theorem indep (z : ℕ) : ∀ (gs : List Gate) (a b : List Bool), (∀ g ∈ gs, z ∉ g.inputs) →
    a.length = b.length → (∀ k, k ≠ z → a.getD k false = b.getD k false) →
    ∀ k, k ≠ z → (gs.foldl stp a).getD k false = (gs.foldl stp b).getD k false := by
  intro gs
  induction gs with
  | nil =>
    intro a b _ _ h
    exact h
  | cons g gs ih =>
    intro a b hno hl h
    refine ih (stp a g) (stp b g) (fun g' h' => hno g' (List.mem_cons_of_mem _ h'))
      (by simp [stp, hl]) ?_
    intro k hk
    have hv : (g.inputs.map fun i => a.getD i false) = (g.inputs.map fun i => b.getD i false) :=
      List.map_congr_left (fun i hi => h i (fun e => hno g List.mem_cons_self (e ▸ hi)))
    unfold stp
    rw [gd_snoc, gd_snoc, hl, hv]
    by_cases c1 : k < b.length
    · rw [ifp c1, ifp c1]
      exact h k hk
    · rw [ifn c1, ifn c1]

theorem fold_keep : ∀ (gs : List Gate) (a : List Bool) (k : ℕ), k < a.length →
    (gs.foldl stp a).getD k false = a.getD k false := by
  intro gs
  induction gs with
  | nil =>
    intro a k _
    rfl
  | cons g gs ih =>
    intro a k hk
    have hk' : k < (stp a g).length := by
      simp [stp]
      omega
    have h1 := ih (stp a g) k hk'
    have e : (stp a g).getD k false = a.getD k false := by
      unfold stp
      rw [gd_snoc, ifp hk]
    exact h1.trans e

def auts : List (List ℕ × List ℕ) := [
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
  ([0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13], [0, 2, 1, 6, 4, 5, 3, 8, 7, 12, 10, 11, 9, 13]),
  ([0, 2, 4, 6, 1, 3, 5, 8, 10, 12, 7, 9, 11, 13], [0, 4, 1, 5, 2, 6, 3, 10, 7, 11, 8, 12, 9, 13]),
  ([1, 3, 5, 0, 2, 4, 6, 7, 9, 11, 13, 8, 10, 12], [3, 0, 4, 1, 5, 2, 6, 7, 11, 8, 12, 9, 13, 10]),
  ([1, 5, 3, 6, 2, 4, 0, 9, 7, 10, 13, 8, 11, 12], [6, 0, 4, 2, 5, 1, 3, 8, 11, 7, 9, 12, 13, 10]),
  ([1, 5, 2, 6, 3, 0, 4, 9, 13, 10, 7, 11, 8, 12], [5, 0, 2, 4, 6, 1, 3, 10, 12, 7, 9, 11, 13, 8]),
  ([2, 0, 3, 6, 1, 4, 5, 8, 12, 10, 13, 9, 11, 7], [1, 4, 0, 2, 5, 6, 3, 13, 7, 11, 9, 12, 8, 10]),
  ([2, 0, 5, 6, 4, 1, 3, 8, 12, 7, 13, 11, 9, 10], [1, 5, 0, 6, 4, 2, 3, 9, 7, 12, 13, 11, 8, 10]),
  ([2, 6, 3, 0, 4, 1, 5, 8, 12, 9, 13, 10, 7, 11], [3, 5, 0, 2, 4, 6, 1, 12, 7, 9, 11, 13, 8, 10]),
  ([2, 6, 5, 0, 1, 4, 3, 8, 12, 11, 13, 7, 10, 9], [3, 4, 0, 6, 5, 2, 1, 11, 7, 13, 12, 9, 8, 10]),
  ([2, 3, 0, 5, 1, 4, 6, 12, 8, 11, 13, 9, 10, 7], [2, 4, 0, 1, 5, 3, 6, 13, 8, 11, 12, 9, 7, 10]),
  ([2, 3, 6, 5, 4, 1, 0, 12, 8, 7, 13, 10, 9, 11], [6, 5, 0, 1, 4, 3, 2, 9, 8, 12, 11, 13, 7, 10]),
  ([2, 5, 0, 3, 4, 1, 6, 12, 8, 9, 13, 11, 7, 10], [2, 5, 0, 3, 4, 1, 6, 12, 8, 9, 13, 11, 7, 10]),
  ([2, 5, 6, 3, 1, 4, 0, 12, 8, 10, 13, 7, 11, 9], [6, 4, 0, 3, 5, 1, 2, 11, 8, 13, 9, 12, 7, 10]),
  ([3, 4, 5, 6, 0, 1, 2, 11, 12, 13, 7, 8, 9, 10], [4, 5, 6, 0, 1, 2, 3, 10, 11, 12, 13, 7, 8, 9]),
  ([8, 7, 13, 10, 9, 11, 12, 0, 2, 3, 6, 5, 4, 1], [7, 13, 8, 9, 12, 11, 10, 1, 0, 4, 3, 5, 6, 2]),
  ([8, 12, 7, 13, 11, 9, 10, 2, 0, 5, 6, 4, 1, 3], [8, 12, 7, 13, 11, 9, 10, 2, 0, 5, 6, 4, 1, 3]),
  ([9, 10, 8, 12, 7, 13, 11, 5, 6, 4, 1, 3, 2, 0], [13, 10, 12, 11, 9, 7, 8, 4, 2, 0, 1, 6, 3, 5]),
  ([13, 8, 11, 12, 9, 7, 10, 2, 4, 0, 1, 5, 3, 6], [9, 10, 7, 12, 8, 11, 13, 5, 1, 4, 6, 2, 3, 0]),
  ([13, 12, 11, 8, 7, 9, 10, 2, 4, 5, 1, 0, 6, 3], [11, 10, 7, 13, 8, 9, 12, 4, 3, 5, 6, 2, 1, 0]),
  ([2, 5, 1, 3, 6, 0, 4, 12, 13, 10, 8, 11, 7, 9], [5, 2, 0, 3, 6, 1, 4, 12, 10, 13, 9, 11, 7, 8]),
  ([5, 1, 0, 6, 3, 2, 4, 9, 10, 13, 12, 11, 8, 7], [2, 1, 5, 4, 6, 0, 3, 13, 12, 7, 8, 11, 10, 9]),
  ([5, 0, 6, 4, 2, 3, 1, 10, 9, 7, 12, 13, 11, 8], [1, 6, 4, 5, 3, 0, 2, 9, 13, 8, 7, 12, 10, 11]),
  ([7, 9, 11, 13, 8, 10, 12, 1, 3, 5, 0, 2, 4, 6], [10, 7, 11, 8, 12, 9, 13, 0, 4, 1, 5, 2, 6, 3]),
  ([7, 11, 8, 12, 9, 13, 10, 3, 0, 4, 1, 5, 2, 6], [8, 10, 12, 7, 9, 11, 13, 0, 2, 4, 6, 1, 3, 5]),
  ([8, 12, 9, 13, 10, 7, 11, 2, 6, 3, 0, 4, 1, 5], [10, 12, 7, 9, 11, 13, 8, 5, 0, 2, 4, 6, 1, 3]),
  ([1, 3, 2, 0, 5, 6, 4, 7, 13, 11, 9, 10, 8, 12], [3, 0, 2, 1, 6, 4, 5, 7, 12, 10, 11, 9, 13, 8]),
  ([1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12], [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7]),
  ([2, 6, 1, 0, 5, 3, 4, 8, 13, 11, 12, 10, 7, 9], [3, 2, 0, 5, 6, 4, 1, 12, 7, 13, 11, 9, 10, 8]),
  ([2, 6, 4, 0, 3, 5, 1, 8, 13, 9, 12, 7, 10, 11], [3, 6, 0, 4, 2, 5, 1, 11, 7, 9, 12, 13, 10, 8]),
  ([3, 0, 4, 1, 5, 2, 6, 7, 11, 8, 12, 9, 13, 10], [1, 3, 5, 0, 2, 4, 6, 7, 9, 11, 13, 8, 10, 12]),
  ([3, 4, 0, 6, 5, 2, 1, 11, 7, 13, 12, 9, 8, 10], [2, 6, 5, 0, 1, 4, 3, 8, 12, 11, 13, 7, 10, 9]),
  ([7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6]),
  ([8, 7, 12, 10, 11, 9, 13, 0, 2, 1, 6, 4, 5, 3], [7, 9, 8, 13, 11, 12, 10, 1, 0, 5, 3, 4, 2, 6]),
  ([8, 10, 12, 7, 9, 11, 13, 0, 2, 4, 6, 1, 3, 5], [7, 11, 8, 12, 9, 13, 10, 3, 0, 4, 1, 5, 2, 6]),
  ([8, 10, 13, 7, 11, 9, 12, 0, 2, 5, 6, 3, 1, 4], [7, 12, 8, 11, 13, 9, 10, 3, 0, 5, 1, 4, 6, 2]),
  ([8, 12, 10, 13, 9, 11, 7, 2, 0, 3, 6, 1, 4, 5], [8, 11, 7, 9, 12, 13, 10, 6, 0, 4, 2, 5, 1, 3]),
  ([8, 13, 7, 12, 9, 11, 10, 2, 0, 4, 6, 5, 3, 1], [8, 13, 7, 12, 9, 11, 10, 2, 0, 4, 6, 5, 3, 1]),
  ([8, 13, 10, 12, 11, 9, 7, 2, 0, 1, 6, 3, 5, 4], [8, 9, 7, 11, 13, 12, 10, 6, 0, 5, 2, 4, 3, 1]),
  ([11, 7, 10, 12, 8, 9, 13, 3, 4, 1, 6, 2, 5, 0], [13, 9, 11, 7, 8, 12, 10, 1, 4, 5, 2, 0, 3, 6]),
  ([11, 12, 10, 7, 9, 8, 13, 3, 4, 2, 6, 1, 0, 5], [12, 11, 9, 7, 8, 13, 10, 3, 5, 4, 2, 0, 1, 6]),
  ([11, 10, 7, 13, 8, 9, 12, 4, 3, 5, 6, 2, 1, 0], [13, 12, 11, 8, 7, 9, 10, 2, 4, 5, 1, 0, 6, 3]),
  ([11, 10, 12, 13, 9, 8, 7, 4, 3, 0, 6, 1, 2, 5], [9, 11, 12, 8, 7, 13, 10, 6, 5, 4, 1, 0, 2, 3]),
  ([11, 10, 8, 13, 7, 12, 9, 4, 6, 5, 3, 1, 2, 0], [13, 11, 12, 10, 7, 9, 8, 4, 2, 6, 1, 0, 5, 3]),
  ([11, 10, 9, 13, 12, 7, 8, 4, 6, 0, 3, 2, 1, 5], [9, 12, 11, 10, 7, 13, 8, 5, 6, 2, 1, 0, 4, 3])]

def E : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]

def FL (w : List Bool) : Bool := E.any fun pq => w.getD pq.1 false && w.getD pq.2 false

def P2 (x : Fin 14 → Bool) : Prop :=
  ∃ (p : Fin 14) (q : Fin 14), ((p : ℕ), (q : ℕ)) ∈ E ∧ x p = true ∧ x q = true

def e07 : List Bool := List.ofFn fun (k : Fin 14) => decide (k = 0 ∨ k = 7)

def ind (p q : ℕ) : List Bool := List.ofFn fun (k : Fin 14) => decide ((k : ℕ) = p ∨ (k : ℕ) = q)

def zero14 : List Bool := List.replicate 14 false

theorem E_bound : ∀ pq ∈ E, pq.1 < 14 ∧ pq.2 < 14 := by decide

theorem E_nopair : ∀ pq ∈ E, ¬((0 = pq.1 ∨ 0 = pq.2) ∧ (1 = pq.1 ∨ 1 = pq.2)) ∧
    ¬((0 = pq.1 ∨ 0 = pq.2) ∧ (9 = pq.1 ∨ 9 = pq.2)) := by decide

theorem gd_ofFn {n : ℕ} (x : Fin n → Bool) (k : Fin n) :
    (List.ofFn x).getD (k : ℕ) false = x k := by
  simp [List.getD_eq_getElem?_getD]

theorem gd_ofFn_lt {n : ℕ} (x : Fin n → Bool) (k : ℕ) (h : k < n) :
    (List.ofFn x).getD k false = x ⟨k, h⟩ := gd_ofFn x ⟨k, h⟩

theorem gd_ofFn_ge {n : ℕ} (x : Fin n → Bool) (k : ℕ) (h : n ≤ k) :
    (List.ofFn x).getD k false = false :=
  List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact h)

theorem perm_gd (l : List ℕ) (y : List Bool) (k : ℕ) (hk : k < 14) :
    (List.ofFn fun (k : Fin 14) => y.getD (l.getD k 0) false).getD k false =
      y.getD (l.getD k 0) false := gd_ofFn_lt _ k hk

theorem perm_len (l : List ℕ) (y : List Bool) :
    (List.ofFn fun (k : Fin 14) => y.getD (l.getD k 0) false).length = 14 := List.length_ofFn

theorem ofFn_gd (y : List Bool) (n : ℕ) (hy : y.length = n) :
    List.ofFn (fun k : Fin n => y.getD k false) = y := by
  subst hy
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem P2_iff (x : Fin 14 → Bool) : P2 x ↔ FL (List.ofFn x) = true := by
  unfold P2 FL
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, q, hE, hp, hq⟩
    refine ⟨((p : ℕ), (q : ℕ)), hE, ?_⟩
    show ((List.ofFn x).getD (p : ℕ) false && (List.ofFn x).getD (q : ℕ) false) = true
    rw [gd_ofFn, gd_ofFn, hp, hq]
    rfl
  · rintro ⟨⟨p, q⟩, hE, h⟩
    obtain ⟨hp, hq⟩ := E_bound _ hE
    have h' : ((List.ofFn x).getD p false && (List.ofFn x).getD q false) = true := h
    rw [gd_ofFn_lt x p hp, gd_ofFn_lt x q hq, Bool.and_eq_true] at h'
    exact ⟨⟨p, hp⟩, ⟨q, hq⟩, hE, h'.1, h'.2⟩

theorem ind_len (p q : ℕ) : (ind p q).length = 14 := List.length_ofFn

theorem ind_gd (p q k : ℕ) : (ind p q).getD k false = true ↔ k < 14 ∧ (k = p ∨ k = q) := by
  by_cases h : k < 14
  · have e : (ind p q).getD k false = decide (k = p ∨ k = q) :=
      gd_ofFn_lt (fun (k : Fin 14) => decide ((k : ℕ) = p ∨ (k : ℕ) = q)) k h
    rw [e]
    simp [h]
  · have e : (ind p q).getD k false = false :=
      gd_ofFn_ge (fun (k : Fin 14) => decide ((k : ℕ) = p ∨ (k : ℕ) = q)) k (by omega)
    rw [e]
    simp [h]

theorem e07_len : e07.length = 14 := List.length_ofFn

theorem zero14_len : zero14.length = 14 := by decide

theorem e07_gd (k : ℕ) (hk : e07.getD k false = true) : k = 0 ∨ k = 7 := by
  by_cases h : k < 14
  · have e : e07.getD k false = decide ((⟨k, h⟩ : Fin 14) = 0 ∨ (⟨k, h⟩ : Fin 14) = 7) :=
      gd_ofFn_lt (fun (k : Fin 14) => decide (k = 0 ∨ k = 7)) k h
    rw [e] at hk
    rcases of_decide_eq_true hk with h0 | h7
    · left
      exact congrArg Fin.val h0
    · right
      exact congrArg Fin.val h7
  · have e : e07.getD k false = false :=
      gd_ofFn_ge (fun (k : Fin 14) => decide (k = 0 ∨ k = 7)) k (by omega)
    rw [e] at hk
    cases hk

theorem FL_e07 : FL e07 = true := by decide

theorem FL_zero : FL zero14 = false := by decide

theorem FL_ind19 : FL (ind 1 9) = true := by decide

theorem FL_ind08 : FL (ind 0 8) = true := by decide

theorem ind08_and : ((ind 0 8).getD 0 false && (ind 0 8).getD 7 false) = false := by decide

theorem e07_0 : e07.getD 0 false = true := by decide

theorem e07_7 : e07.getD 7 false = true := by decide

theorem auts_good : ∀ e ∈ auts,
    (∀ pq ∈ E, (e.1.getD pq.1 0, e.1.getD pq.2 0) ∈ E ∨ (e.1.getD pq.2 0, e.1.getD pq.1 0) ∈ E) ∧
    (∀ pq ∈ E, (e.2.getD pq.1 0, e.2.getD pq.2 0) ∈ E ∨ (e.2.getD pq.2 0, e.2.getD pq.1 0) ∈ E) ∧
    (∀ k < 14, e.1.getD k 0 < 14 ∧ e.2.getD k 0 < 14 ∧ e.1.getD (e.2.getD k 0) 0 = k) ∧
    e.1.length = 14 := by decide +kernel

theorem auts_cover : ∀ i < 14, ∀ j < 14, i ≠ j → (auts.any fun e => decide
    ((e.1.getD i 0 = 0 ∧ (e.1.getD j 0 = 1 ∨ e.1.getD j 0 = 7 ∨ e.1.getD j 0 = 9)) ∨
    (e.1.getD j 0 = 0 ∧ (e.1.getD i 0 = 1 ∨ e.1.getD i 0 = 7 ∨ e.1.getD i 0 = 9)))) = true := by
  decide +kernel

theorem band {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem FL_le (l : List ℕ)
    (hE : ∀ pq ∈ E, (l.getD pq.1 0, l.getD pq.2 0) ∈ E ∨ (l.getD pq.2 0, l.getD pq.1 0) ∈ E)
    (x y : List Bool) (h : ∀ k < 14, x.getD k false = y.getD (l.getD k 0) false) :
    FL x = true → FL y = true := by
  unfold FL
  rw [List.any_eq_true, List.any_eq_true]
  rintro ⟨⟨p, q⟩, hpq, hv⟩
  obtain ⟨hp, hq⟩ := E_bound _ hpq
  have hv' : (x.getD p false && x.getD q false) = true := hv
  rw [Bool.and_eq_true, h p hp, h q hq] at hv'
  rcases hE _ hpq with h1 | h1
  · exact ⟨_, h1, band hv'.1 hv'.2⟩
  · exact ⟨_, h1, band hv'.2 hv'.1⟩

theorem FL_perm (e : List ℕ × List ℕ) (he : e ∈ auts) (y : List Bool) :
    FL (List.ofFn fun (k : Fin 14) => y.getD (e.1.getD k 0) false) = FL y := by
  obtain ⟨h1, h2, h3, -⟩ := auts_good e he
  rw [Bool.eq_iff_iff]
  constructor
  · exact FL_le e.1 h1 _ _ (fun k hk => perm_gd e.1 y k hk)
  · refine FL_le e.2 h2 _ _ ?_
    intro k hk
    obtain ⟨_, hb, hc⟩ := h3 k hk
    rw [perm_gd e.1 y _ hb, hc]

theorem subs (rest : List Gate) (l : List ℕ) (hl : l.length = 14) (L : ℕ) (sy : Bool ⊕ ℕ)
    (hlL : ∀ k < 14, l.getD k 0 < L) (hsy : ∀ i, sy = Sum.inr i → i < L)
    (hrest : ∀ g ∈ rest, AO g) :
    ∃ (ng : List Gate) (m' : List (Bool ⊕ ℕ)), (∀ g ∈ ng, AO g) ∧ ng.length ≤ rest.length ∧
      (sy = Sum.inl false → (∃ g ∈ rest, 14 ∈ g.inputs) → ng.length + 1 ≤ rest.length) ∧
      ∀ (a x : List Bool), a.length = L → x.length = 14 →
        (∀ k < 14, x.getD k false = a.getD (l.getD k 0) false) →
        ∀ o, sval (ng.foldl stp a) (lk m' o) =
          (rest.foldl stp (x ++ [sval a sy])).getD o false := by
  have hlk : ∀ k, lk (l.map Sum.inr ++ [sy]) k =
      if k < 14 then Sum.inr (l.getD k 0) else if k = 14 then sy else Sum.inl false := by
    intro k
    unfold lk
    rw [gd_snoc, List.length_map, hl]
    by_cases h1 : k < 14
    · have h1' : k < l.length := by omega
      rw [ifp h1, ifp h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1']
    · rw [ifn h1, ifn h1]
  have hb : ∀ k i, lk (l.map Sum.inr ++ [sy]) k = Sum.inr i → i < L := by
    intro k i h
    rw [hlk] at h
    by_cases h1 : k < 14
    · rw [ifp h1] at h
      cases h
      exact hlL k h1
    · rw [ifn h1] at h
      by_cases h2 : k = 14
      · rw [ifp h2] at h
        exact hsy i h
      · rw [ifn h2] at h
        cases h
  obtain ⟨ng, m', a1, a2, a3, a4⟩ := sim 14 rest (l.map Sum.inr ++ [sy]) L hrest hb
  refine ⟨ng, m', a1, a2, ?_, ?_⟩
  · rintro hs ⟨g, hg, hz⟩
    have hlen : 14 < (l.map Sum.inr ++ [sy]).length := by
      rw [List.length_append, List.length_map, hl, List.length_singleton]
      omega
    have h14 : lk (l.map Sum.inr ++ [sy]) 14 = Sum.inl false := by
      rw [hlk, ifn (by omega : ¬ (14 < 14)), ifp (rfl : 14 = 14)]
      exact hs
    exact a3 hlen h14 g hg hz
  · intro a x ha hx h o
    have hlen : (x ++ [sval a sy]).length = (l.map Sum.inr ++ [sy]).length := by
      rw [List.length_append, List.length_append, List.length_map, hl, hx]
      rfl
    refine a4 a (x ++ [sval a sy]) ha hlen ?_ o
    intro k
    rw [hlk, gd_snoc, hx]
    by_cases h1 : k < 14
    · rw [ifp h1, ifp h1]
      exact (h k h1).symm
    · rw [ifn h1, ifn h1]
      by_cases h2 : k = 14
      · rw [ifp h2, ifp h2]
      · rw [ifn h2, ifn h2]
        rfl

theorem elim (rest : List Gate) (o : ℕ) (sy : Bool ⊕ ℕ) (hsy : ∀ i, sy = Sum.inr i → i < 14)
    (hrest : ∀ g ∈ rest, AO g) (G : List Bool → Bool) (y0 y1 : List Bool) (h0 : y0.length = 14)
    (h1 : y1.length = 14) (hG0 : G y0 = false) (hG1 : G y1 = true)
    (hT : ∀ y : List Bool, y.length = 14 →
      (rest.foldl stp (y ++ [sval y sy])).getD o false = G y) :
    ∃ D : Circuit, (∀ g ∈ D.gates, AO g) ∧ D.gates.length ≤ rest.length ∧
      (sy = Sum.inl false → (∃ g ∈ rest, 14 ∈ g.inputs) → D.gates.length + 1 ≤ rest.length) ∧
      ∀ y : List Bool, y.length = 14 → D.eval y = G y := by
  have hr : ∀ k < 14, (List.range 14).getD k 0 = k := by decide
  have hrl : (List.range 14).length = 14 := List.length_range
  obtain ⟨ng, m', a1, a2, a3, a4⟩ := subs rest (List.range 14) hrl 14 sy
    (fun k hk => by rw [hr k hk]; exact hk) hsy hrest
  have key : ∀ y : List Bool, y.length = 14 → sval (ng.foldl stp y) (lk m' o) = G y := by
    intro y hy
    rw [← hT y hy]
    exact a4 y y hy hy (fun k hk => by rw [hr k hk]) o
  rcases hlo : lk m' o with c | i
  · exfalso
    have e0 := key y0 h0
    have e1 := key y1 h1
    rw [hlo] at e0 e1
    have e0' : c = false := e0.trans hG0
    have e1' : c = true := e1.trans hG1
    rw [e0'] at e1'
    cases e1'
  · refine ⟨⟨ng, i⟩, a1, a2, a3, fun y hy => ?_⟩
    have e := key y hy
    rw [hlo] at e
    exact e

theorem aut_move (rest : List Gate) (o : ℕ) (hrest : ∀ g ∈ rest, AO g) (bop : Bool → Bool → Bool)
    (hcomm : ∀ p q, bop p q = bop q p) (i j : ℕ) (hi : i < 14) (hj : j < 14) (hij : i ≠ j)
    (hT : ∀ y : List Bool, y.length = 14 →
      (rest.foldl stp (y ++ [bop (y.getD i false) (y.getD j false)])).getD o false = FL y) :
    ∃ (D : Circuit) (v : ℕ), (v = 1 ∨ v = 7 ∨ v = 9) ∧ (∀ g ∈ D.gates, AO g) ∧
      D.gates.length ≤ rest.length ∧
      ∀ y : List Bool, y.length = 14 →
        D.eval (y ++ [bop (y.getD 0 false) (y.getD v false)]) = FL y := by
  obtain ⟨e, he, htg0⟩ := List.any_eq_true.1 (auts_cover i hi j hj hij)
  have htg := of_decide_eq_true htg0
  obtain ⟨g1, g2, g3, g4⟩ := auts_good e he
  obtain ⟨ng, m', a1, a2, -, a4⟩ := subs rest e.1 g4 15 (Sum.inr 14)
    (fun k hk => Nat.lt_succ_of_lt (g3 k hk).1) (fun i' h => by cases h; decide) hrest
  have key : ∀ (y : List Bool) (w : Bool), y.length = 14 →
      sval (ng.foldl stp (y ++ [w])) (lk m' o) =
        (rest.foldl stp ((List.ofFn fun (k : Fin 14) => y.getD (e.1.getD k 0) false) ++
          [w])).getD o false := by
    intro y w hy
    have hw : sval (y ++ [w]) (Sum.inr 14) = w := by
      show (y ++ [w]).getD 14 false = w
      rw [gd_snoc, hy, ifn (by omega : ¬ (14 < 14)), ifp (rfl : 14 = 14)]
    have hlen : (y ++ [w]).length = 15 := by
      rw [List.length_append, hy]
      rfl
    have hperm : ∀ k < 14, (List.ofFn fun (k : Fin 14) => y.getD (e.1.getD k 0) false).getD k false =
        (y ++ [w]).getD (e.1.getD k 0) false := by
      intro k hk
      have hlt : e.1.getD k 0 < y.length := by
        rw [hy]
        exact (g3 k hk).1
      rw [perm_gd e.1 y k hk, gd_snoc, ifp hlt]
    have h5 := a4 (y ++ [w]) (List.ofFn fun (k : Fin 14) => y.getD (e.1.getD k 0) false) hlen
      (perm_len e.1 y) hperm o
    rw [hw] at h5
    exact h5
  have val : ∀ (y : List Bool) (v : ℕ), y.length = 14 →
      ((e.1.getD i 0 = 0 ∧ e.1.getD j 0 = v) ∨ (e.1.getD j 0 = 0 ∧ e.1.getD i 0 = v)) →
      sval (ng.foldl stp (y ++ [bop (y.getD 0 false) (y.getD v false)])) (lk m' o) = FL y := by
    intro y v hy hv
    rw [key y _ hy, ← FL_perm e he y]
    have h5 := hT (List.ofFn fun (k : Fin 14) => y.getD (e.1.getD k 0) false) (perm_len e.1 y)
    rw [perm_gd e.1 y i hi, perm_gd e.1 y j hj] at h5
    rcases hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · rw [hv1, hv2] at h5
      exact h5
    · rw [hv1, hv2, hcomm] at h5
      exact h5
  obtain ⟨v, hv3, hv⟩ : ∃ v, (v = 1 ∨ v = 7 ∨ v = 9) ∧
      ((e.1.getD i 0 = 0 ∧ e.1.getD j 0 = v) ∨ (e.1.getD j 0 = 0 ∧ e.1.getD i 0 = v)) := by
    rcases htg with ⟨h0, hh⟩ | ⟨h0, hh⟩
    · exact ⟨e.1.getD j 0, hh, Or.inl ⟨h0, rfl⟩⟩
    · exact ⟨e.1.getD i 0, hh, Or.inr ⟨h0, rfl⟩⟩
  rcases hlo : lk m' o with c | i'
  · exfalso
    have e0 := val zero14 v zero14_len hv
    have e1 := val e07 v e07_len hv
    rw [hlo] at e0 e1
    have e0' : c = false := e0.trans FL_zero
    have e1' : c = true := e1.trans FL_e07
    rw [e0'] at e1'
    cases e1'
  · refine ⟨⟨ng, i'⟩, v, hv3, a1, a2, fun y hy => ?_⟩
    have e2 := val y v hy hv
    rw [hlo] at e2
    exact e2

theorem classify (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (hlen : ins.length ≤ 2) :
    (∃ sy : Bool ⊕ ℕ, (∀ i, sy = Sum.inr i → i < 14) ∧ ∀ y : List Bool, y.length = 14 →
      op.eval (ins.map fun i => y.getD i false) = sval y sy) ∨
    (∃ i j, i < 14 ∧ j < 14 ∧ i ≠ j ∧ ∀ y : List Bool, y.length = 14 →
      op.eval (ins.map fun i => y.getD i false) = (y.getD i false && y.getD j false)) ∨
    (∃ i j, i < 14 ∧ j < 14 ∧ i ≠ j ∧ ∀ y : List Bool, y.length = 14 →
      op.eval (ins.map fun i => y.getD i false) = (y.getD i false || y.getD j false)) := by
  have hf : ∀ (y : List Bool) (i : ℕ), y.length = 14 → ¬ i < 14 → y.getD i false = false :=
    fun y i hy hi => List.getD_eq_default _ _ (by omega)
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · left
    rcases hop with rfl | rfl
    · exact ⟨Sum.inl true, fun i h => (by cases h), fun y _ => rfl⟩
    · exact ⟨Sum.inl false, fun i h => (by cases h), fun y _ => rfl⟩
  · left
    by_cases hi : i < 14
    · refine ⟨Sum.inr i, fun i' h => (by cases h; exact hi), fun y _ => ?_⟩
      rcases hop with rfl | rfl
      · show (y.getD i false && true) = y.getD i false
        exact Bool.and_true _
      · show (y.getD i false || false) = y.getD i false
        exact Bool.or_false _
    · refine ⟨Sum.inl false, fun i' h => (by cases h), fun y hy => ?_⟩
      rcases hop with rfl | rfl
      · show (y.getD i false && true) = false
        rw [hf y i hy hi]
        rfl
      · show (y.getD i false || false) = false
        rw [hf y i hy hi]
        rfl
  · have va : ∀ y : List Bool, GateOp.and.eval ([i, j].map fun i => y.getD i false) =
        (y.getD i false && y.getD j false) := fun y => by
      show (y.getD i false && (y.getD j false && true)) = _
      rw [Bool.and_true]
    have vo : ∀ y : List Bool, GateOp.or.eval ([i, j].map fun i => y.getD i false) =
        (y.getD i false || y.getD j false) := fun y => by
      show (y.getD i false || (y.getD j false || false)) = _
      rw [Bool.or_false]
    by_cases hi : i < 14
    · by_cases hj : j < 14
      · by_cases hij : i = j
        · left
          refine ⟨Sum.inr i, fun i' h => (by cases h; exact hi), fun y _ => ?_⟩
          subst hij
          rcases hop with rfl | rfl
          · rw [va]
            exact Bool.and_self _
          · rw [vo]
            exact Bool.or_self _
        · rcases hop with rfl | rfl
          · right
            left
            exact ⟨i, j, hi, hj, hij, fun y _ => va y⟩
          · right
            right
            exact ⟨i, j, hi, hj, hij, fun y _ => vo y⟩
      · left
        rcases hop with rfl | rfl
        · refine ⟨Sum.inl false, fun i' h => (by cases h), fun y hy => ?_⟩
          rw [va, hf y j hy hj]
          exact Bool.and_false _
        · refine ⟨Sum.inr i, fun i' h => (by cases h; exact hi), fun y hy => ?_⟩
          rw [vo, hf y j hy hj]
          exact Bool.or_false _
    · left
      rcases hop with rfl | rfl
      · refine ⟨Sum.inl false, fun i' h => (by cases h), fun y hy => ?_⟩
        rw [va, hf y i hy hi]
        rfl
      · by_cases hj : j < 14
        · refine ⟨Sum.inr j, fun i' h => (by cases h; exact hj), fun y hy => ?_⟩
          rw [vo, hf y i hy hi]
          rfl
        · refine ⟨Sum.inl false, fun i' h => (by cases h), fun y hy => ?_⟩
          rw [vo, hf y i hy hi, hf y j hy hj]
          rfl
  · exfalso
    simp only [List.length_cons] at hlen
    omega

def Out (s : ℕ) (D : Circuit) : Prop :=
  (D.gates.length + 2 ≤ s ∧
    (∀ y : List Bool, y.length = 14 → (y.getD 0 false = false ∨ y.getD 7 false = false) →
      D.eval y = FL y) ∧ D.eval e07 = false) ∨
  (D.gates.length + 1 ≤ s ∧ ∃ v, (v = 1 ∨ v = 7 ∨ v = 9) ∧
    ∀ y : List Bool, y.length = 14 →
      D.eval (y ++ [(y.getD 0 false || y.getD v false)]) = FL y)

theorem and_case (s : ℕ) (D : Circuit) (v : ℕ) (hv : v = 1 ∨ v = 7 ∨ v = 9)
    (hD : ∀ g ∈ D.gates, AO g) (hDl : D.gates.length + 1 ≤ s)
    (hDF : ∀ y : List Bool, y.length = 14 →
      D.eval (y ++ [(y.getD 0 false && y.getD v false)]) = FL y)
    (smaller : ∀ D : Circuit, (∀ g ∈ D.gates, AO g) → D.gates.length < s →
      (∀ y : List Bool, y.length = 14 → D.eval y = FL y) →
      ∃ D' : Circuit, (∀ g ∈ D'.gates, AO g) ∧ Out s D') :
    ∃ D' : Circuit, (∀ g ∈ D'.gates, AO g) ∧ Out s D' := by
  have ev : ∀ x : List Bool, D.eval x = (D.gates.foldl stp x).getD D.output false :=
    fun _ => rfl
  have le_snoc : ∀ (y1 y2 : List Bool) (w1 w2 : Bool), y1.length = 14 → y2.length = 14 →
      (∀ k, y1.getD k false = true → y2.getD k false = true) → (w1 = true → w2 = true) →
      ∀ k, (y1 ++ [w1]).getD k false = true → (y2 ++ [w2]).getD k false = true := by
    intro y1 y2 w1 w2 h1 h2 h hw k
    rw [gd_snoc, gd_snoc, h1, h2]
    by_cases c1 : k < 14
    · rw [ifp c1, ifp c1]
      exact h k
    · rw [ifn c1, ifn c1]
      by_cases c2 : k = 14
      · rw [ifp c2, ifp c2]
        exact hw
      · rw [ifn c2, ifn c2]
        exact id
  have monoG : ∀ (y1 y2 : List Bool) (w1 w2 : Bool), y1.length = 14 → y2.length = 14 →
      (∀ k, y1.getD k false = true → y2.getD k false = true) → (w1 = true → w2 = true) →
      D.eval (y1 ++ [w1]) = true → D.eval (y2 ++ [w2]) = true := by
    intro y1 y2 w1 w2 h1 h2 h hw
    have hlen : (y1 ++ [w1]).length = (y2 ++ [w2]).length := by
      rw [List.length_append, List.length_append, h1, h2]
      rfl
    exact mono D.gates (y1 ++ [w1]) (y2 ++ [w2]) hD hlen (le_snoc y1 y2 w1 w2 h1 h2 h hw)
      D.output
  have m1 : ∀ y : List Bool, y.length = 14 → D.eval (y ++ [false]) = true → FL y = true := by
    intro y hy h
    rw [← hDF y hy]
    exact monoG y y false _ hy hy (fun _ h => h) (fun h => by cases h) h
  have m2 : ∀ y : List Bool, y.length = 14 → (y.getD 0 false && y.getD v false) = false →
      D.eval (y ++ [false]) = FL y := by
    intro y hy h
    rw [← hDF y hy, h]
  by_cases hcase : v = 7 ∧ D.eval (e07 ++ [false]) = false
  · obtain ⟨hv7, hG⟩ := hcase
    subst hv7
    have hread : ∃ g ∈ D.gates, 14 ∈ g.inputs := by
      by_contra hno
      have hno' : ∀ g ∈ D.gates, 14 ∉ g.inputs := fun g hg h => hno ⟨g, hg, h⟩
      have htrue : D.eval (e07 ++ [true]) = true := by
        have h5 := hDF e07 e07_len
        rw [e07_0, e07_7, FL_e07] at h5
        exact h5
      by_cases ho : D.output = 14
      · have h8 := m2 (ind 0 8) (ind_len 0 8) ind08_and
        have hlt : 14 < (ind 0 8 ++ [false]).length := by
          rw [List.length_append, ind_len]
          decide
        rw [FL_ind08, ev, ho, fold_keep D.gates (ind 0 8 ++ [false]) 14 hlt] at h8
        rw [gd_snoc, ind_len, ifn (by omega : ¬ (14 < 14)), ifp (rfl : 14 = 14)] at h8
        cases h8
      · have hlen : (e07 ++ [false]).length = (e07 ++ [true]).length := by
          rw [List.length_append, List.length_append]
          rfl
        have h6 := indep 14 D.gates (e07 ++ [false]) (e07 ++ [true]) hno' hlen (fun k hk => by
          rw [gd_snoc, gd_snoc, e07_len]
          by_cases c1 : k < 14
          · rw [ifp c1, ifp c1]
          · rw [ifn c1, ifn c1, ifn hk, ifn hk]) D.output ho
        rw [ev, h6, ← ev, htrue] at hG
        cases hG
    obtain ⟨D', hD', -, hstrict, hD'F⟩ := elim D.gates D.output (Sum.inl false)
      (fun i h => by cases h) hD (fun y => D.eval (y ++ [false])) e07 (ind 0 8) e07_len
      (ind_len 0 8) hG ((m2 _ (ind_len 0 8) ind08_and).trans FL_ind08) (fun y hy => rfl)
    have hs := hstrict rfl hread
    refine ⟨D', hD', Or.inl ⟨by omega, fun y hy h07 => ?_, ?_⟩⟩
    · rw [hD'F y hy]
      refine m2 y hy ?_
      rcases h07 with h | h
      · rw [h]
        rfl
      · rw [h]
        exact Bool.and_false _
    · rw [hD'F e07 e07_len]
      exact hG
  · have hGF : ∀ y : List Bool, y.length = 14 → D.eval (y ++ [false]) = FL y := by
      intro y hy
      rw [Bool.eq_iff_iff]
      refine ⟨m1 y hy, fun hF => ?_⟩
      by_cases hb : (y.getD 0 false && y.getD v false) = false
      · rw [m2 y hy hb]
        exact hF
      · have hb' := bne hb
        rw [Bool.and_eq_true] at hb'
        by_cases hv7 : v = 7
        · subst hv7
          have hG : D.eval (e07 ++ [false]) = true := by
            by_contra h
            exact hcase ⟨rfl, bnt h⟩
          refine monoG e07 y false false e07_len hy (fun k hk => ?_) id hG
          rcases e07_gd k hk with h0 | h7
          · rw [h0]
            exact hb'.1
          · rw [h7]
            exact hb'.2
        · have hv19 : v = 1 ∨ v = 9 := by omega
          unfold FL at hF
          rw [List.any_eq_true] at hF
          obtain ⟨⟨p, q⟩, hpq, hval⟩ := hF
          have hval' : (y.getD p false && y.getD q false) = true := hval
          rw [Bool.and_eq_true] at hval'
          obtain ⟨hp, hq⟩ := E_bound _ hpq
          have hnp := E_nopair _ hpq
          have hindF : FL (ind p q) = true := by
            unfold FL
            rw [List.any_eq_true]
            exact ⟨(p, q), hpq, band ((ind_gd p q p).2 ⟨hp, Or.inl rfl⟩)
              ((ind_gd p q q).2 ⟨hq, Or.inr rfl⟩)⟩
          have hand : ((ind p q).getD 0 false && (ind p q).getD v false) = false := by
            by_contra hne
            have hne' := bne hne
            rw [Bool.and_eq_true, ind_gd, ind_gd] at hne'
            rcases hv19 with h1 | h9
            · rw [h1] at hne'
              exact hnp.1 ⟨hne'.1.2, hne'.2.2⟩
            · rw [h9] at hne'
              exact hnp.2 ⟨hne'.1.2, hne'.2.2⟩
          have hGi : D.eval (ind p q ++ [false]) = true :=
            (m2 _ (ind_len p q) hand).trans hindF
          refine monoG (ind p q) y false false (ind_len p q) hy (fun k hk => ?_) id hGi
          rcases ((ind_gd p q k).1 hk).2 with hkp | hkq
          · rw [hkp]
            exact hval'.1
          · rw [hkq]
            exact hval'.2
    obtain ⟨D', hD', hlen', -, hD'F⟩ := elim D.gates D.output (Sum.inl false)
      (fun i h => by cases h) hD FL zero14 e07 zero14_len e07_len FL_zero FL_e07
      (fun y hy => hGF y hy)
    exact smaller D' hD' (by omega) hD'F

theorem core : ∀ (s : ℕ) (C : Circuit), C.gates.length = s → (∀ g ∈ C.gates, AO g) →
    (∀ y : List Bool, y.length = 14 → C.eval y = FL y) →
    ∃ D : Circuit, (∀ g ∈ D.gates, AO g) ∧ Out s D := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs hAO hC
    have smaller : ∀ D : Circuit, (∀ g ∈ D.gates, AO g) → D.gates.length < s →
        (∀ y : List Bool, y.length = 14 → D.eval y = FL y) →
        ∃ D' : Circuit, (∀ g ∈ D'.gates, AO g) ∧ Out s D' := by
      intro D hD hlt hDF
      obtain ⟨D', h1, h2⟩ := ih _ hlt D rfl hD hDF
      refine ⟨D', h1, ?_⟩
      rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨by omega, h4⟩
      · exact Or.inr ⟨by omega, h4⟩
    obtain ⟨gs, o⟩ := C
    cases gs with
    | nil =>
      exfalso
      have e1 : e07.getD o false = true := (hC e07 e07_len).trans FL_e07
      have e2 : (ind 1 9).getD o false = true := (hC (ind 1 9) (ind_len 1 9)).trans FL_ind19
      have h5 := e07_gd o e1
      have h6 := ((ind_gd 1 9 o).1 e2).2
      omega
    | cons g0 rest =>
      have hg0 : AO g0 := hAO g0 List.mem_cons_self
      have hrest : ∀ g ∈ rest, AO g := fun g h => hAO g (List.mem_cons_of_mem _ h)
      have hlen : rest.length + 1 = s := hs
      have hT : ∀ y : List Bool, y.length = 14 →
          (rest.foldl stp (y ++ [g0.op.eval (g0.inputs.map fun i => y.getD i false)])).getD o
            false = FL y := fun y hy => hC y hy
      rcases classify g0.op hg0.1 g0.inputs hg0.2 with
        ⟨sy, hsy, hu⟩ | ⟨i, j, hi, hj, hij, hu⟩ | ⟨i, j, hi, hj, hij, hu⟩
      · obtain ⟨D, hD, hDl, -, hDF⟩ := elim rest o sy hsy hrest FL zero14 e07 zero14_len e07_len
          FL_zero FL_e07 (fun y hy => by
            have h5 := hT y hy
            rw [hu y hy] at h5
            exact h5)
        exact smaller D hD (by omega) hDF
      · obtain ⟨D, v, hv, hD, hDl, hDF⟩ := aut_move rest o hrest (fun p q => p && q)
          (fun p q => Bool.and_comm p q) i j hi hj hij (fun y hy => by
            have h5 := hT y hy
            rw [hu y hy] at h5
            exact h5)
        exact and_case s D v hv hD (by omega) hDF smaller
      · obtain ⟨D, v, hv, hD, hDl, hDF⟩ := aut_move rest o hrest (fun p q => p || q)
          (fun p q => Bool.or_comm p q) i j hi hj hij (fun y hy => by
            have h5 := hT y hy
            rw [hu y hy] at h5
            exact h5)
        exact ⟨D, hD, Or.inr ⟨by omega, v, hv, hDF⟩⟩

theorem main (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ P2 x) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (D.size + 2 ≤ C.size ∧
        ((∀ x : Fin 14 → Bool, x 0 = false ∨ x 7 = false →
          (D.eval (List.ofFn x) = true ↔ P2 x)) ∧ D.eval e07 = false) ∨
       D.size + 1 ≤ C.size ∧
        ((∀ x : Fin 14 → Bool,
            D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 1]]) = true ↔ P2 x) ∨
          (∀ x : Fin 14 → Bool,
            D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 7]]) = true ↔ P2 x) ∨
          (∀ x : Fin 14 → Bool,
            D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x 9]]) = true ↔ P2 x))) := by
  have hAO : ∀ g ∈ C.gates, AO g := fun g hg => hM g hg
  have hL : ∀ y : List Bool, y.length = 14 → C.eval y = FL y := by
    intro y hy
    rw [← ofFn_gd y 14 hy, Bool.eq_iff_iff]
    exact (hC _).trans (P2_iff _)
  obtain ⟨D, hD, hOut⟩ := core C.gates.length C rfl hAO hL
  refine ⟨D, fun g hg => hD g hg, ?_⟩
  have hlen : ∀ x : Fin 14 → Bool, (List.ofFn x).length = 14 := fun x => List.length_ofFn
  have orv : ∀ (x : Fin 14 → Bool) (v : Fin 14), GateOp.or.eval [x 0, x v] =
      ((List.ofFn x).getD 0 false || (List.ofFn x).getD (v : ℕ) false) := by
    intro x v
    have h0 : (List.ofFn x).getD 0 false = x 0 := gd_ofFn x 0
    rw [h0, gd_ofFn x v]
    show (x 0 || (x v || false)) = _
    rw [Bool.or_false]
  rcases hOut with ⟨h1, h2, h3⟩ | ⟨h1, v, hv, h2⟩
  · left
    refine ⟨h1, fun x hx => ?_, h3⟩
    have h0 : (List.ofFn x).getD 0 false = x 0 := gd_ofFn x 0
    have h7 : (List.ofFn x).getD 7 false = x 7 := gd_ofFn x 7
    have h07 : (List.ofFn x).getD 0 false = false ∨ (List.ofFn x).getD 7 false = false := by
      rw [h0, h7]
      exact hx
    rw [h2 (List.ofFn x) (hlen x) h07]
    exact (P2_iff x).symm
  · right
    refine ⟨h1, ?_⟩
    have hx : ∀ (x : Fin 14 → Bool) (w : Fin 14), (w : ℕ) = v →
        (D.eval (List.ofFn x ++ [GateOp.or.eval [x 0, x w]]) = true ↔ P2 x) := by
      intro x w hw
      rw [orv x w, hw, h2 (List.ofFn x) (hlen x)]
      exact (P2_iff x).symm
    rcases hv with h | h | h
    · exact Or.inl fun x => hx x 1 h.symm
    · exact Or.inr (Or.inl fun x => hx x 7 h.symm)
    · exact Or.inr (Or.inr fun x => hx x 9 h.symm)

end PEqualNP.Outside.L_meta_2274

theorem PEqualNP.Outside.L_meta_2274 : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (14 : ℕ)) => ∀ (x5 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x5 (0 : Fin (14 : ℕ)), x5 x4]]) = Bool.true ↔ x2 x5; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 : Fin (14 : ℕ) → Bool), x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x5) = Bool.true ↔ x2 x5)) ∧ x4.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = (0 : Fin (14 : ℕ)) ∨ x5 = (7 : Fin (14 : ℕ)))) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x7 : Fin (14 : ℕ) → Bool), x5.eval (List.ofFn x7) = Bool.true ↔ x2 x7) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (x8.size + (2 : ℕ) ≤ x5.size ∧ x4 x8 ∨ x8.size + (1 : ℕ) ≤ x5.size ∧ (x3 x8 (1 : Fin (14 : ℕ)) ∨ x3 x8 (7 : Fin (14 : ℕ)) ∨ x3 x8 (9 : Fin (14 : ℕ)))) := by
  intro x1 x2 x3 x4 C hM hC
  exact PEqualNP.Outside.L_meta_2274.main C hM hC
