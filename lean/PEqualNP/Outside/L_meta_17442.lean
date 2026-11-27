import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17442

namespace Evaluation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read {N : ℕ} (x : Fin N → Bool) (i : Fin N) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

def part (w : List Bool) (v : ℕ) (rest : List ℕ) (i : ℕ) : Bool :=
  w.getD v false || (rest.take i).any fun r => w.getD r false

def acc (w : List Bool) (v : ℕ) (rest : List ℕ) (k : ℕ) : List Bool :=
  w ++ (List.range k).map fun i => part w v rest (i + 1)

theorem acc_length (w v rest k) : (acc w v rest k).length = w.length + k := by simp [acc]

theorem acc_low (w v rest k) (i : ℕ) (h : i < w.length) :
    (acc w v rest k).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem acc_chain (w : List Bool) (v : ℕ) (rest : List ℕ) (k : ℕ) (hv : v < w.length)
    (hk : k ≤ rest.length) :
    (acc w v rest k).getD ((v :: (List.range rest.length).map (fun j => w.length + j)).getD k 0) false =
      part w v rest k := by
  cases k with
  | zero =>
    rw [List.getD_cons_zero, acc_low _ _ _ _ _ hv]
    simp [part]
  | succ k =>
    rw [List.getD_cons_succ]
    have : ((List.range rest.length).map (fun j => w.length + j)).getD k 0 = w.length + k := by
      rw [List.getD_eq_getElem?_getD]
      simp [show k < rest.length by omega]
    rw [this, acc, List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD]
    simp

theorem chain_run (w : List Bool) (v : ℕ) (rest : List ℕ) (hv : v < w.length)
    (hr : ∀ r ∈ rest, r < w.length) (k : ℕ) (hk : k ≤ rest.length) :
    ((List.range k).map (fun i => (⟨GateOp.or,
      [(v :: (List.range rest.length).map (fun j => w.length + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = acc w v rest k := by
  induction k with
  | zero => simp [acc]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step, GateOp.eval]
    rw [acc_chain w v rest k hv (by omega)]
    have hk' : k < rest.length := by omega
    have g : rest.getD k 0 = rest[k] := by
      rw [List.getD_eq_getElem?_getD]
      simp [hk']
    rw [g, acc_low _ _ _ _ _ (hr _ (List.getElem_mem hk'))]
    rw [acc, acc, List.range_succ, List.map_append, List.append_assoc]
    congr 2
    simp only [List.map_cons, List.map_nil, part, List.any_cons, List.any_nil, id, Bool.or_false]
    rw [List.take_succ_eq_append_getElem hk', List.any_append]
    simp [Bool.or_assoc]

theorem block_length (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).length = rest.length + 1 + if lead then 0 else 1 := by
  cases lead <;> simp [blockGates]

theorem block_run (w : List Bool) (a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : lead = false → a < w.length) (ht : t < w.length) (hv : v < w.length)
    (hr : ∀ r ∈ rest, r < w.length) :
    ((blockGates w.length a t v rest lead).foldl step w).length =
        w.length + (blockGates w.length a t v rest lead).length ∧
      (∀ i < w.length, ((blockGates w.length a t v rest lead).foldl step w).getD i false = w.getD i false) ∧
      ((blockGates w.length a t v rest lead).foldl step w).getD
        (w.length + (blockGates w.length a t v rest lead).length - 1) false =
        ((!lead && w.getD a false) || (w.getD t false && (v :: rest).any fun r => w.getD r false)) := by
  have full : part w v rest rest.length = (v :: rest).any fun r => w.getD r false := by
    simp [part]
  let w1 := acc w v rest rest.length
  let b : Bool := w.getD t false && (v :: rest).any fun r => w.getD r false
  have l1 : w1.length = w.length + rest.length := acc_length _ _ _ _
  have first : step w1 ⟨GateOp.and, [t, (v :: (List.range rest.length).map
      (fun j => w.length + j)).getD rest.length 0]⟩ = w1 ++ [b] := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, w1]
    rw [acc_chain w v rest _ hv le_rfl, acc_low _ _ _ _ _ ht, full]
    simp [b]
  have low (i : ℕ) (hi : i < w.length) (l : List Bool) : (w1 ++ l).getD i false = w.getD i false := by
    rw [List.getD_append _ _ _ _ (by omega)]
    exact acc_low _ _ _ _ _ hi
  have last (u : List Bool) (c : Bool) (j : ℕ) (hj : j = u.length) : (u ++ [c]).getD j false = c := by
    rw [hj, List.getD_append_right _ _ _ _ le_rfl]
    simp
  cases lead with
  | true =>
    have run : (blockGates w.length a t v rest true).foldl step w = w1 ++ [b] := by
      rw [blockGates, List.foldl_append, chain_run w v rest hv hr _ le_rfl]
      simp only [if_true, List.foldl_cons, List.foldl_nil]
      exact first
    rw [run, block_length]
    refine ⟨by simp [l1]; omega, fun i hi => low i hi _, ?_⟩
    rw [last _ _ _ (by rw [l1]; simp)]
    simp [b]
  | false =>
    have run : (blockGates w.length a t v rest false).foldl step w = (w1 ++ [b]) ++ [w.getD a false || b] := by
      rw [blockGates, List.foldl_append, chain_run w v rest hv hr _ le_rfl]
      simp only [Bool.false_eq_true, if_false, List.foldl_cons, List.foldl_nil]
      rw [show step (acc w v rest rest.length) _ = _ from first]
      simp only [step, GateOp.eval, List.map_cons, List.map_nil]
      rw [low a (ha rfl), last w1 b _ (by rw [l1])]
      simp
    rw [run, block_length]
    refine ⟨by simp [l1]; omega, fun i hi => ?_, ?_⟩
    · rw [List.append_assoc]
      exact low i hi _
    · rw [last _ _ _ (by simp [l1]; omega)]
      simp [b]

def hit (w : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any fun o => w.getD o.1 false && o.2.any fun r => w.getD r false

theorem hit_congr (w w' : List Bool) (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ i < n, w.getD i false = w'.getD i false) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n) :
    hit w own = hit w' own := by
  rw [Bool.eq_iff_iff]
  simp only [hit, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨o, hm, h1, r, hr, h2⟩
    exact ⟨o, hm, by rw [← h _ (ho o hm).1]; exact h1, r, hr, by rw [← h _ ((ho o hm).2 r hr)]; exact h2⟩
  · rintro ⟨o, hm, h1, r, hr, h2⟩
    exact ⟨o, hm, by rw [h _ (ho o hm).1]; exact h1, r, hr, by rw [h _ ((ho o hm).2 r hr)]; exact h2⟩

theorem cover_run (n : ℕ) (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (w : List Bool) (hw : n ≤ w.length) (a : ℕ) (ha : a < w.length) :
    ((coverGatesB w.length false a own).foldl step w).getD
      (if (coverGatesB w.length false a own).length = 0 then a
        else w.length + (coverGatesB w.length false a own).length - 1) false =
      (w.getD a false || hit w own) := by
  induction own generalizing w a with
  | nil => simp [coverGatesB, hit]
  | cons o os ih =>
    have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n := fun o h => ho o (List.mem_cons_of_mem _ h)
    obtain ⟨t, l⟩ := o
    cases l with
    | nil =>
      rw [coverGatesB, ih hos w hw a ha]
      simp [hit]
    | cons v rest =>
      obtain ⟨h1, h2⟩ := ho (t, v :: rest) List.mem_cons_self
      have ht : t < w.length := by have : t < n := h1; omega
      have hr : ∀ r ∈ v :: rest, r < w.length := fun r h => lt_of_lt_of_le (h2 r h) hw
      obtain ⟨q1, q2, q3⟩ := block_run w a t v rest false (fun _ => ha) ht (hr v List.mem_cons_self)
        (fun r h => hr r (List.mem_cons_of_mem _ h))
      have pos : 0 < (blockGates w.length a t v rest false).length := by rw [block_length]; omega
      rw [coverGatesB, List.foldl_append]
      generalize hbg : blockGates w.length a t v rest false = bg at *
      have key := ih hos (bg.foldl step w) (by omega) (w.length + bg.length - 1) (by omega)
      rw [q1] at key
      rw [q3] at key
      rw [List.length_append]
      have idx : (if bg.length + (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
          then a else w.length + (bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length) - 1) =
          if (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
            then w.length + bg.length - 1 else w.length + bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length - 1 := by
        rw [if_neg (by omega)]
        split <;> omega
      rw [idx, key, hit_congr _ w n os (fun i hi => q2 i (by omega)) hos]
      simp [hit, Bool.or_assoc]

theorem cover_length (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.2 ≠ []) (B a : ℕ) :
    (coverGatesB B false a own).length = (own.map fun o => o.2.length).sum + own.length := by
  induction own generalizing B a with
  | nil => simp [coverGatesB]
  | cons o os ih =>
    obtain ⟨t, l⟩ := o
    cases l with
    | nil => exact absurd rfl (ho (t, []) List.mem_cons_self)
    | cons v rest =>
      rw [coverGatesB, List.length_append, ih (fun o h => ho o (List.mem_cons_of_mem _ h)), block_length]
      simp
      omega

theorem cover_all (n : ℕ) (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (hne : ∀ o ∈ own, o.2 ≠ []) :
    (coverCircuitB n own).size = (own.map fun o => o.2.length).sum + own.length - 1 ∧
      ∀ w : List Bool, w.length = n → (coverCircuitB n own).eval w = hit w own := by
  cases own with
  | nil =>
    refine ⟨by simp [coverCircuitB, coverGatesB, Circuit.size], ?_⟩
    intro w hw
    simp only [coverCircuitB, coverGatesB, if_true]
    change w.getD n false = false
    exact List.getD_eq_default _ _ hw.le
  | cons o os =>
    obtain ⟨t, l⟩ := o
    cases l with
    | nil => exact absurd rfl (hne (t, []) List.mem_cons_self)
    | cons v rest =>
      have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n := fun o h => ho o (List.mem_cons_of_mem _ h)
      have len := block_length n 0 t v rest true
      rw [coverCircuitB, if_neg (by
        rw [coverGatesB]
        intro h
        have := congrArg List.length h
        rw [List.length_append, len] at this
        simp at this)]
      constructor
      · change (coverGatesB n true 0 ((t, v :: rest) :: os)).length = _
        rw [coverGatesB, List.length_append, cover_length os (fun o h => hne o (List.mem_cons_of_mem _ h)), len]
        simp
        omega
      · intro w hw
        subst hw
        obtain ⟨h1, h2⟩ := ho (t, v :: rest) List.mem_cons_self
        obtain ⟨q1, q2, q3⟩ := block_run w 0 t v rest true (fun h => by cases h) h1
          (h2 v List.mem_cons_self) (fun r h => h2 r (List.mem_cons_of_mem _ h))
        change ((coverGatesB w.length true 0 ((t, v :: rest) :: os)).foldl step w).getD _ false = _
        rw [coverGatesB, List.foldl_append, List.length_append]
        generalize hbg : blockGates w.length 0 t v rest true = bg at *
        have pos : 0 < bg.length := by rw [len]; omega
        have key := cover_run w.length os hos (bg.foldl step w) (by omega) (w.length + bg.length - 1) (by omega)
        rw [q1, q3] at key
        have idx : w.length + (bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length) - 1 =
          if (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
            then w.length + bg.length - 1 else w.length + bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length - 1 := by
          split <;> omega
        rw [idx, key, hit_congr _ w w.length os q2 hos]
        simp [hit]

theorem main : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro n m R _ own N hshape hedge
  have hlt : ∀ o ∈ own, o.1 < n + m ∧ ∀ r ∈ o.2, r < n + m := by
    intro o ho
    rcases (hshape o ho).2 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨by omega, fun r hr => (h2 r hr).2⟩
    · exact ⟨h2, fun r hr => by have := h3 r hr; omega⟩
  obtain ⟨hs, hv⟩ := cover_all (n + m) own hlt (fun o h => (hshape o h).1)
  refine ⟨hs, fun x => ?_⟩
  change (coverCircuitB (n + m) own).eval (List.ofFn x) = _
  rw [hv _ List.length_ofFn, Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [hit, List.any_eq_true, Bool.and_eq_true]
  have pt (p : Fin n) : (List.ofFn x).getD p.val false = x (Fin.castAdd m p) := read x (Fin.castAdd m p)
  have ln (l : Fin m) : (List.ofFn x).getD (n + l.val) false = x (Fin.natAdd n l) := read x (Fin.natAdd n l)
  constructor
  · rintro ⟨o, ho, h1, r, hr, h2⟩
    rcases (hshape o ho).2 with ⟨s1, s2⟩ | ⟨s1, s2, s3⟩
    · obtain ⟨r1, r2⟩ := s2 r hr
      obtain ⟨l, hl⟩ : ∃ l : Fin m, n + l.val = r := ⟨⟨r - n, by omega⟩, by simp; omega⟩
      refine ⟨⟨o.1, s1⟩, l, (hedge _ _).mpr ⟨o, ho, Or.inl ⟨rfl, hl ▸ hr⟩⟩, ?_, ?_⟩
      · rw [← pt]
        exact h1
      · rw [← ln, hl]
        exact h2
    · obtain ⟨l, hl⟩ : ∃ l : Fin m, n + l.val = o.1 := ⟨⟨o.1 - n, by omega⟩, by simp; omega⟩
      refine ⟨⟨r, s3 r hr⟩, l, (hedge _ _).mpr ⟨o, ho, Or.inr ⟨hl.symm, hr⟩⟩, ?_, ?_⟩
      · rw [← pt]
        exact h2
      · rw [← ln, hl]
        exact h1
  · rintro ⟨p, l, hR, h1, h2⟩
    obtain ⟨o, ho, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := (hedge p l).mp hR
    · exact ⟨o, ho, by rw [e1, pt]; exact h1, _, e2, by rw [ln]; exact h2⟩
    · exact ⟨o, ho, by rw [e1, ln]; exact h2, _, e2, by rw [pt]; exact h1⟩

end Evaluation

theorem Evaluation : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) :=
  Evaluation.main

namespace Topology.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Inv (p q : ℕ → Prop) (B : ℕ) (L : List Gate) (S T : Finset ℕ) : Prop :=
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
    ∀ i ∈ g.inputs, i < B + k) ∧
  (∀ w ∈ S, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, p i ∨ i ∈ S) ∧
  (∀ w ∈ T, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, q i ∨ i ∈ T) ∧
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
     (((p a ∨ a ∈ S) ∧ (q b ∨ b ∈ T)) ∨ ((q a ∨ a ∈ T) ∧ (p b ∨ b ∈ S))))

theorem inv_swap {p q : ℕ → Prop} {B : ℕ} {L : List Gate} {S T : Finset ℕ}
    (h : Inv p q B L S T) : Inv q p B L T S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h3, h2, ?_⟩
  intro k g hk ho
  obtain ⟨a, b, e, h⟩ := h4 k g hk ho
  exact ⟨a, b, e, h.symm⟩

theorem inv_nil (p q : ℕ → Prop) (B : ℕ) : Inv p q B [] ∅ ∅ := by
  simp [Inv]

theorem app_cases {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : (L1 ++ L2)[k]? = some g) :
    L1[k]? = some g ∨ ∃ k2, k = L1.length + k2 ∧ L2[k2]? = some g := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · exact Or.inr ⟨k - L1.length, by omega, h⟩

theorem app_left {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L1[k]? = some g) :
    (L1 ++ L2)[k]? = some g := by
  have hk : k < L1.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hk]
  exact h

theorem app_right {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L2[k]? = some g) :
    (L1 ++ L2)[L1.length + k]? = some g := by
  rw [List.getElem?_append_right (by omega)]
  simpa using h

theorem inv_app {p q : ℕ → Prop} {B : ℕ} {L1 L2 : List Gate} {S1 T1 S2 T2 : Finset ℕ}
    (h : Inv p q B L1 S1 T1) (h' : Inv p q (B + L1.length) L2 S2 T2) :
    Inv p q B (L1 ++ L2) (S1 ∪ S2) (T1 ∪ T2) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · exact a1 k g h
    · obtain ⟨x, y, z⟩ := b1 k2 g h
      exact ⟨x, y, fun i hi => by have := z i hi; omega⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a2 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b2 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a3 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b3 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro k g hk ho
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · obtain ⟨a, b, e, hh⟩ := a4 k g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto
    · obtain ⟨a, b, e, hh⟩ := b4 k2 g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto

theorem cval (B v1 m i : ℕ) (hi : i ≤ m) :
    (i = 0 ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = v1) ∨
    (0 < i ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = B + (i - 1)) := by
  cases i with
  | zero => left; simp
  | succ j =>
    right
    have hj : j < m := by omega
    simp [List.getD_eq_getElem?_getD, hj]

theorem block_get {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} {g : Gate}
    (h : (blockGates B a t v1 rest lead)[k]? = some g) :
    (k < rest.length ∧ g = ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩) ∨
    (k = rest.length ∧ g = ⟨GateOp.and,
      [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩) ∨
    (k = rest.length + 1 ∧ lead = false ∧ g = ⟨GateOp.or, [a, B + rest.length]⟩) := by
  unfold blockGates at h
  rcases app_cases h with h | ⟨k2, hk, h⟩
  · left
    have hk : k < rest.length := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simpa using this
    refine ⟨hk, ?_⟩
    simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at h
    exact h.symm
  · right
    simp only [List.length_map, List.length_range] at hk
    cases k2 with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    | succ k3 =>
      right
      cases lead with
      | true => simp at h
      | false =>
        cases k3 with
        | zero =>
          simp only [List.getElem?_cons_succ, Bool.false_eq_true, ite_false,
            List.getElem?_cons_zero, Option.some.injEq] at h
          exact ⟨by omega, rfl, h.symm⟩
        | succ k4 => simp at h

theorem block_chain {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} (hk : k < rest.length) :
    (blockGates B a t v1 rest lead)[k]? = some ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩ := by
  unfold blockGates
  apply app_left
  simp [hk]

theorem rest_mem {rest : List ℕ} {k : ℕ} (hk : k < rest.length) : rest.getD k 0 ∈ rest := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem inv_block {p q : ℕ → Prop} {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool}
    (hp : ∀ i, p i → i < B) (hq : ∀ i, q i → i < B) (ha : lead = false → a < B)
    (ht : q t) (hv : p v1) (hr : ∀ v ∈ rest, p v) :
    Inv p q B (blockGates B a t v1 rest lead)
      ((Finset.range rest.length).image (fun j => B + j)) ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
      · have := hp _ (hr _ (rest_mem h1)); omega
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := hq _ ht; omega
      · rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have := ha h2
      rcases hi with rfl | rfl <;> omega
  · intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    have hk : k < rest.length := Finset.mem_range.mp hk
    refine ⟨k, _, block_chain hk, rfl, rfl, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Or.inl (hr _ (rest_mem hk))
  · intro w hw
    simp at hw
  · intro k g hk ho
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · simp at ho
    · refine ⟨_, _, rfl, Or.inr ⟨Or.inl ht, ?_⟩⟩
      rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨rest.length - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · simp at ho

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    1 ≤ (blockGates B a t v1 rest lead).length := by
  unfold blockGates
  simp
  omega

theorem inv_cover (p q : ℕ → Prop) (own : List (ℕ × List ℕ)) :
    ∀ (B : ℕ) (lead : Bool) (a : ℕ), (∀ i, p i → i < B) → (∀ i, q i → i < B) →
      (lead = false → a < B) →
      (∀ o ∈ own, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v)) →
      ∃ S T, Inv p q B (coverGatesB B lead a own) S T := by
  induction own with
  | nil =>
    intro B lead a _ _ _ _
    exact ⟨∅, ∅, by simpa [coverGatesB] using inv_nil p q B⟩
  | cons o os ih =>
    intro B lead a hp hq ha ho
    obtain ⟨t, l⟩ := o
    have hos : ∀ o ∈ os, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v) :=
      fun o h => ho o (List.mem_cons_of_mem _ h)
    cases l with
    | nil =>
      simp only [coverGatesB]
      exact ih B lead a hp hq ha hos
    | cons v1 rest =>
      simp only [coverGatesB]
      have hl := block_len B a t v1 rest lead
      obtain ⟨S2, T2, h2⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
        (B + (blockGates B a t v1 rest lead).length - 1)
        (fun i h => by have := hp i h; omega) (fun i h => by have := hq i h; omega)
        (fun _ => by omega) hos
      have h0 := ho (t, v1 :: rest) List.mem_cons_self
      simp only [List.mem_cons, forall_eq_or_imp] at h0
      rcases h0 with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
      · exact ⟨_, _, inv_app (inv_block hp hq ha h1 h3 h4) h2⟩
      · exact ⟨_, _, inv_app (inv_swap (inv_block hq hp ha h1 h3 h4)) h2⟩

theorem gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split <;> simp_all

theorem gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  simp [List.getD_eq_getElem?_getD, hj]

end Topology.Helpers

open Topology.Helpers in
theorem Topology : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro x1 x2 x3 x4 hyp x6 x7
  obtain ⟨S, T, h1, h2, h3, h4⟩ := inv_cover (fun i => i < x1) (fun i => x1 ≤ i ∧ i < x4) x3 x4 true 0
    (fun i h => by show i < x1 + x2; omega) (fun i h => h.2) (fun h => by simp at h)
    (fun o ho => by
      rcases (hyp o ho).2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  have hg : x6.gates = PEqualNP.MetaComplexity.coverGatesB x4 true 0 x3 := gates_eq x4 x3
  rw [← hg] at h1 h2 h3 h4
  have key : ∀ k g, x6.gates[k]? = some g → k < x6.gates.length ∧ x7 k = g := by
    intro k g h
    have hk : k < x6.gates.length := (List.getElem?_eq_some_iff.mp h).1
    refine ⟨hk, ?_⟩
    have := gateAt_get x6 k hk
    rw [h] at this
    exact (Option.some.inj this).symm
  refine ⟨Finset.range x1 ∪ S, Finset.Ico x1 x4 ∪ T, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
    exact (h1 k g hk).1
  · intro j hj i hi
    exact (h1 j _ (gateAt_get x6 j hj)).2.2 i hi
  · intro g hg2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
    exact (h1 k g hk).2.1
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl (Finset.mem_range.mp hw)
    · right
      obtain ⟨k, g, e1, e2, e3, e4⟩ := h2 w hw
      obtain ⟨hk, rfl⟩ := key k g e1
      refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
      rcases e4 i hi with h | h
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ h
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl (Finset.mem_Ico.mp hw)
    · right
      obtain ⟨k, g, e1, e2, e3, e4⟩ := h3 w hw
      obtain ⟨hk, rfl⟩ := key k g e1
      refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
      rcases e4 i hi with h | h
      · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
      · exact Finset.mem_union_right _ h
  · intro k hk ho
    obtain ⟨a, b, e, h⟩ := h4 k _ (gateAt_get x6 k hk) ho
    refine ⟨a, b, e, ?_⟩
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    exact h

namespace Construction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable def groups {α β : Type} [DecidableEq β] (E : Finset α) (key : α → β)
    (center : β → ℕ) (leaf : α → ℕ) : List (ℕ × List ℕ) :=
  (E.image key).toList.map fun k =>
    (center k, ((E.filter fun e => key e = k).toList.map leaf))

theorem groups_length {α β : Type} [DecidableEq β] (E : Finset α) (key : α → β)
    (center : β → ℕ) (leaf : α → ℕ) :
    (groups E key center leaf).length = (E.image key).card := by simp [groups]

theorem groups_leaves {α β : Type} [DecidableEq β] (E : Finset α) (key : α → β)
    (center : β → ℕ) (leaf : α → ℕ) :
    ((groups E key center leaf).map fun t => t.2.length).sum = E.card := by
  simpa [groups, List.map_map, Function.comp_def, Finset.sum_map_toList] using
    (Finset.card_eq_sum_card_image key E).symm

theorem groups_tag {α β : Type} [DecidableEq β] (E : Finset α) (key : α → β)
    (center : β → ℕ) (leaf : α → ℕ) (p q : ℕ → Prop)
    (hc : ∀ k ∈ E.image key, p (center k)) (hl : ∀ e ∈ E, q (leaf e)) :
    ∀ t ∈ groups E key center leaf, t.2 ≠ [] ∧ p t.1 ∧ ∀ w ∈ t.2, q w := by
  intro t ht
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
  have inKey : k ∈ E.image key := Finset.mem_toList.mp hk
  obtain ⟨e,he,ek⟩ := Finset.mem_image.mp inKey
  refine ⟨?_, hc k inKey, ?_⟩
  · intro empty
    have mem : leaf e ∈ (E.filter fun a => key a = k).toList.map leaf :=
      List.mem_map.mpr ⟨e, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨he,ek⟩), rfl⟩
    simp only at empty
    rw [empty] at mem
    exact List.not_mem_nil mem
  · intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact hl a (Finset.mem_filter.mp (Finset.mem_toList.mp ha)).1

theorem groups_edge {α β : Type} [DecidableEq β] (E : Finset α) (key : α → β)
    (center : β → ℕ) (leaf : α → ℕ) (u v : ℕ) :
    (∃ t ∈ groups E key center leaf, t.1 = u ∧ v ∈ t.2) ↔
      ∃ e ∈ E, center (key e) = u ∧ leaf e = v := by
  constructor
  · rintro ⟨t,ht,hu,hv⟩
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
    obtain ⟨e,he,hv⟩ := List.mem_map.mp hv
    obtain ⟨he,ek⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp he)
    exact ⟨e,he,ek ▸ hu,hv⟩
  · rintro ⟨e,he,rfl,rfl⟩
    let k := key e
    refine ⟨_, List.mem_map.mpr ⟨k, Finset.mem_toList.mpr (Finset.mem_image_of_mem key he), rfl⟩, rfl, ?_⟩
    exact List.mem_map.mpr ⟨e, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨he,rfl⟩), rfl⟩

theorem makeOwners (n m : ℕ) (A B : Finset (Fin n × Fin m)) :
    ∃ own : List (ℕ × List ℕ),
      (∀ tx ∈ own, tx.2 ≠ [] ∧ ((tx.1 < n ∧ ∀ u ∈ tx.2, n ≤ u ∧ u < n+m) ∨
        n ≤ tx.1 ∧ tx.1 < n+m ∧ ∀ u ∈ tx.2, u < n)) ∧
      (∀ p : Fin n, ∀ l : Fin m, (p,l) ∈ A ∪ B ↔ ∃ tx ∈ own,
        (tx.1 = p.val ∧ n+l.val ∈ tx.2) ∨ (tx.1 = n+l.val ∧ p.val ∈ tx.2)) ∧
      (own.map fun tx => tx.2.length).sum = A.card + B.card ∧
      own.length = (A.image Prod.fst).card + (B.image Prod.snd).card := by
  classical
  let left := groups A Prod.fst Fin.val (fun e => n+e.2.val)
  let right := groups B Prod.snd (fun j => n+j.val) (fun e => e.1.val)
  have tagL := groups_tag A Prod.fst Fin.val (fun e => n+e.2.val)
      (fun w => w < n) (fun w => n ≤ w ∧ w < n+m)
      (fun k _ => k.isLt) (fun e _ => ⟨by omega, by have := e.2.isLt; omega⟩)
  have tagR := groups_tag B Prod.snd (fun j => n+j.val) (fun e => e.1.val)
      (fun w => n ≤ w ∧ w < n+m) (fun w => w < n)
      (fun k _ => ⟨by omega, by have := k.isLt; omega⟩) (fun e _ => e.1.isLt)
  have leftHit (p : Fin n) (l : Fin m) :
      (∃ t ∈ left, t.1 = p.val ∧ n+l.val ∈ t.2) ↔ (p,l) ∈ A := by
    rw [groups_edge]
    constructor
    · rintro ⟨⟨i,j⟩,h,e,f⟩
      have hi : i = p := Fin.ext e
      have hj : j = l := Fin.ext (Nat.add_left_cancel f)
      simpa [hi,hj] using h
    · intro h
      exact ⟨(p,l),h,rfl,rfl⟩
  have rightHit (p : Fin n) (l : Fin m) :
      (∃ t ∈ right, t.1 = n+l.val ∧ p.val ∈ t.2) ↔ (p,l) ∈ B := by
    rw [groups_edge]
    constructor
    · rintro ⟨⟨i,j⟩,h,e,f⟩
      have hi : i = p := Fin.ext f
      have hj : j = l := Fin.ext (Nat.add_left_cancel e)
      simpa [hi,hj] using h
    · intro h
      exact ⟨(p,l),h,rfl,rfl⟩
  refine ⟨left ++ right, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact ⟨(tagL _ h).1, Or.inl (tagL _ h).2⟩
    · obtain ⟨ne,⟨lo,hi⟩,s⟩ := tagR _ h
      exact ⟨ne, Or.inr ⟨lo,hi,s⟩⟩
  · intro p l
    constructor
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨t,ht,hit⟩ := (leftHit p l).mpr h
        exact ⟨t,List.mem_append_left _ ht,Or.inl hit⟩
      · obtain ⟨t,ht,hit⟩ := (rightHit p l).mpr h
        exact ⟨t,List.mem_append_right _ ht,Or.inr hit⟩
    · rintro ⟨t,ht,hit⟩
      rcases List.mem_append.mp ht with hl | hr
      · rcases hit with hit | hit
        · exact Finset.mem_union_left _ ((leftHit p l).mp ⟨t,hl,hit⟩)
        · have small := (tagL t hl).2.1
          omega
      · rcases hit with hit | hit
        · have large := (tagR t hr).2.1.1
          have := p.isLt
          omega
        · exact Finset.mem_union_right _ ((rightHit p l).mp ⟨t,hr,hit⟩)
  · simp only [List.map_append, List.sum_append, left, right, groups_leaves]
  · simp only [List.length_append, left, right, groups_length]

def turn (P L : Finset ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.headD 0 ∈ L ∧ g.inputs.getD 1 0 ∈ P then g
            else ⟨.and, g.inputs.reverse⟩
  | _ => g

theorem turn_op (P L : Finset ℕ) (g : Gate) : (turn P L g).op = g.op := by
  obtain ⟨op,ins⟩ := g
  cases op <;> simp [turn] <;> split <;> rfl

theorem turn_inputs (P L : Finset ℕ) (g : Gate) :
    (turn P L g).inputs = g.inputs ∨ (turn P L g).inputs = g.inputs.reverse := by
  obtain ⟨op,ins⟩ := g
  cases op <;> simp [turn] <;> split <;> simp

theorem turn_or (P L : Finset ℕ) (g : Gate) (h : g.op = .or) : turn P L g = g := by
  simp [turn,h]

theorem turn_value (P L : Finset ℕ) (g : Gate) (f : ℕ → Bool) :
    (turn P L g).op.eval ((turn P L g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op,ins⟩ := g
  cases op <;> simp [turn] <;> split <;> simp [GateOp.eval, List.map_reverse]

def normalize (P L : Finset ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (turn P L), C.output⟩

theorem normalize_at (P L : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (normalize P L C) j = turn P L (gateAt C j) := by
  exact List.getD_map C.gates ⟨.or, []⟩ (turn P L)

theorem normalize_eval (P L : Finset ℕ) (C : Circuit) (x : List Bool) :
    (normalize P L C).eval x = C.eval x := by
  simp only [Circuit.eval, Circuit.wires, normalize, List.foldl_map, turn_value]

theorem normalize_model (n : ℕ) (P L : Finset ℕ) (C : Circuit)
    (legal : PEqualNP.TopForm.IsAO2 n C) : PEqualNP.TopForm.IsAO2 n (normalize P L C) := by
  obtain ⟨op,back,arity⟩ := legal
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    rw [turn_op]
    exact op k hk
  · intro j hj i hi
    have bound : j < C.gates.length := by simpa [normalize] using hj
    apply back j bound i
    rw [normalize_at] at hi
    rcases turn_inputs P L (gateAt C j) with h | h
    · rwa [h] at hi
    · simpa [h] using hi
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    rcases turn_inputs P L k with h | h <;> simp [h, arity k hk]

theorem turn_orient (P L : Finset ℕ) (g : Gate) (hg : g.op = .and) (u v : ℕ)
    (ins : g.inputs = [u,v]) (side : (u ∈ P ∧ v ∈ L) ∨ (u ∈ L ∧ v ∈ P)) :
    ∃ a ∈ L, ∃ b ∈ P, (turn P L g).inputs = [a,b] := by
  by_cases ready : u ∈ L ∧ v ∈ P
  · exact ⟨u,ready.1,v,ready.2,by simp [turn,hg,ins,ready]⟩
  · have uv := side.resolve_right ready
    exact ⟨v,uv.2,u,uv.1,by simp [turn,hg,ins,ready]⟩

theorem compileStars (n m : ℕ) (A B : Finset (Fin n × Fin m)) :
    ∃ D : Circuit, ∃ S : Bool → Finset ℕ,
      PEqualNP.TopForm.IsAO2 (n+m) D ∧
      (∀ z : Fin (n+m) → Bool, circuitFun (n+m) D z =
        decide (∃ i j, (i,j) ∈ A ∪ B ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)) ∧
      D.size ≤ A.card + B.card + (A.image Prod.fst).card + (B.image Prod.snd).card - 1 ∧
      (let g := gateAt D
       ∀ side, ∀ w ∈ S side,
         (if side then n ≤ w ∧ w < n+m else w < n) ∨
         ∃ j < D.gates.length, w = n+m+j ∧
           (g j).op = GateOp.or ∧ ∀ u ∈ (g j).inputs, u ∈ S side) ∧
      (let g := gateAt D
       ∀ j < D.gates.length, (g j).op = GateOp.and →
         ∃ a ∈ S true, ∃ b ∈ S false, (g j).inputs = [a,b]) := by
  classical
  obtain ⟨own,tag,edges,sum,len⟩ := makeOwners n m A B
  let C := coverCircuitB (n+m) own
  obtain ⟨size,eval⟩ := Evaluation n m (fun i j => (i,j) ∈ A ∪ B) own tag edges
  obtain ⟨P,L,model,lc,rc,gates⟩ := Topology n m own tag
  let D := normalize P L C
  have length : D.gates.length = C.gates.length := by simp [D,normalize]
  have fixed (j : ℕ) (op : (gateAt C j).op = GateOp.or) : gateAt D j = gateAt C j :=
    (normalize_at P L C j).trans (turn_or P L _ op)
  refine ⟨D, (fun s => if s then L else P), normalize_model _ _ _ _ model, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (normalize_eval P L C (List.ofFn z)).trans (eval z)
  · change D.gates.length ≤ _
    rw [length]
    change C.size ≤ _
    rw [show C.size = _ from size,sum,len]
    omega
  · dsimp only
    intro s w hw
    cases s with
    | false =>
      rcases lc w hw with source | ⟨j,hj,eq,op,ins⟩
      · exact Or.inl source
      · exact Or.inr ⟨j,length ▸ hj,eq,by rw [fixed j op]; exact op,by rw [fixed j op]; exact ins⟩
    | true =>
      rcases rc w hw with source | ⟨j,hj,eq,op,ins⟩
      · exact Or.inl source
      · exact Or.inr ⟨j,length ▸ hj,eq,by rw [fixed j op]; exact op,by rw [fixed j op]; exact ins⟩
  · dsimp only
    intro j hj op
    have opC : (gateAt C j).op = .and := by
      simpa only [D,normalize_at,turn_op] using op
    obtain ⟨a,b,ins,side⟩ := gates j (length ▸ hj) opC
    rw [normalize_at]
    exact turn_orient P L _ opC a b ins side

end Construction

end PEqualNP.Outside.L_meta_17442

theorem PEqualNP.Outside.L_meta_17442 : (∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)),   ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Bool → Finset ℕ),     PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∪ x4 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) ∧         x5.size ≤ x3.card + x4.card + (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x4).card - (1 : ℕ) ∧           (have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;             ∀ (x8 : Bool), ∀ x9 ∈ x6 x8, (if x8 = Bool.true then x1 ≤ x9 ∧ x9 < x1 + x2 else x9 < x1) ∨ ∃ x11 < x5.gates.length, x9 = x1 + x2 + x11 ∧ (x7 x11).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x12 ∈ (x7 x11).inputs, x12 ∈ x6 x8) ∧             have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;             ∀ x8 < x5.gates.length, (x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ x11 ∈ x6 Bool.true, ∃ x12 ∈ x6 Bool.false, (x7 x8).inputs = [x11, x12]) :=
  PEqualNP.Outside.L_meta_17442.Construction.compileStars
