import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3243

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

end PEqualNP.Outside.L_meta_3243

theorem PEqualNP.Outside.L_meta_3243 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) :=
  PEqualNP.Outside.L_meta_3243.main
