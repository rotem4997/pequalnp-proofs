import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4273

open PEqualNP.CircuitLowerBounds

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

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuit (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := restrict n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, h2, fun y => (hk' y).symm⟩

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



theorem two_drop {Y : Type} (n j : ℕ) (F : ℕ → Y → Bool) (b : Bool) (c : ℕ)
    (hc : (∀ y, F (n + j) y = (b && if c < n + j then F c y else false)) ∨
      (∀ y, F (n + j) y = (b || if c < n + j then F c y else false))) : Drop n F j := by
  by_cases hcl : c < n + j
  · simp only [hcl, if_true] at hc
    rcases hc with hc | hc <;> cases b
    · exact Or.inl ⟨false, fun y => by rw [hc y]; rfl⟩
    · exact Or.inr ⟨c, hcl, fun y => by rw [hc y]; rfl⟩
    · exact Or.inr ⟨c, hcl, fun y => by rw [hc y]; rfl⟩
    · exact Or.inl ⟨true, fun y => by rw [hc y]; rfl⟩
  · simp only [hcl, if_false] at hc
    rcases hc with hc | hc
    · exact Or.inl ⟨b && false, fun y => hc y⟩
    · exact Or.inl ⟨b || false, fun y => hc y⟩

theorem const_drop {Y : Type} (n j : ℕ) (F : ℕ → Y → Bool) (o : GateOp) (I : List ℕ)
    (hop : o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not) (hlen : I.length ≤ 2)
    (hnot : o = GateOp.not → I.length ≤ 1)
    (hv : ∀ y, F (n + j) y = o.eval (I.map fun i => if i < n + j then F i y else false))
    (i : ℕ) (hi : i ∈ I) (b : Bool) (hb : ∀ y, (if i < n + j then F i y else false) = b) :
    Drop n F j := by
  match I, hlen with
  | [], _ => simp at hi
  | [a], _ =>
    obtain rfl : i = a := by simpa using hi
    exact Or.inl ⟨o.eval [b], fun y => by rw [hv y, List.map_singleton, hb y]⟩
  | [a, c], _ =>
    have hac : i = a ∨ i = c := by simpa using hi
    rcases hop with rfl | rfl | rfl
    · rcases hac with rfl | rfl
      · refine two_drop n j F b c (Or.inl fun y => ?_)
        rw [hv y, List.map_cons, List.map_singleton, hb y]
        simp [GateOp.eval]
      · refine two_drop n j F b a (Or.inl fun y => ?_)
        rw [hv y, List.map_cons, List.map_singleton, hb y]
        simp [GateOp.eval, Bool.and_comm]
    · rcases hac with rfl | rfl
      · refine two_drop n j F b c (Or.inr fun y => ?_)
        rw [hv y, List.map_cons, List.map_singleton, hb y]
        simp [GateOp.eval]
      · refine two_drop n j F b a (Or.inr fun y => ?_)
        rw [hv y, List.map_cons, List.map_singleton, hb y]
        simp [GateOp.eval, Bool.or_comm]
    · have := hnot rfl
      simp at this

theorem side (Y : Type) (n j c : ℕ) (F : ℕ → Y → Bool)
    (h : ∀ y, F (n + j) y = if c < n + j then F c y else false) (hnc : ¬ Const (F (n + j))) :
    ¬ Const (F c) := by
  rintro ⟨b, hb⟩
  by_cases hc : c < n + j
  · exact hnc ⟨b, fun y => by rw [h y, if_pos hc, hb]⟩
  · exact hnc ⟨false, fun y => by rw [h y, if_neg hc]⟩

theorem touch {Y : Type} (j : ℕ) (F : ℕ → Y → Bool) (o : GateOp) (I : List ℕ)
    (hop : o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not) (hlen : I.length ≤ 2)
    (hnot : o = GateOp.not → I.length ≤ 1)
    (hv : ∀ y, F (10 + j) y = o.eval (I.map fun i => if i < 10 + j then F i y else false))
    (h0 : ∀ y, F 0 y = false) (h9 : ∀ y, F 9 y = true)
    (hi : 0 ∈ I ∨ 9 ∈ I) (hnc : ¬ Const (F (10 + j))) :
    ∃ c, ¬ Const (F c) ∧ ((o = GateOp.or ∧ (I = [0, c] ∨ I = [c, 0])) ∨
      (o = GateOp.and ∧ (I = [9, c] ∨ I = [c, 9]))) := by
  have v0 : ∀ y, (if 0 < 10 + j then F 0 y else false) = false := fun y => by
    rw [if_pos (by omega), h0]
  have v9 : ∀ y, (if 9 < 10 + j then F 9 y else false) = true := fun y => by
    rw [if_pos (by omega), h9]
  match I, hlen with
  | [], _ => simp at hi
  | [a], _ =>
    exfalso
    apply hnc
    rcases hi with hi | hi
    · obtain rfl : 0 = a := by simpa using hi
      exact ⟨o.eval [false], fun y => by rw [hv y, List.map_singleton, v0 y]⟩
    · obtain rfl : 9 = a := by simpa using hi
      exact ⟨o.eval [true], fun y => by rw [hv y, List.map_singleton, v9 y]⟩
  | [a, c], _ =>
    simp only [List.map_cons, List.map_nil] at hv
    have hi' : (a = 0 ∨ c = 0) ∨ (a = 9 ∨ c = 9) := by
      simpa [eq_comm] using hi
    rcases hop with rfl | rfl | rfl
    · rcases hi' with (rfl | rfl) | (rfl | rfl)
      · exact absurd ⟨false, fun y => by rw [hv y, v0 y]; simp [GateOp.eval]⟩ hnc
      · exact absurd ⟨false, fun y => by rw [hv y, v0 y]; simp [GateOp.eval]⟩ hnc
      · exact ⟨c, side Y 10 j c F (fun y => by rw [hv y, v9 y]; simp [GateOp.eval]) hnc,
          Or.inr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨a, side Y 10 j a F (fun y => by rw [hv y, v9 y]; simp [GateOp.eval]) hnc,
          Or.inr ⟨rfl, Or.inr rfl⟩⟩
    · rcases hi' with (rfl | rfl) | (rfl | rfl)
      · exact ⟨c, side Y 10 j c F (fun y => by rw [hv y, v0 y]; simp [GateOp.eval]) hnc,
          Or.inl ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨a, side Y 10 j a F (fun y => by rw [hv y, v0 y]; simp [GateOp.eval]) hnc,
          Or.inl ⟨rfl, Or.inr rfl⟩⟩
      · exact absurd ⟨true, fun y => by rw [hv y, v9 y]; simp [GateOp.eval]⟩ hnc
      · exact absurd ⟨true, fun y => by rw [hv y, v9 y]; simp [GateOp.eval]⟩ hnc
    · have := hnot rfl
      simp at this

theorem filter_card (p : Gate → Bool) (d : Gate) (l : List Gate) :
    (l.filter p).length = ((Finset.range l.length).filter fun j => p (l.getD j d) = true).card := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    have e : ((Finset.range l.length).filter fun j => p ((l ++ [g]).getD j d) = true) =
        (Finset.range l.length).filter fun j => p (l.getD j d) = true := by
      refine Finset.filter_congr fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
    have e2 : (l ++ [g]).getD l.length d = g := by simp [List.getD_eq_getElem?_getD]
    rw [List.filter_append, List.length_append, ih, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert, e, e2]
    by_cases hg : p g = true
    · rw [if_pos hg, Finset.card_insert_of_notMem (by simp)]
      simp [hg]
    · rw [if_neg hg]
      simp [hg]

end PEqualNP.Outside.L_meta_4273

open PEqualNP.Outside.L_meta_4273 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4273 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) →       (12 : ℕ) + (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any x4.inputs.contains) x1.gates).length = x1.size →         have x5 : (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Fin (8 : ℕ) → Bool) => x1.eval (Bool.false :: List.ofFn x5 ++ [Bool.true]);         (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 x6 ≠ x5 x7) → ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x5 (11 : ℕ) → ∃ (x8 : Set ℕ), x1.output ∈ x8 ∧ (0 : ℕ) ∉ x8 ∧ (9 : ℕ) ∉ x8 ∧ ∀ (x9 : List PEqualNP.CircuitLowerBounds.Gate) (x10 : PEqualNP.CircuitLowerBounds.Gate) (x11 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x9 ++ x10 :: x11 → if [(0 : ℕ), (9 : ℕ)].any x10.inputs.contains = Bool.true then (10 : ℕ) + x9.length ∈ x8 → ∃ x14 ∈ x8, x10.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x10.inputs = [(0 : ℕ), x14] ∨ x10.inputs = [x14, (0 : ℕ)]) ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x10.inputs = [(9 : ℕ), x14] ∨ x10.inputs = [x14, (9 : ℕ)]) else (10 : ℕ) + x9.length ∈ x8 ∧ ∀ x13 ∈ x10.inputs, x13 ∈ x8 := by
  classical
  intro C hC hnot hsz f hfnc hfs
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have hw : ∀ x, C.wires x = run C.gates x := fun _ => rfl
  have hev : ∀ x, C.eval x = (run C.gates x).getD C.output false := fun _ => rfl
  let X : (Fin 8 → Bool) → List Bool := fun y => Bool.false :: List.ofFn y ++ [Bool.true]
  let F : ℕ → (Fin 8 → Bool) → Bool := fun w y => (C.wires (X y)).getD w false
  have hXl : ∀ y, (X y).length = 10 := fun y => by simp [X]
  have hnc : ¬ Const (F C.output) := by
    rintro ⟨c, hc⟩
    obtain ⟨x, y, hxy⟩ := hfnc
    exact hxy ((hc x).trans (hc y).symm)
  have hout : C.output < 10 + C.gates.length := by
    by_contra hcon
    refine hnc ⟨false, fun y => ?_⟩
    exact List.getD_eq_default _ _ (by rw [hw, run_length, hXl]; omega)
  have hinw : ∀ k < 10, ∀ y, F k y = (X y).getD k false := by
    intro k hk y
    change (C.wires (X y)).getD k false = _
    rw [hw]
    exact run_input _ _ _ (by rw [hXl]; exact hk)
  have hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin 8 → Bool),
      F (10 + j) y = C.gates[j].op.eval
        (C.gates[j].inputs.map fun k => if k < 10 + j then F k y else false) := by
    intro j hj y
    have h := run_gate C.gates (X y) j hj
    rw [hXl] at h
    exact h
  have h0 : ∀ y, F 0 y = false := fun y => by rw [hinw 0 (by omega)]; rfl
  have h9 : ∀ y, F 9 y = true := fun y => by
    rw [hinw 9 (by omega)]
    simp [X, List.getD_eq_getElem?_getD]
  obtain ⟨D, T, d1, -, -, d4, d5, d6⟩ := circuit 10 8 C X hops hXl (fun k hk => by
      by_cases hk0 : k = 0
      · exact Or.inl ⟨false, fun y => by rw [hk0]; rfl⟩
      · by_cases hk9 : k = 9
        · exact Or.inl ⟨true, fun y => by rw [hk9]; simp [X, List.getD_eq_getElem?_getD]⟩
        · refine Or.inr ⟨k - 1, by omega, fun y => ?_⟩
          obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
          have hi : i < 8 := by omega
          change (List.ofFn y ++ [Bool.true]).getD i false = _
          exact getD_lt _ _ _ (by simpa using hi)) hrec hinw hout hnc
  let p : Gate → Bool := fun g => [(0 : ℕ), (9 : ℕ)].any g.inputs.contains
  have hp : ∀ g : Gate, p g = true ↔ (0 ∈ g.inputs ∨ 9 ∈ g.inputs) := fun g => by simp [p]
  let d : Gate := ⟨GateOp.or, []⟩
  have hgd : ∀ (j : ℕ) (hj : j < C.gates.length), C.gates.getD j d = C.gates[j] :=
    fun j hj => List.getD_eq_getElem _ _ hj
  have htd : ∀ (j : ℕ) (hj : j < C.gates.length), p C.gates[j] = true → Drop 10 F j := by
    intro j hj hpj
    obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
    rcases (hp _).1 hpj with hi | hi
    · exact const_drop 10 j F _ _ hop hlen (hnot _ (List.getElem_mem hj)) (hrec j hj) 0 hi false
        (fun y => by rw [if_pos (by omega), h0])
    · exact const_drop 10 j F _ _ hop hlen (hnot _ (List.getElem_mem hj)) (hrec j hj) 9 hi true
        (fun y => by rw [if_pos (by omega), h9])
  have hcard : ((Finset.range C.gates.length).filter fun j => ¬ p (C.gates.getD j d) = true).card
      = 12 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range C.gates.length)
      (fun j => p (C.gates.getD j d) = true)
    rw [← filter_card p d C.gates, Finset.card_range] at h1
    change 12 + (C.gates.filter p).length = C.gates.length at hsz
    omega
  have hnd : ∀ (j : ℕ) (hj : j < C.gates.length), ¬ p C.gates[j] = true → ¬ Drop 10 F j := by
    intro j hj hpj hdj
    apply hfs
    refine ⟨D, fun g hg => ?_, ?_, d6⟩
    · obtain ⟨h1, h2⟩ := d1 g hg
      exact ⟨by simpa using h1, h2⟩
    · have hsub : T ⊆ ((Finset.range C.gates.length).filter
          fun j => ¬ p (C.gates.getD j d) = true).erase j := by
        intro k hk
        obtain ⟨e1, e2⟩ := d5 k hk
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_range.2 e1, ?_⟩⟩
        · rintro rfl
          exact e2 hdj
        · rw [hgd k e1]
          exact fun h => e2 (htd k e1 h)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, by
        rw [hgd j hj]; exact hpj⟩), hcard] at h1
      change D.gates.length ≤ 11
      omega
  refine ⟨{w | ¬ Const (F w)}, hnc, fun h => h ⟨false, h0⟩, fun h => h ⟨true, h9⟩, ?_⟩
  intro as g bs hg
  have hj : as.length < C.gates.length := by rw [hg]; simp
  have hgj : C.gates[as.length] = g := by simp [hg]
  have hmem : g ∈ C.gates := by rw [hg]; simp
  obtain ⟨hop, hlen⟩ := hops g hmem
  have hr := hrec as.length hj
  rw [hgj] at hr
  split_ifs with hpg
  · intro hncg
    exact touch as.length F g.op g.inputs hop hlen (hnot g hmem) hr h0 h9 ((hp g).1 hpg) hncg
  · have hd := hnd as.length hj (by rw [hgj]; exact hpg)
    refine ⟨fun hc => hd (Or.inl hc), fun k hk hc => hd ?_⟩
    obtain ⟨b, hb⟩ := hc
    by_cases hkl : k < 10 + as.length
    · exact const_drop 10 as.length F _ _ hop hlen (hnot g hmem) hr k hk b
        (fun y => by rw [if_pos hkl, hb])
    · exact const_drop 10 as.length F _ _ hop hlen (hnot g hmem) hr k hk false
        (fun y => by rw [if_neg hkl])
