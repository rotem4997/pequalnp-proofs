import Mathlib
import PEqualNP.Defs

-- Setting vertices 2 and then 1 to false leaves the five-vertex clique. Each
-- restriction removes a binary gate. A verified finite search shows the clique
-- needs ten binary gates even with every wire complement available for free.
-- The seven-input function has an explicit 13-gate monotone circuit, so this
-- witness is short enough whenever the supplied circuit contains a NOT gate.
-- Binary gate elimination and finite circuit searches adapt the project proofs
-- of L-meta-8724 and L-meta-9148 under the Apache 2.0 license.
namespace PEqualNP.Outside.L_meta_10570_aux

namespace SevenSearch
namespace Elim
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

def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

end Elim
end SevenSearch

namespace SevenTrack
open PEqualNP.CircuitLowerBounds SevenSearch.Elim

def ntag (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

def tagged (gs : List Gate) (i : ℕ) : Bool := (gs[i]?.map ntag).getD false

theorem restrictTagged (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
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
      (ds.filter ntag).length = (S.filter (tagged gs ·)).card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, htag, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, htag, fun w hw => ?_⟩
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
          ntag g = tagged gs K → g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      (ds.filter ntag).length = (S.filter (tagged gs ·)).card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hopTag hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        · have hno : K ∉ S.filter (tagged gs ·) := fun h => hKS (Finset.mem_filter.mp h).1
          rw [List.filter_append, List.length_append, htag, Finset.filter_insert]
          cases hn : tagged gs K <;> simp [hn, hopTag, hno]
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
      generalize hO : gs[K].op = o at *
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
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using hk) fun y => ?_
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
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
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
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp [tagged, List.getElem?_eq_getElem hj, ntag, hO]) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuitTagged (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
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
      (D.gates.filter ntag).length = (S.filter (tagged C.gates ·)).card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, htag, h4⟩ := restrictTagged n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, htag, h2, fun y => (hk' y).symm⟩

end SevenTrack

namespace SevenDrop
open PEqualNP.CircuitLowerBounds SevenSearch.Elim

theorem const_read_drop {Y : Type} (n j : ℕ) (F : ℕ → Y → Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (ev : ∀ y, F (n+j) y = g.op.eval (g.inputs.map (fun q => if q < n+j then F q y else false)))
    {r : ℕ} (hr : r ∈ rds g) (hc : Const (F r)) (hlt : r < n+j) :
    Drop n F j ∧ (g.op = .not → Const (F (n+j))) := by
  obtain ⟨b, hb⟩ := hc
  have hin : ∀ y, (if r < n+j then F r y else false) = b := by simpa [hlt] using hb
  have two : ∀ q : ℕ, (∀ y, F (n+j) y = (b && if q < n+j then F q y else false)) ∨
      (∀ y, F (n+j) y = (b || if q < n+j then F q y else false)) → Drop n F j := by
    intro q h
    by_cases hq : q < n+j
    · simp only [hq, if_true] at h
      rcases h with h|h <;> cases b
      · exact Or.inl ⟨false, fun y => by rw [h y]; rfl⟩
      · exact Or.inr ⟨q,hq,fun y => by rw [h y]; rfl⟩
      · exact Or.inr ⟨q,hq,fun y => by rw [h y]; rfl⟩
      · exact Or.inl ⟨true,fun y => by rw [h y]; rfl⟩
    · simp only [hq, if_false] at h
      rcases h with h|h
      · exact Or.inl ⟨b && false, h⟩
      · exact Or.inl ⟨b || false,h⟩
  generalize hi : g.inputs = I at *
  generalize ho : g.op = o at *
  match I, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl <;> simp [rds, ho, hi] at hr
  | [a], _ =>
    have ha : a = r := by
      rcases hop with rfl | rfl | rfl <;> simpa [rds, ho, hi, eq_comm] using hr
    subst a
    have e : Const (F (n+j)) := ⟨o.eval [b], fun y => by rw [ev y,List.map_singleton,hin]⟩
    exact ⟨Or.inl e,fun _ => e⟩
  | [a,c], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨?_, by simp⟩
      have hr' : r = a ∨ r = c := by simpa [rds, ho, hi] using hr
      rcases hr' with rfl|rfl
      · exact two c (Or.inl fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval])
      · exact two a (Or.inl fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval,Bool.and_comm])
    · refine ⟨?_, by simp⟩
      have hr' : r = a ∨ r = c := by simpa [rds, ho, hi] using hr
      rcases hr' with rfl|rfl
      · exact two c (Or.inr fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval])
      · exact two a (Or.inr fun y => by rw [ev y, List.map_cons, List.map_singleton, hin y]; simp [GateOp.eval,Bool.or_comm])
    · have hr' : r = a := by simpa [rds, ho, hi] using hr
      subst a
      have e : Const (F (n+j)) := ⟨!b,fun y => by rw [ev y, List.map_cons, hin y]; rfl⟩
      exact ⟨Or.inl e, fun _ => e⟩

theorem exists_binary_drop {Y : Type} (n : ℕ) (gs : List Gate) (F : ℕ → Y → Bool) (A B : ℕ → Bool)
    (hops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrec : ∀ (j : ℕ) (hj : j < gs.length) y, F (n+j) y = gs[j].op.eval
      (gs[j].inputs.map fun i => if i < n+j then F i y else false))
    (hA : ∀ (j : ℕ) (hj : j < gs.length), A (n+j) = gs[j].op.eval
      (gs[j].inputs.map fun i => if i < n+j then A i else false))
    (hB : ∀ (j : ℕ) (hj : j < gs.length), B (n+j) = gs[j].op.eval
      (gs[j].inputs.map fun i => if i < n+j then B i else false))
    (hin : ∀ w < n, A w ≠ B w → Const (F w))
    {out : ℕ} (hout : out < n + gs.length) (hd : A out ≠ B out) (hnc : ¬ Const (F out)) :
    ∃ j, ∃ hj : j < gs.length, gs[j].op ≠ .not ∧ Drop n F j := by
  by_contra! h
  apply hnc
  have allw : ∀ w < n+gs.length, A w ≠ B w → Const (F w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro bound diff
      by_cases hw : w < n
      · exact hin w hw diff
      let j := w-n
      have hj : j < gs.length := by dsimp [j];omega
      have eqw : w = n+j := by dsimp [j];omega
      obtain ⟨hop,hl⟩ := hops _ (List.getElem_mem hj)
      have hex : ∃ r ∈ rds gs[j], (if r < n+j then A r else false) ≠ (if r < n+j then B r else false) := by
        by_contra! hzero
        apply diff
        rw [eqw,hA j hj,hB j hj]
        exact eval_congr _ _ _ hop hzero
      obtain ⟨r, hr, hne⟩ := hex
      by_cases hr_lt : r < n+j
      · simp only [hr_lt,if_true] at hne
        have hrw : r < w := by omega
        have hc := ih r hrw (by omega) hne
        obtain ⟨hdrop, hnot⟩ := const_read_drop n j F _ hop hl (hrec j hj) hr hc hr_lt
        rw [eqw]
        by_cases hg : gs[j].op = .not
        · exact hnot hg
        · exact False.elim (h j hj hg hdrop)
      · simp [hr_lt] at hne
  exact allw out hout hd
end SevenDrop

namespace BinaryPin
open PEqualNP.CircuitLowerBounds SevenSearch.Elim SevenTrack SevenDrop

def bc (gs : List Gate) : ℕ := gs.length - (gs.filter ntag).length

theorem tag_card (gs : List Gate) :
    ((Finset.range gs.length).filter (tagged gs ·)).card = (gs.filter ntag).length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have sub : (Finset.range gs.length).filter (tagged (gs ++ [g]) ·) =
        (Finset.range gs.length).filter (tagged gs ·) := by
      apply Finset.filter_congr
      intro i hi
      simp [tagged,List.getElem?_append_left (Finset.mem_range.mp hi)]
    have atg : tagged (gs ++ [g]) gs.length = ntag g := by simp [tagged]
    have fresh : gs.length ∉ (Finset.range gs.length).filter (tagged gs ·) := by simp
    simp only [List.length_append,List.length_singleton,Finset.range_add_one, Finset.filter_insert, sub,
      List.filter_append]
    cases h : ntag g <;> simp [atg,h,fresh,ih]

theorem project {n m : ℕ} (v : Fin n) (pi : Fin n → Fin m) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (ess : f (Function.update x v false) ≠ f (Function.update x v true))
    (nc : ∃ y z : Fin m → Bool, f (Function.update (y ∘ pi) v false) ≠ f (Function.update (z ∘ pi) v false))
    (C : Circuit)
    (hops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ D : Circuit,
      (∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) ∧
      (∀ y : Fin m → Bool, D.eval (List.ofFn y) = f (Function.update (y ∘ pi) v false)) ∧
      bc D.gates + 1 ≤ bc C.gates := by
  let pin := fun y => Function.update (y ∘ pi) v false
  let x0 := Function.update x v false
  let x1 := Function.update x v true
  let X := fun y => List.ofFn (pin y)
  let F := fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false
  let A := fun w => (C.wires (List.ofFn x0)).getD w false
  let B := fun w => (C.wires (List.ofFn x1)).getD w false
  have wire : ∀ xs, C.wires xs = run C.gates xs := fun _ => rfl
  have dif : A C.output ≠ B C.output := by
    change C.eval (List.ofFn x0) ≠ C.eval (List.ofFn x1)
    rw [hev,hev]
    exact ess
  have nconst : ¬ Const (F C.output) := by
    rintro ⟨v,hv⟩
    obtain ⟨u,w,hd⟩ := nc
    apply hd
    exact (hev (pin u)).symm.trans ((hv u).trans ((hv w).symm.trans (hev (pin w))))
  have out : C.output < n + C.gates.length := by
    by_contra! h
    apply dif
    simp [A,B,wire,List.getD_eq_default,run_length,h]
  have recF : ∀ j (hj : j < C.gates.length) y, F (n+j) y = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < n+j then F i y else false) := by
    intro j hj y
    simpa [F,X,wire] using run_gate C.gates (X y) j hj
  have recA : ∀ j (hj : j < C.gates.length), A (n+j) = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < n+j then A i else false) := by
    intro j hj
    simpa [A,wire] using run_gate C.gates (List.ofFn x0) j hj
  have recB : ∀ j (hj : j < C.gates.length), B (n+j) = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < n+j then B i else false) := by
    intro j hj
    simpa [B,wire] using run_gate C.gates (List.ofFn x1) j hj
  have inputs : ∀ (k : Fin n) y, F k.val y = pin y k := by
    intro k y
    dsimp [F, X]
    rw [wire,run_input _ _ _ (by simpa using k.isLt),List.getD_eq_getElem _ _ (by simpa using k.isLt),List.getElem_ofFn]
  have varies : ∀ k < n, A k ≠ B k → Const (F k) := by
    intro k hk hkdiff
    have h5 : k = v.val := by
      by_contra hk5
      apply hkdiff
      simp only [A,B,wire]
      rw [run_input _ _ _ (by simpa using hk),run_input _ _ _ (by simpa using hk)]
      rw [List.getD_eq_getElem _ _ (by simpa using hk),List.getD_eq_getElem _ _ (by simpa using hk)]
      simp only [List.getElem_ofFn]
      rw [show x0 = Function.update x v false from rfl, show x1 = Function.update x v true from rfl,
        Function.update_of_ne (show (⟨k,hk⟩ : Fin n) ≠ v from fun h => hk5 (congrArg Fin.val h)),
        Function.update_of_ne (show (⟨k,hk⟩ : Fin n) ≠ v from fun h => hk5 (congrArg Fin.val h))]
    subst k
    exact ⟨false,fun y => (inputs v y).trans (by simp [pin])⟩
  obtain ⟨j,hj,hjop,hjdrop⟩ := exists_binary_drop n C.gates F A B hops recF recA recB varies out dif nconst
  have hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨ ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false := by
    intro i hi
    let a : Fin n := ⟨i,hi⟩
    have hv : ∀ y, (X y).getD i false = pin y a := by
      intro y
      have q := inputs a y
      change (run C.gates (X y)).getD i false = pin y a at q
      rw [run_input _ _ _ (by simpa [X] using hi)] at q
      exact q
    by_cases h : a = v
    · exact Or.inl ⟨false,fun y => (hv y).trans (by simp [h,pin])⟩
    · refine Or.inr ⟨(pi a).val,(pi a).isLt,fun y => ?_⟩
      rw [hv, List.getD_eq_getElem _ _ (by simpa using (pi a).isLt),List.getElem_ofFn]
      exact Function.update_of_ne h _ _
  obtain ⟨D,S,hg,_,_,hc,ht,hs,he⟩ := circuitTagged n m C X hops (by simp [X]) hin recF
    (fun i hi y => run_input _ _ _ (by simpa [X] using hi)) out nconst
  refine ⟨D,hg,fun y => (he y).trans (hev _), ?_⟩
  let p := fun k => tagged C.gates k = true
  have hjtag : ¬p j := by
    dsimp [p,tagged]
    rw [List.getElem?_eq_getElem hj]
    generalize heq : C.gates[j] = gate at *
    obtain ⟨op,args⟩ := gate
    cases op <;> simp_all [ntag]
  have sep := Finset.card_filter_add_card_filter_not (s := S) p
  have sep0 := Finset.card_filter_add_card_filter_not (s := Finset.range C.gates.length) p
  have loc : S.filter (fun a => ¬p a) ⊆ ((Finset.range C.gates.length).filter (fun a => ¬p a)).erase j := by
    intro i hi
    obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hs i hi).1,hn⟩⟩
    rintro rfl
    exact (hs i hi).2 hjdrop
  have hb := Finset.card_le_card loc
  rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hjtag⟩)] at hb
  have positive : 0 < ((Finset.range C.gates.length).filter (fun a => ¬p a)).card :=
    Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hjtag⟩⟩
  dsimp [p] at sep sep0 hb positive
  rw [tag_card,Finset.card_range] at sep0
  dsimp [bc]
  omega
end BinaryPin

namespace GUpper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def w : Circuit := ⟨[
    ⟨.or, [0, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [9, 6]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.and, [13, 7]⟩,
    ⟨.and, [12, 11]⟩,
    ⟨.and, [14, 8]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [18, 17]⟩], 19⟩
theorem witnessBasis : Monotone2 w := by simp [w, Monotone2]
set_option maxRecDepth 250000 in
set_option maxHeartbeats 3000000 in
theorem witnessEval : ∀ x : Fin 7 → Bool, w.eval (List.ofFn x) = graph x := by decide +kernel
theorem witnessSize : w.size = 13 := rfl

end GUpper
namespace GraphPin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity BinaryPin SevenTrack

def pi7 : Fin 7 → Fin 6 := ![0,1,0,2,3,4,5]
def pi6 : Fin 6 → Fin 5 := ![0,0,1,2,3,4]
def f6 (y : Fin 6 → Bool) := GUpper.graph (Function.update (y ∘ pi7) 2 false)
def clique (x : Fin 5 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
  (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4)
set_option maxRecDepth 100000 in
theorem eq5 : ∀ y : Fin 5 → Bool, f6 (Function.update (y ∘ pi6) 1 false) = clique y := by decide +kernel

theorem replacement
  (base : ∀ D : Circuit,
    (∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
    (∀ y : Fin 5 → Bool, D.eval (List.ofFn y) = clique y) → 10 ≤ bc D.gates) :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hg _ hf
  by_cases hnot : ∃ g ∈ gs, g.op = .not
  · let C : Circuit := ⟨gs,o⟩
    have h6 := project (2: Fin 7) pi7 GUpper.graph (fun i => decide (i=0)) (by decide +kernel)
      ⟨fun _ => false,fun _ => true,by decide +kernel⟩ C hg hf
    obtain ⟨D,hok6,hit6,ds⟩ := h6
    obtain ⟨H,hok5,hit5,hs⟩ := project (1: Fin 6) pi6 f6 (fun i => decide (i=2)) (by decide +kernel)
      ⟨fun _ => false,fun _ => true,by decide +kernel⟩ D hok6 hit6
    have hb := base H hok5 (fun y => (hit5 y).trans (eq5 y))
    obtain ⟨g,hm,ho⟩ := hnot
    have hpos : 0 < (gs.filter ntag).length := List.length_pos_iff.mpr <| List.ne_nil_of_mem
      (List.mem_filter.mpr ⟨hm,by simp [ntag,ho]⟩ : g ∈ gs.filter ntag)
    change bc D.gates + 1 ≤ bc gs at ds
    have low : 13 ≤ gs.length := by unfold bc at *; omega
    refine ⟨GUpper.w.gates,GUpper.w.output,?_,GUpper.witnessSize.le.trans low,GUpper.witnessEval⟩
    intro g hg
    obtain ⟨h1,h2⟩ := GUpper.witnessBasis g hg
    exact ⟨by simpa using h1,h2⟩
  · exact ⟨gs,o,fun g hm => ⟨by
      rcases (hg g hm).1 with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hnot ⟨g,hm,h⟩).elim,(hg g hm).2⟩,le_rfl,hf⟩
end GraphPin

namespace GThreshold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 512

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def table (x : Fin 5 → Bool) : Bool := Nat.testBit 0xfffefee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def ins_fffefee8 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082, 0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104, 0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208, 0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410, 0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]

theorem spec_fffefee8 : ∀ j : Fin 512, Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (ins_fffefee8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 512))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)

def k4inputs : List W := [0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842, 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084, 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108, 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem k4exact : search 6 k4inputs = false := by decide +kernel

def vinput (i : Fin 5) : W := ins_fffefee8.getD i.val 0

def pairIx : Fin 5 → List ℕ := ![[12, 14, 15, 16, 17, 30, 32, 33, 34, 35, 42, 44, 45, 46, 47, 54, 56, 57, 58, 59, 72, 74, 75, 76, 77, 84, 86, 87, 88, 89, 96, 98, 99, 100, 101, 108, 110, 111, 112, 113, 120, 122, 123, 124, 125, 132, 134, 135, 136, 137, 144, 146, 147, 148, 149],
[6, 7, 9, 10, 11, 24, 25, 27, 28, 29, 42, 43, 45, 46, 47, 48, 49, 51, 52, 53, 66, 67, 69, 70, 71, 84, 85, 87, 88, 89, 90, 91, 93, 94, 95, 108, 109, 111, 112, 113, 114, 115, 117, 118, 119, 132, 133, 135, 136, 137, 138, 139, 141, 142, 143],
[0, 1, 2, 4, 5, 24, 25, 26, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 66, 67, 68, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 82, 83, 108, 109, 110, 112, 113, 114, 115, 116, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 130, 131],
[0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 66, 67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 101, 102, 103, 104, 105, 107],
[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64]]

def sourceRow (i : Fin 5) (j : Fin 512) : Fin 512 :=
  ⟨((if j.val < 256 then 0 else 256) + (pairIx i).getD ((j.val % 256) % 55) 0) % 512,
    Nat.mod_lt _ (by decide)⟩

def restriction (i : Fin 5) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(sourceRow i k).val]))).cast List.length_ofFn

theorem restriction_bit (i : Fin 5) (w : W) (j : ℕ) (hj : j < 512) :
    (restriction i w)[j] = w[(sourceRow i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [restriction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem restriction_not (i : Fin 5) (u : W) : restriction i (~~~u) = ~~~restriction i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_not]

theorem restriction_ops (i : Fin 5) (a b z : W) (hz : z ∈ basicOps a b) :
    restriction i z ∈ basicOps (restriction i a) (restriction i b) := by
  have hand (u v : W) : restriction i (u &&& v) = (restriction i u &&& restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_and]
  have hor (u v : W) : restriction i (u ||| v) = (restriction i u ||| restriction i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [restriction_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, restriction_not]

def remaining (i : Fin 5) : List W :=
  ((List.finRange 5).filter (· != i)).map fun j => restriction i (vinput j)

set_option maxRecDepth 8000 in
theorem projected_input : ∀ i : Fin 5, restriction i (vinput i) = 0 := by decide +kernel
set_option maxRecDepth 8000 in
theorem projected_goal : ∀ i : Fin 5, restriction i goal = goal := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_nd : ∀ i : Fin 5, (remaining i).Nodup := by decide +kernel

set_option maxRecDepth 8000 in
theorem remaining_same : ∀ i : Fin 5, remaining i = k4inputs := by decide +kernel

set_option maxRecDepth 8000 in
theorem input_index : ∀ w ∈ ins_fffefee8, ∃ i : Fin 5, vinput i = w := by
  intro w hw
  simp only [ins_fffefee8, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | exact ⟨4,rfl⟩

theorem goal_changes : ∀ k : Fin 256, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel

end GThreshold

namespace GThreshold

def lost (f : W → W) (s : Finset W) := (s.filter fun x => f x = 0).card

theorem lost_insert (f : W → W) (c : W) (s : Finset W) :
    lost f (insert c s) = lost f s + (if f c = 0 ∧ c ∉ s then 1 else 0) := by
  by_cases mem : c ∈ s
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : f c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem live_transport_saves {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} (ng : f g ≠ 0) {k : ℕ} {s av : Finset W}
    (run : live basicOps g k s) (hav : ∀ w ∈ s, holds av (f w)) :
    lost f s ≤ k ∧ SignedBuild (k - lost f s) av (f g) := by
  induction k generalizing s av with
  | zero =>
    change s = {g} at run
    subst s
    have hn : lost f {g} = 0 := by simp [lost]; exact ng
    rw [hn]
    exact ⟨Nat.le_refl _, sb_zero (hav g (by simp))⟩
  | succ k ih =>
    rcases run with skip | ⟨a,ha,b,hb,ne,c,op,fresh,U,he,tail⟩
    · obtain ⟨hl, h⟩ := ih skip hav
      exact ⟨by omega, sb_le (by omega) h⟩
    subst s
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := hm a b c op
    have both (ha0 : f a = 0) (hb0 : f b = 0) : f c = 0 := by
      rw [ha0,hb0] at repr
      simpa [basicOps,ops] using repr
    have limit : lost f prev ≤ lost f (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have old : ∀ u ∈ U, holds av (f u) := fun u hu => hav _ (by simp [hu])
    have H {av' : Finset W} (sub : av ⊆ av') (ok : holds av' (f c)) :
        lost f (insert c U) ≤ k ∧ SignedBuild (k - lost f (insert c U)) av' (f g) := by
      apply ih tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ok
      · exact holds_mono sub (old u hu)
    by_cases zero : f a = 0 ∨ f b = 0
    · obtain ⟨z,build⟩ := H (Finset.Subset.refl av) (mem_ops_zero (hav a ha) (hav b hb) zero repr)
      change lost f prev ≤ k + 1 ∧ SignedBuild (k+1-lost f prev) av (f g)
      exact ⟨by omega,sb_le (by omega) build⟩
    · have cost : lost f prev ≤ lost f (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let av' := insert (f c) av
      have z := (H (av' := av') (Finset.subset_insert _ _) (Or.inr (Or.inr ⟨f c,by simp [av'],Or.inl rfl⟩))).1
      change lost f prev ≤ k + 1 ∧ SignedBuild (k+1-lost f prev) av (f g)
      refine ⟨by omega, sb_le (k := k - lost f (insert c U) + 1) (by omega) ?_⟩
      apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) repr)
      intro av'' sub ok
      exact (H sub ok).2

end GThreshold

namespace GThreshold

theorem projection_rejects {g : W} (hg : g = goal ∨ g = ~~~goal) (i : Fin 5)
    {k : ℕ} {s : Finset W} (xs : List W) (nd : xs.Nodup)
    (hav : ∀ w ∈ s, holds xs.toFinset (restriction i w))
    {budget : ℕ} (cost : k ≤ budget + lost (restriction i) s)
    (reject : search budget xs = false) (run : live basicOps g k s) : False := by
  have signs : restriction i g = goal ∨ restriction i g = ~~~goal := by
    rcases hg with rfl|rfl
    · exact Or.inl (projected_goal i)
    · exact Or.inr (by rw [restriction_not, projected_goal])
  have ne : goal ≠ 0 ∧ goal ≠ ~~~0 ∧ ~~~goal ≠ 0 ∧ ~~~goal ≠ ~~~0 := by decide +kernel
  have ng : restriction i g ≠ 0 := by
    rcases signs with s|s
    · exact fun z => ne.1 (s.symm.trans z)
    · exact fun z => ne.2.2.1 (s.symm.trans z)
  obtain ⟨_, h⟩ := live_transport_saves (restriction_ops i) ng run hav
  have h' : SignedBuild budget xs.toFinset (restriction i g) := sb_le (by omega) h
  have opp : ~~~restriction i g = goal ∨ ~~~restriction i g = ~~~goal := by
    rcases signs with h|h <;> simp [h]
  have no {u : W} (hu : u = goal ∨ u = ~~~goal) (path : build basicOps u budget xs.toFinset) : False := by
    have hit := search_complete hu budget xs nd path
    exact Bool.noConfusion (reject.symm.trans hit)
  rcases h' with z | z | b | b
  · rcases signs with s|s
    · exact ne.1 (s.symm.trans z)
    · exact ne.2.2.1 (s.symm.trans z)
  · rcases signs with s|s
    · exact ne.2.1 (s.symm.trans z)
    · exact ne.2.2.2 (s.symm.trans z)
  · exact no signs b
  · exact no opp b

end GThreshold

namespace GThreshold

def codeAt : Array Nat := #[0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 8, 16, 0, 1, 2, 4, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 31, 31, 31, 31, 31, 31, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22]
def repAt : Array Nat := #[0, 1, 2, 256, 3, 262, 268, 274, 4, 280, 286, 292, 298, 304, 310, 316, 5, 322, 328, 334, 340, 346, 352, 358, 364, 370, 376, 382, 388, 394, 400, 406]

def mapRow (m : Array Nat) (k : Fin 512) : Fin 512 :=
  Fin.ofNat 512 (repAt[m[codeAt[k.val]?.getD 0]?.getD 0]?.getD 0)

def rowAction (m : Array Nat) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 512 => w[(mapRow m k).val]))).cast List.length_ofFn

theorem rowAction_bit (m : Array Nat) (w : W) (j : ℕ) (hj : j < 512) :
    (rowAction m w)[j] = w[(mapRow m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowAction, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem row_and (m : Array Nat) (x y : W) : rowAction m (x &&& y) = rowAction m x &&& rowAction m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowAction_bit,BitVec.getElem_and]
theorem row_or (m : Array Nat) (x y : W) : rowAction m (x ||| y) = rowAction m x ||| rowAction m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowAction_bit,BitVec.getElem_or]
theorem row_not (m : Array Nat) (x : W) : rowAction m (~~~x) = ~~~rowAction m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowAction_bit,BitVec.getElem_not]

theorem relive_rows (m back : Array Nat) {g : W} {k : ℕ} {s : Finset W}
    (h : live basicOps g k s)
    (ok : ∀ w ∈ s, rowAction back (rowAction m w) = w) :
    live basicOps (rowAction m g) k (s.image (rowAction m)) := by
  induction k generalizing s with
  | zero => change s = {g} at h; subst s; simp [live]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,ho,r,hs,tail⟩
    · exact Or.inl (ih skip ok)
    have op : rowAction m z ∈ basicOps (rowAction m a) (rowAction m b) := by
      simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      rcases hz with rfl | rfl | rfl | rfl
      · exact Or.inl (row_and ..)
      · exact Or.inr (Or.inl (row_or ..))
      · exact Or.inr (Or.inr (Or.inl (by rw [row_and,row_not])))
      · exact Or.inr (Or.inr (Or.inr (by rw [row_and,row_not])))
    have zok : rowAction back (rowAction m z) = z := by
      simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> simp only [row_and,row_or,row_not,ok a ha,ok b hb]
    refine .inr ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,?_,_,op,?_,
      r.image (rowAction m),?_,?_⟩
    · intro eq
      exact hab ((ok a ha).symm.trans ((congrArg (rowAction back) eq).trans (ok b hb)))
    · intro mem
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp mem
      have e := (ok u hu).symm.trans ((congrArg (rowAction back) eq).trans zok)
      exact ho (e ▸ hu)
    · simp [hs]
    · have sub : r ⊆ s := by intro u hu; rw [hs]; simp [hu]
      apply (show live basicOps (rowAction m g) k ((insert z r).image (rowAction m)) →
        live basicOps (rowAction m g) k (insert (rowAction m z) (Finset.image (rowAction m) r)) by simp)
      apply ih tail
      intro u hu
      exact (Finset.mem_insert.mp hu).elim (fun e => e ▸ zok) (fun hr => ok u (sub hr))

theorem reject_relabel_rows (m back : Array Nat) {g : W} (ht : g = goal ∨ g = ~~~goal)
    (preserves : rowAction m goal = goal) (ws us : List W)
    (backward : (ws.all fun w => rowAction back (rowAction m w) == w) = true)
    (same : (ws.map (rowAction m)).toFinset = us.toFinset) (k : Nat)
    (reject : ¬live basicOps g k us.toFinset) : ¬live basicOps g k ws.toFinset := by
  intro h
  have mapped := relive_rows m back h (by
    intro w hw
    exact beq_iff_eq.mp (List.all_eq_true.mp backward w (List.mem_toFinset.mp hw)))
  have gg : rowAction m g = g := by rcases ht with rfl | rfl <;> simp [preserves,row_not]
  apply reject
  rw [gg] at mapped
  rw [← same]
  have hset : (ws.map (rowAction m)).toFinset = ws.toFinset.image (rowAction m) := by
    ext u
    simp
  rw [hset]
  exact mapped

end GThreshold

namespace GThreshold
set_option maxRecDepth 20000 in
def classMasks : Array W := #[0x1041041041041041041041041041041041041041041041041041041041041041,0x2082082082082082082082082082082082082082082082082082082082082082,0x4104104104104104104104104104104104104104104104104104104104104104,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000,0x8208208208208208208208208208208208208208208208208208208208208208,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000,0x410410410410410410410410410410410410410410410410410410410410410,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000000,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000000000,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000,0x820820820820820820820820820820820820820820820820820820820820820,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc0000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf00000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 20000 in
def cls (n : Nat) : W := classMasks[n]?.getD 0
set_option maxRecDepth 20000 in
def code (k : Fin 512) : Nat := codeAt[k.val]?.getD 0

set_option maxRecDepth 20000 in
theorem runAll (f : Fin 512 → Bool)
    (h : ((List.range 512).all fun i => f (Fin.ofNat 512 i)) = true) (i : Fin 512) : f i = true := by
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa using hi
set_option maxRecDepth 20000 in
def values (b0 b1 b2 b3 b4 : Bool) : Nat := (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0) + (if b4 then 16 else 0)
set_option maxRecDepth 20000 in
def choose (b : Bool) (w : W) : W := if b then w else ~~~w
set_option maxRecDepth 20000 in
def matchWord (c : Fin 32) : W := choose (c.val.testBit 0) (vinput 0) &&& choose (c.val.testBit 1) (vinput 1) &&& choose (c.val.testBit 2) (vinput 2) &&& choose (c.val.testBit 3) (vinput 3) &&& choose (c.val.testBit 4) (vinput 4)
set_option maxRecDepth 20000 in
theorem cbits (b : Bool) (w : W) (j : Fin 512) :
    (choose b w)[j.val] = (if b then w[j.val] else !w[j.val]) := by
  cases b <;> simp [choose]
set_option maxRecDepth 20000 in
theorem masksOK : ∀ c : Fin 32, cls c.val = matchWord c := by decide +kernel
set_option maxRecDepth 20000 in
theorem choicesOK : ∀ (c : Fin 32) (b0 b1 b2 b3 b4 : Bool),
    ((if c.val.testBit 0 then b0 else !b0) && (if c.val.testBit 1 then b1 else !b1) && (if c.val.testBit 2 then b2 else !b2) && (if c.val.testBit 3 then b3 else !b3) && (if c.val.testBit 4 then b4 else !b4)) = decide (values b0 b1 b2 b3 b4 = c.val) := by decide +kernel
set_option maxRecDepth 20000 in
theorem codesOK (j : Fin 512) : code j = values ((vinput 0)[j.val]) ((vinput 1)[j.val]) ((vinput 2)[j.val]) ((vinput 3)[j.val]) ((vinput 4)[j.val]) :=
  of_decide_eq_true (runAll (fun j => decide (code j = values ((vinput 0)[j.val]) ((vinput 1)[j.val]) ((vinput 2)[j.val]) ((vinput 3)[j.val]) ((vinput 4)[j.val]))) (by decide +kernel) j)
set_option maxRecDepth 20000 in
theorem classExact (c : Fin 32) (j : Fin 512) : (cls c.val)[j.val] = decide (code j = c.val) := by
  rw [masksOK,codesOK]
  simpa only [matchWord,BitVec.getElem_and,cbits] using (choicesOK c ((vinput 0)[j.val]) ((vinput 1)[j.val]) ((vinput 2)[j.val]) ((vinput 3)[j.val]) ((vinput 4)[j.val]))
set_option maxRecDepth 20000 in
theorem codeBound (j : Fin 512) : code j < 32 := by
  rw [codesOK]
  have : ∀ b0 b1 b2 b3 b4 : Bool, values b0 b1 b2 b3 b4 < 32 := by decide +kernel
  apply this
end GThreshold

namespace GThreshold
def packRows (f : Nat → Bool) : Nat → W
  | 0 => 0
  | n+1 => if f n then packRows f n ||| cls n else packRows f n
theorem packBit (f : Nat → Bool) (n : Nat) (hn : n ≤ 32) (j : Fin 512) :
    (packRows f n)[j.val] = (decide (code j < n) && f (code j)) := by
  induction n with
  | zero => simp [packRows]
  | succ n ih =>
    have hn' : n < 32 := by omega
    have cf := classExact ⟨n,hn'⟩ j
    by_cases eq : code j = n
    · by_cases hf : f n <;> simp [packRows,hf,eq,ih (by omega),cf]
    · have hc : code j < n + 1 ↔ code j < n := by omega
      by_cases hf : f n <;> simp [packRows,hf,ih (by omega),cf,eq,hc]
def fastRows (m : Array Nat) (w : W) : W :=
  packRows (fun c => w[(Fin.ofNat 512 (repAt[m[c]?.getD 0]?.getD 0)).val]) 32
theorem fastRows_eq (m : Array Nat) (w : W) : fastRows m w = rowAction m w := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have eq := packBit (fun c => w[(Fin.ofNat 512 (repAt[m[c]?.getD 0]?.getD 0)).val]) 32 (by decide) ⟨j,hj⟩
  rw [decide_eq_true (codeBound ⟨j,hj⟩), Bool.true_and] at eq
  simpa only [rowAction_bit,fastRows,mapRow,code] using eq
theorem reject_fast_rows (m back : Array Nat) {g : W} (ht : g = goal ∨ g = ~~~goal)
    (preserves : fastRows m goal = goal) (ws us : List W)
    (backward : (ws.all fun w => fastRows back (fastRows m w) == w) = true)
    (same : (ws.map (fastRows m)).toFinset = us.toFinset) (k : Nat)
    (reject : ¬live basicOps g k us.toFinset) : ¬live basicOps g k ws.toFinset := by
  have e (a : Array Nat) : fastRows a = rowAction a := funext (fastRows_eq a)
  rw [e] at preserves same
  simp only [e] at backward
  exact reject_relabel_rows m back ht preserves ws us backward same k reject
end GThreshold

namespace GThreshold
def validRow (m back : Array Nat) (l : List (W × W)) : Bool :=
  l.all (fun p => fastRows m p.1 == p.2 && fastRows back p.2 == p.1)
theorem relink {m back : Array Nat} {l : List (W×W)}
    (valid : validRow m back l = true) {source target : List W}
    (lk : ∀ w ∈ source, ∃ z ∈ target, (w,z) ∈ l)
    (rk : ∀ z ∈ target, ∃ w ∈ source, (w,z) ∈ l)
    (preserves : fastRows m goal = goal) {g : W} (tg : g = goal ∨ g = ~~~goal)
    {k : Nat} (reject : ¬live basicOps g k target.toFinset) :
      ¬live basicOps g k source.toFinset := by
  have certified {w z : W} (edge : (w,z) ∈ l) :
      fastRows m w = z ∧ fastRows back z = w := by
    simpa using List.all_eq_true.mp valid (w,z) edge
  apply reject_fast_rows m back tg preserves source target _ _ k reject
  · apply List.all_eq_true.mpr
    intro w hw
    obtain ⟨z,_,e⟩ := lk w hw
    rw [(certified e).1,(certified e).2]
    <;> simp
  · ext z
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨t,ht,e⟩ := lk w hw
      simpa [(certified e).1] using ht
    · intro hz
      obtain ⟨w,hw,e⟩ := rk z hz
      exact ⟨w,hw,(certified e).1⟩
theorem relink_checked {m back : Array Nat} {l : List (W×W)}
    (valid : validRow m back l = true) {source target : List W}
    (lk : (source.all fun w => target.any fun z => l.contains (w,z)) = true)
    (rk : (target.all fun z => source.any fun w => l.contains (w,z)) = true)
    (preserves : fastRows m goal = goal) {g : W} (tg : g = goal ∨ g = ~~~goal)
    {k : Nat} (reject : ¬live basicOps g k target.toFinset) :
      ¬live basicOps g k source.toFinset := by
  apply relink valid (source := source) (target := target) _ _ preserves tg reject
  · simpa using lk
  · simpa using rk
end GThreshold

namespace GThreshold

def follows (k : Nat) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if ws.contains z then [] else
      ((keepChoices a b r).map (fun keep => z :: keep)).filter
        (fun n => decide (n.length ≤ k+1) && cuts n == -1)

theorem follows_complete {k : Nat} {ws : List W} (nd : ws.Nodup) {t : W}
    (tg : t = goal ∨ t = ~~~goal) (h : live basicOps t (k+1) ws.toFinset) :
    ws.toFinset = {t} ∨ ∃ ns ∈ follows k ws, ns.Nodup ∧ live basicOps t k ns.toFinset := by
  rcases first_live h with h|⟨a,ha,b,hb,ne,z,hop,fresh,rest,he,tail⟩
  · exact Or.inl h
  right
  have go {a b : W} (r : List W) (hp : ws.Perm (a::b::r))
      (hpair : (a,b,r) ∈ pairs ws)
      (hop : z ∈ basicOps a b) (hs : ws.toFinset = insert a (insert b rest)) :
      ∃ ns ∈ follows k ws, ns.Nodup ∧ live basicOps t k ns.toFinset := by
    obtain ⟨keep,hk,hn,hfin⟩ := recover_kept hp nd hs
    have zk : z ∉ keep := by
      intro hm
      exact fresh (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hm)))
    have nds := List.nodup_cons.mpr ⟨zk,hn⟩
    have run : live basicOps t k (z::keep).toFinset := by simpa [hfin] using tail
    have size := live_card run
    rw [List.toFinset_card_of_nodup nds] at size
    have hz : ws.contains z = false := Bool.eq_false_iff.mpr (fun hz => fresh (List.mem_toFinset.mpr (List.contains_iff_mem.mp hz)))
    refine ⟨z::keep, List.mem_flatMap.mpr ⟨(a,b,r),hpair,?_⟩, nds,run⟩
    apply List.mem_flatMap.mpr
    refine ⟨z,List.mem_toFinset.mp hop,?_⟩
    simp only [hz, Bool.false_eq_true, ↓reduceIte, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    exact ⟨List.mem_map.mpr ⟨keep,hk,rfl⟩,size,cuts_full tg run⟩
  obtain ⟨r,hh,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) ne
  rcases hh with hh|hh
  · exact go r hp hh hop he
  · exact go r (hp.trans (.swap _ _ _)) hh (ops_swap a b ▸ hop) (by rw [he,Finset.insert_comm])

end GThreshold

namespace K5Cache
open GThreshold
def four12 : W := 0x1f0000000000003e0000000000007c000000000000f8000000000001f1084210842108421084210842108421084210842108421084210842108421084
def four34 : W := 0x3e0000000000007c000000000000f8000000000001f0000000000003e00842108421084210842108421084210842108421084210842108421084210842
def four48 : W := 0x3e0000000000007c000000000000f8000000000001f0000000000003e02108421084210842108421084210842108421084210842108421084210842108
def four68 : W := 0x7c000000000000f8000000000001f0000000000003e0000000000007c001084210842108421084210842108421084210842108421084210842108421084
def four80 : W := 0x7c000000000000f8000000000001f0000000000003e0000000000007c002108421084210842108421084210842108421084210842108421084210842108
def four170 : W := 0xf83ff000000001f07fe000000003e0ffc000000007c1ff800000000f83ff0842108421084210842108421084210842108421084210842108421084210842
def four204 : W := 0xffc1f000000001ff83e000000003ff07c000000007fe0f800000000ffc1f1084210842108421084210842108421084210842108421084210842108421084
def four238 : W := 0xfffff000000001ffffe000000003ffffc000000007ffff800000000fffff18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6
def four240 : W := 0xfffe0000000001fffc0000000003fff80000000007fff0000000000fffe02108421084210842108421084210842108421084210842108421084210842108
def four252 : W := 0xfffff000000001ffffe000000003ffffc000000007ffff800000000fffff318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c
def four514 : W := 0x1f0000000000003e0000000000007c000000000000f8000000000001f000000842108421084210842108421084210842108421084210842108421084210842
def four768 : W := 0x1f0000000000003e0000000000007c000000000000f8000000000001f000004210842108421084210842108421084210842108421084210842108421084210
def four2570 : W := 0x7c1f0001f00000f83e0003e00001f07c0007c00003e0f8000f800007c1f0001f0842108421084210842108421084210842108421084210842108421084210842
def four3084 : W := 0x7fe00001f00000ffc00003e00001ff800007c00003ff00000f800007fe00001f1084210842108421084210842108421084210842108421084210842108421084
def four3598 : W := 0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6
def four3840 : W := 0x7fff0000000000fffe0000000001fffc0000000003fff80000000007fff000004210842108421084210842108421084210842108421084210842108421084210
def four3850 : W := 0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f4a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a52
def four3852 : W := 0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294
def four4112 : W := 0x8000000000001f0000000000003e0000000000007c000000000000f8000000002108421084210842108421084210842108421084210842108421084210842108
def four8738 : W := 0x1f003e0003e0003e007c0007c0007c00f8000f8000f801f0001f0001f003e00842108421084210842108421084210842108421084210842108421084210842
def four12336 : W := 0x8000003e0003ff0000007c0007fe000000f8000ffc000001f0001ff8000003e02108421084210842108421084210842108421084210842108421084210842108
def four12850 : W := 0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e0294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a
def four13056 : W := 0x801f00000003ff003e00000007fe007c0000000ffc00f80000001ff801f000004210842108421084210842108421084210842108421084210842108421084210
def four13090 : W := 0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e04a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a52
def four13104 : W := 0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e06318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318
def four17476 : W := 0x3e007c0007c0007c00f8000f8000f801f0001f0001f003e0003e0003e007c001084210842108421084210842108421084210842108421084210842108421084
def four20560 : W := 0x800007c0007c1f00000f8000f83e00001f0001f07c00003e0003e0f800007c002108421084210842108421084210842108421084210842108421084210842108
def four21588 : W := 0x83e007c0007c1f07c00f8000f83e0f801f0001f07c1f003e0003e0f83e007c00318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c
def four21760 : W := 0x83e00000007c1f07c0000000f83e0f80000001f07c1f00000003e0f83e0000004210842108421084210842108421084210842108421084210842108421084210
def four21828 : W := 0x83e007c0007c1f07c00f8000f83e0f801f0001f07c1f003e0003e0f83e007c005294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294
def four21840 : W := 0x83e007c0007c1f07c00f8000f83e0f801f0001f07c1f003e0003e0f83e007c006318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318
def four43176 : W := 0x7c00f83fff83e0f801f07fff07c1f003e0fffe0f83e007c1fffc1f07c00f83ff0000000000000000000000000000000000000000000000000000000000000000
def four43520 : W := 0x7c1f00000f83e0f83e00001f07c1f07c00003e0f83e0f800007c1f07c1f000000000000000000000000000000000000000000000000000000000000000000000
def four43656 : W := 0x7c1ff801ff83e0f83ff003ff07c1f07fe007fe0f83e0ffc00ffc1f07c1ff801f0000000000000000000000000000000000000000000000000000000000000000
def four43680 : W := 0x7c1ff83e0f83e0f83ff07c1f07c1f07fe0f83e0f83e0ffc1f07c1f07c1ff83e00000000000000000000000000000000000000000000000000000000000000000
def four43690 : W := 0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842
def four51400 : W := 0x7c00ffc1fffc00f801ff83fff801f003ff07fff003e007fe0fffe007c00ffc1f0000000000000000000000000000000000000000000000000000000000000000
def four52224 : W := 0x7fe000000ffc00ffc000001ff801ff8000003ff003ff0000007fe007fe0000000000000000000000000000000000000000000000000000000000000000000000
def four52360 : W := 0x7fe0f801fffc00ffc1f003fff801ff83e007fff003ff07c00fffe007fe0f801f0000000000000000000000000000000000000000000000000000000000000000
def four52416 : W := 0x7fe0ffc00ffc00ffc1ff801ff801ff83ff003ff003ff07fe007fe007fe0ffc000000000000000000000000000000000000000000000000000000000000000000
def four52428 : W := 0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084
def four57568 : W := 0xfffe0fffe00001fffc1fffc00003fff83fff800007fff07fff00000fffe00000000000000000000000000000000000000000000000000000000000000000
def four60138 : W := 0x7c1fffffffffe0f83fffffffffc1f07fffffffff83e0ffffffffff07c1ffffff0842108421084210842108421084210842108421084210842108421084210842
def four61166 : W := 0x7fffffffffffe0ffffffffffffc1ffffffffffff83ffffffffffff07ffffffff18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6
def four61600 : W := 0x8000f83e0fffff0001f07c1ffffe0003e0f83ffffc0007c1f07ffff8000f83e00000000000000000000000000000000000000000000000000000000000000000
def four61632 : W := 0x8000ffc00fffff0001ff801ffffe0003ff003ffffc0007fe007ffff8000ffc000000000000000000000000000000000000000000000000000000000000000000
def four61680 : W := 0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108
def four64250 : W := 0xfc1ffffffffffff83ffffffffffff07fffffffffffe0ffffffffffffc1ffffff294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a
def four64764 : W := 0xffe0ffffffffffffc1ffffffffffff83ffffffffffff07fffffffffffe0fffff318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c
def four65278 : W := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff39ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce
def four65280 : W := 0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210
def four65416 : W := 0xfffff801fffffffffff003ffffffffffe007ffffffffffc00fffffffffff801f4210842108421084210842108421084210842108421084210842108421084210
def four65440 : W := 0xfffff83e0ffffffffff07c1fffffffffe0f83fffffffffc1f07fffffffff83e04210842108421084210842108421084210842108421084210842108421084210
def four65450 : W := 0xfffff83ffffffffffff07fffffffffffe0ffffffffffffc1ffffffffffff83ff4a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a52
def four65472 : W := 0xffffffc00fffffffffff801fffffffffff003ffffffffffe007ffffffffffc004210842108421084210842108421084210842108421084210842108421084210
def four65484 : W := 0xffffffc1ffffffffffff83ffffffffffff07fffffffffffe0ffffffffffffc1f5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294
def four65518 : W := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6
def four65520 : W := 0xfffffffe0ffffffffffffc1ffffffffffff83ffffffffffff07fffffffffffe06318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318
def four65530 : W := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5a
def four65532 : W := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739c
def q0 : List W := [four43690,four52428,four61680,four65280]
def q1 : List W := [four43690,four52428,four61680,four65280]
def q2 : List W := [four43690,four52428,four61680,four65280,four65450]
def q3 : List W := [four43690,four64764,four65484,four65520]
def q4 : List W := [four43690,four64764,four65484,four65520]
def q5 : List W := [four43690,four65278,four65484,four65520]
def q6 : List W := [four21588,four43690,four65484,four65520]
def q7 : List W := [four43690,four64764,four65518,four65520]
def q8 : List W := [four21828,four43690,four64764,four65520]
def q9 : List W := [four43690,four64764,four65484,four65530]
def q10 : List W := [four21840,four43690,four64764,four65484]
def q11 : List W := [four43690,four52428,four61680,four65280,four65520]
def q12 : List W := [four48,four43690,four64764,four65520]
def q13 : List W := [four48,four43690,four64764,four65484,four65520]
def q14 : List W := [four768,four43690,four65484,four65520]
def q15 : List W := [four768,four43690,four64764,four65484,four65520]
def q16 : List W := [four12,four43690,four64764,four65484]
def q17 : List W := [four12,four43690,four64764,four65484,four65520]
def q18 : List W := [four43690,four52428,four61680,four65280,four65450]
def q19 : List W := [four43690,four52428,four65278,four65280,four65520]
def q20 : List W := [four17476,four43690,four61680,four65484,four65520]
def q21 : List W := [four20560,four43690,four52428,four65484,four65520]
def q22 : List W := [four43690,four52428,four61680,four65518,four65520]
def q23 : List W := [four21828,four43690,four52428,four61680,four65520]
def q24 : List W := [four43690,four52428,four61680,four65484,four65530]
def q25 : List W := [four21840,four43690,four52428,four61680,four65484]
def q26 : List W := [four43690,four52416,four61680,four65484]
def q27 : List W := [four43690,four52416,four52428,four61680,four65484]
def q28 : List W := [four43690,four52416,four61680,four65484,four65520]
def q29 : List W := [four12,four43690,four52428,four61680,four65484]
def q30 : List W := [four13104,four43690,four61680,four65484,four65520]
def q31 : List W := [four43690,four52428,four61632,four65520]
def q32 : List W := [four43690,four52428,four61632,four61680,four65520]
def q33 : List W := [four43690,four52428,four61632,four65484,four65520]
def q34 : List W := [four48,four43690,four52428,four61680,four65520]
def q35 : List W := [four3852,four43690,four52428,four65484,four65520]
def q36 : List W := [four43690,four52428,four61680,four65450,four65520]
def q37 : List W := [four43690,four52428,four64250,four65280,four65520]
def q38 : List W := [four61166,four61680,four65484,four65530]
def q39 : List W := [four52428,four64250,four65518,four65520]
def q40 : List W := [four43690,four65278,four65484,four65520]
def q41 : List W := [four20560,four52428,four64250,four65280,four65520]
def q42 : List W := [four52428,four64250,four65450,four65520]
def q43 : List W := [four52428,four64250,four65280,four65450,four65520]
def q44 : List W := [four21840,four52428,four64250,four65280,four65520]
def q45 : List W := [four8738,four52428,four61680,four65450,four65520]
def q46 : List W := [four43690,four52428,four64250,four65450,four65520]
def q47 : List W := [four52428,four61680,four64250,four65450,four65520]
def q48 : List W := [four2570,four52428,four61680,four65450,four65520]
def q49 : List W := [four20560,four43690,four52428,four65450,four65520]
def q50 : List W := [four21760,four43690,four52428,four61680,four65520]
def q51 : List W := [four21760,four52428,four61680,four65450,four65520]
def q52 : List W := [four43680,four52428,four61680,four65450,four65520]
def q53 : List W := [four21840,four52428,four61680,four65450,four65520]
def q54 : List W := [four12336,four43690,four52428,four65450,four65520]
def q55 : List W := [four13090,four43690,four52428,four61680,four65520]
def q56 : List W := [four43690,four52428,four61680,four65450,four65532]
def q57 : List W := [four13104,four43690,four52428,four61680,four65450]
def q58 : List W := [four43690,four52428,four61600,four65520]
def q59 : List W := [four43690,four52428,four61600,four61680,four65520]
def q60 : List W := [four43690,four52428,four61600,four65450,four65520]
def q61 : List W := [four80,four43690,four52428,four61680,four65520]
def q62 : List W := [four3850,four43690,four52428,four65450,four65520]
def q63 : List W := [four43690,four52428,four61680,four65280]
def q64 : List W := [four43690,four52428,four61680,four65440,four65520]
def q65 : List W := [four43690,four52428,four61680,four65450,four65484]
def q66 : List W := [four21760,four52428,four61680,four65280,four65450]
def q67 : List W := [four8738,four52428,four61680,four65280,four65450]
def q68 : List W := [four2570,four52428,four61680,four65280,four65450]
def q69 : List W := [four43690,four52428,four61680,four65484,four65520]
def q70 : List W := [four43690,four52428,four61680,four65472]
def q71 : List W := [four43690,four52428,four61680,four65280,four65518]
def q72 : List W := [four61166,four61680,four65450,four65484]
def q73 : List W := [four43656,four52428,four61680,four65450]
def q74 : List W := [four21828,four52428,four61680,four65280,four65450]
def q75 : List W := [four61166,four61680,four65280,four65450,four65484]
def q76 : List W := [four43520,four52428,four61680,four65450,four65484]
def q77 : List W := [four21760,four52428,four61680,four65450,four65484]
def q78 : List W := [four43656,four52428,four61680,four65280,four65450]
def q79 : List W := [four43690,four52224,four61680,four65450,four65484]
def q80 : List W := [four13056,four43690,four61680,four65450,four65484]
def q81 : List W := [four43690,four52428,four61680,four65280,four65484]
def q82 : List W := [four43690,four52428,four61680,four65280,four65416]
def q83 : List W := [four68,four43690,four52428,four61680,four65280]
def q84 : List W := [four13056,four43690,four52428,four61680,four65450]
def q85 : List W := [four13056,four43690,four52428,four61680,four65280,four65450]
def q86 : List W := [four13090,four43690,four52428,four61680,four65280]
def q87 : List W := [four13090,four43690,four52428,four61680,four65280,four65450]
def q88 : List W := [four43690,four52428,four61680,four65280,four65530]
def q89 : List W := [four3840,four43690,four52428,four61680,four65450]
def q90 : List W := [four3840,four43690,four52428,four61680,four65280,four65450]
def q91 : List W := [four3850,four43690,four52428,four61680,four65280]
def q92 : List W := [four3850,four43690,four52428,four61680,four65280,four65450]
def q93 : List W := [four43690,four52428,four61166,four61680,four65280]
def q94 : List W := [four43690,four52428,four61166,four61680,four65280]
def q95 : List W := [four17476,four52428,four61166,four61680,four65280]
def q96 : List W := [four43690,four52428,four61680,four65278,four65280]
def q97 : List W := [four43690,four52428,four61680,four65278,four65280]
def q98 : List W := [four52428,four61680,four65278,four65280,four65450]
def q99 : List W := [four17476,four43690,four52428,four61680,four65280]
def q100 : List W := [four2570,four52428,four61166,four61680,four65280]
def q101 : List W := [four43690,four61680,four65278,four65280,four65484]
def q102 : List W := [four170,four52428,four61166,four61680,four65280]
def q103 : List W := [four8738,four43690,four52428,four61680,four65280]
def q104 : List W := [four8738,four43690,four61166,four61680,four65280]
def q105 : List W := [four3084,four43690,four61166,four61680,four65280]
def q106 : List W := [four43690,four52428,four65278,four65280,four65520]
def q107 : List W := [four204,four43690,four61166,four61680,four65280]
def q108 : List W := [four3598,four43690,four52428,four61680,four65280]
def q109 : List W := [four238,four43690,four52428,four61680,four65280]
def q110 : List W := [four52428,four61166,four61680,four64250,four65280]
def q111 : List W := [four43690,four61166,four64250,four64764,four65280]
def q112 : List W := [four43690,four51400,four61166,four61680,four65280]
def q113 : List W := [four12850,four43690,four61166,four61680,four65280]
def q114 : List W := [four43690,four52428,four57568,four64250,four65280]
def q115 : List W := [four3598,four43690,four52428,four64250,four65280]
def q116 : List W := [four43690,four52428,four60138,four61680,four65280]
def q117 : List W := [four43690,four52428,four61680,four65280]
def q118 : List W := [four2570,four43690,four52428,four61166,four61680,four65280]
def q119 : List W := [four170,four43690,four52428,four61166,four61680,four65280]
def q120 : List W := [four43690,four61166,four61680,four65450,four65484]
def q121 : List W := [four21760,four43690,four52428,four61680,four65484]
def q122 : List W := [four17476,four43690,four61680,four65450,four65484]
def q123 : List W := [four43656,four43690,four52428,four61680,four65450]
def q124 : List W := [four34,four43690,four52428,four61680,four65450]
def q125 : List W := [four43690,four52360,four61680,four65484]
def q126 : List W := [four43690,four52428,four61680,four65416]
def q127 : List W := [four8738,four43690,four52428,four61680,four65280]
def q128 : List W := [four2570,four43690,four52428,four61680,four65280]
def q129 : List W := [four170,four43690,four52428,four61680,four65280]
def q130 : List W := [four43690,four52428,four61680,four64764,four65280]
def q131 : List W := [four43690,four52428,four61680,four64764,four65280]
def q132 : List W := [four17476,four43690,four61680,four64764,four65280]
def q133 : List W := [four20560,four43690,four52428,four64764,four65280]
def q134 : List W := [four21588,four43690,four52428,four61680,four65280]
def q135 : List W := [four43176,four43690,four52428,four61680,four65280]
def q136 : List W := [four43690,four52428,four57568,four61680,four65280]
def q137 : List W := [four514,four43690,four52428,four61680,four65280]
def q138 : List W := [four4112,four43690,four52428,four61680,four65280]
def q139 : List W := [four43690,four52428,four61680,four65280,four65520]
def q140 : List W := [four204,four43690,four61680,four64764,four65280]
def q141 : List W := [four240,four43690,four52428,four64764,four65280]
def q142 : List W := [four43690,four52428,four61680,four65280,four65532]
def q143 : List W := [four252,four43690,four52428,four61680,four65280]
def r0 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]
def r1 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]
def r2 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffff03f03f03ffc0fffffffffffffffffffffffffff03f03f03ffc0fff28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a2,0xfffffffffffc003ffc0fff03ffffffffffffffffffffffffffc003ffc0fff03f4924924924924924924924924924924924924924924924924924924924924924]
def r3 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003ffffffffffffffc0ffffffffffffffffff00003ffffffffffffffc08618618618618618618618618618618618618618618618618618618618618618,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30]
def r4 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xfc0fc0fffffffffffffc0ffffffffffffffffc0fc0fc0fffffffffffffc0fff2492492492492492492492492492492492492492492492492492492492492492,0xfffffffffffc003ffc0fff03ffffffffffffffffffffffffffc003ffc0fff03f4924924924924924924924924924924924924924924924924924924924924924,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30]
def r5 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xfffffff03ffffffffc0fffffffffffffff000fffffffff03ffffffffc0ffffffc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c,0xf000fff03fffffffffffff03ffffffffffffffff000fff03fffffffffffff03f4514514514514514514514514514514514514514514514514514514514514514,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30]
def r6 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xfffffc0fffffffff03ffffffffffffffc0fc0fffffffc0fffffffff03fffffffa28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a,0xf000fff03fffffffffffff03ffffffffffffffff000fff03fffffffffffff03f4514514514514514514514514514514514514514514514514514514514514514,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30]
def r7 : List W := [0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xfffffc0fffffffff03ffffffffffffffc0fc0fffffffc0fffffffff03fffffffa28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a,0xf000fff03fffffffffffff03ffffffffffffffff000fff03fffffffffffff03f4514514514514514514514514514514514514514514514514514514514514514,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30]
def r8 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30]
def r9 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffff03f03f03ffc0fffffffffffffffffffffffffff03f03f03ffc0fff28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a2,0xfffffffffffc003ffc0fff03ffffffffffffffffffffffffffc003ffc0fff03f4924924924924924924924924924924924924924924924924924924924924924,0xffffffffffffffff03fffffffffffffffffffffffffffffffffffff03fffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa]
def r10 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xfffffffffffffffffffffffffffffffffffc0fffffffffffffffffffffffffffe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]
def r11 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xfffffffffffffffffffffffffffffffffffc0fffffffffffffffffffffffffffe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]
def r12 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xfffffffffffffffffffffffffffffffffffc0fffffffffffffffffffffffffffe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffc0fffffffffffffffffffffffffffffffffffffc0fffffffffffffffffffff6596596596596596596596596596596596596596596596596596596596596596,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]
def r13 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xfffffffffffff03fffffffffffffffffffffffffffffffffffff03ffffffffff69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a6,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28]
def r14 : List W := [0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffff00003ffffffffffffffc0ffffffffffffffffff00003ffffffffffffffc08618618618618618618618618618618618618618618618618618618618618618,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820]
end K5Cache

namespace K5Cache
open GThreshold
def recipe : List (Nat × Nat × Nat) := [(0, 1, 0),(0, 1, 1),(0, 1, 2),(0, 1, 3),(0, 2, 0),(0, 2, 1),(0, 2, 2),(0, 2, 3),(0, 3, 0),(0, 3, 1),(0, 3, 2),(0, 3, 3),(0, 4, 0),(0, 4, 1),(0, 4, 2),(0, 4, 3),(1, 2, 0),(1, 2, 1),(1, 2, 2),(1, 2, 3),(1, 3, 0),(1, 3, 1),(1, 3, 2),(1, 3, 3),(1, 4, 0),(1, 4, 1),(1, 4, 2),(1, 4, 3),(2, 3, 0),(2, 3, 1),(2, 3, 2),(2, 3, 3),(2, 4, 0),(2, 4, 1),(2, 4, 2),(2, 4, 3),(3, 4, 0),(3, 4, 1),(3, 4, 2),(3, 4, 3),(0, 24, 1),(0, 24, 3),(0, 26, 3),(0, 28, 1),(0, 28, 3),(0, 29, 3),(0, 30, 3),(0, 32, 0),(0, 32, 1),(0, 32, 2),(0, 32, 3),(0, 33, 3),(0, 34, 3),(0, 36, 0),(0, 36, 1),(0, 36, 2),(0, 36, 3),(0, 40, 0),(0, 40, 1),(0, 40, 2),(0, 40, 3),(0, 41, 3),(0, 44, 0),(0, 44, 1),(0, 44, 2),(0, 44, 3),(0, 45, 3),(0, 46, 3),(1, 12, 3),(1, 16, 3),(1, 20, 0),(1, 20, 3),(1, 36, 0),(1, 36, 1),(1, 36, 2),(1, 36, 3),(1, 40, 0),(1, 40, 1),(1, 40, 2),(1, 40, 3),(1, 41, 3),(1, 44, 0),(1, 44, 1),(1, 44, 2),(1, 44, 3),(1, 45, 3),(2, 8, 0),(2, 8, 3),(2, 16, 3),(2, 20, 0),(2, 20, 3),(2, 32, 0),(2, 32, 3),(2, 43, 1),(2, 44, 0),(2, 44, 1),(2, 44, 2),(2, 44, 3),(2, 45, 3),(2, 46, 3),(3, 8, 0),(3, 8, 3),(3, 19, 1),(3, 20, 0),(3, 20, 3),(3, 32, 0),(3, 32, 3),(3, 39, 1),(3, 40, 0),(4, 7, 1),(4, 8, 0),(4, 8, 3),(4, 27, 1),(4, 35, 1),(4, 36, 0),(4, 36, 3),(8, 35, 1),(8, 36, 0),(8, 36, 1),(8, 36, 2),(8, 36, 3),(8, 37, 3),(8, 38, 3),(8, 40, 0),(8, 40, 1),(8, 40, 2),(8, 40, 3),(8, 42, 3),(8, 44, 1),(8, 44, 3),(12, 32, 2),(16, 32, 0),(16, 32, 2),(16, 32, 3),(24, 44, 0),(24, 44, 2),(24, 44, 3),(28, 40, 0),(28, 40, 2),(28, 40, 3),(1, 65, 0),(1, 65, 3),(2, 50, 0),(2, 50, 3),(2, 55, 0),(3, 47, 0),(3, 47, 3),(4, 47, 0),(4, 47, 3),(4, 93, 1),(23, 116, 1)]
def selected : Array Nat := #[5,71,90,103,142,66,85,132,105,145,56,87,137,92,139,58,68,73,21,33,118,41,155,45,122,62,81,126,106,128,146,52,74,140,17,29,108,37,153,46,111,113,129,134,143,13,25,94,38,95,150,42,97,99,104,49,53,127,59,133,136,9,26,75,30,76,82,34,78,86,148,91,10,14,48,18,51,63,22,57,67,72,7,11,15,60,19,54,64,69,0,23,27,79,31,77,83,147,88,1,93,107,124,117,130,8,35,149,39,96,98,151,101,2,12,141,24,152,123,154,47,43,110,112,115,3,138,109,16,144,28,50,121,100,114,36,61,80,125,4,116,20,157,119,32,156,55,120,40,65,84,131,44,70,89,135,102]
def fullInputs : Array W := #[0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820,0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def ib0 : Array W := #[0x0,0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def ib1 : Array W := #[0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,0x0,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def ib2 : Array W := #[0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0x0,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def ib3 : Array W := #[0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0x0,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def ib4 : Array W := #[0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0x0,0x0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def pinInputs (i : Fin 5) : Array W := (![ib0,ib1,ib2,ib3,ib4] : Fin 5 → Array W) i
def w4bank : Array W := #[0x0,0x1f0000000000003e0000000000007c000000000000f8000000000001f0842108421084210842108421084210842108421084210842108421084210842,0x1f0000000000003e0000000000007c000000000000f8000000000001f1084210842108421084210842108421084210842108421084210842108421084,0x1f0000000000003e0000000000007c000000000000f8000000000001f18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6,0x2108421084210842108421084210842108421084210842108421084210842108,0x3e0000000000007c000000000000f8000000000001f0000000000003e00842108421084210842108421084210842108421084210842108421084210842,0x3e0000000000007c000000000000f8000000000001f0000000000003e02108421084210842108421084210842108421084210842108421084210842108,0x3e0000000000007c000000000000f8000000000001f0000000000003e0294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a,0x7c000000000000f8000000000001f0000000000003e0000000000007c001084210842108421084210842108421084210842108421084210842108421084,0x7c000000000000f8000000000001f0000000000003e0000000000007c002108421084210842108421084210842108421084210842108421084210842108,0xf83ff000000001f07fe000000003e0ffc000000007c1ff800000000f83ff0842108421084210842108421084210842108421084210842108421084210842,0xffc1f000000001ff83e000000003ff07c000000007fe0f800000000ffc1f1084210842108421084210842108421084210842108421084210842108421084,0xfffff000000001ffffe000000003ffffc000000007ffff800000000fffff18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6,0xfffe0000000001fffc0000000003fff80000000007fff0000000000fffe02108421084210842108421084210842108421084210842108421084210842108,0xfffff000000001ffffe000000003ffffc000000007ffff800000000fffff294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a,0xfffff000000001ffffe000000003ffffc000000007ffff800000000fffff318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c,0xfffff000000001ffffe000000003ffffc000000007ffff800000000fffff39ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce,0x4210842108421084210842108421084210842108421084210842108421084210,0x1f0000000000003e0000000000007c000000000000f8000000000001f000000842108421084210842108421084210842108421084210842108421084210842,0x1f0000000000003e0000000000007c000000000000f8000000000001f000004210842108421084210842108421084210842108421084210842108421084210,0x3e0000000000007c000000000000f8000000000001f0000000000003e0000001084210842108421084210842108421084210842108421084210842108421084,0x3e0000000000007c000000000000f8000000000001f0000000000003e0000004210842108421084210842108421084210842108421084210842108421084210,0x3e0000000000007c000000000000f8000000000001f0000000000003e0000005294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294,0x7c1f0001f00000f83e0003e00001f07c0007c00003e0f8000f800007c1f0001f0842108421084210842108421084210842108421084210842108421084210842,0x7fe00001f00000ffc00003e00001ff800007c00003ff00000f800007fe00001f1084210842108421084210842108421084210842108421084210842108421084,0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6,0x7fff0000000000fffe0000000001fffc0000000003fff80000000007fff000004210842108421084210842108421084210842108421084210842108421084210,0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f4a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a52,0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294,0x7fff0001f00000fffe0003e00001fffc0007c00003fff8000f800007fff0001f5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6,0x8000000000001f0000000000003e0000000000007c000000000000f8000000002108421084210842108421084210842108421084210842108421084210842108,0x8000000000001f0000000000003e0000000000007c000000000000f8000000004210842108421084210842108421084210842108421084210842108421084210,0x8000000000001f0000000000003e0000000000007c000000000000f8000000006318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318,0x1f003e0003e0003e007c0007c0007c00f8000f8000f801f0001f0001f003e00842108421084210842108421084210842108421084210842108421084210842,0x8000003e0003ff0000007c0007fe000000f8000ffc000001f0001ff8000003e02108421084210842108421084210842108421084210842108421084210842108,0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e0294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a,0x801f00000003ff003e00000007fe007c0000000ffc00f80000001ff801f000004210842108421084210842108421084210842108421084210842108421084210,0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e04a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a52,0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e06318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318,0x801f003e0003ff003e007c0007fe007c00f8000ffc00f801f0001ff801f003e06b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5a,0x3e007c0007c0007c00f8000f8000f801f0001f0001f003e0003e0003e007c001084210842108421084210842108421084210842108421084210842108421084,0x800007c0007c1f00000f8000f83e00001f0001f07c00003e0003e0f800007c002108421084210842108421084210842108421084210842108421084210842108,0x83e007c0007c1f07c00f8000f83e0f801f0001f07c1f003e0003e0f83e007c00318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c,0x83e00000007c1f07c0000000f83e0f80000001f07c1f00000003e0f83e0000004210842108421084210842108421084210842108421084210842108421084210,0x83e007c0007c1f07c00f8000f83e0f801f0001f07c1f003e0003e0f83e007c005294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294,0x83e007c0007c1f07c00f8000f83e0f801f0001f07c1f003e0003e0f83e007c006318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318,0x7c00f801ff8000f801f003ff0001f003e007fe0003e007c00ffc0007c00f801f0000000000000000000000000000000000000000000000000000000000000000,0xf83e0f83e00001f07c1f07c00003e0f83e0f800007c1f07c1f00000f83e00000000000000000000000000000000000000000000000000000000000000000,0x7c00f83fff83e0f801f07fff07c1f003e0fffe0f83e007c1fffc1f07c00f83ff0000000000000000000000000000000000000000000000000000000000000000,0x7c1f00000f83e0f83e00001f07c1f07c00003e0f83e0f800007c1f07c1f000000000000000000000000000000000000000000000000000000000000000000000,0x7c1ff801ff83e0f83ff003ff07c1f07fe007fe0f83e0ffc00ffc1f07c1ff801f0000000000000000000000000000000000000000000000000000000000000000,0x7c1ff83e0f83e0f83ff07c1f07c1f07fe0f83e0f83e0ffc1f07c1f07c1ff83e00000000000000000000000000000000000000000000000000000000000000000,0x7c1ff83fff83e0f83ff07fff07c1f07fe0fffe0f83e0ffc1fffc1f07c1ff83ff0842108421084210842108421084210842108421084210842108421084210842,0xffc00ffc000001ff801ff8000003ff003ff0000007fe007fe000000ffc000000000000000000000000000000000000000000000000000000000000000000,0x7c00ffc1fffc00f801ff83fff801f003ff07fff003e007fe0fffe007c00ffc1f0000000000000000000000000000000000000000000000000000000000000000,0x7fe000000ffc00ffc000001ff801ff8000003ff003ff0000007fe007fe0000000000000000000000000000000000000000000000000000000000000000000000,0x7fe0f801fffc00ffc1f003fff801ff83e007fff003ff07c00fffe007fe0f801f0000000000000000000000000000000000000000000000000000000000000000,0x7fe0ffc00ffc00ffc1ff801ff801ff83ff003ff003ff07fe007fe007fe0ffc000000000000000000000000000000000000000000000000000000000000000000,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f0000000000000000000000000000000000000000000000000000000000000000,0x7fe0ffc1fffc00ffc1ff83fff801ff83ff07fff003ff07fe0fffe007fe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0xfffe0fffe00001fffc1fffc00003fff83fff800007fff07fff00000fffe00000000000000000000000000000000000000000000000000000000000000000,0x7c1fffffffffe0f83fffffffffc1f07fffffffff83e0ffffffffff07c1ffffff0842108421084210842108421084210842108421084210842108421084210842,0x7fff00000fffe0fffe00001fffc1fffc00003fff83fff800007fff07fff000000000000000000000000000000000000000000000000000000000000000000000,0x7ffffffe0fffe0fffffffc1fffc1fffffff83fff83fffffff07fff07ffffffe00000000000000000000000000000000000000000000000000000000000000000,0x7fffffffffffe0ffffffffffffc1ffffffffffff83ffffffffffff07ffffffff18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6,0x800000000fffff000000001ffffe000000003ffffc000000007ffff8000000000000000000000000000000000000000000000000000000000000000000000000,0x8000f83e0fffff0001f07c1ffffe0003e0f83ffffc0007c1f07ffff8000f83e00000000000000000000000000000000000000000000000000000000000000000,0x8000ffc00fffff0001ff801ffffe0003ff003ffffc0007fe007ffff8000ffc000000000000000000000000000000000000000000000000000000000000000000,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe00000000000000000000000000000000000000000000000000000000000000000,0x8000fffe0fffff0001fffc1ffffe0003fff83ffffc0007fff07ffff8000fffe02108421084210842108421084210842108421084210842108421084210842108,0xfc1f00000ffffff83e00001ffffff07c00003fffffe0f800007fffffc1f000000000000000000000000000000000000000000000000000000000000000000000,0xfc1fffc1fffffff83fff83fffffff07fff07ffffffe0fffe0fffffffc1fffc1f0000000000000000000000000000000000000000000000000000000000000000,0xfc1ffffe0ffffff83ffffc1ffffff07ffff83fffffe0fffff07fffffc1ffffe02108421084210842108421084210842108421084210842108421084210842108,0xfc1ffffffffffff83ffffffffffff07fffffffffffe0ffffffffffffc1ffffff294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a,0xffe000000fffffffc000001fffffff8000003fffffff0000007ffffffe0000000000000000000000000000000000000000000000000000000000000000000000,0xffe0ffc1ffffffffc1ff83ffffffff83ff07ffffffff07fe0ffffffffe0ffc1f1084210842108421084210842108421084210842108421084210842108421084,0xffe0fffe0fffffffc1fffc1fffffff83fff83fffffff07fff07ffffffe0fffe02108421084210842108421084210842108421084210842108421084210842108,0xffe0ffffffffffffc1ffffffffffff83ffffffffffff07fffffffffffe0fffff318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff39ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce,0xffff00000ffffffffe00001ffffffffc00003ffffffff800007ffffffff000004210842108421084210842108421084210842108421084210842108421084210,0xfffff801fffffffffff003ffffffffffe007ffffffffffc00fffffffffff801f4210842108421084210842108421084210842108421084210842108421084210,0xfffff83e0ffffffffff07c1fffffffffe0f83fffffffffc1f07fffffffff83e04210842108421084210842108421084210842108421084210842108421084210,0xfffff83ffffffffffff07fffffffffffe0ffffffffffffc1ffffffffffff83ff4a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a52,0xffffffc00fffffffffff801fffffffffff003ffffffffffe007ffffffffffc004210842108421084210842108421084210842108421084210842108421084210,0xffffffc1ffffffffffff83ffffffffffff07fffffffffffe0ffffffffffffc1f4210842108421084210842108421084210842108421084210842108421084210,0xffffffc1ffffffffffff83ffffffffffff07fffffffffffe0ffffffffffffc1f5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294,0xfffffffe0ffffffffffffc1ffffffffffff83ffffffffffff07fffffffffffe04210842108421084210842108421084210842108421084210842108421084210,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6,0xfffffffe0ffffffffffffc1ffffffffffff83ffffffffffff07fffffffffffe06318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5a,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739c,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bde]
def pi0 : Array Nat := #[0,0,1,2,3,0,5,5,6,7,0,8,8,9,9,10,11,13,0,10,10,11,12,13,15,0,18,18,19,20,22,23,26,27,0,23,23,24,25,26,26,27,30,31,32,0,33,33,34,34,35,36,36,37,38,40,41,42,43,44,45,0,40,40,41,41,42,43,43,44,44,45,52,59,64,69,73,77,81,84,87,90,0,0,0,0,0,0,0,0,0,46,47,48,49,49,50,50,51,52,46,47,48,49,50,52,53,54,55,55,56,56,57,59,59,63,64,60,61,62,64,65,65,66,67,69,66,69,69,71,73,73,74,75,76,77,77,80,80,81,81,81,82,83,84,82,84,85,87,87,89,89,90,90,91,91,92]
def pi1 : Array Nat := #[0,1,0,2,2,5,0,5,6,6,10,11,12,13,14,0,8,9,10,0,10,11,12,13,15,18,0,18,19,20,28,0,21,21,23,0,23,24,25,26,27,26,30,31,38,33,0,33,34,35,35,36,37,36,38,40,41,42,43,44,45,52,59,64,69,73,77,81,84,87,89,90,0,40,40,41,41,42,43,43,44,45,0,46,47,48,49,49,50,51,52,0,0,0,0,0,0,0,0,0,46,47,48,49,50,52,53,54,55,56,55,56,57,59,64,57,59,60,61,62,64,65,66,65,67,69,70,72,73,67,69,73,74,75,76,77,80,77,80,81,81,84,81,81,81,82,84,85,87,89,87,89,90,91,90,91,92]
def pi2 : Array Nat := #[0,1,2,0,2,10,11,12,13,15,5,0,5,6,7,8,0,9,10,11,12,0,12,13,13,23,24,25,26,0,19,20,21,22,23,24,25,0,25,26,27,28,30,31,38,52,59,64,69,73,80,81,84,87,90,0,30,30,31,31,32,33,0,33,34,35,34,36,37,36,37,38,40,0,40,41,42,41,43,44,43,45,46,0,47,47,49,50,49,51,52,0,53,53,55,56,55,56,57,59,0,60,60,62,62,64,0,0,0,0,0,0,0,0,52,57,59,60,64,62,64,65,66,67,65,69,71,72,73,74,77,80,65,65,69,69,73,77,80,81,82,84,82,85,87,81,89,81,81,84,87,89,90,91,92,93,90]
def pi3 : Array Nat := #[0,10,11,13,15,1,2,3,0,2,5,6,7,0,5,8,9,0,10,11,12,13,16,0,13,23,24,25,26,30,38,40,43,44,52,59,64,69,80,81,84,87,0,17,19,23,24,25,0,23,25,26,27,28,26,30,0,30,31,32,31,33,34,35,0,33,34,36,37,38,39,36,40,41,42,0,40,41,43,44,45,43,46,47,0,47,49,50,51,49,52,53,0,53,55,56,57,58,55,59,60,0,60,62,63,64,0,60,65,66,67,68,65,69,73,74,77,0,64,78,80,0,0,0,0,0,50,49,52,57,59,64,65,69,65,69,73,77,80,81,82,84,86,81,87,88,89,81,90,91,92,93,81,84,87,89,90]
def pi4 : Array Nat := #[0,10,11,13,15,23,24,25,26,28,33,34,35,36,37,40,41,43,52,59,64,69,80,81,90,1,2,3,0,4,6,8,0,8,10,11,12,13,16,0,10,11,17,0,19,23,24,25,26,27,29,0,23,24,26,30,31,32,0,30,31,33,34,35,36,37,38,0,33,34,35,36,40,41,42,43,44,45,0,40,41,43,46,47,49,51,0,46,47,49,52,53,55,57,0,46,53,54,55,59,60,62,63,0,60,64,65,68,0,47,53,60,65,69,73,74,77,78,79,0,80,0,49,55,65,81,56,81,84,67,87,89,0,69,81,90,91,92,93,0,46,52,54,55,59,60,64,65,69,73,77,80,81,84,87,89,90]
def pinIDs (i : Fin 5) : Array Nat := (![pi0,pi1,pi2,pi3,pi4] : Fin 5 → Array Nat) i
def fastPin (i : Fin 5) (j : Nat) : W := w4bank[((pinIDs i)[j]?.getD 0)]?.getD 0
end K5Cache

namespace K5Cache
open GThreshold
def words5 : Array W := #[0x0,0xfc0fff000000000000000000000000000000000fc0fff2082082082082082082082082082082082082082082082082082082082082082,0xfff03f000000000000000000000000000000000fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffffc0000000000000000000000000000000000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xffffff000000000000000000000000000000000ffffffc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c,0x3f03f00003f00000000000000000000000000003f03f00003f2082082082082082082082082082082082082082082082082082082082082082,0x3ffc000003f00000000000000000000000000003ffc000003f4104104104104104104104104104104104104104104104104104104104104104,0x3ffff00003f00000000000000000000000000003ffff00003f6186186186186186186186186186186186186186186186186186186186186186,0x3ffff00000000000000000000000000000000003ffff0000000410410410410410410410410410410410410410410410410410410410410410,0x3ffff00003f00000000000000000000000000003ffff00003f4514514514514514514514514514514514514514514514514514514514514514,0x3f00003f000fc000000000000000000000000003f00003f000fc02082082082082082082082082082082082082082082082082082082082082082,0x3ffc0000000fc000000000000000000000000003ffc0000000fc08208208208208208208208208208208208208208208208208208208208208208,0x3ffc003f000fc000000000000000000000000003ffc003f000fc0a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a,0x3ffc003f00000000000000000000000000000003ffc003f0000000410410410410410410410410410410410410410410410410410410410410410,0x3ffc003f000fc000000000000000000000000003ffc003f000fc02492492492492492492492492492492492492492492492492492492492492492,0xfc0000fc003f000000000000000000000000000fc0000fc003f0004104104104104104104104104104104104104104104104104104104104104104,0xfc0fc000003f000000000000000000000000000fc0fc000003f0008208208208208208208208208208208208208208208208208208208208208208,0xfc0fc0fc0000000000000000000000000000000fc0fc0fc00000000410410410410410410410410410410410410410410410410410410410410410,0x3f03f03f03ffc0fff00000000000000000000003f03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0x3ffc003ffc0fff03f00000000000000000000003ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0x3ffff03ffffffffff00000000000000000000003ffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0x3fffffc0000ffffc000000000000000000000003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0x3ffffffffffffffff00000000000000000000003ffffffffffffffffe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e,0x3ffffffffff00000000000000000000000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0x3ffffffffffffffc000000000000000000000003ffffffffffffffc08618618618618618618618618618618618618618618618618618618618618618,0xfc0fc000000000000003f000000000000000000fc0fc000000000000003f2082082082082082082082082082082082082082082082082082082082082082,0xfff00000000000000003f000000000000000000fff00000000000000003f4104104104104104104104104104104104104104104104104104104104104104,0xffffc000000000000003f000000000000000000ffffc000000000000003f6186186186186186186186186186186186186186186186186186186186186186,0xffffc0000000000000000000000000000000000ffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820,0x3f00000000000000000000000000000000000003f0000000000000000000008208208208208208208208208208208208208208208208208208208208208208,0xfff000fc0000000000000fc0000000000000000fff000fc0000000000000fc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xf00003f00000000000003f00000000000000003f00003f00000000000003f0004104104104104104104104104104104104104104104104104104104104104104,0xf03f03f00000000000000000000000000000003f03f03f0000000000000000000820820820820820820820820820820820820820820820820820820820820820,0xf03f03f00000000000003f00000000000000003f03f03f00000000000003f0004924924924924924924924924924924924924924924924924924924924924924,0xfc0fc0fc0000000000fc0fff000000000000fc0fc0fc0fc0000000000fc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf000fff000000000000fff03f000000000000fff000fff000000000000fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc0ffffc0000000000ffffff000000000000ffffc0ffffc0000000000ffffff6186186186186186186186186186186186186186186186186186186186186186,0xffff000000000000000ffffc0000000000000ffffff000000000000000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xffffffffc0000000000ffffff000000000000ffffffffffc0000000000ffffffe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e,0xffffffffc0000000000000000000000000000ffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820,0xffffffffc0000000000fc0fff000000000000ffffffffffc0000000000fc0fff28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a2,0xffffffffc0000000000fff03f000000000000ffffffffffc0000000000fff03f4924924924924924924924924924924924924924924924924924924924924924,0x3f0000000000000000000000000000410410410410410410410410410410410410410410410410410410410410410,0x3f0000000000000000000000000000820820820820820820820820820820820820820820820820820820820820820,0xfc000000003f000000000000000fff000000000fc000000003f0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0xfc0fc000003f03f00003f000000fc0fc0000000fc0fc000003f03f00003f2082082082082082082082082082082082082082082082082082082082082082,0xfff00000003ffc000003f000000fff000000000fff00000003ffc000003f4104104104104104104104104104104104104104104104104104104104104104,0xffffc000003ffff00003f000000ffffc0000000ffffc000003ffff00003f6186186186186186186186186186186186186186186186186186186186186186,0x3ffff000000000000ffffff00000000000000003ffff0000000410410410410410410410410410410410410410410410410410410410410410,0xfc0fc000003ffff00003f000000ffffff000000fc0fc000003ffff00003f2492492492492492492492492492492492492492492492492492492492492492,0xffffc000003ffff00003f000000ffffff000000ffffc000003ffff00003f6596596596596596596596596596596596596596596596596596596596596596,0xffffc0000000000000000000000ffffff000000ffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820,0xffffc000003f03f00003f000000ffffff000000ffffc000003f03f00003f28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a2,0xffffc000003ffc000003f000000ffffff000000ffffc000003ffc000003f4924924924924924924924924924924924924924924924924924924924924924,0xffffc000003ffff000000000000ffffff000000ffffc000003ffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0x3f000000000fc000000000000003f00000000003f000000000fc00000000008208208208208208208208208208208208208208208208208208208208208208,0xfc000000000000003f00003f000000000000000fc00000000000410410410410410410410410410410410410410410410410410410410410410,0x3f000000000fc000000000000003f00003f00003f000000000fc00000000008618618618618618618618618618618618618618618618618618618618618618,0x3f00000000000000000000000003f00003f00003f0000000000000000000000820820820820820820820820820820820820820820820820820820820820820,0x3f000000000fc000000000000003f00003f00003f000000000fc00000000008a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0x3f000000000fc000000000000003f00003f00003f000000000fc00000000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0xfc0000fc003f00003f000fc0000fc0000fc0000fc0000fc003f00003f000fc02082082082082082082082082082082082082082082082082082082082082082,0xfff00000003ffc0000000fc0000fff000000000fff00000003ffc0000000fc08208208208208208208208208208208208208208208208208208208208208208,0xfff000fc003ffc003f000fc0000fff000fc0000fff000fc003ffc003f000fc0a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a,0x3ffc003f000000000fff000fff00000000000003ffc003f0000000410410410410410410410410410410410410410410410410410410410410410,0xfc0000fc003ffc003f000fc0000fff000fff000fc0000fc003ffc003f000fc02492492492492492492492492492492492492492492492492492492492492492,0xfff00000003ffc003f000fc0000fff000fff000fff00000003ffc003f000fc08618618618618618618618618618618618618618618618618618618618618618,0xfff000fc0000000000000000000fff000fff000fff000fc00000000000000000820820820820820820820820820820820820820820820820820820820820820,0xfff000fc003f00003f000fc0000fff000fff000fff000fc003f00003f000fc028a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a2,0xfff000fc003ffc0000000fc0000fff000fff000fff000fc003ffc0000000fc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xfff000fc003ffc003f000fc0000fff000fff000fff000fc003ffc003f000fc0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfff000fc003ffc003f000000000fff000fff000fff000fc003ffc003f0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0xf00003f000fc0000fc003f00003f00003f00003f00003f000fc0000fc003f0004104104104104104104104104104104104104104104104104104104104104104,0xf03f000000fc0fc000003f00003f03f00000003f03f000000fc0fc000003f0008208208208208208208208208208208208208208208208208208208208208208,0xf03f03f000fc0fc0fc003f00003f03f03f00003f03f03f000fc0fc0fc003f000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c,0xfc0fc0fc000000003f03f03f03f000000000000fc0fc0fc00000000410410410410410410410410410410410410410410410410410410410410410,0xf00003f000fc0fc0fc003f00003f03f03f03f03f00003f000fc0fc0fc003f0004514514514514514514514514514514514514514514514514514514514514514,0xf03f000000fc0fc0fc003f00003f03f03f03f03f03f000000fc0fc0fc003f0008618618618618618618618618618618618618618618618618618618618618618,0xf03f03f00000000000000000003f03f03f03f03f03f03f0000000000000000000820820820820820820820820820820820820820820820820820820820820820,0xf03f03f000fc0000fc003f00003f03f03f03f03f03f03f000fc0000fc003f0004924924924924924924924924924924924924924924924924924924924924924,0xf03f03f000fc0fc000003f00003f03f03f03f03f03f03f000fc0fc000003f0008a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xf03f03f000fc0fc0fc000000003f03f03f03f03f03f03f000fc0fc0fc00000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0xfc003f00003f000fc003ffc0000fc0000fc0000fc003f00003f000fc003f0000000000000000000000000000000000000000000000000000000000000000,0xfc000003f03f000000fc0fc0fc0fc0000000fc0fc000003f03f000000fc0fc00000000000000000000000000000000000000000000000000000000000000000,0x3f03f03f03f000000fc0fc0fc0fc000000000003f03f03f03f0000000000000000000000000000000000000000000000000000000000000000000000,0xfc000003f03f03f03ffc0fc0fc0fc0fc0fc0fc0fc000003f03f03f03ffc0fc00000000000000000000000000000000000000000000000000000000000000000,0xfc0fc0fc0000000000000000fc0fc0fc0fc0fc0fc0fc0fc00000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfc0fc0fff00003f000fc003ffc0fc0fc0fc0fc0fc0fc0fff00003f000fc003f0000000000000000000000000000000000000000000000000000000000000000,0xfc0fc0fff03f000000fc0fc0fc0fc0fc0fc0fc0fc0fc0fff03f000000fc0fc00000000000000000000000000000000000000000000000000000000000000000,0xfc0fc0fff03f03f03f000000fc0fc0fc0fc0fc0fc0fc0fff03f03f03f0000000000000000000000000000000000000000000000000000000000000000000000,0xfc0fc0fff03f03f03ffc0ffffc0fc0fc0fc0fc0fc0fc0fff03f03f03ffc0fff2082082082082082082082082082082082082082082082082082082082082082,0xf00000003ffc0000000fff000fff000000000fff00000003ffc0000000fff0000000000000000000000000000000000000000000000000000000000000000000,0x3ffc003ffc0000000fff000fff00000000000003ffc003ffc00000000000000000000000000000000000000000000000000000000000000000000000,0xf00000003ffc003ffc0fff000fff000fff000fff00000003ffc003ffc0fff0000000000000000000000000000000000000000000000000000000000000000000,0xf000fff000000000000000000fff000fff000fff000fff0000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xf000fff03f00003f000fc003ffff000fff000fff000fff03f00003f000fc003f0000000000000000000000000000000000000000000000000000000000000000,0xf000fff03ffc0000000fff000fff000fff000fff000fff03ffc0000000fff0000000000000000000000000000000000000000000000000000000000000000000,0xf000fff03ffc003f000fff03ffff000fff000fff000fff03ffc003f000fff03f0000000000000000000000000000000000000000000000000000000000000000,0xf000fff03ffc003ffc0000000fff000fff000fff000fff03ffc003ffc00000000000000000000000000000000000000000000000000000000000000000000000,0xf000fff03ffc003ffc0fff03ffff000fff000fff000fff03ffc003ffc0fff03f4104104104104104104104104104104104104104104104104104104104104104,0xffc000003ffff000000ffffc0ffffc0000000ffffc000003ffff000000ffffc00000000000000000000000000000000000000000000000000000000000000000,0x3ffff03ffff000000ffffc0ffffc000000000003ffff03ffff0000000000000000000000000000000000000000000000000000000000000000000000,0xffc000003ffff03ffffffffc0ffffc0ffffc0ffffc000003ffff03ffffffffc00000000000000000000000000000000000000000000000000000000000000000,0xffc0ffffc0000000000000000ffffc0ffffc0ffffc0ffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffc0fffffffff000000ffffc0ffffc0ffffc0ffffc0fffffffff000000ffffc00000000000000000000000000000000000000000000000000000000000000000,0xffc0fffffffff03ffffffffffffffc0ffffc0ffffc0fffffffff03ffffffffff6186186186186186186186186186186186186186186186186186186186186186,0x3fffffc0000000000ffffff00000000000000003fffffc00000000000000000000000000000000000000000000000000000000000000000000000000,0xffc000003fffffc0000ffffc0ffffff000000ffffc000003fffffc0000ffffc00000000000000000000000000000000000000000000000000000000000000000,0xffff000000000000000000000ffffff000000ffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffff00003f03f000000fc0fc0ffffff000000ffffff00003f03f000000fc0fc00000000000000000000000000000000000000000000000000000000000000000,0xffff00003ffc0000000fff000ffffff000000ffffff00003ffc0000000fff0000000000000000000000000000000000000000000000000000000000000000000,0xffff00003ffff000000ffffc0ffffff000000ffffff00003ffff000000ffffc00000000000000000000000000000000000000000000000000000000000000000,0xffff00003fffffc0000000000ffffff000000ffffff00003fffffc00000000000000000000000000000000000000000000000000000000000000000000000000,0xffff00003fffffc0000ffffc0ffffff000000ffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xfffffc0fffffffff03ffffffffffffffc0fc0fffffffc0fffffffff03fffffffa28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a,0xfffffff03ffffffffc0000000fffffffff000fffffffff03ffffffffc00000000000000000000000000000000000000000000000000000000000000000000000,0xfffffff03ffffffffc0fffffffffffffff000fffffffff03ffffffffc0ffffffc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c,0x3ffffffffff000000ffffffffffc000000000003ffffffffff0000000000000000000000000000000000000000000000000000000000000000000000,0xffc0fffffffffffffffffffffffffffffffc0ffffc0fffffffffffffffffffff6186186186186186186186186186186186186186186186186186186186186186,0xffffffffc0000000000000000ffffffffffc0ffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffc0fffffffffffffffffffffffffffe38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e,0xffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3f03f03f03f000000ffffffffffff00000000003f03f03f03f0000000000000000000000000000000000000000000000000000000000000000000000,0x3ffc003ffc0000000ffffffffffff00000000003ffc003ffc00000000000000000000000000000000000000000000000000000000000000000000000,0x3fffffc0000000000ffffffffffff00000000003fffffc00000000000000000000000000000000000000000000000000000000000000000000000000,0x3ffffffffff000000ffffffffffff00000000003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xfc0fc0ffffc003ffc0fc003ffffffffffffffc0fc0fc0ffffc003ffc0fc003f0000000000000000000000000000000000000000000000000000000000000000,0xfc0fc0ffffffffffff000000fffffffffffffc0fc0fc0ffffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xfc0fc0fffffffffffffc0ffffffffffffffffc0fc0fc0fffffffffffffc0fff2492492492492492492492492492492492492492492492492492492492492492,0xf000fff03fffffc0000fff000fffffffffffffff000fff03fffffc0000fff0000000000000000000000000000000000000000000000000000000000000000000,0xf000fff03fffffffffffff03ffffffffffffffff000fff03fffffffffffff03f4514514514514514514514514514514514514514514514514514514514514514,0xffc0fffffffffffffffffffffffffffffffffffffc0fffffffffffffffffffff6596596596596596596596596596596596596596596596596596596596596596,0xffff000000000000000000000ffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffff00003fffffc0000ffffc0ffffffffffffffffff00003fffffc0000ffffc08208208208208208208208208208208208208208208208208208208208208208,0xffff00003ffffffffff000000ffffffffffffffffff00003ffffffffff0000000410410410410410410410410410410410410410410410410410410410410410,0xffff00003ffffffffffffffc0ffffffffffffffffff00003ffffffffffffffc08618618618618618618618618618618618618618618618618618618618618618,0xfffffc0fffffffffffffffffffffffffffffffffffffc0ffffffffffffffffffa69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a,0xfffffff03fffffffffffffffffffffffffffffffffffff03ffffffffffffffffc71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e,0xffffffffc0000000000000000ffffffffffffffffffffffc00000000000000000820820820820820820820820820820820820820820820820820820820820820,0xffffffffff00003f000fc003fffffffffffffffffffffffff00003f000fc003f0820820820820820820820820820820820820820820820820820820820820820,0xffffffffff03f03f03ffc0fffffffffffffffffffffffffff03f03f03ffc0fff28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a2,0xfffffffffffc003f000fff03ffffffffffffffffffffffffffc003f000fff03f0820820820820820820820820820820820820820820820820820820820820820,0xfffffffffffc003ffc0000000fffffffffffffffffffffffffc003ffc00000000820820820820820820820820820820820820820820820820820820820820820,0xfffffffffffc003ffc0fff03ffffffffffffffffffffffffffc003ffc0fff03f4924924924924924924924924924924924924924924924924924924924924924,0xfffffffffffff000000ffffc0fffffffffffffffffffffffffff000000ffffc00820820820820820820820820820820820820820820820820820820820820820,0xfffffffffffff03fffffffffffffffffffffffffffffffffffff03ffffffffff69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a69a6,0xffffffffffffffc0000000000ffffffffffffffffffffffffffffc00000000000820820820820820820820820820820820820820820820820820820820820820,0xffffffffffffffc0000ffffc0ffffffffffffffffffffffffffffc0000ffffc08a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28a28,0xffffffffffffffff03fffffffffffffffffffffffffffffffffffff03fffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffffc0fffffffffffffffffffffffffffffffffffffc0ffffffcb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2c,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebaebae,0xfffffffffffffffffff000000fffffffffffffffffffffffffffffffff0000000c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30,0xffffffffffffffffffffc0fffffffffffffffffffffffffffffffffffffc0fff2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2,0xffffffffffffffffffffff03fffffffffffffffffffffffffffffffffffff03f4d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34d34,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6,0xfffffffffffffffffffffffc0fffffffffffffffffffffffffffffffffffffc08e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38]
def wire (j : Nat) : W := words5[j]?.getD 0
def shape (xs : List Nat) : List W := xs.map wire
def eids0 : Array (List Nat) := #[[82,90,99,113,125,139],[105,90,99,113,125,139],[61,90,99,113,125,139],[72,90,99,113,125,139],[83,90,113,99,125,139],[114,90,113,99,125,139],[45,90,113,99,125,139],[73,90,113,99,125,139],[84,90,125,99,113,139],[128,90,125,99,113,139],[34,90,125,99,113,139],[75,90,125,99,113,139],[86,90,139,99,113,125],[141,90,139,99,113,125],[18,90,139,99,113,125],[78,90,139,99,113,125],[91,99,113,90,125,139],[116,99,113,90,125,139],[46,99,113,90,125,139],[62,99,113,90,125,139],[92,99,125,90,113,139],[130,99,125,90,113,139],[35,99,125,90,113,139],[64,99,125,90,113,139],[94,99,139,90,113,125],[144,99,139,90,113,125],[19,99,139,90,113,125],[67,99,139,90,113,125],[106,113,125,90,99,139],[135,113,125,90,99,139],[37,113,125,90,99,139],[48,113,125,90,99,139],[108,113,139,90,99,125],[148,113,139,90,99,125],[21,113,139,90,99,125],[51,113,139,90,99,125],[121,125,139,90,99,113],[152,125,139,90,99,113],[23,125,139,90,99,113],[39,125,139,90,99,113]]
def edges0 : Array (List W) := eids0.map shape
set_option maxRecDepth 16000 in
theorem follow0 : follows 8 r0 = edges0.toList := by decide +kernel
def eids1 : Array (List Nat) := #[[82,105,113,125,139],[82,90,105,113,125,139],[82,99,105,113,125,139],[82,90,99,105,113,125,139],[61,90,105,113,125,139],[61,90,99,105,113,125,139],[72,99,105,113,125,139],[72,90,99,105,113,125,139],[0,90,99,113,125,139],[0,90,105,99,113,125,139],[72,90,99,113,125,139],[72,105,99,113,125,139],[72,90,105,99,113,125,139],[83,90,113,99,105,125,139],[114,113,99,105,125,139],[114,90,113,99,105,125,139],[45,113,99,105,125,139],[45,90,113,99,105,125,139],[73,90,113,99,105,125,139],[84,90,125,99,105,113,139],[128,125,99,105,113,139],[128,90,125,99,105,113,139],[34,125,99,105,113,139],[34,90,125,99,105,113,139],[75,90,125,99,105,113,139],[86,90,139,99,105,113,125],[141,139,99,105,113,125],[141,90,139,99,105,113,125],[18,139,99,105,113,125],[18,90,139,99,105,113,125],[78,90,139,99,105,113,125],[0,99,90,113,125,139],[0,99,105,90,113,125,139],[61,99,90,113,125,139],[61,105,90,113,125,139],[61,99,105,90,113,125,139],[91,99,113,90,105,125,139],[116,113,90,105,125,139],[116,99,113,90,105,125,139],[46,113,90,105,125,139],[46,99,113,90,105,125,139],[62,99,113,90,105,125,139],[92,99,125,90,105,113,139],[130,125,90,105,113,139],[130,99,125,90,105,113,139],[35,125,90,105,113,139],[35,99,125,90,105,113,139],[64,99,125,90,105,113,139],[94,99,139,90,105,113,125],[144,139,90,105,113,125],[144,99,139,90,105,113,125],[19,139,90,105,113,125],[19,99,139,90,105,113,125],[67,99,139,90,105,113,125],[100,113,90,99,125,139],[100,105,113,90,99,125,139],[120,113,90,99,125,139],[120,105,113,90,99,125,139],[47,113,90,99,125,139],[47,105,113,90,99,125,139],[55,113,90,99,125,139],[55,105,113,90,99,125,139],[101,125,90,99,113,139],[101,105,125,90,99,113,139],[131,125,90,99,113,139],[131,105,125,90,99,113,139],[36,125,90,99,113,139],[36,105,125,90,99,113,139],[56,125,90,99,113,139],[56,105,125,90,99,113,139],[103,139,90,99,113,125],[103,105,139,90,99,113,125],[146,139,90,99,113,125],[146,105,139,90,99,113,125],[20,139,90,99,113,125],[20,105,139,90,99,113,125],[58,139,90,99,113,125],[58,105,139,90,99,113,125],[106,113,125,90,99,105,139],[135,113,125,90,99,105,139],[37,113,125,90,99,105,139],[48,113,125,90,99,105,139],[108,113,139,90,99,105,125],[148,113,139,90,99,105,125],[21,113,139,90,99,105,125],[51,113,139,90,99,105,125],[121,125,139,90,99,105,113],[152,125,139,90,99,105,113],[23,125,139,90,99,105,113],[39,125,139,90,99,105,113]]
def edges1 : Array (List W) := eids1.map shape
set_option maxRecDepth 16000 in
theorem follow1 : follows 7 r1 = edges1.toList := by decide +kernel
def eids2 : Array (List Nat) := #[[82,90,99,113,125,141,144],[105,113,125,141,144],[105,90,113,125,141,144],[105,99,113,125,141,144],[105,90,99,113,125,141,144],[61,99,113,125,141,144],[61,90,99,113,125,141,144],[72,90,113,125,141,144],[72,90,99,113,125,141,144],[83,90,113,99,125,141,144],[114,113,99,125,141,144],[114,90,113,99,125,141,144],[45,113,99,125,141,144],[45,90,113,99,125,141,144],[73,90,113,99,125,141,144],[84,90,125,99,113,141,144],[128,125,99,113,141,144],[128,90,125,99,113,141,144],[34,125,99,113,141,144],[34,90,125,99,113,141,144],[75,90,125,99,113,141,144],[0,90,141,99,113,125,144],[78,90,99,113,125,144],[78,141,99,113,125,144],[78,90,141,99,113,125,144],[87,99,113,125,141],[87,90,99,113,125,141],[87,144,99,113,125,141],[87,90,144,99,113,125,141],[146,90,144,99,113,125,141],[10,90,99,113,125,141],[10,90,144,99,113,125,141],[79,144,99,113,125,141],[79,90,144,99,113,125,141],[91,99,113,90,125,141,144],[116,113,90,125,141,144],[116,99,113,90,125,141,144],[46,113,90,125,141,144],[46,99,113,90,125,141,144],[62,99,113,90,125,141,144],[92,99,125,90,113,141,144],[130,125,90,113,141,144],[130,99,125,90,113,141,144],[35,125,90,113,141,144],[35,99,125,90,113,141,144],[64,99,125,90,113,141,144],[95,90,113,125,144],[95,99,90,113,125,144],[95,141,90,113,125,144],[95,99,141,90,113,125,144],[146,99,141,90,113,125,144],[15,99,90,113,125,144],[15,99,141,90,113,125,144],[68,141,90,113,125,144],[68,99,141,90,113,125,144],[0,99,144,90,113,125,141],[67,99,90,113,125,141],[67,144,90,113,125,141],[67,99,144,90,113,125,141],[106,113,125,90,99,141,144],[135,113,125,90,99,141,144],[37,113,125,90,99,141,144],[48,113,125,90,99,141,144],[109,113,141,90,99,125,144],[149,113,90,99,125,144],[149,113,141,90,99,125,144],[16,113,141,90,99,125,144],[52,113,90,99,125,144],[52,113,141,90,99,125,144],[110,113,144,90,99,125,141],[150,113,90,99,125,141],[150,113,144,90,99,125,141],[11,113,144,90,99,125,141],[53,113,90,99,125,141],[53,113,144,90,99,125,141],[122,125,141,90,99,113,144],[153,125,90,99,113,144],[153,125,141,90,99,113,144],[17,125,141,90,99,113,144],[40,125,90,99,113,144],[40,125,141,90,99,113,144],[123,125,144,90,99,113,141],[154,125,90,99,113,141],[154,125,144,90,99,113,141],[13,125,144,90,99,113,141],[41,125,90,99,113,141],[41,125,144,90,99,113,141],[140,90,99,113,125],[140,141,90,99,113,125],[140,144,90,99,113,125],[140,141,144,90,99,113,125],[146,141,144,90,99,113,125],[10,141,90,99,113,125],[10,141,144,90,99,113,125],[15,144,90,99,113,125],[15,141,144,90,99,113,125]]
def edges2 : Array (List W) := eids2.map shape
set_option maxRecDepth 16000 in
theorem follow2 : follows 6 r2 = edges2.toList := by decide +kernel
def eids3 : Array (List Nat) := #[[82,90,99,135,148,152],[105,90,99,135,148,152],[61,90,99,135,148,152],[72,90,99,135,148,152],[85,90,135,99,148,152],[136,90,99,148,152],[136,90,135,99,148,152],[25,90,135,99,148,152],[77,90,99,148,152],[77,90,135,99,148,152],[88,90,148,99,135,152],[149,90,99,135,152],[149,90,148,99,135,152],[5,90,148,99,135,152],[80,90,99,135,152],[80,90,148,99,135,152],[89,90,152,99,135,148],[153,90,99,135,148],[153,90,152,99,135,148],[1,90,152,99,135,148],[81,90,99,135,148],[81,90,152,99,135,148],[93,99,135,90,148,152],[137,99,90,148,152],[137,99,135,90,148,152],[26,99,135,90,148,152],[66,99,90,148,152],[66,99,135,90,148,152],[96,99,148,90,135,152],[150,99,90,135,152],[150,99,148,90,135,152],[6,99,148,90,135,152],[69,99,90,135,152],[69,99,148,90,135,152],[98,99,152,90,135,148],[154,99,90,135,148],[154,99,152,90,135,148],[2,99,152,90,135,148],[71,99,90,135,148],[71,99,152,90,135,148],[133,90,99,152],[133,135,90,99,152],[133,148,90,99,152],[133,135,148,90,99,152],[156,135,148,90,99,152],[8,135,90,99,152],[8,135,148,90,99,152],[28,148,90,99,152],[28,135,148,90,99,152],[134,90,99,148],[134,135,90,99,148],[134,152,90,99,148],[134,135,152,90,99,148],[156,135,152,90,99,148],[3,135,90,99,148],[3,135,152,90,99,148],[28,152,90,99,148],[28,135,152,90,99,148],[147,90,99,135],[147,148,90,99,135],[147,152,90,99,135],[147,148,152,90,99,135],[156,148,152,90,99,135],[3,148,90,99,135],[3,148,152,90,99,135],[8,152,90,99,135],[8,148,152,90,99,135]]
def edges3 : Array (List W) := eids3.map shape
set_option maxRecDepth 16000 in
theorem follow3 : follows 5 r3 = edges3.toList := by decide +kernel
def eids4 : Array (List Nat) := #[[105,113,128,144,152],[105,90,113,128,144,152],[105,99,113,128,144,152],[61,99,113,128,144,152],[72,90,113,128,144,152],[114,113,99,128,144,152],[45,113,99,128,144,152],[75,90,99,113,144,152],[75,128,99,113,144,152],[146,99,113,128,152],[146,90,99,113,128,152],[146,144,99,113,128,152],[10,144,99,113,128,152],[79,90,99,113,128,152],[89,152,99,113,128,144],[81,152,99,113,128,144],[116,113,90,128,144,152],[46,113,90,128,144,152],[131,90,113,144,152],[131,99,90,113,144,152],[131,128,90,113,144,152],[31,128,90,113,144,152],[65,99,90,113,144,152],[67,99,90,113,128,152],[67,144,90,113,128,152],[98,152,90,113,128,144],[71,152,90,113,128,144],[136,113,90,99,144,152],[49,113,90,99,144,152],[150,113,90,99,128,152],[53,113,90,99,128,152],[156,113,90,99,128,144],[54,113,90,99,128,144],[126,90,99,113,152],[126,128,90,99,113,152],[126,144,90,99,113,152],[14,128,90,99,113,152],[33,144,90,99,113,152],[127,152,90,99,113,144],[32,152,90,99,113,144],[143,152,90,99,113,128],[13,152,90,99,113,128]]
def edges4 : Array (List W) := eids4.map shape
set_option maxRecDepth 16000 in
theorem follow4 : follows 5 r4 = edges4.toList := by decide +kernel
def eids5 : Array (List Nat) := #[[120,90,130,148,152],[74,90,130,148,152],[131,90,116,148,152],[76,90,116,148,152],[149,90,116,130,152],[80,90,116,130,152],[153,90,116,130,148],[81,90,116,130,148],[115,90,130,148],[115,116,90,130,148],[115,152,90,130,148],[4,116,90,130,148],[44,152,90,130,148],[129,90,116,152],[129,130,90,116,152],[129,148,90,116,152],[9,130,90,116,152],[30,148,90,116,152]]
def edges5 : Array (List W) := eids5.map shape
set_option maxRecDepth 16000 in
theorem follow5 : follows 4 r5 = edges5.toList := by decide +kernel
def eids6 : Array (List Nat) := #[[105,114,130,148,152],[131,99,114,148,152],[153,99,114,130,148],[120,90,130,148,152],[150,90,114,130,152],[138,90,99,148,152]]
def edges6 : Array (List W) := eids6.map shape
set_option maxRecDepth 16000 in
theorem follow6 : follows 4 r6 = edges6.toList := by decide +kernel
def eids7 : Array (List Nat) := #[]
def edges7 : Array (List W) := eids7.map shape
set_option maxRecDepth 16000 in
theorem follow7 : follows 3 r7 = edges7.toList := by decide +kernel
def eids8 : Array (List Nat) := #[[82,105,113,125,148,152],[114,99,105,125,148,152],[128,99,105,113,148,152],[149,99,105,113,125,152],[153,99,105,113,125,148],[116,90,105,125,148,152],[130,90,105,113,148,152],[150,90,105,113,125,152],[154,90,105,113,125,148],[120,90,99,125,148,152],[55,90,99,125,148,152],[131,90,99,113,148,152],[56,90,99,113,148,152],[151,90,99,113,125,152],[59,90,99,113,125,152],[155,90,99,113,125,148],[60,90,99,113,125,148],[135,90,99,105,148,152],[112,90,99,105,125,148],[124,90,99,105,113,152],[147,90,99,105,113,125]]
def edges8 : Array (List W) := eids8.map shape
set_option maxRecDepth 16000 in
theorem follow8 : follows 5 r8 = edges8.toList := by decide +kernel
def eids9 : Array (List Nat) := #[[105,113,125,141,144,149],[87,99,113,125,141,149],[80,99,113,125,141,144],[116,90,125,141,144,149],[95,90,113,125,144,149],[68,90,113,125,144,149],[97,90,113,125,141,144],[70,90,113,125,141,144],[109,90,99,125,144,149],[52,90,99,125,144,149],[140,90,99,113,125,149],[142,90,99,113,125,141],[12,90,99,113,125,141]]
def edges9 : Array (List W) := eids9.map shape
set_option maxRecDepth 16000 in
theorem follow9 : follows 5 r9 = edges9.toList := by decide +kernel
def eids10 : Array (List Nat) := #[[82,90,99,113,120,125,139],[105,90,99,113,120,125,139],[61,90,99,113,120,125,139],[72,90,99,113,120,125,139],[83,90,113,99,120,125,139],[114,90,113,99,120,125,139],[45,90,113,99,120,125,139],[73,90,113,99,120,125,139],[0,90,99,113,125,139],[0,90,120,99,113,125,139],[74,90,99,113,125,139],[74,120,99,113,125,139],[74,90,120,99,113,125,139],[84,90,125,99,113,120,139],[128,125,99,113,120,139],[128,90,125,99,113,120,139],[34,125,99,113,120,139],[34,90,125,99,113,120,139],[75,90,125,99,113,120,139],[86,90,139,99,113,120,125],[141,139,99,113,120,125],[141,90,139,99,113,120,125],[18,139,99,113,120,125],[18,90,139,99,113,120,125],[78,90,139,99,113,120,125],[91,99,113,90,120,125,139],[116,99,113,90,120,125,139],[46,99,113,90,120,125,139],[62,99,113,90,120,125,139],[0,99,90,113,125,139],[0,99,120,90,113,125,139],[63,99,90,113,125,139],[63,120,90,113,125,139],[63,99,120,90,113,125,139],[92,99,125,90,113,120,139],[130,125,90,113,120,139],[130,99,125,90,113,120,139],[35,125,90,113,120,139],[35,99,125,90,113,120,139],[64,99,125,90,113,120,139],[94,99,139,90,113,120,125],[144,139,90,113,120,125],[144,99,139,90,113,120,125],[19,139,90,113,120,125],[19,99,139,90,113,120,125],[67,99,139,90,113,120,125],[0,113,90,99,125,139],[0,113,120,90,99,125,139],[47,113,90,99,125,139],[47,120,90,99,125,139],[47,113,120,90,99,125,139],[106,113,125,90,99,120,139],[135,125,90,99,120,139],[135,113,125,90,99,120,139],[37,125,90,99,120,139],[37,113,125,90,99,120,139],[48,113,125,90,99,120,139],[108,113,139,90,99,120,125],[148,139,90,99,120,125],[148,113,139,90,99,120,125],[21,139,90,99,120,125],[21,113,139,90,99,120,125],[51,113,139,90,99,120,125],[117,125,90,99,113,139],[117,120,125,90,99,113,139],[138,125,90,99,113,139],[138,120,125,90,99,113,139],[38,125,90,99,113,139],[38,120,125,90,99,113,139],[42,125,90,99,113,139],[42,120,125,90,99,113,139],[119,139,90,99,113,125],[119,120,139,90,99,113,125],[151,139,90,99,113,125],[151,120,139,90,99,113,125],[22,139,90,99,113,125],[22,120,139,90,99,113,125],[43,139,90,99,113,125],[43,120,139,90,99,113,125],[121,125,139,90,99,113,120],[152,125,139,90,99,113,120],[23,125,139,90,99,113,120],[39,125,139,90,99,113,120]]
def edges10 : Array (List W) := eids10.map shape
set_option maxRecDepth 16000 in
theorem follow10 : follows 6 r10 = edges10.toList := by decide +kernel
def eids11 : Array (List Nat) := #[[82,105,113,120,125,139],[82,90,105,113,120,125,139],[82,99,105,113,120,125,139],[61,90,105,113,120,125,139],[72,99,105,113,120,125,139],[0,90,99,113,120,125,139],[72,90,99,113,120,125,139],[72,105,99,113,120,125,139],[114,113,99,105,120,125,139],[45,113,99,105,120,125,139],[0,90,99,105,113,125,139],[74,99,105,113,125,139],[74,90,99,105,113,125,139],[74,120,99,105,113,125,139],[128,125,99,105,113,120,139],[34,125,99,105,113,120,139],[141,139,99,105,113,120,125],[18,139,99,105,113,120,125],[0,99,90,113,120,125,139],[61,99,90,113,120,125,139],[61,105,90,113,120,125,139],[116,113,90,105,120,125,139],[46,113,90,105,120,125,139],[0,99,90,105,113,125,139],[63,90,105,113,125,139],[63,99,90,105,113,125,139],[63,120,90,105,113,125,139],[130,125,90,105,113,120,139],[35,125,90,105,113,120,139],[144,139,90,105,113,120,125],[19,139,90,105,113,120,125],[100,90,99,120,125,139],[100,105,90,99,120,125,139],[100,113,90,99,120,125,139],[47,90,99,120,125,139],[47,105,90,99,120,125,139],[47,113,90,99,120,125,139],[55,113,90,99,120,125,139],[0,90,99,113,125,139],[0,105,90,99,113,125,139],[0,120,90,99,113,125,139],[55,90,99,113,125,139],[55,105,90,99,113,125,139],[55,120,90,99,113,125,139],[101,125,90,99,113,120,139],[131,125,90,99,113,120,139],[36,125,90,99,113,120,139],[56,125,90,99,113,120,139],[103,139,90,99,113,120,125],[146,139,90,99,113,120,125],[20,139,90,99,113,120,125],[58,139,90,99,113,120,125],[0,113,90,99,105,125,139],[47,113,90,99,105,125,139],[47,120,90,99,105,125,139],[135,125,90,99,105,120,139],[37,125,90,99,105,120,139],[148,139,90,99,105,120,125],[21,139,90,99,105,120,125],[117,125,90,99,105,113,139],[138,125,90,99,105,113,139],[38,125,90,99,105,113,139],[42,125,90,99,105,113,139],[119,139,90,99,105,113,125],[151,139,90,99,105,113,125],[22,139,90,99,105,113,125],[43,139,90,99,105,113,125]]
def edges11 : Array (List W) := eids11.map shape
set_option maxRecDepth 16000 in
theorem follow11 : follows 6 r11 = edges11.toList := by decide +kernel
def eids12 : Array (List Nat) := #[[82,113,120,125,131,139],[135,90,99,120,131,139],[107,90,99,120,125,139],[50,90,99,120,125,139],[117,90,99,113,131,139],[38,90,99,113,131,139],[118,90,99,113,125,139],[138,90,99,113,125,139],[29,90,99,113,125,139],[42,90,99,113,125,139]]
def edges12 : Array (List W) := eids12.map shape
set_option maxRecDepth 16000 in
theorem follow12 : follows 5 r12 = edges12.toList := by decide +kernel
def eids13 : Array (List Nat) := #[[82,105,113,125,146,148],[114,99,105,125,146,148],[79,99,105,113,125,148],[116,90,105,125,146,148],[68,90,105,113,125,148],[120,90,99,125,146,148],[55,90,99,125,146,148],[58,90,99,113,125,148],[104,90,99,113,125,146],[7,90,99,113,125,146],[111,90,99,105,125,148],[145,90,99,105,113,125]]
def edges13 : Array (List W) := eids13.map shape
set_option maxRecDepth 16000 in
theorem follow13 : follows 5 r13 = edges13.toList := by decide +kernel
def eids14 : Array (List Nat) := #[[82,105,113,125,135,139],[82,90,105,113,125,135,139],[82,99,105,113,125,135,139],[61,90,105,113,125,135,139],[72,99,105,113,125,135,139],[0,90,99,113,125,135,139],[72,90,99,113,125,135,139],[72,105,99,113,125,135,139],[114,99,105,125,135,139],[114,90,99,105,125,135,139],[114,113,99,105,125,135,139],[45,113,99,105,125,135,139],[73,90,99,105,125,135,139],[128,99,105,113,135,139],[128,90,99,105,113,135,139],[128,125,99,105,113,135,139],[34,125,99,105,113,135,139],[75,90,99,105,113,135,139],[85,90,99,105,113,125,139],[136,99,105,113,125,139],[136,90,99,105,113,125,139],[136,135,99,105,113,125,139],[25,99,105,113,125,139],[25,90,99,105,113,125,139],[25,135,99,105,113,125,139],[77,90,99,105,113,125,139],[141,139,99,105,113,125,135],[18,139,99,105,113,125,135],[0,99,90,113,125,135,139],[61,99,90,113,125,135,139],[61,105,90,113,125,135,139],[116,90,105,125,135,139],[116,99,90,105,125,135,139],[116,113,90,105,125,135,139],[46,113,90,105,125,135,139],[62,99,90,105,125,135,139],[130,90,105,113,135,139],[130,99,90,105,113,135,139],[130,125,90,105,113,135,139],[35,125,90,105,113,135,139],[64,99,90,105,113,135,139],[93,99,90,105,113,125,139],[137,90,105,113,125,139],[137,99,90,105,113,125,139],[137,135,90,105,113,125,139],[26,90,105,113,125,139],[26,99,90,105,113,125,139],[26,135,90,105,113,125,139],[66,99,90,105,113,125,139],[144,139,90,105,113,125,135],[19,139,90,105,113,125,135],[100,113,90,99,125,135,139],[120,90,99,125,135,139],[120,105,90,99,125,135,139],[120,113,90,99,125,135,139],[47,113,90,99,125,135,139],[55,90,99,125,135,139],[55,105,90,99,125,135,139],[55,113,90,99,125,135,139],[101,125,90,99,113,135,139],[131,90,99,113,135,139],[131,105,90,99,113,135,139],[131,125,90,99,113,135,139],[36,125,90,99,113,135,139],[56,90,99,113,135,139],[56,105,90,99,113,135,139],[56,125,90,99,113,135,139],[102,90,99,113,125,139],[102,105,90,99,113,125,139],[102,135,90,99,113,125,139],[138,90,99,113,125,139],[138,105,90,99,113,125,139],[138,135,90,99,113,125,139],[27,90,99,113,125,139],[27,105,90,99,113,125,139],[27,135,90,99,113,125,139],[57,90,99,113,125,139],[57,105,90,99,113,125,139],[57,135,90,99,113,125,139],[103,139,90,99,113,125,135],[146,139,90,99,113,125,135],[20,139,90,99,113,125,135],[58,139,90,99,113,125,135],[106,90,99,105,135,139],[106,113,90,99,105,135,139],[106,125,90,99,105,135,139],[37,113,90,99,105,135,139],[48,125,90,99,105,135,139],[0,113,90,99,105,125,139],[48,113,90,99,105,125,139],[48,135,90,99,105,125,139],[148,139,90,99,105,125,135],[21,139,90,99,105,125,135],[0,125,90,99,105,113,139],[37,125,90,99,105,113,139],[37,135,90,99,105,113,139],[152,139,90,99,105,113,135],[23,139,90,99,105,113,135],[132,139,90,99,105,113,125],[156,139,90,99,105,113,125],[24,139,90,99,105,113,125],[28,139,90,99,105,113,125]]
def edges14 : Array (List W) := eids14.map shape
set_option maxRecDepth 16000 in
theorem follow14 : follows 6 r14 = edges14.toList := by decide +kernel
end K5Cache

namespace K5Cache
open GThreshold

def rd (a : Array W) (j : Nat) : W := a[j]?.getD 0

def op4 (o : Nat) (a b : W) : W :=
  if o = 0 then a &&& b else if o = 1 then a ||| b else
    if o = 2 then a &&& ~~~b else b &&& ~~~a

def appendWire (v : Array W) (g : Nat × Nat × Nat) : Array W :=
  v.push (op4 g.2.2 (rd v g.1) (rd v g.2.1))

def runProg (gs : List (Nat × Nat × Nat)) (v : Array W) := gs.foldl appendWire v

theorem pin_zero (i : Fin 5) : restriction i 0 = 0 := by
  have h0 : ∀ q : Fin 512, (0 : W)[q.val] = false := by decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [restriction_bit]
  exact (h0 _).trans (h0 ⟨j,hj⟩).symm

theorem pin_op4 (i : Fin 5) (o : Nat) (x y : W) :
    restriction i (op4 o x y) = op4 o (restriction i x) (restriction i y) := by
  unfold op4
  split_ifs <;> apply BitVec.eq_of_getElem_eq <;> intro j hj <;>
    simp only [restriction_bit,BitVec.getElem_or,BitVec.getElem_and,BitVec.getElem_not]

theorem rd_map_pin (v : Array W) (i : Fin 5) (j : Nat) :
    rd (v.map (restriction i)) j = restriction i (rd v j) := by
  unfold rd
  rw [Array.getElem?_map]
  cases v[j]? with
  | none => exact (pin_zero i).symm
  | some w => rfl

theorem run_map_pin (i : Fin 5) (gs : List (Nat × Nat × Nat)) (v : Array W) :
    (runProg gs v).map (restriction i) = runProg gs (v.map (restriction i)) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    change (runProg gs (appendWire v g)).map _ = runProg gs (appendWire (v.map _) g)
    rw [ih]
    congr 1
    simp [appendWire,Array.map_push,rd_map_pin,pin_op4]

end K5Cache

namespace K5Cache
open GThreshold
set_option maxRecDepth 4000 in
theorem slot0_0 : restriction 0 (rd fullInputs 0) = rd (pinInputs 0) 0 := by
  have src : rd fullInputs 0 = vinput 0 := by decide +kernel
  have dst : rd (pinInputs 0) 0 = (0 : W) := by decide +kernel
  have mid : restriction 0 (vinput 0) = (0 : W) := projected_input 0
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot0_1 : restriction 0 (rd fullInputs 1) = rd (pinInputs 0) 1 := by
  have src : rd fullInputs 1 = vinput 1 := by decide +kernel
  have dst : rd (pinInputs 0) 1 = k4inputs.getD 0 0 := by decide +kernel
  have mid : restriction 0 (vinput 1) = k4inputs.getD 0 0 := congrArg (fun xs : List W => xs.getD 0 0) (remaining_same 0)
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot0_2 : restriction 0 (rd fullInputs 2) = rd (pinInputs 0) 2 := by
  have src : rd fullInputs 2 = vinput 2 := by decide +kernel
  have dst : rd (pinInputs 0) 2 = k4inputs.getD 1 0 := by decide +kernel
  have mid : restriction 0 (vinput 2) = k4inputs.getD 1 0 := congrArg (fun xs : List W => xs.getD 1 0) (remaining_same 0)
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot0_3 : restriction 0 (rd fullInputs 3) = rd (pinInputs 0) 3 := by
  have src : rd fullInputs 3 = vinput 3 := by decide +kernel
  have dst : rd (pinInputs 0) 3 = k4inputs.getD 2 0 := by decide +kernel
  have mid : restriction 0 (vinput 3) = k4inputs.getD 2 0 := congrArg (fun xs : List W => xs.getD 2 0) (remaining_same 0)
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot0_4 : restriction 0 (rd fullInputs 4) = rd (pinInputs 0) 4 := by
  have src : rd fullInputs 4 = vinput 4 := by decide +kernel
  have dst : rd (pinInputs 0) 4 = k4inputs.getD 3 0 := by decide +kernel
  have mid : restriction 0 (vinput 4) = k4inputs.getD 3 0 := congrArg (fun xs : List W => xs.getD 3 0) (remaining_same 0)
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot0_5 : restriction 0 (rd fullInputs 5) = rd (pinInputs 0) 5 := by
  have src : rd fullInputs 5 = (0 : W) := by decide +kernel
  have dst : rd (pinInputs 0) 5 = (0 : W) := by decide +kernel
  have mid : restriction 0 ((0 : W)) = (0 : W) := pin_zero 0
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot0_6 : restriction 0 (rd fullInputs 6) = rd (pinInputs 0) 6 := by
  have src : rd fullInputs 6 = (~~~(0 : W)) := by decide +kernel
  have dst : rd (pinInputs 0) 6 = (~~~(0 : W)) := by decide +kernel
  have mid : restriction 0 ((~~~(0 : W))) = (~~~(0 : W)) := (restriction_not 0 0).trans (congrArg (fun t : W => ~~~t) (pin_zero 0))
  exact (congrArg (restriction 0) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_0 : restriction 1 (rd fullInputs 0) = rd (pinInputs 1) 0 := by
  have src : rd fullInputs 0 = vinput 0 := by decide +kernel
  have dst : rd (pinInputs 1) 0 = k4inputs.getD 0 0 := by decide +kernel
  have mid : restriction 1 (vinput 0) = k4inputs.getD 0 0 := congrArg (fun xs : List W => xs.getD 0 0) (remaining_same 1)
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_1 : restriction 1 (rd fullInputs 1) = rd (pinInputs 1) 1 := by
  have src : rd fullInputs 1 = vinput 1 := by decide +kernel
  have dst : rd (pinInputs 1) 1 = (0 : W) := by decide +kernel
  have mid : restriction 1 (vinput 1) = (0 : W) := projected_input 1
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_2 : restriction 1 (rd fullInputs 2) = rd (pinInputs 1) 2 := by
  have src : rd fullInputs 2 = vinput 2 := by decide +kernel
  have dst : rd (pinInputs 1) 2 = k4inputs.getD 1 0 := by decide +kernel
  have mid : restriction 1 (vinput 2) = k4inputs.getD 1 0 := congrArg (fun xs : List W => xs.getD 1 0) (remaining_same 1)
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_3 : restriction 1 (rd fullInputs 3) = rd (pinInputs 1) 3 := by
  have src : rd fullInputs 3 = vinput 3 := by decide +kernel
  have dst : rd (pinInputs 1) 3 = k4inputs.getD 2 0 := by decide +kernel
  have mid : restriction 1 (vinput 3) = k4inputs.getD 2 0 := congrArg (fun xs : List W => xs.getD 2 0) (remaining_same 1)
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_4 : restriction 1 (rd fullInputs 4) = rd (pinInputs 1) 4 := by
  have src : rd fullInputs 4 = vinput 4 := by decide +kernel
  have dst : rd (pinInputs 1) 4 = k4inputs.getD 3 0 := by decide +kernel
  have mid : restriction 1 (vinput 4) = k4inputs.getD 3 0 := congrArg (fun xs : List W => xs.getD 3 0) (remaining_same 1)
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_5 : restriction 1 (rd fullInputs 5) = rd (pinInputs 1) 5 := by
  have src : rd fullInputs 5 = (0 : W) := by decide +kernel
  have dst : rd (pinInputs 1) 5 = (0 : W) := by decide +kernel
  have mid : restriction 1 ((0 : W)) = (0 : W) := pin_zero 1
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot1_6 : restriction 1 (rd fullInputs 6) = rd (pinInputs 1) 6 := by
  have src : rd fullInputs 6 = (~~~(0 : W)) := by decide +kernel
  have dst : rd (pinInputs 1) 6 = (~~~(0 : W)) := by decide +kernel
  have mid : restriction 1 ((~~~(0 : W))) = (~~~(0 : W)) := (restriction_not 1 0).trans (congrArg (fun t : W => ~~~t) (pin_zero 1))
  exact (congrArg (restriction 1) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_0 : restriction 2 (rd fullInputs 0) = rd (pinInputs 2) 0 := by
  have src : rd fullInputs 0 = vinput 0 := by decide +kernel
  have dst : rd (pinInputs 2) 0 = k4inputs.getD 0 0 := by decide +kernel
  have mid : restriction 2 (vinput 0) = k4inputs.getD 0 0 := congrArg (fun xs : List W => xs.getD 0 0) (remaining_same 2)
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_1 : restriction 2 (rd fullInputs 1) = rd (pinInputs 2) 1 := by
  have src : rd fullInputs 1 = vinput 1 := by decide +kernel
  have dst : rd (pinInputs 2) 1 = k4inputs.getD 1 0 := by decide +kernel
  have mid : restriction 2 (vinput 1) = k4inputs.getD 1 0 := congrArg (fun xs : List W => xs.getD 1 0) (remaining_same 2)
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_2 : restriction 2 (rd fullInputs 2) = rd (pinInputs 2) 2 := by
  have src : rd fullInputs 2 = vinput 2 := by decide +kernel
  have dst : rd (pinInputs 2) 2 = (0 : W) := by decide +kernel
  have mid : restriction 2 (vinput 2) = (0 : W) := projected_input 2
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_3 : restriction 2 (rd fullInputs 3) = rd (pinInputs 2) 3 := by
  have src : rd fullInputs 3 = vinput 3 := by decide +kernel
  have dst : rd (pinInputs 2) 3 = k4inputs.getD 2 0 := by decide +kernel
  have mid : restriction 2 (vinput 3) = k4inputs.getD 2 0 := congrArg (fun xs : List W => xs.getD 2 0) (remaining_same 2)
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_4 : restriction 2 (rd fullInputs 4) = rd (pinInputs 2) 4 := by
  have src : rd fullInputs 4 = vinput 4 := by decide +kernel
  have dst : rd (pinInputs 2) 4 = k4inputs.getD 3 0 := by decide +kernel
  have mid : restriction 2 (vinput 4) = k4inputs.getD 3 0 := congrArg (fun xs : List W => xs.getD 3 0) (remaining_same 2)
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_5 : restriction 2 (rd fullInputs 5) = rd (pinInputs 2) 5 := by
  have src : rd fullInputs 5 = (0 : W) := by decide +kernel
  have dst : rd (pinInputs 2) 5 = (0 : W) := by decide +kernel
  have mid : restriction 2 ((0 : W)) = (0 : W) := pin_zero 2
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot2_6 : restriction 2 (rd fullInputs 6) = rd (pinInputs 2) 6 := by
  have src : rd fullInputs 6 = (~~~(0 : W)) := by decide +kernel
  have dst : rd (pinInputs 2) 6 = (~~~(0 : W)) := by decide +kernel
  have mid : restriction 2 ((~~~(0 : W))) = (~~~(0 : W)) := (restriction_not 2 0).trans (congrArg (fun t : W => ~~~t) (pin_zero 2))
  exact (congrArg (restriction 2) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_0 : restriction 3 (rd fullInputs 0) = rd (pinInputs 3) 0 := by
  have src : rd fullInputs 0 = vinput 0 := by decide +kernel
  have dst : rd (pinInputs 3) 0 = k4inputs.getD 0 0 := by decide +kernel
  have mid : restriction 3 (vinput 0) = k4inputs.getD 0 0 := congrArg (fun xs : List W => xs.getD 0 0) (remaining_same 3)
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_1 : restriction 3 (rd fullInputs 1) = rd (pinInputs 3) 1 := by
  have src : rd fullInputs 1 = vinput 1 := by decide +kernel
  have dst : rd (pinInputs 3) 1 = k4inputs.getD 1 0 := by decide +kernel
  have mid : restriction 3 (vinput 1) = k4inputs.getD 1 0 := congrArg (fun xs : List W => xs.getD 1 0) (remaining_same 3)
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_2 : restriction 3 (rd fullInputs 2) = rd (pinInputs 3) 2 := by
  have src : rd fullInputs 2 = vinput 2 := by decide +kernel
  have dst : rd (pinInputs 3) 2 = k4inputs.getD 2 0 := by decide +kernel
  have mid : restriction 3 (vinput 2) = k4inputs.getD 2 0 := congrArg (fun xs : List W => xs.getD 2 0) (remaining_same 3)
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_3 : restriction 3 (rd fullInputs 3) = rd (pinInputs 3) 3 := by
  have src : rd fullInputs 3 = vinput 3 := by decide +kernel
  have dst : rd (pinInputs 3) 3 = (0 : W) := by decide +kernel
  have mid : restriction 3 (vinput 3) = (0 : W) := projected_input 3
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_4 : restriction 3 (rd fullInputs 4) = rd (pinInputs 3) 4 := by
  have src : rd fullInputs 4 = vinput 4 := by decide +kernel
  have dst : rd (pinInputs 3) 4 = k4inputs.getD 3 0 := by decide +kernel
  have mid : restriction 3 (vinput 4) = k4inputs.getD 3 0 := congrArg (fun xs : List W => xs.getD 3 0) (remaining_same 3)
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_5 : restriction 3 (rd fullInputs 5) = rd (pinInputs 3) 5 := by
  have src : rd fullInputs 5 = (0 : W) := by decide +kernel
  have dst : rd (pinInputs 3) 5 = (0 : W) := by decide +kernel
  have mid : restriction 3 ((0 : W)) = (0 : W) := pin_zero 3
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot3_6 : restriction 3 (rd fullInputs 6) = rd (pinInputs 3) 6 := by
  have src : rd fullInputs 6 = (~~~(0 : W)) := by decide +kernel
  have dst : rd (pinInputs 3) 6 = (~~~(0 : W)) := by decide +kernel
  have mid : restriction 3 ((~~~(0 : W))) = (~~~(0 : W)) := (restriction_not 3 0).trans (congrArg (fun t : W => ~~~t) (pin_zero 3))
  exact (congrArg (restriction 3) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_0 : restriction 4 (rd fullInputs 0) = rd (pinInputs 4) 0 := by
  have src : rd fullInputs 0 = vinput 0 := by decide +kernel
  have dst : rd (pinInputs 4) 0 = k4inputs.getD 0 0 := by decide +kernel
  have mid : restriction 4 (vinput 0) = k4inputs.getD 0 0 := congrArg (fun xs : List W => xs.getD 0 0) (remaining_same 4)
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_1 : restriction 4 (rd fullInputs 1) = rd (pinInputs 4) 1 := by
  have src : rd fullInputs 1 = vinput 1 := by decide +kernel
  have dst : rd (pinInputs 4) 1 = k4inputs.getD 1 0 := by decide +kernel
  have mid : restriction 4 (vinput 1) = k4inputs.getD 1 0 := congrArg (fun xs : List W => xs.getD 1 0) (remaining_same 4)
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_2 : restriction 4 (rd fullInputs 2) = rd (pinInputs 4) 2 := by
  have src : rd fullInputs 2 = vinput 2 := by decide +kernel
  have dst : rd (pinInputs 4) 2 = k4inputs.getD 2 0 := by decide +kernel
  have mid : restriction 4 (vinput 2) = k4inputs.getD 2 0 := congrArg (fun xs : List W => xs.getD 2 0) (remaining_same 4)
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_3 : restriction 4 (rd fullInputs 3) = rd (pinInputs 4) 3 := by
  have src : rd fullInputs 3 = vinput 3 := by decide +kernel
  have dst : rd (pinInputs 4) 3 = k4inputs.getD 3 0 := by decide +kernel
  have mid : restriction 4 (vinput 3) = k4inputs.getD 3 0 := congrArg (fun xs : List W => xs.getD 3 0) (remaining_same 4)
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_4 : restriction 4 (rd fullInputs 4) = rd (pinInputs 4) 4 := by
  have src : rd fullInputs 4 = vinput 4 := by decide +kernel
  have dst : rd (pinInputs 4) 4 = (0 : W) := by decide +kernel
  have mid : restriction 4 (vinput 4) = (0 : W) := projected_input 4
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_5 : restriction 4 (rd fullInputs 5) = rd (pinInputs 4) 5 := by
  have src : rd fullInputs 5 = (0 : W) := by decide +kernel
  have dst : rd (pinInputs 4) 5 = (0 : W) := by decide +kernel
  have mid : restriction 4 ((0 : W)) = (0 : W) := pin_zero 4
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
set_option maxRecDepth 4000 in
theorem slot4_6 : restriction 4 (rd fullInputs 6) = rd (pinInputs 4) 6 := by
  have src : rd fullInputs 6 = (~~~(0 : W)) := by decide +kernel
  have dst : rd (pinInputs 4) 6 = (~~~(0 : W)) := by decide +kernel
  have mid : restriction 4 ((~~~(0 : W))) = (~~~(0 : W)) := (restriction_not 4 0).trans (congrArg (fun t : W => ~~~t) (pin_zero 4))
  exact (congrArg (restriction 4) src).trans (mid.trans dst.symm)
theorem slot_ok : ∀ i : Fin 5, ∀ j : Fin 7, restriction i (rd fullInputs j.val) = rd (pinInputs i) j.val := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact slot0_0
  · exact slot0_1
  · exact slot0_2
  · exact slot0_3
  · exact slot0_4
  · exact slot0_5
  · exact slot0_6
  · exact slot1_0
  · exact slot1_1
  · exact slot1_2
  · exact slot1_3
  · exact slot1_4
  · exact slot1_5
  · exact slot1_6
  · exact slot2_0
  · exact slot2_1
  · exact slot2_2
  · exact slot2_3
  · exact slot2_4
  · exact slot2_5
  · exact slot2_6
  · exact slot3_0
  · exact slot3_1
  · exact slot3_2
  · exact slot3_3
  · exact slot3_4
  · exact slot3_5
  · exact slot3_6
  · exact slot4_0
  · exact slot4_1
  · exact slot4_2
  · exact slot4_3
  · exact slot4_4
  · exact slot4_5
  · exact slot4_6
theorem pin_roots (i : Fin 5) : fullInputs.map (restriction i) = pinInputs i := by
  have sz : (pinInputs i).size = 7 := by fin_cases i <;> rfl
  apply Array.ext (by rw [Array.size_map,sz]; rfl)
  intro j h hj
  rw [Array.getElem_map]
  have ha : j < fullInputs.size := by simpa using h
  have jb : j < 7 := sz ▸ hj
  have eq := slot_ok i ⟨j,jb⟩
  simpa only [rd,Array.getElem?_eq_getElem ha,Array.getElem?_eq_getElem hj,Option.getD_some] using eq
end K5Cache

namespace K5Cache
open GThreshold
def programWord (v : Array W) (j : Nat) : W := rd (runProg recipe v) (selected[j]?.getD 5)

set_option maxRecDepth 4000 in
theorem prog_orig : words5 = selected.map (rd (runProg recipe fullInputs)) := by decide +kernel

set_option maxRecDepth 4000 in
theorem prog_img : ∀ i : Fin 5,
    (pinIDs i).map (rd w4bank) = selected.map (rd (runProg recipe (pinInputs i))) := by decide +kernel

end K5Cache

namespace K5Cache
open GThreshold
set_option maxRecDepth 4000 in
theorem wire_prog (j : Nat) : wire j = programWord fullInputs j := by
  unfold wire programWord
  rw [prog_orig,Array.getElem?_map]
  cases h : selected[j]? with
  | some a => simp only [Option.map_some,Option.getD_some]
  | none => simp only [Option.map_none,Option.getD_none]; decide +kernel

theorem fast_prog (i : Fin 5) (j : Nat) : fastPin i j = programWord (pinInputs i) j := by
  have eq := congrArg (fun a : Array W => a[j]?.getD 0) (prog_img i)
  simp only [Array.getElem?_map] at eq
  unfold fastPin programWord
  cases a : (pinIDs i)[j]? <;> cases b : selected[j]? <;>
    simp only [a,b,Option.map_some,Option.map_none,Option.getD_none,Option.getD_some] at eq ⊢
  · fin_cases i <;> decide +kernel
  · exact eq
  · change rd w4bank _ = rd (runProg recipe (pinInputs i)) 5
    rw [show rd (runProg recipe (pinInputs i)) 5 = 0 from by fin_cases i <;> decide +kernel]
    exact eq
  · exact eq

theorem pin_wire (i : Fin 5) (j : Nat) : restriction i (wire j) = fastPin i j := by
  rw [wire_prog,fast_prog]
  unfold programWord
  rw [← rd_map_pin,run_map_pin,pin_roots]

end K5Cache

namespace K5Cache
open GThreshold

def okPin (k b : Nat) (i : Fin 5) (ns : List Nat) (xs : List W) : Bool :=
  decide (k ≤ b + ((ns.filter (fun j => fastPin i j == 0)).map wire).toFinset.card) &&
    ns.all (fun j => fastPin i j == 0 || xs.contains (fastPin i j))

theorem lost_codes (i : Fin 5) (ns : List Nat) :
    lost (restriction i) (shape ns).toFinset =
      ((ns.filter (fun j => fastPin i j == 0)).map wire).toFinset.card := by
  unfold lost
  congr 1
  ext w
  simp only [shape, Finset.mem_filter,List.mem_toFinset,List.mem_map,List.mem_filter,beq_iff_eq]
  constructor
  · rintro ⟨⟨j,hj,rfl⟩,hz⟩
    exact ⟨j,⟨hj,pin_wire i j ▸ hz⟩,rfl⟩
  · rintro ⟨j,⟨hj,hz⟩,rfl⟩
    exact ⟨⟨j,hj,rfl⟩,(pin_wire i j).trans hz⟩

theorem cutLink {t : W} (tg : t = goal ∨ t = ~~~goal)
    (ns : List Nat) (i : Fin 5) (k b : Nat) (xs : List W) (nd : xs.Nodup)
    (bound : search b xs = false) (ok : okPin k b i ns xs = true) :
    ¬live basicOps t k (shape ns).toFinset := by
  simp only [okPin,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨size,hall⟩ := ok
  refine projection_rejects tg i xs nd ?_ ?_ bound
  · intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    rw [pin_wire]
    have mem := List.all_eq_true.mp hall j hj
    simp only [Bool.or_eq_true] at mem
    rcases mem with z|h
    · exact Or.inl (beq_iff_eq.mp z)
    · exact .inr (.inr ⟨_,List.mem_toFinset.mpr (List.contains_iff_mem.mp h),Or.inl rfl⟩)
  · rw [lost_codes]
    exact size

theorem by_rows {t : W} (tg : t = goal ∨ t = ~~~goal) (k : Nat) (ws : List W)
    (nd : ws.Nodup) (neq : ws.toFinset ≠ {goal} ∧ ws.toFinset ≠ {~~~goal})
    (edges : Array (List W)) (same : follows k ws = edges.toList)
    (blocked : ∀ j : Fin edges.size, ¬live basicOps t k edges[j.val]!.toFinset) :
    ¬live basicOps t (k+1) ws.toFinset := by
  intro run
  rcases follows_complete nd tg run with he|⟨ns,hn,_,tail⟩
  · rcases tg with rfl|rfl
    · exact neq.1 he
    · exact neq.2 he
  · rw [same] at hn
    obtain ⟨j,hj,he⟩ := List.getElem_of_mem hn
    have ja : j < edges.size := by simpa using hj
    have eq : edges[j]! = ns := by
      rw [getElem!_pos edges j ja]
      exact he
    exact blocked ⟨j,ja⟩ (eq ▸ tail)

end K5Cache

namespace K5Cache
open GThreshold
def queries : Array (List W) := #[q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20,q21,q22,q23,q24,q25,q26,q27,q28,q29,q30,q31,q32,q33,q34,q35,q36,q37,q38,q39,q40,q41,q42,q43,q44,q45,q46,q47,q48,q49,q50,q51,q52,q53,q54,q55,q56,q57,q58,q59,q60,q61,q62,q63,q64,q65,q66,q67,q68,q69,q70,q71,q72,q73,q74,q75,q76,q77,q78,q79,q80,q81,q82,q83,q84,q85,q86,q87,q88,q89,q90,q91,q92,q93,q94,q95,q96,q97,q98,q99,q100,q101,q102,q103,q104,q105,q106,q107,q108,q109,q110,q111,q112,q113,q114,q115,q116,q117,q118,q119,q120,q121,q122,q123,q124,q125,q126,q127,q128,q129,q130,q131,q132,q133,q134,q135,q136,q137,q138,q139,q140,q141,q142,q143]
def budgets : Array Nat := #[6,5,4,3,4,4,4,4,4,4,4,5,4,4,4,4,4,4,5,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,4,4,5,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,4,5,5,4,5,5,5,5,5,5,5,5,5,5,5,5,4,4,4,4,4,4,4,3,5,5,4,4,4,4,4,4,4,6,6,6,5,4,5,5,5,5,5,5,5,4,5,5,5,5]
def Oracle : Prop := ∀ i : Fin 144, search budgets[i.val]! queries[i.val]! = false
end K5Cache

namespace K5Cache
open GThreshold
set_option maxRecDepth 16000 in
theorem hq2 : search 4 q2 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq3 : search 3 q3 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq4 : search 4 q4 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq5 : search 4 q5 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq6 : search 4 q6 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq7 : search 4 q7 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq8 : search 4 q8 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq9 : search 4 q9 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq10 : search 4 q10 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq12 : search 4 q12 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq13 : search 4 q13 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq14 : search 4 q14 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq15 : search 4 q15 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq16 : search 4 q16 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq17 : search 4 q17 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq19 : search 4 q19 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq20 : search 4 q20 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq21 : search 4 q21 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq22 : search 4 q22 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq23 : search 4 q23 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq24 : search 4 q24 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq25 : search 4 q25 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq26 : search 4 q26 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq27 : search 4 q27 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq28 : search 4 q28 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq29 : search 4 q29 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq30 : search 4 q30 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq31 : search 4 q31 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq32 : search 4 q32 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq33 : search 4 q33 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq34 : search 4 q34 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq35 : search 4 q35 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq36 : search 4 q36 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq37 : search 4 q37 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq38 : search 3 q38 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq39 : search 3 q39 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq40 : search 3 q40 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq41 : search 4 q41 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq42 : search 4 q42 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq43 : search 4 q43 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq44 : search 4 q44 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq45 : search 4 q45 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq46 : search 4 q46 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq47 : search 4 q47 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq48 : search 4 q48 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq49 : search 4 q49 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq50 : search 4 q50 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq51 : search 4 q51 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq52 : search 4 q52 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq53 : search 4 q53 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq54 : search 4 q54 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq55 : search 4 q55 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq56 : search 4 q56 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq57 : search 4 q57 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq58 : search 4 q58 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq59 : search 4 q59 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq60 : search 4 q60 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq61 : search 4 q61 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq62 : search 4 q62 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq63 : search 4 q63 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq64 : search 4 q64 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq65 : search 4 q65 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq69 : search 4 q69 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq70 : search 4 q70 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq72 : search 4 q72 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq73 : search 4 q73 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq74 : search 4 q74 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq75 : search 4 q75 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq76 : search 4 q76 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq77 : search 4 q77 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq78 : search 4 q78 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq79 : search 4 q79 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq80 : search 4 q80 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq81 : search 4 q81 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq82 : search 4 q82 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq83 : search 4 q83 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq94 : search 4 q94 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq97 : search 4 q97 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq110 : search 4 q110 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq111 : search 4 q111 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq112 : search 4 q112 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq113 : search 4 q113 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq114 : search 4 q114 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq115 : search 4 q115 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq116 : search 4 q116 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq117 : search 3 q117 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq120 : search 4 q120 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq121 : search 4 q121 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq122 : search 4 q122 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq123 : search 4 q123 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq124 : search 4 q124 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq125 : search 4 q125 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq126 : search 4 q126 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq131 : search 4 q131 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq139 : search 4 q139 = false := by decide +kernel
end K5Cache

namespace K5Cache
open GThreshold
set_option maxRecDepth 16000 in
theorem hq1 : search 5 q1 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq11 : search 5 q11 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq18 : search 5 q18 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq66 : search 5 q66 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq67 : search 5 q67 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq68 : search 5 q68 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq71 : search 5 q71 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq84 : search 5 q84 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq85 : search 5 q85 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq86 : search 5 q86 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq87 : search 5 q87 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq88 : search 5 q88 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq89 : search 5 q89 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq90 : search 5 q90 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq91 : search 5 q91 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq92 : search 5 q92 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq93 : search 5 q93 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq95 : search 5 q95 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq96 : search 5 q96 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq98 : search 5 q98 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq99 : search 5 q99 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq100 : search 5 q100 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq101 : search 5 q101 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq102 : search 5 q102 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq103 : search 5 q103 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq104 : search 5 q104 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq105 : search 5 q105 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq106 : search 5 q106 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq107 : search 5 q107 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq108 : search 5 q108 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq109 : search 5 q109 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq118 : search 5 q118 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq119 : search 5 q119 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq130 : search 5 q130 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq132 : search 5 q132 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq133 : search 5 q133 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq134 : search 5 q134 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq135 : search 5 q135 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq136 : search 5 q136 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq137 : search 5 q137 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq138 : search 5 q138 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq140 : search 5 q140 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq141 : search 5 q141 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq142 : search 5 q142 = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem hq143 : search 5 q143 = false := by decide +kernel
end K5Cache

namespace K5Cache
open GThreshold

theorem validHard (q raw : List W)
    (sizes : raw.length = 4 ∧ q.length = 5)
    (how : q.sublists.all (fun ws => (cuts ws != -1) || (ws == raw) || (ws == q)) = true)
    (a : optimized 6 3 raw = false) (b : optimized 6 2 q = false) :
    search 6 q = false := by
  unfold search
  apply List.any_eq_false.mpr
  intro ws hw
  by_cases hc : cuts ws = -1
  · have choice := List.all_eq_true.mp how ws hw
    simp only [hc, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at choice
    rcases choice with rfl | rfl
    · simp [sizes.1, a]
    · simp [sizes.2, b]
  · have hf : (cuts ws == (-1 : BitVec 256)) = false := beq_eq_false_iff_ne.mpr hc
    rw [hf]
    simp

set_option maxRecDepth 16000 in
theorem qh_r_0_1 : dispatch 3 (optimized 5) four43690 four52428 [four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_r_0_2 : dispatch 3 (optimized 5) four43690 four61680 [four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_r_0_3 : dispatch 3 (optimized 5) four43690 four65280 [four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_r_1_2 : dispatch 3 (optimized 5) four52428 four61680 [four43690,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_r_1_3 : dispatch 3 (optimized 5) four52428 four65280 [four43690,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_r_2_3 : dispatch 3 (optimized 5) four61680 four65280 [four43690,four52428] = false := by decide +kernel
theorem halt_r : optimized 6 3 [four43690,four52428,four61680,four65280] = false := by
  rw [optimized]
  have head : (([four43690,four52428,four61680,four65280] == [goal]) || ([four43690,four52428,four61680,four65280] == [~~~goal])) = false := by decide +kernel
  rw [head, Bool.false_or]
  simp only [pairs, singles, List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.any_cons, List.any_nil, qh_r_0_1, qh_r_0_2, qh_r_0_3, qh_r_1_2, qh_r_1_3, qh_r_2_3, Bool.false_or]
set_option maxRecDepth 16000 in
theorem qh_127_0_1 : dispatch 2 (optimized 5) four8738 four43690 [four52428,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_0_2 : dispatch 2 (optimized 5) four8738 four52428 [four43690,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_0_3 : dispatch 2 (optimized 5) four8738 four61680 [four43690,four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_0_4 : dispatch 2 (optimized 5) four8738 four65280 [four43690,four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_1_2 : dispatch 2 (optimized 5) four43690 four52428 [four8738,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_1_3 : dispatch 2 (optimized 5) four43690 four61680 [four8738,four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_1_4 : dispatch 2 (optimized 5) four43690 four65280 [four8738,four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_2_3 : dispatch 2 (optimized 5) four52428 four61680 [four8738,four43690,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_2_4 : dispatch 2 (optimized 5) four52428 four65280 [four8738,four43690,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_127_3_4 : dispatch 2 (optimized 5) four61680 four65280 [four8738,four43690,four52428] = false := by decide +kernel
theorem halt_127 : optimized 6 2 [four8738,four43690,four52428,four61680,four65280] = false := by
  rw [optimized]
  have head : (([four8738,four43690,four52428,four61680,four65280] == [goal]) || ([four8738,four43690,four52428,four61680,four65280] == [~~~goal])) = false := by decide +kernel
  rw [head, Bool.false_or]
  simp only [pairs, singles, List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.any_cons, List.any_nil, qh_127_0_1, qh_127_0_2, qh_127_0_3, qh_127_0_4, qh_127_1_2, qh_127_1_3, qh_127_1_4, qh_127_2_3, qh_127_2_4, qh_127_3_4, Bool.false_or]
set_option maxRecDepth 16000 in
theorem hq127 : search 6 q127 = false := validHard q127 q0 (by decide) (by decide +kernel) halt_r halt_127
set_option maxRecDepth 16000 in
theorem qh_128_0_1 : dispatch 2 (optimized 5) four2570 four43690 [four52428,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_0_2 : dispatch 2 (optimized 5) four2570 four52428 [four43690,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_0_3 : dispatch 2 (optimized 5) four2570 four61680 [four43690,four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_0_4 : dispatch 2 (optimized 5) four2570 four65280 [four43690,four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_1_2 : dispatch 2 (optimized 5) four43690 four52428 [four2570,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_1_3 : dispatch 2 (optimized 5) four43690 four61680 [four2570,four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_1_4 : dispatch 2 (optimized 5) four43690 four65280 [four2570,four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_2_3 : dispatch 2 (optimized 5) four52428 four61680 [four2570,four43690,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_2_4 : dispatch 2 (optimized 5) four52428 four65280 [four2570,four43690,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_128_3_4 : dispatch 2 (optimized 5) four61680 four65280 [four2570,four43690,four52428] = false := by decide +kernel
theorem halt_128 : optimized 6 2 [four2570,four43690,four52428,four61680,four65280] = false := by
  rw [optimized]
  have head : (([four2570,four43690,four52428,four61680,four65280] == [goal]) || ([four2570,four43690,four52428,four61680,four65280] == [~~~goal])) = false := by decide +kernel
  rw [head, Bool.false_or]
  simp only [pairs, singles, List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.any_cons, List.any_nil, qh_128_0_1, qh_128_0_2, qh_128_0_3, qh_128_0_4, qh_128_1_2, qh_128_1_3, qh_128_1_4, qh_128_2_3, qh_128_2_4, qh_128_3_4, Bool.false_or]
set_option maxRecDepth 16000 in
theorem hq128 : search 6 q128 = false := validHard q128 q0 (by decide) (by decide +kernel) halt_r halt_128
set_option maxRecDepth 16000 in
theorem qh_129_0_1 : dispatch 2 (optimized 5) four170 four43690 [four52428,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_0_2 : dispatch 2 (optimized 5) four170 four52428 [four43690,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_0_3 : dispatch 2 (optimized 5) four170 four61680 [four43690,four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_0_4 : dispatch 2 (optimized 5) four170 four65280 [four43690,four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_1_2 : dispatch 2 (optimized 5) four43690 four52428 [four170,four61680,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_1_3 : dispatch 2 (optimized 5) four43690 four61680 [four170,four52428,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_1_4 : dispatch 2 (optimized 5) four43690 four65280 [four170,four52428,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_2_3 : dispatch 2 (optimized 5) four52428 four61680 [four170,four43690,four65280] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_2_4 : dispatch 2 (optimized 5) four52428 four65280 [four170,four43690,four61680] = false := by decide +kernel
set_option maxRecDepth 16000 in
theorem qh_129_3_4 : dispatch 2 (optimized 5) four61680 four65280 [four170,four43690,four52428] = false := by decide +kernel
theorem halt_129 : optimized 6 2 [four170,four43690,four52428,four61680,four65280] = false := by
  rw [optimized]
  have head : (([four170,four43690,four52428,four61680,four65280] == [goal]) || ([four170,four43690,four52428,four61680,four65280] == [~~~goal])) = false := by decide +kernel
  rw [head, Bool.false_or]
  simp only [pairs, singles, List.map_nil, List.map_cons, List.nil_append, List.cons_append, List.any_cons, List.any_nil, qh_129_0_1, qh_129_0_2, qh_129_0_3, qh_129_0_4, qh_129_1_2, qh_129_1_3, qh_129_1_4, qh_129_2_3, qh_129_2_4, qh_129_3_4, Bool.false_or]
set_option maxRecDepth 16000 in
theorem hq129 : search 6 q129 = false := validHard q129 q0 (by decide) (by decide +kernel) halt_r halt_129
theorem hq0 : search 6 q0 = false := k4exact
end K5Cache

namespace K5Cache
open GThreshold
set_option maxRecDepth 10000 in
theorem verifiedOracle : Oracle := by
  intro j
  fin_cases j
  · exact hq0
  · exact hq1
  · exact hq2
  · exact hq3
  · exact hq4
  · exact hq5
  · exact hq6
  · exact hq7
  · exact hq8
  · exact hq9
  · exact hq10
  · exact hq11
  · exact hq12
  · exact hq13
  · exact hq14
  · exact hq15
  · exact hq16
  · exact hq17
  · exact hq18
  · exact hq19
  · exact hq20
  · exact hq21
  · exact hq22
  · exact hq23
  · exact hq24
  · exact hq25
  · exact hq26
  · exact hq27
  · exact hq28
  · exact hq29
  · exact hq30
  · exact hq31
  · exact hq32
  · exact hq33
  · exact hq34
  · exact hq35
  · exact hq36
  · exact hq37
  · exact hq38
  · exact hq39
  · exact hq40
  · exact hq41
  · exact hq42
  · exact hq43
  · exact hq44
  · exact hq45
  · exact hq46
  · exact hq47
  · exact hq48
  · exact hq49
  · exact hq50
  · exact hq51
  · exact hq52
  · exact hq53
  · exact hq54
  · exact hq55
  · exact hq56
  · exact hq57
  · exact hq58
  · exact hq59
  · exact hq60
  · exact hq61
  · exact hq62
  · exact hq63
  · exact hq64
  · exact hq65
  · exact hq66
  · exact hq67
  · exact hq68
  · exact hq69
  · exact hq70
  · exact hq71
  · exact hq72
  · exact hq73
  · exact hq74
  · exact hq75
  · exact hq76
  · exact hq77
  · exact hq78
  · exact hq79
  · exact hq80
  · exact hq81
  · exact hq82
  · exact hq83
  · exact hq84
  · exact hq85
  · exact hq86
  · exact hq87
  · exact hq88
  · exact hq89
  · exact hq90
  · exact hq91
  · exact hq92
  · exact hq93
  · exact hq94
  · exact hq95
  · exact hq96
  · exact hq97
  · exact hq98
  · exact hq99
  · exact hq100
  · exact hq101
  · exact hq102
  · exact hq103
  · exact hq104
  · exact hq105
  · exact hq106
  · exact hq107
  · exact hq108
  · exact hq109
  · exact hq110
  · exact hq111
  · exact hq112
  · exact hq113
  · exact hq114
  · exact hq115
  · exact hq116
  · exact hq117
  · exact hq118
  · exact hq119
  · exact hq120
  · exact hq121
  · exact hq122
  · exact hq123
  · exact hq124
  · exact hq125
  · exact hq126
  · exact hq127
  · exact hq128
  · exact hq129
  · exact hq130
  · exact hq131
  · exact hq132
  · exact hq133
  · exact hq134
  · exact hq135
  · exact hq136
  · exact hq137
  · exact hq138
  · exact hq139
  · exact hq140
  · exact hq141
  · exact hq142
  · exact hq143
end K5Cache

namespace K5Cache
open GThreshold
theorem nb {t : W} (tg : t = goal ∨ t = ~~~goal) (ans : Oracle)
    (ns : List Nat) (i : Fin 5) (k : Nat) (j : Fin 144)
    (ok : okPin k budgets[j.val]! i ns queries[j.val]! = true) :
    ¬ live basicOps t k (shape ns).toFinset := by
  have nd : ∀ j : Fin 144, queries[j.val]!.Nodup := by decide +kernel
  exact cutLink tg ns i k budgets[j.val]! queries[j.val]! (nd j) (ans j) ok
theorem nbAt {t : W} (tg : t = goal ∨ t = ~~~goal) (ans : Oracle)
    (ar : Array (List Nat)) (e : Nat) (he : e < ar.size) (i : Fin 5) (k : Nat) (j : Fin 144)
    (ok : okPin k budgets[j.val]! i ar[e]! queries[j.val]! = true) :
    ¬ live basicOps t k ((ar.map shape)[e]!).toFinset := by
  have eq : (ar.map shape)[e]! = shape ar[e]! := by
    rw [getElem!_pos (ar.map shape) e (by simpa using he), getElem!_pos ar e he, Array.getElem_map]
  rw [eq]
  exact nb tg ans ar[e]! i k j ok
theorem n0_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[0]!).toFinset :=
  nbAt h a eids0 0 (by decide) 0 8 0 (by decide +kernel)
theorem n0_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[2]!).toFinset :=
  nbAt h a eids0 2 (by decide) 0 8 0 (by decide +kernel)
theorem n0_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[3]!).toFinset :=
  nbAt h a eids0 3 (by decide) 1 8 0 (by decide +kernel)
theorem n0_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[4]!).toFinset :=
  nbAt h a eids0 4 (by decide) 0 8 0 (by decide +kernel)
theorem n0_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[6]!).toFinset :=
  nbAt h a eids0 6 (by decide) 0 8 0 (by decide +kernel)
theorem n0_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[7]!).toFinset :=
  nbAt h a eids0 7 (by decide) 2 8 0 (by decide +kernel)
theorem n0_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[8]!).toFinset :=
  nbAt h a eids0 8 (by decide) 0 8 0 (by decide +kernel)
theorem n0_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[10]!).toFinset :=
  nbAt h a eids0 10 (by decide) 0 8 0 (by decide +kernel)
theorem n0_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[11]!).toFinset :=
  nbAt h a eids0 11 (by decide) 3 8 0 (by decide +kernel)
theorem n0_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[12]!).toFinset :=
  nbAt h a eids0 12 (by decide) 0 8 0 (by decide +kernel)
theorem n0_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[14]!).toFinset :=
  nbAt h a eids0 14 (by decide) 0 8 0 (by decide +kernel)
theorem n0_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[15]!).toFinset :=
  nbAt h a eids0 15 (by decide) 4 8 0 (by decide +kernel)
theorem n0_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[16]!).toFinset :=
  nbAt h a eids0 16 (by decide) 1 8 0 (by decide +kernel)
theorem n0_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[18]!).toFinset :=
  nbAt h a eids0 18 (by decide) 1 8 0 (by decide +kernel)
theorem n0_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[19]!).toFinset :=
  nbAt h a eids0 19 (by decide) 2 8 0 (by decide +kernel)
theorem n0_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[20]!).toFinset :=
  nbAt h a eids0 20 (by decide) 1 8 0 (by decide +kernel)
theorem n0_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[22]!).toFinset :=
  nbAt h a eids0 22 (by decide) 1 8 0 (by decide +kernel)
theorem n0_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[23]!).toFinset :=
  nbAt h a eids0 23 (by decide) 3 8 0 (by decide +kernel)
theorem n0_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[24]!).toFinset :=
  nbAt h a eids0 24 (by decide) 1 8 0 (by decide +kernel)
theorem n0_26 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[26]!).toFinset :=
  nbAt h a eids0 26 (by decide) 1 8 0 (by decide +kernel)
theorem n0_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[27]!).toFinset :=
  nbAt h a eids0 27 (by decide) 4 8 0 (by decide +kernel)
theorem n0_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[28]!).toFinset :=
  nbAt h a eids0 28 (by decide) 2 8 0 (by decide +kernel)
theorem n0_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[30]!).toFinset :=
  nbAt h a eids0 30 (by decide) 2 8 0 (by decide +kernel)
theorem n0_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[31]!).toFinset :=
  nbAt h a eids0 31 (by decide) 3 8 0 (by decide +kernel)
theorem n0_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[32]!).toFinset :=
  nbAt h a eids0 32 (by decide) 2 8 0 (by decide +kernel)
theorem n0_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[34]!).toFinset :=
  nbAt h a eids0 34 (by decide) 2 8 0 (by decide +kernel)
theorem n0_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[35]!).toFinset :=
  nbAt h a eids0 35 (by decide) 4 8 0 (by decide +kernel)
theorem n0_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[36]!).toFinset :=
  nbAt h a eids0 36 (by decide) 3 8 0 (by decide +kernel)
theorem n0_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[38]!).toFinset :=
  nbAt h a eids0 38 (by decide) 3 8 0 (by decide +kernel)
theorem n0_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 (edges0[39]!).toFinset :=
  nbAt h a eids0 39 (by decide) 4 8 0 (by decide +kernel)
theorem n1_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[0]!).toFinset :=
  nbAt h a eids1 0 (by decide) 0 7 0 (by decide +kernel)
theorem n1_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[1]!).toFinset :=
  nbAt h a eids1 1 (by decide) 0 7 1 (by decide +kernel)
theorem n1_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[2]!).toFinset :=
  nbAt h a eids1 2 (by decide) 1 7 1 (by decide +kernel)
theorem n1_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[3]!).toFinset :=
  nbAt h a eids1 3 (by decide) 0 7 1 (by decide +kernel)
theorem n1_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[4]!).toFinset :=
  nbAt h a eids1 4 (by decide) 0 7 1 (by decide +kernel)
theorem n1_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[5]!).toFinset :=
  nbAt h a eids1 5 (by decide) 0 7 1 (by decide +kernel)
theorem n1_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[6]!).toFinset :=
  nbAt h a eids1 6 (by decide) 1 7 1 (by decide +kernel)
theorem n1_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[7]!).toFinset :=
  nbAt h a eids1 7 (by decide) 1 7 1 (by decide +kernel)
theorem n1_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[8]!).toFinset :=
  nbAt h a eids1 8 (by decide) 0 7 1 (by decide +kernel)
theorem n1_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[9]!).toFinset :=
  nbAt h a eids1 9 (by decide) 0 7 1 (by decide +kernel)
theorem n1_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[10]!).toFinset :=
  nbAt h a eids1 10 (by decide) 1 7 1 (by decide +kernel)
theorem n1_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[11]!).toFinset :=
  nbAt h a eids1 11 (by decide) 1 7 1 (by decide +kernel)
theorem n1_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[12]!).toFinset :=
  nbAt h a eids1 12 (by decide) 1 7 1 (by decide +kernel)
theorem n1_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[13]!).toFinset :=
  nbAt h a eids1 13 (by decide) 0 7 1 (by decide +kernel)
theorem n1_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[15]!).toFinset :=
  nbAt h a eids1 15 (by decide) 0 7 0 (by decide +kernel)
theorem n1_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[16]!).toFinset :=
  nbAt h a eids1 16 (by decide) 0 7 0 (by decide +kernel)
theorem n1_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[17]!).toFinset :=
  nbAt h a eids1 17 (by decide) 0 7 1 (by decide +kernel)
theorem n1_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[18]!).toFinset :=
  nbAt h a eids1 18 (by decide) 2 7 93 (by decide +kernel)
theorem n1_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[19]!).toFinset :=
  nbAt h a eids1 19 (by decide) 0 7 1 (by decide +kernel)
theorem n1_21 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[21]!).toFinset :=
  nbAt h a eids1 21 (by decide) 0 7 0 (by decide +kernel)
theorem n1_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[22]!).toFinset :=
  nbAt h a eids1 22 (by decide) 0 7 0 (by decide +kernel)
theorem n1_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[23]!).toFinset :=
  nbAt h a eids1 23 (by decide) 0 7 1 (by decide +kernel)
theorem n1_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[24]!).toFinset :=
  nbAt h a eids1 24 (by decide) 3 7 93 (by decide +kernel)
theorem n1_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[25]!).toFinset :=
  nbAt h a eids1 25 (by decide) 0 7 1 (by decide +kernel)
theorem n1_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[27]!).toFinset :=
  nbAt h a eids1 27 (by decide) 0 7 0 (by decide +kernel)
theorem n1_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[28]!).toFinset :=
  nbAt h a eids1 28 (by decide) 0 7 0 (by decide +kernel)
theorem n1_29 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[29]!).toFinset :=
  nbAt h a eids1 29 (by decide) 0 7 1 (by decide +kernel)
theorem n1_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[30]!).toFinset :=
  nbAt h a eids1 30 (by decide) 4 7 93 (by decide +kernel)
theorem n1_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[31]!).toFinset :=
  nbAt h a eids1 31 (by decide) 0 7 1 (by decide +kernel)
theorem n1_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[32]!).toFinset :=
  nbAt h a eids1 32 (by decide) 0 7 1 (by decide +kernel)
theorem n1_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[33]!).toFinset :=
  nbAt h a eids1 33 (by decide) 0 7 1 (by decide +kernel)
theorem n1_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[34]!).toFinset :=
  nbAt h a eids1 34 (by decide) 0 7 1 (by decide +kernel)
theorem n1_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[35]!).toFinset :=
  nbAt h a eids1 35 (by decide) 0 7 1 (by decide +kernel)
theorem n1_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[36]!).toFinset :=
  nbAt h a eids1 36 (by decide) 1 7 1 (by decide +kernel)
theorem n1_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[38]!).toFinset :=
  nbAt h a eids1 38 (by decide) 1 7 0 (by decide +kernel)
theorem n1_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[39]!).toFinset :=
  nbAt h a eids1 39 (by decide) 1 7 0 (by decide +kernel)
theorem n1_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[40]!).toFinset :=
  nbAt h a eids1 40 (by decide) 1 7 1 (by decide +kernel)
theorem n1_41 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[41]!).toFinset :=
  nbAt h a eids1 41 (by decide) 2 7 93 (by decide +kernel)
theorem n1_42 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[42]!).toFinset :=
  nbAt h a eids1 42 (by decide) 1 7 1 (by decide +kernel)
theorem n1_44 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[44]!).toFinset :=
  nbAt h a eids1 44 (by decide) 1 7 0 (by decide +kernel)
theorem n1_45 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[45]!).toFinset :=
  nbAt h a eids1 45 (by decide) 1 7 0 (by decide +kernel)
theorem n1_46 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[46]!).toFinset :=
  nbAt h a eids1 46 (by decide) 1 7 1 (by decide +kernel)
theorem n1_47 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[47]!).toFinset :=
  nbAt h a eids1 47 (by decide) 3 7 93 (by decide +kernel)
theorem n1_48 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[48]!).toFinset :=
  nbAt h a eids1 48 (by decide) 1 7 1 (by decide +kernel)
theorem n1_50 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[50]!).toFinset :=
  nbAt h a eids1 50 (by decide) 1 7 0 (by decide +kernel)
theorem n1_51 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[51]!).toFinset :=
  nbAt h a eids1 51 (by decide) 1 7 0 (by decide +kernel)
theorem n1_52 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[52]!).toFinset :=
  nbAt h a eids1 52 (by decide) 1 7 1 (by decide +kernel)
theorem n1_53 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[53]!).toFinset :=
  nbAt h a eids1 53 (by decide) 4 7 93 (by decide +kernel)
theorem n1_54 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[54]!).toFinset :=
  nbAt h a eids1 54 (by decide) 2 7 1 (by decide +kernel)
theorem n1_55 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[55]!).toFinset :=
  nbAt h a eids1 55 (by decide) 2 7 93 (by decide +kernel)
theorem n1_58 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[58]!).toFinset :=
  nbAt h a eids1 58 (by decide) 0 7 127 (by decide +kernel)
theorem n1_59 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[59]!).toFinset :=
  nbAt h a eids1 59 (by decide) 0 7 127 (by decide +kernel)
theorem n1_60 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[60]!).toFinset :=
  nbAt h a eids1 60 (by decide) 2 7 1 (by decide +kernel)
theorem n1_61 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[61]!).toFinset :=
  nbAt h a eids1 61 (by decide) 2 7 93 (by decide +kernel)
theorem n1_62 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[62]!).toFinset :=
  nbAt h a eids1 62 (by decide) 3 7 1 (by decide +kernel)
theorem n1_63 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[63]!).toFinset :=
  nbAt h a eids1 63 (by decide) 3 7 93 (by decide +kernel)
theorem n1_66 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[66]!).toFinset :=
  nbAt h a eids1 66 (by decide) 0 7 128 (by decide +kernel)
theorem n1_67 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[67]!).toFinset :=
  nbAt h a eids1 67 (by decide) 0 7 128 (by decide +kernel)
theorem n1_68 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[68]!).toFinset :=
  nbAt h a eids1 68 (by decide) 3 7 1 (by decide +kernel)
theorem n1_69 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[69]!).toFinset :=
  nbAt h a eids1 69 (by decide) 3 7 93 (by decide +kernel)
theorem n1_70 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[70]!).toFinset :=
  nbAt h a eids1 70 (by decide) 4 7 1 (by decide +kernel)
theorem n1_71 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[71]!).toFinset :=
  nbAt h a eids1 71 (by decide) 4 7 93 (by decide +kernel)
theorem n1_74 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[74]!).toFinset :=
  nbAt h a eids1 74 (by decide) 0 7 129 (by decide +kernel)
theorem n1_75 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[75]!).toFinset :=
  nbAt h a eids1 75 (by decide) 0 7 129 (by decide +kernel)
theorem n1_76 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[76]!).toFinset :=
  nbAt h a eids1 76 (by decide) 4 7 1 (by decide +kernel)
theorem n1_77 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[77]!).toFinset :=
  nbAt h a eids1 77 (by decide) 4 7 93 (by decide +kernel)
theorem n1_78 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[78]!).toFinset :=
  nbAt h a eids1 78 (by decide) 2 7 93 (by decide +kernel)
theorem n1_80 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[80]!).toFinset :=
  nbAt h a eids1 80 (by decide) 2 7 93 (by decide +kernel)
theorem n1_81 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[81]!).toFinset :=
  nbAt h a eids1 81 (by decide) 3 7 93 (by decide +kernel)
theorem n1_82 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[82]!).toFinset :=
  nbAt h a eids1 82 (by decide) 2 7 93 (by decide +kernel)
theorem n1_84 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[84]!).toFinset :=
  nbAt h a eids1 84 (by decide) 2 7 93 (by decide +kernel)
theorem n1_85 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[85]!).toFinset :=
  nbAt h a eids1 85 (by decide) 4 7 93 (by decide +kernel)
theorem n1_86 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[86]!).toFinset :=
  nbAt h a eids1 86 (by decide) 3 7 93 (by decide +kernel)
theorem n1_88 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[88]!).toFinset :=
  nbAt h a eids1 88 (by decide) 3 7 93 (by decide +kernel)
theorem n1_89 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 (edges1[89]!).toFinset :=
  nbAt h a eids1 89 (by decide) 4 7 93 (by decide +kernel)
theorem n2_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[0]!).toFinset :=
  nbAt h a eids2 0 (by decide) 0 6 2 (by decide +kernel)
theorem n2_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[2]!).toFinset :=
  nbAt h a eids2 2 (by decide) 0 6 18 (by decide +kernel)
theorem n2_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[3]!).toFinset :=
  nbAt h a eids2 3 (by decide) 1 6 18 (by decide +kernel)
theorem n2_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[4]!).toFinset :=
  nbAt h a eids2 4 (by decide) 0 6 18 (by decide +kernel)
theorem n2_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[5]!).toFinset :=
  nbAt h a eids2 5 (by decide) 0 6 18 (by decide +kernel)
theorem n2_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[6]!).toFinset :=
  nbAt h a eids2 6 (by decide) 0 6 2 (by decide +kernel)
theorem n2_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[7]!).toFinset :=
  nbAt h a eids2 7 (by decide) 0 6 18 (by decide +kernel)
theorem n2_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[8]!).toFinset :=
  nbAt h a eids2 8 (by decide) 1 6 2 (by decide +kernel)
theorem n2_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[9]!).toFinset :=
  nbAt h a eids2 9 (by decide) 0 6 2 (by decide +kernel)
theorem n2_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[11]!).toFinset :=
  nbAt h a eids2 11 (by decide) 0 6 18 (by decide +kernel)
theorem n2_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[12]!).toFinset :=
  nbAt h a eids2 12 (by decide) 0 6 18 (by decide +kernel)
theorem n2_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[13]!).toFinset :=
  nbAt h a eids2 13 (by decide) 0 6 2 (by decide +kernel)
theorem n2_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[14]!).toFinset :=
  nbAt h a eids2 14 (by decide) 2 6 65 (by decide +kernel)
theorem n2_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[15]!).toFinset :=
  nbAt h a eids2 15 (by decide) 0 6 2 (by decide +kernel)
theorem n2_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[17]!).toFinset :=
  nbAt h a eids2 17 (by decide) 0 6 18 (by decide +kernel)
theorem n2_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[18]!).toFinset :=
  nbAt h a eids2 18 (by decide) 0 6 18 (by decide +kernel)
theorem n2_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[19]!).toFinset :=
  nbAt h a eids2 19 (by decide) 0 6 2 (by decide +kernel)
theorem n2_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[20]!).toFinset :=
  nbAt h a eids2 20 (by decide) 3 6 65 (by decide +kernel)
theorem n2_21 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[21]!).toFinset :=
  nbAt h a eids2 21 (by decide) 0 6 2 (by decide +kernel)
theorem n2_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[22]!).toFinset :=
  nbAt h a eids2 22 (by decide) 4 6 1 (by decide +kernel)
theorem n2_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[23]!).toFinset :=
  nbAt h a eids2 23 (by decide) 4 6 1 (by decide +kernel)
theorem n2_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[24]!).toFinset :=
  nbAt h a eids2 24 (by decide) 4 6 1 (by decide +kernel)
theorem n2_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[25]!).toFinset :=
  nbAt h a eids2 25 (by decide) 0 6 1 (by decide +kernel)
theorem n2_26 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[26]!).toFinset :=
  nbAt h a eids2 26 (by decide) 0 6 63 (by decide +kernel)
theorem n2_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[27]!).toFinset :=
  nbAt h a eids2 27 (by decide) 0 6 18 (by decide +kernel)
theorem n2_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[28]!).toFinset :=
  nbAt h a eids2 28 (by decide) 0 6 2 (by decide +kernel)
theorem n2_29 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[29]!).toFinset :=
  nbAt h a eids2 29 (by decide) 0 6 18 (by decide +kernel)
theorem n2_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[30]!).toFinset :=
  nbAt h a eids2 30 (by decide) 0 6 63 (by decide +kernel)
theorem n2_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[31]!).toFinset :=
  nbAt h a eids2 31 (by decide) 0 6 2 (by decide +kernel)
theorem n2_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[32]!).toFinset :=
  nbAt h a eids2 32 (by decide) 1 6 66 (by decide +kernel)
theorem n2_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[33]!).toFinset :=
  nbAt h a eids2 33 (by decide) 0 6 18 (by decide +kernel)
theorem n2_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[34]!).toFinset :=
  nbAt h a eids2 34 (by decide) 1 6 2 (by decide +kernel)
theorem n2_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[36]!).toFinset :=
  nbAt h a eids2 36 (by decide) 1 6 18 (by decide +kernel)
theorem n2_37 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[37]!).toFinset :=
  nbAt h a eids2 37 (by decide) 0 6 67 (by decide +kernel)
theorem n2_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[38]!).toFinset :=
  nbAt h a eids2 38 (by decide) 1 6 2 (by decide +kernel)
theorem n2_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[39]!).toFinset :=
  nbAt h a eids2 39 (by decide) 2 6 65 (by decide +kernel)
theorem n2_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[40]!).toFinset :=
  nbAt h a eids2 40 (by decide) 1 6 2 (by decide +kernel)
theorem n2_42 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[42]!).toFinset :=
  nbAt h a eids2 42 (by decide) 1 6 18 (by decide +kernel)
theorem n2_43 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[43]!).toFinset :=
  nbAt h a eids2 43 (by decide) 0 6 68 (by decide +kernel)
theorem n2_44 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[44]!).toFinset :=
  nbAt h a eids2 44 (by decide) 1 6 2 (by decide +kernel)
theorem n2_45 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[45]!).toFinset :=
  nbAt h a eids2 45 (by decide) 3 6 65 (by decide +kernel)
theorem n2_46 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[46]!).toFinset :=
  nbAt h a eids2 46 (by decide) 1 6 1 (by decide +kernel)
theorem n2_47 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[47]!).toFinset :=
  nbAt h a eids2 47 (by decide) 1 6 63 (by decide +kernel)
theorem n2_48 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[48]!).toFinset :=
  nbAt h a eids2 48 (by decide) 1 6 18 (by decide +kernel)
theorem n2_49 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[49]!).toFinset :=
  nbAt h a eids2 49 (by decide) 1 6 2 (by decide +kernel)
theorem n2_50 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[50]!).toFinset :=
  nbAt h a eids2 50 (by decide) 0 6 18 (by decide +kernel)
theorem n2_51 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[51]!).toFinset :=
  nbAt h a eids2 51 (by decide) 1 6 63 (by decide +kernel)
theorem n2_52 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[52]!).toFinset :=
  nbAt h a eids2 52 (by decide) 1 6 2 (by decide +kernel)
theorem n2_53 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[53]!).toFinset :=
  nbAt h a eids2 53 (by decide) 0 6 66 (by decide +kernel)
theorem n2_54 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[54]!).toFinset :=
  nbAt h a eids2 54 (by decide) 1 6 18 (by decide +kernel)
theorem n2_55 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[55]!).toFinset :=
  nbAt h a eids2 55 (by decide) 0 6 2 (by decide +kernel)
theorem n2_56 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[56]!).toFinset :=
  nbAt h a eids2 56 (by decide) 4 6 1 (by decide +kernel)
theorem n2_57 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[57]!).toFinset :=
  nbAt h a eids2 57 (by decide) 4 6 1 (by decide +kernel)
theorem n2_58 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[58]!).toFinset :=
  nbAt h a eids2 58 (by decide) 4 6 1 (by decide +kernel)
theorem n2_59 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[59]!).toFinset :=
  nbAt h a eids2 59 (by decide) 2 6 65 (by decide +kernel)
theorem n2_61 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[61]!).toFinset :=
  nbAt h a eids2 61 (by decide) 2 6 65 (by decide +kernel)
theorem n2_62 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[62]!).toFinset :=
  nbAt h a eids2 62 (by decide) 3 6 65 (by decide +kernel)
theorem n2_63 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[63]!).toFinset :=
  nbAt h a eids2 63 (by decide) 2 6 65 (by decide +kernel)
theorem n2_64 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[64]!).toFinset :=
  nbAt h a eids2 64 (by decide) 1 6 71 (by decide +kernel)
theorem n2_66 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[66]!).toFinset :=
  nbAt h a eids2 66 (by decide) 2 6 65 (by decide +kernel)
theorem n2_67 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[67]!).toFinset :=
  nbAt h a eids2 67 (by decide) 0 6 84 (by decide +kernel)
theorem n2_68 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[68]!).toFinset :=
  nbAt h a eids2 68 (by decide) 0 6 85 (by decide +kernel)
theorem n2_69 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[69]!).toFinset :=
  nbAt h a eids2 69 (by decide) 2 6 65 (by decide +kernel)
theorem n2_70 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[70]!).toFinset :=
  nbAt h a eids2 70 (by decide) 0 6 71 (by decide +kernel)
theorem n2_72 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[72]!).toFinset :=
  nbAt h a eids2 72 (by decide) 2 6 65 (by decide +kernel)
theorem n2_73 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[73]!).toFinset :=
  nbAt h a eids2 73 (by decide) 0 6 86 (by decide +kernel)
theorem n2_74 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[74]!).toFinset :=
  nbAt h a eids2 74 (by decide) 0 6 87 (by decide +kernel)
theorem n2_75 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[75]!).toFinset :=
  nbAt h a eids2 75 (by decide) 3 6 65 (by decide +kernel)
theorem n2_76 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[76]!).toFinset :=
  nbAt h a eids2 76 (by decide) 1 6 88 (by decide +kernel)
theorem n2_78 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[78]!).toFinset :=
  nbAt h a eids2 78 (by decide) 3 6 65 (by decide +kernel)
theorem n2_79 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[79]!).toFinset :=
  nbAt h a eids2 79 (by decide) 0 6 89 (by decide +kernel)
theorem n2_80 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[80]!).toFinset :=
  nbAt h a eids2 80 (by decide) 0 6 90 (by decide +kernel)
theorem n2_81 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[81]!).toFinset :=
  nbAt h a eids2 81 (by decide) 3 6 65 (by decide +kernel)
theorem n2_82 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[82]!).toFinset :=
  nbAt h a eids2 82 (by decide) 0 6 88 (by decide +kernel)
theorem n2_84 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[84]!).toFinset :=
  nbAt h a eids2 84 (by decide) 3 6 65 (by decide +kernel)
theorem n2_85 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[85]!).toFinset :=
  nbAt h a eids2 85 (by decide) 0 6 91 (by decide +kernel)
theorem n2_86 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[86]!).toFinset :=
  nbAt h a eids2 86 (by decide) 0 6 92 (by decide +kernel)
theorem n2_87 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[87]!).toFinset :=
  nbAt h a eids2 87 (by decide) 0 6 1 (by decide +kernel)
theorem n2_88 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[88]!).toFinset :=
  nbAt h a eids2 88 (by decide) 0 6 1 (by decide +kernel)
theorem n2_89 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[89]!).toFinset :=
  nbAt h a eids2 89 (by decide) 1 6 1 (by decide +kernel)
theorem n2_90 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[90]!).toFinset :=
  nbAt h a eids2 90 (by decide) 0 6 18 (by decide +kernel)
theorem n2_91 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[91]!).toFinset :=
  nbAt h a eids2 91 (by decide) 0 6 18 (by decide +kernel)
theorem n2_92 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[92]!).toFinset :=
  nbAt h a eids2 92 (by decide) 0 6 63 (by decide +kernel)
theorem n2_93 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[93]!).toFinset :=
  nbAt h a eids2 93 (by decide) 0 6 2 (by decide +kernel)
theorem n2_94 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[94]!).toFinset :=
  nbAt h a eids2 94 (by decide) 1 6 63 (by decide +kernel)
theorem n2_95 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges2[95]!).toFinset :=
  nbAt h a eids2 95 (by decide) 1 6 2 (by decide +kernel)
theorem n3_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[0]!).toFinset :=
  nbAt h a eids3 0 (by decide) 0 5 3 (by decide +kernel)
theorem n3_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[1]!).toFinset :=
  nbAt h a eids3 1 (by decide) 0 5 4 (by decide +kernel)
theorem n3_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[2]!).toFinset :=
  nbAt h a eids3 2 (by decide) 0 5 3 (by decide +kernel)
theorem n3_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[3]!).toFinset :=
  nbAt h a eids3 3 (by decide) 1 5 3 (by decide +kernel)
theorem n3_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[4]!).toFinset :=
  nbAt h a eids3 4 (by decide) 0 5 3 (by decide +kernel)
theorem n3_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[5]!).toFinset :=
  nbAt h a eids3 5 (by decide) 0 5 4 (by decide +kernel)
theorem n3_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[6]!).toFinset :=
  nbAt h a eids3 6 (by decide) 0 5 4 (by decide +kernel)
theorem n3_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[7]!).toFinset :=
  nbAt h a eids3 7 (by decide) 0 5 3 (by decide +kernel)
theorem n3_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[8]!).toFinset :=
  nbAt h a eids3 8 (by decide) 0 5 4 (by decide +kernel)
theorem n3_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[9]!).toFinset :=
  nbAt h a eids3 9 (by decide) 0 5 4 (by decide +kernel)
theorem n3_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[10]!).toFinset :=
  nbAt h a eids3 10 (by decide) 0 5 3 (by decide +kernel)
theorem n3_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[11]!).toFinset :=
  nbAt h a eids3 11 (by decide) 0 5 4 (by decide +kernel)
theorem n3_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[12]!).toFinset :=
  nbAt h a eids3 12 (by decide) 0 5 4 (by decide +kernel)
theorem n3_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[13]!).toFinset :=
  nbAt h a eids3 13 (by decide) 0 5 3 (by decide +kernel)
theorem n3_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[14]!).toFinset :=
  nbAt h a eids3 14 (by decide) 0 5 4 (by decide +kernel)
theorem n3_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[15]!).toFinset :=
  nbAt h a eids3 15 (by decide) 0 5 4 (by decide +kernel)
theorem n3_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[16]!).toFinset :=
  nbAt h a eids3 16 (by decide) 0 5 3 (by decide +kernel)
theorem n3_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[17]!).toFinset :=
  nbAt h a eids3 17 (by decide) 0 5 4 (by decide +kernel)
theorem n3_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[18]!).toFinset :=
  nbAt h a eids3 18 (by decide) 0 5 4 (by decide +kernel)
theorem n3_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[19]!).toFinset :=
  nbAt h a eids3 19 (by decide) 0 5 3 (by decide +kernel)
theorem n3_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[20]!).toFinset :=
  nbAt h a eids3 20 (by decide) 0 5 4 (by decide +kernel)
theorem n3_21 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[21]!).toFinset :=
  nbAt h a eids3 21 (by decide) 0 5 4 (by decide +kernel)
theorem n3_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[22]!).toFinset :=
  nbAt h a eids3 22 (by decide) 1 5 3 (by decide +kernel)
theorem n3_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[23]!).toFinset :=
  nbAt h a eids3 23 (by decide) 0 5 5 (by decide +kernel)
theorem n3_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[24]!).toFinset :=
  nbAt h a eids3 24 (by decide) 1 5 4 (by decide +kernel)
theorem n3_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[25]!).toFinset :=
  nbAt h a eids3 25 (by decide) 1 5 3 (by decide +kernel)
theorem n3_26 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[26]!).toFinset :=
  nbAt h a eids3 26 (by decide) 0 5 6 (by decide +kernel)
theorem n3_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[27]!).toFinset :=
  nbAt h a eids3 27 (by decide) 1 5 4 (by decide +kernel)
theorem n3_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[28]!).toFinset :=
  nbAt h a eids3 28 (by decide) 1 5 3 (by decide +kernel)
theorem n3_29 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[29]!).toFinset :=
  nbAt h a eids3 29 (by decide) 0 5 7 (by decide +kernel)
theorem n3_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[30]!).toFinset :=
  nbAt h a eids3 30 (by decide) 1 5 4 (by decide +kernel)
theorem n3_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[31]!).toFinset :=
  nbAt h a eids3 31 (by decide) 1 5 3 (by decide +kernel)
theorem n3_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[32]!).toFinset :=
  nbAt h a eids3 32 (by decide) 0 5 8 (by decide +kernel)
theorem n3_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[33]!).toFinset :=
  nbAt h a eids3 33 (by decide) 1 5 4 (by decide +kernel)
theorem n3_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[34]!).toFinset :=
  nbAt h a eids3 34 (by decide) 1 5 3 (by decide +kernel)
theorem n3_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[35]!).toFinset :=
  nbAt h a eids3 35 (by decide) 0 5 9 (by decide +kernel)
theorem n3_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[36]!).toFinset :=
  nbAt h a eids3 36 (by decide) 1 5 4 (by decide +kernel)
theorem n3_37 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[37]!).toFinset :=
  nbAt h a eids3 37 (by decide) 1 5 3 (by decide +kernel)
theorem n3_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[38]!).toFinset :=
  nbAt h a eids3 38 (by decide) 0 5 10 (by decide +kernel)
theorem n3_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[39]!).toFinset :=
  nbAt h a eids3 39 (by decide) 1 5 4 (by decide +kernel)
theorem n3_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[40]!).toFinset :=
  nbAt h a eids3 40 (by decide) 3 5 1 (by decide +kernel)
theorem n3_41 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[41]!).toFinset :=
  nbAt h a eids3 41 (by decide) 3 5 1 (by decide +kernel)
theorem n3_42 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[42]!).toFinset :=
  nbAt h a eids3 42 (by decide) 4 5 1 (by decide +kernel)
theorem n3_43 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[43]!).toFinset :=
  nbAt h a eids3 43 (by decide) 3 5 11 (by decide +kernel)
theorem n3_44 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[44]!).toFinset :=
  nbAt h a eids3 44 (by decide) 2 5 11 (by decide +kernel)
theorem n3_45 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[45]!).toFinset :=
  nbAt h a eids3 45 (by decide) 0 5 12 (by decide +kernel)
theorem n3_46 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[46]!).toFinset :=
  nbAt h a eids3 46 (by decide) 0 5 13 (by decide +kernel)
theorem n3_47 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[47]!).toFinset :=
  nbAt h a eids3 47 (by decide) 0 5 14 (by decide +kernel)
theorem n3_48 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[48]!).toFinset :=
  nbAt h a eids3 48 (by decide) 0 5 15 (by decide +kernel)
theorem n3_49 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[49]!).toFinset :=
  nbAt h a eids3 49 (by decide) 2 5 1 (by decide +kernel)
theorem n3_50 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[50]!).toFinset :=
  nbAt h a eids3 50 (by decide) 2 5 1 (by decide +kernel)
theorem n3_51 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[51]!).toFinset :=
  nbAt h a eids3 51 (by decide) 4 5 1 (by decide +kernel)
theorem n3_52 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[52]!).toFinset :=
  nbAt h a eids3 52 (by decide) 2 5 11 (by decide +kernel)
theorem n3_53 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[53]!).toFinset :=
  nbAt h a eids3 53 (by decide) 2 5 11 (by decide +kernel)
theorem n3_54 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[54]!).toFinset :=
  nbAt h a eids3 54 (by decide) 0 5 16 (by decide +kernel)
theorem n3_55 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[55]!).toFinset :=
  nbAt h a eids3 55 (by decide) 0 5 17 (by decide +kernel)
theorem n3_56 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[56]!).toFinset :=
  nbAt h a eids3 56 (by decide) 0 5 14 (by decide +kernel)
theorem n3_57 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[57]!).toFinset :=
  nbAt h a eids3 57 (by decide) 0 5 15 (by decide +kernel)
theorem n3_58 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[58]!).toFinset :=
  nbAt h a eids3 58 (by decide) 2 5 1 (by decide +kernel)
theorem n3_59 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[59]!).toFinset :=
  nbAt h a eids3 59 (by decide) 2 5 1 (by decide +kernel)
theorem n3_60 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[60]!).toFinset :=
  nbAt h a eids3 60 (by decide) 3 5 1 (by decide +kernel)
theorem n3_61 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[61]!).toFinset :=
  nbAt h a eids3 61 (by decide) 2 5 11 (by decide +kernel)
theorem n3_62 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[62]!).toFinset :=
  nbAt h a eids3 62 (by decide) 2 5 11 (by decide +kernel)
theorem n3_63 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[63]!).toFinset :=
  nbAt h a eids3 63 (by decide) 0 5 16 (by decide +kernel)
theorem n3_64 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[64]!).toFinset :=
  nbAt h a eids3 64 (by decide) 0 5 17 (by decide +kernel)
theorem n3_65 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[65]!).toFinset :=
  nbAt h a eids3 65 (by decide) 0 5 12 (by decide +kernel)
theorem n3_66 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges3[66]!).toFinset :=
  nbAt h a eids3 66 (by decide) 0 5 13 (by decide +kernel)
theorem n4_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[1]!).toFinset :=
  nbAt h a eids4 1 (by decide) 0 5 36 (by decide +kernel)
theorem n4_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[2]!).toFinset :=
  nbAt h a eids4 2 (by decide) 1 5 37 (by decide +kernel)
theorem n4_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[3]!).toFinset :=
  nbAt h a eids4 3 (by decide) 0 5 36 (by decide +kernel)
theorem n4_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[4]!).toFinset :=
  nbAt h a eids4 4 (by decide) 0 5 36 (by decide +kernel)
theorem n4_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[6]!).toFinset :=
  nbAt h a eids4 6 (by decide) 0 5 36 (by decide +kernel)
theorem n4_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[7]!).toFinset :=
  nbAt h a eids4 7 (by decide) 0 5 36 (by decide +kernel)
theorem n4_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[8]!).toFinset :=
  nbAt h a eids4 8 (by decide) 1 5 41 (by decide +kernel)
theorem n4_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[9]!).toFinset :=
  nbAt h a eids4 9 (by decide) 1 5 42 (by decide +kernel)
theorem n4_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[10]!).toFinset :=
  nbAt h a eids4 10 (by decide) 0 5 36 (by decide +kernel)
theorem n4_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[11]!).toFinset :=
  nbAt h a eids4 11 (by decide) 1 5 43 (by decide +kernel)
theorem n4_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[12]!).toFinset :=
  nbAt h a eids4 12 (by decide) 0 5 36 (by decide +kernel)
theorem n4_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[13]!).toFinset :=
  nbAt h a eids4 13 (by decide) 0 5 36 (by decide +kernel)
theorem n4_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[14]!).toFinset :=
  nbAt h a eids4 14 (by decide) 0 5 36 (by decide +kernel)
theorem n4_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[15]!).toFinset :=
  nbAt h a eids4 15 (by decide) 1 5 44 (by decide +kernel)
theorem n4_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[17]!).toFinset :=
  nbAt h a eids4 17 (by decide) 0 5 45 (by decide +kernel)
theorem n4_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[18]!).toFinset :=
  nbAt h a eids4 18 (by decide) 0 5 42 (by decide +kernel)
theorem n4_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[19]!).toFinset :=
  nbAt h a eids4 19 (by decide) 0 5 46 (by decide +kernel)
theorem n4_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[20]!).toFinset :=
  nbAt h a eids4 20 (by decide) 0 5 47 (by decide +kernel)
theorem n4_21 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[21]!).toFinset :=
  nbAt h a eids4 21 (by decide) 0 5 48 (by decide +kernel)
theorem n4_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[22]!).toFinset :=
  nbAt h a eids4 22 (by decide) 0 5 49 (by decide +kernel)
theorem n4_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[23]!).toFinset :=
  nbAt h a eids4 23 (by decide) 0 5 50 (by decide +kernel)
theorem n4_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[24]!).toFinset :=
  nbAt h a eids4 24 (by decide) 0 5 51 (by decide +kernel)
theorem n4_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[25]!).toFinset :=
  nbAt h a eids4 25 (by decide) 0 5 52 (by decide +kernel)
theorem n4_26 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[26]!).toFinset :=
  nbAt h a eids4 26 (by decide) 0 5 53 (by decide +kernel)
theorem n4_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[27]!).toFinset :=
  nbAt h a eids4 27 (by decide) 1 5 19 (by decide +kernel)
theorem n4_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[28]!).toFinset :=
  nbAt h a eids4 28 (by decide) 0 5 54 (by decide +kernel)
theorem n4_29 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[29]!).toFinset :=
  nbAt h a eids4 29 (by decide) 0 5 22 (by decide +kernel)
theorem n4_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[30]!).toFinset :=
  nbAt h a eids4 30 (by decide) 0 5 55 (by decide +kernel)
theorem n4_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[31]!).toFinset :=
  nbAt h a eids4 31 (by decide) 0 5 56 (by decide +kernel)
theorem n4_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[32]!).toFinset :=
  nbAt h a eids4 32 (by decide) 0 5 57 (by decide +kernel)
theorem n4_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[33]!).toFinset :=
  nbAt h a eids4 33 (by decide) 0 5 58 (by decide +kernel)
theorem n4_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[34]!).toFinset :=
  nbAt h a eids4 34 (by decide) 0 5 59 (by decide +kernel)
theorem n4_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[35]!).toFinset :=
  nbAt h a eids4 35 (by decide) 0 5 60 (by decide +kernel)
theorem n4_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[36]!).toFinset :=
  nbAt h a eids4 36 (by decide) 0 5 61 (by decide +kernel)
theorem n4_37 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[37]!).toFinset :=
  nbAt h a eids4 37 (by decide) 0 5 62 (by decide +kernel)
theorem n4_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[38]!).toFinset :=
  nbAt h a eids4 38 (by decide) 0 5 36 (by decide +kernel)
theorem n4_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[39]!).toFinset :=
  nbAt h a eids4 39 (by decide) 4 5 63 (by decide +kernel)
theorem n4_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[40]!).toFinset :=
  nbAt h a eids4 40 (by decide) 0 5 64 (by decide +kernel)
theorem n4_41 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges4[41]!).toFinset :=
  nbAt h a eids4 41 (by decide) 3 5 63 (by decide +kernel)
theorem n5_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[0]!).toFinset :=
  nbAt h a eids5 0 (by decide) 3 4 19 (by decide +kernel)
theorem n5_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[1]!).toFinset :=
  nbAt h a eids5 1 (by decide) 1 4 20 (by decide +kernel)
theorem n5_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[2]!).toFinset :=
  nbAt h a eids5 2 (by decide) 2 4 19 (by decide +kernel)
theorem n5_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[3]!).toFinset :=
  nbAt h a eids5 3 (by decide) 1 4 21 (by decide +kernel)
theorem n5_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[4]!).toFinset :=
  nbAt h a eids5 4 (by decide) 1 4 22 (by decide +kernel)
theorem n5_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[5]!).toFinset :=
  nbAt h a eids5 5 (by decide) 1 4 23 (by decide +kernel)
theorem n5_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[6]!).toFinset :=
  nbAt h a eids5 6 (by decide) 1 4 24 (by decide +kernel)
theorem n5_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[7]!).toFinset :=
  nbAt h a eids5 7 (by decide) 1 4 25 (by decide +kernel)
theorem n5_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[8]!).toFinset :=
  nbAt h a eids5 8 (by decide) 1 4 26 (by decide +kernel)
theorem n5_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[9]!).toFinset :=
  nbAt h a eids5 9 (by decide) 1 4 27 (by decide +kernel)
theorem n5_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[10]!).toFinset :=
  nbAt h a eids5 10 (by decide) 1 4 28 (by decide +kernel)
theorem n5_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[11]!).toFinset :=
  nbAt h a eids5 11 (by decide) 1 4 29 (by decide +kernel)
theorem n5_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[12]!).toFinset :=
  nbAt h a eids5 12 (by decide) 1 4 30 (by decide +kernel)
theorem n5_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[13]!).toFinset :=
  nbAt h a eids5 13 (by decide) 1 4 31 (by decide +kernel)
theorem n5_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[14]!).toFinset :=
  nbAt h a eids5 14 (by decide) 1 4 32 (by decide +kernel)
theorem n5_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[15]!).toFinset :=
  nbAt h a eids5 15 (by decide) 1 4 33 (by decide +kernel)
theorem n5_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[16]!).toFinset :=
  nbAt h a eids5 16 (by decide) 1 4 34 (by decide +kernel)
theorem n5_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges5[17]!).toFinset :=
  nbAt h a eids5 17 (by decide) 1 4 35 (by decide +kernel)
theorem n6_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges6[1]!).toFinset :=
  nbAt h a eids6 1 (by decide) 2 4 19 (by decide +kernel)
theorem n6_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges6[2]!).toFinset :=
  nbAt h a eids6 2 (by decide) 1 4 38 (by decide +kernel)
theorem n6_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges6[3]!).toFinset :=
  nbAt h a eids6 3 (by decide) 3 4 19 (by decide +kernel)
theorem n6_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges6[4]!).toFinset :=
  nbAt h a eids6 4 (by decide) 0 4 39 (by decide +kernel)
theorem n6_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 (edges6[5]!).toFinset :=
  nbAt h a eids6 5 (by decide) 0 4 40 (by decide +kernel)
theorem n8_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[0]!).toFinset :=
  nbAt h a eids8 0 (by decide) 0 5 69 (by decide +kernel)
theorem n8_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[3]!).toFinset :=
  nbAt h a eids8 3 (by decide) 1 5 22 (by decide +kernel)
theorem n8_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[4]!).toFinset :=
  nbAt h a eids8 4 (by decide) 1 5 24 (by decide +kernel)
theorem n8_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[7]!).toFinset :=
  nbAt h a eids8 7 (by decide) 0 5 22 (by decide +kernel)
theorem n8_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[8]!).toFinset :=
  nbAt h a eids8 8 (by decide) 0 5 24 (by decide +kernel)
theorem n8_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[9]!).toFinset :=
  nbAt h a eids8 9 (by decide) 3 5 19 (by decide +kernel)
theorem n8_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[10]!).toFinset :=
  nbAt h a eids8 10 (by decide) 0 5 20 (by decide +kernel)
theorem n8_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[11]!).toFinset :=
  nbAt h a eids8 11 (by decide) 2 5 19 (by decide +kernel)
theorem n8_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[12]!).toFinset :=
  nbAt h a eids8 12 (by decide) 0 5 21 (by decide +kernel)
theorem n8_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[13]!).toFinset :=
  nbAt h a eids8 13 (by decide) 0 5 22 (by decide +kernel)
theorem n8_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[14]!).toFinset :=
  nbAt h a eids8 14 (by decide) 0 5 23 (by decide +kernel)
theorem n8_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[15]!).toFinset :=
  nbAt h a eids8 15 (by decide) 0 5 24 (by decide +kernel)
theorem n8_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[16]!).toFinset :=
  nbAt h a eids8 16 (by decide) 0 5 25 (by decide +kernel)
theorem n8_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[17]!).toFinset :=
  nbAt h a eids8 17 (by decide) 0 5 4 (by decide +kernel)
theorem n8_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[18]!).toFinset :=
  nbAt h a eids8 18 (by decide) 0 5 26 (by decide +kernel)
theorem n8_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[19]!).toFinset :=
  nbAt h a eids8 19 (by decide) 0 5 31 (by decide +kernel)
theorem n8_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges8[20]!).toFinset :=
  nbAt h a eids8 20 (by decide) 0 5 70 (by decide +kernel)
theorem n9_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[0]!).toFinset :=
  nbAt h a eids9 0 (by decide) 2 5 72 (by decide +kernel)
theorem n9_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[1]!).toFinset :=
  nbAt h a eids9 1 (by decide) 2 5 73 (by decide +kernel)
theorem n9_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[2]!).toFinset :=
  nbAt h a eids9 2 (by decide) 1 5 74 (by decide +kernel)
theorem n9_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[3]!).toFinset :=
  nbAt h a eids9 3 (by decide) 0 5 75 (by decide +kernel)
theorem n9_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[4]!).toFinset :=
  nbAt h a eids9 4 (by decide) 0 5 76 (by decide +kernel)
theorem n9_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[5]!).toFinset :=
  nbAt h a eids9 5 (by decide) 0 5 77 (by decide +kernel)
theorem n9_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[6]!).toFinset :=
  nbAt h a eids9 6 (by decide) 0 5 78 (by decide +kernel)
theorem n9_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[7]!).toFinset :=
  nbAt h a eids9 7 (by decide) 0 5 74 (by decide +kernel)
theorem n9_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[8]!).toFinset :=
  nbAt h a eids9 8 (by decide) 0 5 79 (by decide +kernel)
theorem n9_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[9]!).toFinset :=
  nbAt h a eids9 9 (by decide) 0 5 80 (by decide +kernel)
theorem n9_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[10]!).toFinset :=
  nbAt h a eids9 10 (by decide) 0 5 81 (by decide +kernel)
theorem n9_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[11]!).toFinset :=
  nbAt h a eids9 11 (by decide) 0 5 82 (by decide +kernel)
theorem n9_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges9[12]!).toFinset :=
  nbAt h a eids9 12 (by decide) 0 5 83 (by decide +kernel)
theorem n10_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[0]!).toFinset :=
  nbAt h a eids10 0 (by decide) 0 6 94 (by decide +kernel)
theorem n10_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[1]!).toFinset :=
  nbAt h a eids10 1 (by decide) 0 6 93 (by decide +kernel)
theorem n10_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[2]!).toFinset :=
  nbAt h a eids10 2 (by decide) 0 6 94 (by decide +kernel)
theorem n10_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[3]!).toFinset :=
  nbAt h a eids10 3 (by decide) 1 6 94 (by decide +kernel)
theorem n10_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[4]!).toFinset :=
  nbAt h a eids10 4 (by decide) 0 6 94 (by decide +kernel)
theorem n10_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[5]!).toFinset :=
  nbAt h a eids10 5 (by decide) 0 6 93 (by decide +kernel)
theorem n10_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[6]!).toFinset :=
  nbAt h a eids10 6 (by decide) 0 6 94 (by decide +kernel)
theorem n10_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[7]!).toFinset :=
  nbAt h a eids10 7 (by decide) 2 6 94 (by decide +kernel)
theorem n10_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[8]!).toFinset :=
  nbAt h a eids10 8 (by decide) 0 6 63 (by decide +kernel)
theorem n10_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[9]!).toFinset :=
  nbAt h a eids10 9 (by decide) 0 6 94 (by decide +kernel)
theorem n10_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[10]!).toFinset :=
  nbAt h a eids10 10 (by decide) 0 6 93 (by decide +kernel)
theorem n10_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[11]!).toFinset :=
  nbAt h a eids10 11 (by decide) 1 6 95 (by decide +kernel)
theorem n10_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[12]!).toFinset :=
  nbAt h a eids10 12 (by decide) 0 6 93 (by decide +kernel)
theorem n10_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[13]!).toFinset :=
  nbAt h a eids10 13 (by decide) 0 6 94 (by decide +kernel)
theorem n10_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[14]!).toFinset :=
  nbAt h a eids10 14 (by decide) 3 6 96 (by decide +kernel)
theorem n10_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[15]!).toFinset :=
  nbAt h a eids10 15 (by decide) 0 6 93 (by decide +kernel)
theorem n10_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[16]!).toFinset :=
  nbAt h a eids10 16 (by decide) 0 6 93 (by decide +kernel)
theorem n10_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[17]!).toFinset :=
  nbAt h a eids10 17 (by decide) 0 6 94 (by decide +kernel)
theorem n10_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[18]!).toFinset :=
  nbAt h a eids10 18 (by decide) 3 6 97 (by decide +kernel)
theorem n10_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[19]!).toFinset :=
  nbAt h a eids10 19 (by decide) 0 6 94 (by decide +kernel)
theorem n10_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[20]!).toFinset :=
  nbAt h a eids10 20 (by decide) 3 6 98 (by decide +kernel)
theorem n10_21 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[21]!).toFinset :=
  nbAt h a eids10 21 (by decide) 0 6 93 (by decide +kernel)
theorem n10_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[22]!).toFinset :=
  nbAt h a eids10 22 (by decide) 0 6 93 (by decide +kernel)
theorem n10_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[23]!).toFinset :=
  nbAt h a eids10 23 (by decide) 0 6 94 (by decide +kernel)
theorem n10_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[24]!).toFinset :=
  nbAt h a eids10 24 (by decide) 4 6 97 (by decide +kernel)
theorem n10_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[25]!).toFinset :=
  nbAt h a eids10 25 (by decide) 1 6 94 (by decide +kernel)
theorem n10_26 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[26]!).toFinset :=
  nbAt h a eids10 26 (by decide) 0 6 93 (by decide +kernel)
theorem n10_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[27]!).toFinset :=
  nbAt h a eids10 27 (by decide) 1 6 94 (by decide +kernel)
theorem n10_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[28]!).toFinset :=
  nbAt h a eids10 28 (by decide) 2 6 94 (by decide +kernel)
theorem n10_29 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[29]!).toFinset :=
  nbAt h a eids10 29 (by decide) 0 6 63 (by decide +kernel)
theorem n10_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[30]!).toFinset :=
  nbAt h a eids10 30 (by decide) 0 6 94 (by decide +kernel)
theorem n10_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[31]!).toFinset :=
  nbAt h a eids10 31 (by decide) 0 6 99 (by decide +kernel)
theorem n10_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[32]!).toFinset :=
  nbAt h a eids10 32 (by decide) 0 6 95 (by decide +kernel)
theorem n10_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[33]!).toFinset :=
  nbAt h a eids10 33 (by decide) 1 6 93 (by decide +kernel)
theorem n10_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[34]!).toFinset :=
  nbAt h a eids10 34 (by decide) 1 6 94 (by decide +kernel)
theorem n10_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[35]!).toFinset :=
  nbAt h a eids10 35 (by decide) 3 6 96 (by decide +kernel)
theorem n10_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[36]!).toFinset :=
  nbAt h a eids10 36 (by decide) 1 6 93 (by decide +kernel)
theorem n10_37 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[37]!).toFinset :=
  nbAt h a eids10 37 (by decide) 0 6 100 (by decide +kernel)
theorem n10_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[38]!).toFinset :=
  nbAt h a eids10 38 (by decide) 1 6 94 (by decide +kernel)
theorem n10_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[39]!).toFinset :=
  nbAt h a eids10 39 (by decide) 3 6 97 (by decide +kernel)
theorem n10_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[40]!).toFinset :=
  nbAt h a eids10 40 (by decide) 1 6 94 (by decide +kernel)
theorem n10_41 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[41]!).toFinset :=
  nbAt h a eids10 41 (by decide) 3 6 101 (by decide +kernel)
theorem n10_42 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[42]!).toFinset :=
  nbAt h a eids10 42 (by decide) 1 6 93 (by decide +kernel)
theorem n10_43 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[43]!).toFinset :=
  nbAt h a eids10 43 (by decide) 0 6 102 (by decide +kernel)
theorem n10_44 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[44]!).toFinset :=
  nbAt h a eids10 44 (by decide) 1 6 94 (by decide +kernel)
theorem n10_45 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[45]!).toFinset :=
  nbAt h a eids10 45 (by decide) 4 6 97 (by decide +kernel)
theorem n10_46 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[46]!).toFinset :=
  nbAt h a eids10 46 (by decide) 0 6 63 (by decide +kernel)
theorem n10_47 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[47]!).toFinset :=
  nbAt h a eids10 47 (by decide) 0 6 94 (by decide +kernel)
theorem n10_48 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[48]!).toFinset :=
  nbAt h a eids10 48 (by decide) 0 6 103 (by decide +kernel)
theorem n10_49 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[49]!).toFinset :=
  nbAt h a eids10 49 (by decide) 0 6 104 (by decide +kernel)
theorem n10_50 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[50]!).toFinset :=
  nbAt h a eids10 50 (by decide) 2 6 93 (by decide +kernel)
theorem n10_51 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[51]!).toFinset :=
  nbAt h a eids10 51 (by decide) 2 6 94 (by decide +kernel)
theorem n10_52 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[52]!).toFinset :=
  nbAt h a eids10 52 (by decide) 3 6 96 (by decide +kernel)
theorem n10_53 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[53]!).toFinset :=
  nbAt h a eids10 53 (by decide) 2 6 93 (by decide +kernel)
theorem n10_54 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[54]!).toFinset :=
  nbAt h a eids10 54 (by decide) 0 6 105 (by decide +kernel)
theorem n10_55 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[55]!).toFinset :=
  nbAt h a eids10 55 (by decide) 2 6 94 (by decide +kernel)
theorem n10_56 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[56]!).toFinset :=
  nbAt h a eids10 56 (by decide) 3 6 97 (by decide +kernel)
theorem n10_57 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[57]!).toFinset :=
  nbAt h a eids10 57 (by decide) 2 6 94 (by decide +kernel)
theorem n10_58 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[58]!).toFinset :=
  nbAt h a eids10 58 (by decide) 3 6 106 (by decide +kernel)
theorem n10_59 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[59]!).toFinset :=
  nbAt h a eids10 59 (by decide) 2 6 93 (by decide +kernel)
theorem n10_60 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[60]!).toFinset :=
  nbAt h a eids10 60 (by decide) 0 6 107 (by decide +kernel)
theorem n10_61 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[61]!).toFinset :=
  nbAt h a eids10 61 (by decide) 2 6 94 (by decide +kernel)
theorem n10_62 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[62]!).toFinset :=
  nbAt h a eids10 62 (by decide) 4 6 97 (by decide +kernel)
theorem n10_63 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[63]!).toFinset :=
  nbAt h a eids10 63 (by decide) 3 6 63 (by decide +kernel)
theorem n10_64 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[64]!).toFinset :=
  nbAt h a eids10 64 (by decide) 3 6 97 (by decide +kernel)
theorem n10_65 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[65]!).toFinset :=
  nbAt h a eids10 65 (by decide) 0 6 96 (by decide +kernel)
theorem n10_66 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[66]!).toFinset :=
  nbAt h a eids10 66 (by decide) 3 6 96 (by decide +kernel)
theorem n10_67 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[67]!).toFinset :=
  nbAt h a eids10 67 (by decide) 0 6 108 (by decide +kernel)
theorem n10_68 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[68]!).toFinset :=
  nbAt h a eids10 68 (by decide) 3 6 96 (by decide +kernel)
theorem n10_69 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[69]!).toFinset :=
  nbAt h a eids10 69 (by decide) 3 6 63 (by decide +kernel)
theorem n10_70 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[70]!).toFinset :=
  nbAt h a eids10 70 (by decide) 3 6 97 (by decide +kernel)
theorem n10_71 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[71]!).toFinset :=
  nbAt h a eids10 71 (by decide) 4 6 63 (by decide +kernel)
theorem n10_72 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[72]!).toFinset :=
  nbAt h a eids10 72 (by decide) 4 6 97 (by decide +kernel)
theorem n10_73 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[73]!).toFinset :=
  nbAt h a eids10 73 (by decide) 0 6 71 (by decide +kernel)
theorem n10_74 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[74]!).toFinset :=
  nbAt h a eids10 74 (by decide) 4 6 96 (by decide +kernel)
theorem n10_75 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[75]!).toFinset :=
  nbAt h a eids10 75 (by decide) 0 6 109 (by decide +kernel)
theorem n10_76 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[76]!).toFinset :=
  nbAt h a eids10 76 (by decide) 4 6 96 (by decide +kernel)
theorem n10_77 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[77]!).toFinset :=
  nbAt h a eids10 77 (by decide) 4 6 63 (by decide +kernel)
theorem n10_78 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[78]!).toFinset :=
  nbAt h a eids10 78 (by decide) 4 6 97 (by decide +kernel)
theorem n10_79 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[79]!).toFinset :=
  nbAt h a eids10 79 (by decide) 3 6 97 (by decide +kernel)
theorem n10_80 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[80]!).toFinset :=
  nbAt h a eids10 80 (by decide) 3 6 96 (by decide +kernel)
theorem n10_81 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[81]!).toFinset :=
  nbAt h a eids10 81 (by decide) 3 6 97 (by decide +kernel)
theorem n10_82 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges10[82]!).toFinset :=
  nbAt h a eids10 82 (by decide) 4 6 97 (by decide +kernel)
theorem n11_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[0]!).toFinset :=
  nbAt h a eids11 0 (by decide) 0 6 93 (by decide +kernel)
theorem n11_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[1]!).toFinset :=
  nbAt h a eids11 1 (by decide) 0 6 94 (by decide +kernel)
theorem n11_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[2]!).toFinset :=
  nbAt h a eids11 2 (by decide) 1 6 94 (by decide +kernel)
theorem n11_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[3]!).toFinset :=
  nbAt h a eids11 3 (by decide) 0 6 94 (by decide +kernel)
theorem n11_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[4]!).toFinset :=
  nbAt h a eids11 4 (by decide) 1 6 94 (by decide +kernel)
theorem n11_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[5]!).toFinset :=
  nbAt h a eids11 5 (by decide) 0 6 94 (by decide +kernel)
theorem n11_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[6]!).toFinset :=
  nbAt h a eids11 6 (by decide) 1 6 94 (by decide +kernel)
theorem n11_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[7]!).toFinset :=
  nbAt h a eids11 7 (by decide) 1 6 94 (by decide +kernel)
theorem n11_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[8]!).toFinset :=
  nbAt h a eids11 8 (by decide) 1 6 93 (by decide +kernel)
theorem n11_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[9]!).toFinset :=
  nbAt h a eids11 9 (by decide) 0 6 93 (by decide +kernel)
theorem n11_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[10]!).toFinset :=
  nbAt h a eids11 10 (by decide) 0 6 63 (by decide +kernel)
theorem n11_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[11]!).toFinset :=
  nbAt h a eids11 11 (by decide) 1 6 99 (by decide +kernel)
theorem n11_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[12]!).toFinset :=
  nbAt h a eids11 12 (by decide) 0 6 93 (by decide +kernel)
theorem n11_13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[13]!).toFinset :=
  nbAt h a eids11 13 (by decide) 2 6 95 (by decide +kernel)
theorem n11_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[15]!).toFinset :=
  nbAt h a eids11 15 (by decide) 0 6 93 (by decide +kernel)
theorem n11_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[17]!).toFinset :=
  nbAt h a eids11 17 (by decide) 0 6 93 (by decide +kernel)
theorem n11_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[18]!).toFinset :=
  nbAt h a eids11 18 (by decide) 0 6 94 (by decide +kernel)
theorem n11_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[19]!).toFinset :=
  nbAt h a eids11 19 (by decide) 0 6 94 (by decide +kernel)
theorem n11_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[20]!).toFinset :=
  nbAt h a eids11 20 (by decide) 0 6 94 (by decide +kernel)
theorem n11_21 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[21]!).toFinset :=
  nbAt h a eids11 21 (by decide) 0 6 93 (by decide +kernel)
theorem n11_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[22]!).toFinset :=
  nbAt h a eids11 22 (by decide) 1 6 93 (by decide +kernel)
theorem n11_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[23]!).toFinset :=
  nbAt h a eids11 23 (by decide) 0 6 63 (by decide +kernel)
theorem n11_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[24]!).toFinset :=
  nbAt h a eids11 24 (by decide) 0 6 99 (by decide +kernel)
theorem n11_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[25]!).toFinset :=
  nbAt h a eids11 25 (by decide) 0 6 99 (by decide +kernel)
theorem n11_26 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[26]!).toFinset :=
  nbAt h a eids11 26 (by decide) 2 6 104 (by decide +kernel)
theorem n11_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[28]!).toFinset :=
  nbAt h a eids11 28 (by decide) 1 6 93 (by decide +kernel)
theorem n11_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[30]!).toFinset :=
  nbAt h a eids11 30 (by decide) 1 6 93 (by decide +kernel)
theorem n11_31 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[31]!).toFinset :=
  nbAt h a eids11 31 (by decide) 2 6 93 (by decide +kernel)
theorem n11_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[32]!).toFinset :=
  nbAt h a eids11 32 (by decide) 2 6 93 (by decide +kernel)
theorem n11_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[33]!).toFinset :=
  nbAt h a eids11 33 (by decide) 2 6 94 (by decide +kernel)
theorem n11_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[34]!).toFinset :=
  nbAt h a eids11 34 (by decide) 0 6 104 (by decide +kernel)
theorem n11_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[35]!).toFinset :=
  nbAt h a eids11 35 (by decide) 0 6 104 (by decide +kernel)
theorem n11_36 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[36]!).toFinset :=
  nbAt h a eids11 36 (by decide) 2 6 93 (by decide +kernel)
theorem n11_37 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[37]!).toFinset :=
  nbAt h a eids11 37 (by decide) 2 6 94 (by decide +kernel)
theorem n11_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[38]!).toFinset :=
  nbAt h a eids11 38 (by decide) 0 6 63 (by decide +kernel)
theorem n11_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[39]!).toFinset :=
  nbAt h a eids11 39 (by decide) 0 6 63 (by decide +kernel)
theorem n11_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[40]!).toFinset :=
  nbAt h a eids11 40 (by decide) 0 6 94 (by decide +kernel)
theorem n11_41 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[41]!).toFinset :=
  nbAt h a eids11 41 (by decide) 2 6 63 (by decide +kernel)
theorem n11_42 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[42]!).toFinset :=
  nbAt h a eids11 42 (by decide) 2 6 94 (by decide +kernel)
theorem n11_43 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[43]!).toFinset :=
  nbAt h a eids11 43 (by decide) 2 6 94 (by decide +kernel)
theorem n11_44 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[44]!).toFinset :=
  nbAt h a eids11 44 (by decide) 3 6 97 (by decide +kernel)
theorem n11_46 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[46]!).toFinset :=
  nbAt h a eids11 46 (by decide) 0 6 118 (by decide +kernel)
theorem n11_47 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[47]!).toFinset :=
  nbAt h a eids11 47 (by decide) 3 6 97 (by decide +kernel)
theorem n11_48 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[48]!).toFinset :=
  nbAt h a eids11 48 (by decide) 4 6 97 (by decide +kernel)
theorem n11_50 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[50]!).toFinset :=
  nbAt h a eids11 50 (by decide) 0 6 119 (by decide +kernel)
theorem n11_51 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[51]!).toFinset :=
  nbAt h a eids11 51 (by decide) 4 6 97 (by decide +kernel)
theorem n11_52 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[52]!).toFinset :=
  nbAt h a eids11 52 (by decide) 0 6 63 (by decide +kernel)
theorem n11_53 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[53]!).toFinset :=
  nbAt h a eids11 53 (by decide) 0 6 103 (by decide +kernel)
theorem n11_54 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[54]!).toFinset :=
  nbAt h a eids11 54 (by decide) 0 6 104 (by decide +kernel)
theorem n11_56 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[56]!).toFinset :=
  nbAt h a eids11 56 (by decide) 0 6 105 (by decide +kernel)
theorem n11_58 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[58]!).toFinset :=
  nbAt h a eids11 58 (by decide) 0 6 107 (by decide +kernel)
theorem n11_59 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[59]!).toFinset :=
  nbAt h a eids11 59 (by decide) 3 6 94 (by decide +kernel)
theorem n11_60 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[60]!).toFinset :=
  nbAt h a eids11 60 (by decide) 0 6 96 (by decide +kernel)
theorem n11_61 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[61]!).toFinset :=
  nbAt h a eids11 61 (by decide) 0 6 108 (by decide +kernel)
theorem n11_62 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[62]!).toFinset :=
  nbAt h a eids11 62 (by decide) 3 6 94 (by decide +kernel)
theorem n11_63 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[63]!).toFinset :=
  nbAt h a eids11 63 (by decide) 4 6 94 (by decide +kernel)
theorem n11_64 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[64]!).toFinset :=
  nbAt h a eids11 64 (by decide) 0 6 71 (by decide +kernel)
theorem n11_65 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[65]!).toFinset :=
  nbAt h a eids11 65 (by decide) 0 6 109 (by decide +kernel)
theorem n11_66 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges11[66]!).toFinset :=
  nbAt h a eids11 66 (by decide) 4 6 94 (by decide +kernel)
theorem n12_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[0]!).toFinset :=
  nbAt h a eids12 0 (by decide) 0 5 110 (by decide +kernel)
theorem n12_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[1]!).toFinset :=
  nbAt h a eids12 1 (by decide) 0 5 111 (by decide +kernel)
theorem n12_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[2]!).toFinset :=
  nbAt h a eids12 2 (by decide) 0 5 112 (by decide +kernel)
theorem n12_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[3]!).toFinset :=
  nbAt h a eids12 3 (by decide) 0 5 113 (by decide +kernel)
theorem n12_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[4]!).toFinset :=
  nbAt h a eids12 4 (by decide) 0 5 114 (by decide +kernel)
theorem n12_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[5]!).toFinset :=
  nbAt h a eids12 5 (by decide) 0 5 115 (by decide +kernel)
theorem n12_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[6]!).toFinset :=
  nbAt h a eids12 6 (by decide) 0 5 116 (by decide +kernel)
theorem n12_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[7]!).toFinset :=
  nbAt h a eids12 7 (by decide) 0 5 97 (by decide +kernel)
theorem n12_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[8]!).toFinset :=
  nbAt h a eids12 8 (by decide) 2 5 117 (by decide +kernel)
theorem n12_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges12[9]!).toFinset :=
  nbAt h a eids12 9 (by decide) 3 5 117 (by decide +kernel)
theorem n13_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[0]!).toFinset :=
  nbAt h a eids13 0 (by decide) 0 5 65 (by decide +kernel)
theorem n13_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[1]!).toFinset :=
  nbAt h a eids13 1 (by decide) 1 5 120 (by decide +kernel)
theorem n13_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[2]!).toFinset :=
  nbAt h a eids13 2 (by decide) 1 5 121 (by decide +kernel)
theorem n13_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[3]!).toFinset :=
  nbAt h a eids13 3 (by decide) 0 5 120 (by decide +kernel)
theorem n13_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[4]!).toFinset :=
  nbAt h a eids13 4 (by decide) 0 5 121 (by decide +kernel)
theorem n13_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[5]!).toFinset :=
  nbAt h a eids13 5 (by decide) 0 5 120 (by decide +kernel)
theorem n13_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[6]!).toFinset :=
  nbAt h a eids13 6 (by decide) 0 5 122 (by decide +kernel)
theorem n13_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[7]!).toFinset :=
  nbAt h a eids13 7 (by decide) 4 5 63 (by decide +kernel)
theorem n13_8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[8]!).toFinset :=
  nbAt h a eids13 8 (by decide) 0 5 123 (by decide +kernel)
theorem n13_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[9]!).toFinset :=
  nbAt h a eids13 9 (by decide) 0 5 124 (by decide +kernel)
theorem n13_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[10]!).toFinset :=
  nbAt h a eids13 10 (by decide) 0 5 125 (by decide +kernel)
theorem n13_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 (edges13[11]!).toFinset :=
  nbAt h a eids13 11 (by decide) 0 5 126 (by decide +kernel)
theorem n14_0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[0]!).toFinset :=
  nbAt h a eids14 0 (by decide) 0 6 130 (by decide +kernel)
theorem n14_1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[1]!).toFinset :=
  nbAt h a eids14 1 (by decide) 0 6 131 (by decide +kernel)
theorem n14_2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[2]!).toFinset :=
  nbAt h a eids14 2 (by decide) 1 6 131 (by decide +kernel)
theorem n14_3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[3]!).toFinset :=
  nbAt h a eids14 3 (by decide) 0 6 131 (by decide +kernel)
theorem n14_4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[4]!).toFinset :=
  nbAt h a eids14 4 (by decide) 1 6 131 (by decide +kernel)
theorem n14_5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[5]!).toFinset :=
  nbAt h a eids14 5 (by decide) 2 6 63 (by decide +kernel)
theorem n14_6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[6]!).toFinset :=
  nbAt h a eids14 6 (by decide) 1 6 131 (by decide +kernel)
theorem n14_7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[7]!).toFinset :=
  nbAt h a eids14 7 (by decide) 1 6 131 (by decide +kernel)
theorem n14_9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[9]!).toFinset :=
  nbAt h a eids14 9 (by decide) 0 6 130 (by decide +kernel)
theorem n14_10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[10]!).toFinset :=
  nbAt h a eids14 10 (by decide) 2 6 93 (by decide +kernel)
theorem n14_11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[11]!).toFinset :=
  nbAt h a eids14 11 (by decide) 0 6 130 (by decide +kernel)
theorem n14_12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[12]!).toFinset :=
  nbAt h a eids14 12 (by decide) 0 6 130 (by decide +kernel)
theorem n14_14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[14]!).toFinset :=
  nbAt h a eids14 14 (by decide) 0 6 130 (by decide +kernel)
theorem n14_15 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[15]!).toFinset :=
  nbAt h a eids14 15 (by decide) 3 6 93 (by decide +kernel)
theorem n14_16 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[16]!).toFinset :=
  nbAt h a eids14 16 (by decide) 0 6 130 (by decide +kernel)
theorem n14_17 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[17]!).toFinset :=
  nbAt h a eids14 17 (by decide) 0 6 130 (by decide +kernel)
theorem n14_18 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[18]!).toFinset :=
  nbAt h a eids14 18 (by decide) 0 6 63 (by decide +kernel)
theorem n14_19 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[19]!).toFinset :=
  nbAt h a eids14 19 (by decide) 1 6 96 (by decide +kernel)
theorem n14_20 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[20]!).toFinset :=
  nbAt h a eids14 20 (by decide) 0 6 130 (by decide +kernel)
theorem n14_22 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[22]!).toFinset :=
  nbAt h a eids14 22 (by decide) 0 6 1 (by decide +kernel)
theorem n14_23 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[23]!).toFinset :=
  nbAt h a eids14 23 (by decide) 0 6 63 (by decide +kernel)
theorem n14_24 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[24]!).toFinset :=
  nbAt h a eids14 24 (by decide) 0 6 130 (by decide +kernel)
theorem n14_25 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[25]!).toFinset :=
  nbAt h a eids14 25 (by decide) 0 6 130 (by decide +kernel)
theorem n14_27 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[27]!).toFinset :=
  nbAt h a eids14 27 (by decide) 0 6 130 (by decide +kernel)
theorem n14_28 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[28]!).toFinset :=
  nbAt h a eids14 28 (by decide) 2 6 63 (by decide +kernel)
theorem n14_29 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[29]!).toFinset :=
  nbAt h a eids14 29 (by decide) 0 6 131 (by decide +kernel)
theorem n14_30 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[30]!).toFinset :=
  nbAt h a eids14 30 (by decide) 0 6 131 (by decide +kernel)
theorem n14_32 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[32]!).toFinset :=
  nbAt h a eids14 32 (by decide) 1 6 130 (by decide +kernel)
theorem n14_33 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[33]!).toFinset :=
  nbAt h a eids14 33 (by decide) 2 6 93 (by decide +kernel)
theorem n14_34 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[34]!).toFinset :=
  nbAt h a eids14 34 (by decide) 1 6 130 (by decide +kernel)
theorem n14_35 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[35]!).toFinset :=
  nbAt h a eids14 35 (by decide) 0 6 132 (by decide +kernel)
theorem n14_37 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[37]!).toFinset :=
  nbAt h a eids14 37 (by decide) 1 6 130 (by decide +kernel)
theorem n14_38 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[38]!).toFinset :=
  nbAt h a eids14 38 (by decide) 3 6 93 (by decide +kernel)
theorem n14_39 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[39]!).toFinset :=
  nbAt h a eids14 39 (by decide) 1 6 130 (by decide +kernel)
theorem n14_40 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[40]!).toFinset :=
  nbAt h a eids14 40 (by decide) 0 6 133 (by decide +kernel)
theorem n14_41 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[41]!).toFinset :=
  nbAt h a eids14 41 (by decide) 1 6 63 (by decide +kernel)
theorem n14_42 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[42]!).toFinset :=
  nbAt h a eids14 42 (by decide) 0 6 96 (by decide +kernel)
theorem n14_43 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[43]!).toFinset :=
  nbAt h a eids14 43 (by decide) 0 6 96 (by decide +kernel)
theorem n14_45 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[45]!).toFinset :=
  nbAt h a eids14 45 (by decide) 1 6 1 (by decide +kernel)
theorem n14_46 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[46]!).toFinset :=
  nbAt h a eids14 46 (by decide) 1 6 63 (by decide +kernel)
theorem n14_47 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[47]!).toFinset :=
  nbAt h a eids14 47 (by decide) 1 6 130 (by decide +kernel)
theorem n14_48 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[48]!).toFinset :=
  nbAt h a eids14 48 (by decide) 0 6 134 (by decide +kernel)
theorem n14_50 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[50]!).toFinset :=
  nbAt h a eids14 50 (by decide) 1 6 130 (by decide +kernel)
theorem n14_51 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[51]!).toFinset :=
  nbAt h a eids14 51 (by decide) 2 6 63 (by decide +kernel)
theorem n14_52 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[52]!).toFinset :=
  nbAt h a eids14 52 (by decide) 3 6 96 (by decide +kernel)
theorem n14_54 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[54]!).toFinset :=
  nbAt h a eids14 54 (by decide) 2 6 93 (by decide +kernel)
theorem n14_55 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[55]!).toFinset :=
  nbAt h a eids14 55 (by decide) 2 6 93 (by decide +kernel)
theorem n14_56 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[56]!).toFinset :=
  nbAt h a eids14 56 (by decide) 2 6 1 (by decide +kernel)
theorem n14_57 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[57]!).toFinset :=
  nbAt h a eids14 57 (by decide) 0 6 132 (by decide +kernel)
theorem n14_58 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[58]!).toFinset :=
  nbAt h a eids14 58 (by decide) 2 6 63 (by decide +kernel)
theorem n14_59 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[59]!).toFinset :=
  nbAt h a eids14 59 (by decide) 3 6 63 (by decide +kernel)
theorem n14_60 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[60]!).toFinset :=
  nbAt h a eids14 60 (by decide) 2 6 96 (by decide +kernel)
theorem n14_62 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[62]!).toFinset :=
  nbAt h a eids14 62 (by decide) 2 6 96 (by decide +kernel)
theorem n14_63 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[63]!).toFinset :=
  nbAt h a eids14 63 (by decide) 2 6 108 (by decide +kernel)
theorem n14_64 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[64]!).toFinset :=
  nbAt h a eids14 64 (by decide) 3 6 1 (by decide +kernel)
theorem n14_65 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[65]!).toFinset :=
  nbAt h a eids14 65 (by decide) 0 6 133 (by decide +kernel)
theorem n14_66 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[66]!).toFinset :=
  nbAt h a eids14 66 (by decide) 3 6 63 (by decide +kernel)
theorem n14_67 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[67]!).toFinset :=
  nbAt h a eids14 67 (by decide) 0 6 135 (by decide +kernel)
theorem n14_68 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[68]!).toFinset :=
  nbAt h a eids14 68 (by decide) 0 6 135 (by decide +kernel)
theorem n14_69 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[69]!).toFinset :=
  nbAt h a eids14 69 (by decide) 2 6 136 (by decide +kernel)
theorem n14_70 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[70]!).toFinset :=
  nbAt h a eids14 70 (by decide) 0 6 96 (by decide +kernel)
theorem n14_71 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[71]!).toFinset :=
  nbAt h a eids14 71 (by decide) 0 6 96 (by decide +kernel)
theorem n14_72 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[72]!).toFinset :=
  nbAt h a eids14 72 (by decide) 2 6 96 (by decide +kernel)
theorem n14_73 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[73]!).toFinset :=
  nbAt h a eids14 73 (by decide) 0 6 137 (by decide +kernel)
theorem n14_74 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[74]!).toFinset :=
  nbAt h a eids14 74 (by decide) 0 6 137 (by decide +kernel)
theorem n14_75 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[75]!).toFinset :=
  nbAt h a eids14 75 (by decide) 2 6 108 (by decide +kernel)
theorem n14_76 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[76]!).toFinset :=
  nbAt h a eids14 76 (by decide) 0 6 134 (by decide +kernel)
theorem n14_77 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[77]!).toFinset :=
  nbAt h a eids14 77 (by decide) 0 6 134 (by decide +kernel)
theorem n14_78 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[78]!).toFinset :=
  nbAt h a eids14 78 (by decide) 2 6 138 (by decide +kernel)
theorem n14_79 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[79]!).toFinset :=
  nbAt h a eids14 79 (by decide) 4 6 139 (by decide +kernel)
theorem n14_80 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[80]!).toFinset :=
  nbAt h a eids14 80 (by decide) 2 6 71 (by decide +kernel)
theorem n14_81 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[81]!).toFinset :=
  nbAt h a eids14 81 (by decide) 2 6 109 (by decide +kernel)
theorem n14_82 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[82]!).toFinset :=
  nbAt h a eids14 82 (by decide) 4 6 139 (by decide +kernel)
theorem n14_83 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[83]!).toFinset :=
  nbAt h a eids14 83 (by decide) 2 6 93 (by decide +kernel)
theorem n14_84 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[84]!).toFinset :=
  nbAt h a eids14 84 (by decide) 2 6 94 (by decide +kernel)
theorem n14_85 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[85]!).toFinset :=
  nbAt h a eids14 85 (by decide) 3 6 94 (by decide +kernel)
theorem n14_86 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[86]!).toFinset :=
  nbAt h a eids14 86 (by decide) 2 6 94 (by decide +kernel)
theorem n14_87 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[87]!).toFinset :=
  nbAt h a eids14 87 (by decide) 3 6 94 (by decide +kernel)
theorem n14_88 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[88]!).toFinset :=
  nbAt h a eids14 88 (by decide) 0 6 63 (by decide +kernel)
theorem n14_89 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[89]!).toFinset :=
  nbAt h a eids14 89 (by decide) 3 6 94 (by decide +kernel)
theorem n14_90 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[90]!).toFinset :=
  nbAt h a eids14 90 (by decide) 3 6 94 (by decide +kernel)
theorem n14_92 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[92]!).toFinset :=
  nbAt h a eids14 92 (by decide) 0 6 140 (by decide +kernel)
theorem n14_93 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[93]!).toFinset :=
  nbAt h a eids14 93 (by decide) 0 6 63 (by decide +kernel)
theorem n14_94 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[94]!).toFinset :=
  nbAt h a eids14 94 (by decide) 2 6 94 (by decide +kernel)
theorem n14_95 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[95]!).toFinset :=
  nbAt h a eids14 95 (by decide) 2 6 94 (by decide +kernel)
theorem n14_97 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[97]!).toFinset :=
  nbAt h a eids14 97 (by decide) 0 6 141 (by decide +kernel)
theorem n14_98 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[98]!).toFinset :=
  nbAt h a eids14 98 (by decide) 4 6 94 (by decide +kernel)
theorem n14_99 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[99]!).toFinset :=
  nbAt h a eids14 99 (by decide) 0 6 142 (by decide +kernel)
theorem n14_100 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[100]!).toFinset :=
  nbAt h a eids14 100 (by decide) 0 6 143 (by decide +kernel)
theorem n14_101 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 (edges14[101]!).toFinset :=
  nbAt h a eids14 101 (by decide) 4 6 94 (by decide +kernel)
end K5Cache

namespace K5Cache
open GThreshold
set_option maxRecDepth 20000 in
def pm0 : Array Nat := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 20000 in
def pm1 : Array Nat := #[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 20000 in
def pm2 : Array Nat := #[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]
set_option maxRecDepth 20000 in
def pm3 : Array Nat := #[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31]
set_option maxRecDepth 20000 in
def pm4 : Array Nat := #[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
set_option maxRecDepth 20000 in
def pm5 : Array Nat := #[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]
set_option maxRecDepth 20000 in
def pm6 : Array Nat := #[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31]
set_option maxRecDepth 20000 in
def pm7 : Array Nat := #[0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31]
set_option maxRecDepth 20000 in
def pm8 : Array Nat := #[0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31]
set_option maxRecDepth 20000 in
def pm9 : Array Nat := #[0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31]
set_option maxRecDepth 20000 in
def pm10 : Array Nat := #[0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31]
set_option maxRecDepth 20000 in
def pm12 : Array Nat := #[0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31]
set_option maxRecDepth 20000 in
def pm13 : Array Nat := #[0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31]
set_option maxRecDepth 20000 in
def pm15 : Array Nat := #[0,1,16,17,4,5,20,21,2,3,18,19,6,7,22,23,8,9,24,25,12,13,28,29,10,11,26,27,14,15,30,31]
set_option maxRecDepth 20000 in
def pm16 : Array Nat := #[0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31]
set_option maxRecDepth 20000 in
def pm18 : Array Nat := #[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]
set_option maxRecDepth 20000 in
def pm20 : Array Nat := #[0,1,8,9,4,5,12,13,16,17,24,25,20,21,28,29,2,3,10,11,6,7,14,15,18,19,26,27,22,23,30,31]
set_option maxRecDepth 20000 in
def pm21 : Array Nat := #[0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31]
set_option maxRecDepth 20000 in
def pm24 : Array Nat := #[0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31]
set_option maxRecDepth 20000 in
def pm26 : Array Nat := #[0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]
set_option maxRecDepth 20000 in
def pm30 : Array Nat := #[0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15,16,20,17,21,18,22,19,23,24,28,25,29,26,30,27,31]
set_option maxRecDepth 20000 in
def pm31 : Array Nat := #[0,4,1,5,2,6,3,7,16,20,17,21,18,22,19,23,8,12,9,13,10,14,11,15,24,28,25,29,26,30,27,31]
set_option maxRecDepth 20000 in
def pm33 : Array Nat := #[0,16,1,17,2,18,3,19,4,20,5,21,6,22,7,23,8,24,9,25,10,26,11,27,12,28,13,29,14,30,15,31]
set_option maxRecDepth 20000 in
def pm34 : Array Nat := #[0,8,1,9,2,10,3,11,16,24,17,25,18,26,19,27,4,12,5,13,6,14,7,15,20,28,21,29,22,30,23,31]
set_option maxRecDepth 20000 in
def pm36 : Array Nat := #[0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15,16,20,17,21,24,28,25,29,18,22,19,23,26,30,27,31]
set_option maxRecDepth 20000 in
def pm37 : Array Nat := #[0,4,1,5,16,20,17,21,2,6,3,7,18,22,19,23,8,12,9,13,24,28,25,29,10,14,11,15,26,30,27,31]
set_option maxRecDepth 20000 in
def pm39 : Array Nat := #[0,16,1,17,4,20,5,21,2,18,3,19,6,22,7,23,8,24,9,25,12,28,13,29,10,26,11,27,14,30,15,31]
set_option maxRecDepth 20000 in
def pm40 : Array Nat := #[0,8,1,9,16,24,17,25,2,10,3,11,18,26,19,27,4,12,5,13,20,28,21,29,6,14,7,15,22,30,23,31]
set_option maxRecDepth 20000 in
def pm42 : Array Nat := #[0,4,1,5,8,12,9,13,16,20,17,21,24,28,25,29,2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31]
set_option maxRecDepth 20000 in
def pm45 : Array Nat := #[0,16,1,17,4,20,5,21,8,24,9,25,12,28,13,29,2,18,3,19,6,22,7,23,10,26,11,27,14,30,15,31]
set_option maxRecDepth 20000 in
def pm48 : Array Nat := #[0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15,16,18,20,22,17,19,21,23,24,26,28,30,25,27,29,31]
set_option maxRecDepth 20000 in
def pm49 : Array Nat := #[0,2,4,6,1,3,5,7,16,18,20,22,17,19,21,23,8,10,12,14,9,11,13,15,24,26,28,30,25,27,29,31]
set_option maxRecDepth 20000 in
def pm50 : Array Nat := #[0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15,16,18,24,26,17,19,25,27,20,22,28,30,21,23,29,31]
set_option maxRecDepth 20000 in
def pm51 : Array Nat := #[0,2,16,18,1,3,17,19,4,6,20,22,5,7,21,23,8,10,24,26,9,11,25,27,12,14,28,30,13,15,29,31]
set_option maxRecDepth 20000 in
def pm52 : Array Nat := #[0,2,8,10,1,3,9,11,16,18,24,26,17,19,25,27,4,6,12,14,5,7,13,15,20,22,28,30,21,23,29,31]
set_option maxRecDepth 20000 in
def pm55 : Array Nat := #[0,4,2,6,1,5,3,7,16,20,18,22,17,21,19,23,8,12,10,14,9,13,11,15,24,28,26,30,25,29,27,31]
set_option maxRecDepth 20000 in
def pm56 : Array Nat := #[0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15,16,24,18,26,17,25,19,27,20,28,22,30,21,29,23,31]
set_option maxRecDepth 20000 in
def pm60 : Array Nat := #[0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15,16,20,24,28,17,21,25,29,18,22,26,30,19,23,27,31]
set_option maxRecDepth 20000 in
def pm61 : Array Nat := #[0,4,16,20,1,5,17,21,2,6,18,22,3,7,19,23,8,12,24,28,9,13,25,29,10,14,26,30,11,15,27,31]
set_option maxRecDepth 20000 in
def pm63 : Array Nat := #[0,16,4,20,1,17,5,21,2,18,6,22,3,19,7,23,8,24,12,28,9,25,13,29,10,26,14,30,11,27,15,31]
set_option maxRecDepth 20000 in
def pm64 : Array Nat := #[0,8,16,24,1,9,17,25,2,10,18,26,3,11,19,27,4,12,20,28,5,13,21,29,6,14,22,30,7,15,23,31]
set_option maxRecDepth 20000 in
def pm66 : Array Nat := #[0,4,8,12,1,5,9,13,16,20,24,28,17,21,25,29,2,6,10,14,3,7,11,15,18,22,26,30,19,23,27,31]
set_option maxRecDepth 20000 in
def pm73 : Array Nat := #[0,2,4,6,16,18,20,22,1,3,5,7,17,19,21,23,8,10,12,14,24,26,28,30,9,11,13,15,25,27,29,31]
set_option maxRecDepth 20000 in
def pm76 : Array Nat := #[0,2,8,10,16,18,24,26,1,3,9,11,17,19,25,27,4,6,12,14,20,22,28,30,5,7,13,15,21,23,29,31]
set_option maxRecDepth 20000 in
def pm78 : Array Nat := #[0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15,16,20,18,22,24,28,26,30,17,21,19,23,25,29,27,31]
set_option maxRecDepth 20000 in
def pm80 : Array Nat := #[0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15,16,24,18,26,20,28,22,30,17,25,19,27,21,29,23,31]
set_option maxRecDepth 20000 in
def pm90 : Array Nat := #[0,4,8,12,16,20,24,28,1,5,9,13,17,21,25,29,2,6,10,14,18,22,26,30,3,7,11,15,19,23,27,31]
set_option maxRecDepth 20000 in
def pm96 : Array Nat := #[0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31]
set_option maxRecDepth 20000 in
def pm98 : Array Nat := #[0,2,8,10,4,6,12,14,16,18,24,26,20,22,28,30,1,3,9,11,5,7,13,15,17,19,25,27,21,23,29,31]
set_option maxRecDepth 20000 in
def pm99 : Array Nat := #[0,2,16,18,4,6,20,22,8,10,24,26,12,14,28,30,1,3,17,19,5,7,21,23,9,11,25,27,13,15,29,31]
set_option maxRecDepth 20000 in
def pm108 : Array Nat := #[0,4,8,12,2,6,10,14,16,20,24,28,18,22,26,30,1,5,9,13,3,7,11,15,17,21,25,29,19,23,27,31]
set_option maxRecDepth 20000 in
def pairs0 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[99]!),(words5[105]!,words5[105]!),(words5[113]!,words5[113]!),(words5[114]!,words5[114]!),(words5[120]!,words5[120]!),(words5[125]!,words5[125]!),(words5[130]!,words5[130]!),(words5[131]!,words5[131]!),(words5[135]!,words5[135]!),(words5[139]!,words5[139]!),(words5[141]!,words5[141]!),(words5[144]!,words5[144]!),(words5[148]!,words5[148]!),(words5[149]!,words5[149]!),(words5[152]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert0 : validRow pm0 pm0 pairs0 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert0 : fastRows pm0 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs30 : List (W×W) := [(words5[105]!,words5[116]!),(words5[113]!,words5[90]!),(words5[128]!,words5[130]!),(words5[144]!,words5[148]!),(words5[152]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert30 : validRow pm30 pm48 pairs30 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert30 : fastRows pm30 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs55 : List (W×W) := [(words5[99]!,words5[99]!),(words5[113]!,words5[90]!),(words5[114]!,words5[114]!),(words5[128]!,words5[148]!),(words5[144]!,words5[130]!),(words5[152]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert55 : validRow pm55 pm55 pairs55 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert55 : fastRows pm55 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs12 : List (W×W) := [(words5[90]!,words5[90]!),(words5[113]!,words5[99]!),(words5[116]!,words5[130]!),(words5[128]!,words5[114]!),(words5[144]!,words5[152]!),(words5[152]!,words5[148]!)]
set_option maxRecDepth 20000 in
theorem pcert12 : validRow pm12 pm8 pairs12 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert12 : fastRows pm12 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs52 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[114]!),(words5[114]!,words5[148]!),(words5[125]!,words5[99]!),(words5[148]!,words5[152]!),(words5[152]!,words5[130]!)]
set_option maxRecDepth 20000 in
theorem pcert52 : validRow pm52 pm37 pairs52 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert52 : fastRows pm52 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs49 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[114]!),(words5[113]!,words5[99]!),(words5[128]!,words5[148]!),(words5[148]!,words5[130]!),(words5[152]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert49 : validRow pm49 pm31 pairs49 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert49 : fastRows pm49 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs10 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[114]!),(words5[116]!,words5[148]!),(words5[125]!,words5[99]!),(words5[148]!,words5[152]!),(words5[152]!,words5[130]!)]
set_option maxRecDepth 20000 in
theorem pcert10 : validRow pm10 pm13 pairs10 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert10 : fastRows pm10 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs7 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[114]!),(words5[113]!,words5[99]!),(words5[130]!,words5[148]!),(words5[148]!,words5[130]!),(words5[152]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert7 : validRow pm7 pm7 pairs7 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert7 : fastRows pm7 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs60 : List (W×W) := [(words5[90]!,words5[113]!),(words5[99]!,words5[125]!),(words5[105]!,words5[135]!),(words5[113]!,words5[90]!),(words5[125]!,words5[99]!),(words5[135]!,words5[105]!),(words5[139]!,words5[139]!),(words5[141]!,words5[148]!),(words5[144]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert60 : validRow pm60 pm60 pairs60 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert60 : fastRows pm60 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs78 : List (W×W) := [(words5[99]!,words5[99]!),(words5[113]!,words5[90]!),(words5[114]!,words5[128]!),(words5[125]!,words5[113]!),(words5[141]!,words5[152]!),(words5[144]!,words5[144]!)]
set_option maxRecDepth 20000 in
theorem pcert78 : validRow pm78 pm56 pairs78 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert78 : fastRows pm78 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs80 : List (W×W) := [(words5[99]!,words5[99]!),(words5[113]!,words5[113]!),(words5[125]!,words5[90]!),(words5[128]!,words5[128]!),(words5[141]!,words5[152]!),(words5[144]!,words5[144]!)]
set_option maxRecDepth 20000 in
theorem pcert80 : validRow pm80 pm80 pairs80 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert80 : fastRows pm80 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs18 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[141]!),(words5[113]!,words5[99]!),(words5[116]!,words5[144]!),(words5[125]!,words5[113]!),(words5[139]!,words5[125]!),(words5[141]!,words5[128]!),(words5[144]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert18 : validRow pm18 pm9 pairs18 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert18 : fastRows pm18 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs20 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[141]!),(words5[113]!,words5[113]!),(words5[120]!,words5[149]!),(words5[125]!,words5[99]!),(words5[130]!,words5[144]!),(words5[139]!,words5[125]!),(words5[141]!,words5[128]!),(words5[144]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert20 : validRow pm20 pm15 pairs20 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert20 : fastRows pm20 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs24 : List (W×W) := [(words5[90]!,words5[99]!),(words5[99]!,words5[90]!),(words5[113]!,words5[113]!),(words5[125]!,words5[125]!),(words5[141]!,words5[144]!),(words5[144]!,words5[141]!),(words5[150]!,words5[149]!)]
set_option maxRecDepth 20000 in
theorem pcert24 : validRow pm24 pm24 pairs24 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert24 : fastRows pm24 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs2 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[99]!),(words5[105]!,words5[105]!),(words5[113]!,words5[125]!),(words5[125]!,words5[113]!),(words5[131]!,words5[120]!),(words5[139]!,words5[139]!),(words5[141]!,words5[141]!),(words5[144]!,words5[144]!),(words5[153]!,words5[149]!)]
set_option maxRecDepth 20000 in
theorem pcert2 : validRow pm2 pm2 pairs2 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert2 : fastRows pm2 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs26 : List (W×W) := [(words5[90]!,words5[99]!),(words5[99]!,words5[90]!),(words5[113]!,words5[125]!),(words5[125]!,words5[113]!),(words5[141]!,words5[144]!),(words5[144]!,words5[141]!),(words5[154]!,words5[149]!)]
set_option maxRecDepth 20000 in
theorem pcert26 : validRow pm26 pm26 pairs26 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert26 : fastRows pm26 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs98 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[141]!),(words5[113]!,words5[113]!),(words5[120]!,words5[149]!),(words5[125]!,words5[99]!),(words5[128]!,words5[144]!),(words5[139]!,words5[125]!)]
set_option maxRecDepth 20000 in
theorem pcert98 : validRow pm98 pm39 pairs98 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert98 : fastRows pm98 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs99 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[141]!),(words5[113]!,words5[113]!),(words5[120]!,words5[149]!),(words5[125]!,words5[125]!),(words5[139]!,words5[99]!),(words5[141]!,words5[144]!)]
set_option maxRecDepth 20000 in
theorem pcert99 : validRow pm99 pm45 pairs99 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert99 : fastRows pm99 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs21 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[141]!),(words5[113]!,words5[113]!),(words5[120]!,words5[149]!),(words5[125]!,words5[125]!),(words5[139]!,words5[99]!),(words5[144]!,words5[144]!)]
set_option maxRecDepth 20000 in
theorem pcert21 : validRow pm21 pm21 pairs21 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert21 : fastRows pm21 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs1 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[99]!),(words5[105]!,words5[105]!),(words5[113]!,words5[113]!),(words5[120]!,words5[120]!),(words5[125]!,words5[139]!),(words5[131]!,words5[146]!),(words5[135]!,words5[148]!),(words5[139]!,words5[125]!),(words5[146]!,words5[131]!),(words5[148]!,words5[135]!),(words5[152]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert1 : validRow pm1 pm1 pairs1 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert1 : fastRows pm1 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs4 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[99]!),(words5[105]!,words5[105]!),(words5[113]!,words5[139]!),(words5[120]!,words5[146]!),(words5[125]!,words5[113]!),(words5[135]!,words5[148]!),(words5[139]!,words5[125]!),(words5[148]!,words5[152]!),(words5[152]!,words5[135]!)]
set_option maxRecDepth 20000 in
theorem pcert4 : validRow pm4 pm3 pairs4 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert4 : fastRows pm4 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs5 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[99]!),(words5[105]!,words5[105]!),(words5[120]!,words5[146]!),(words5[125]!,words5[125]!),(words5[139]!,words5[113]!),(words5[148]!,words5[148]!)]
set_option maxRecDepth 20000 in
theorem pcert5 : validRow pm5 pm5 pairs5 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert5 : fastRows pm5 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs76 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[128]!),(words5[114]!,words5[152]!),(words5[125]!,words5[99]!),(words5[135]!,words5[144]!),(words5[139]!,words5[113]!)]
set_option maxRecDepth 20000 in
theorem pcert76 : validRow pm76 pm40 pairs76 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert76 : fastRows pm76 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs73 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[128]!),(words5[113]!,words5[99]!),(words5[128]!,words5[152]!),(words5[135]!,words5[144]!),(words5[139]!,words5[113]!)]
set_option maxRecDepth 20000 in
theorem pcert73 : validRow pm73 pm34 pairs73 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert73 : fastRows pm73 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs108 : List (W×W) := [(words5[99]!,words5[113]!),(words5[105]!,words5[148]!),(words5[113]!,words5[90]!),(words5[125]!,words5[99]!),(words5[135]!,words5[105]!),(words5[136]!,words5[146]!),(words5[139]!,words5[125]!),(words5[141]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert108 : validRow pm108 pm63 pairs108 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert108 : fastRows pm108 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs16 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[128]!),(words5[116]!,words5[152]!),(words5[125]!,words5[99]!),(words5[135]!,words5[144]!),(words5[139]!,words5[113]!)]
set_option maxRecDepth 20000 in
theorem pcert16 : validRow pm16 pm16 pairs16 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert16 : fastRows pm16 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs13 : List (W×W) := [(words5[90]!,words5[90]!),(words5[105]!,words5[128]!),(words5[113]!,words5[99]!),(words5[130]!,words5[152]!),(words5[135]!,words5[144]!),(words5[139]!,words5[113]!)]
set_option maxRecDepth 20000 in
theorem pcert13 : validRow pm13 pm10 pairs13 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert13 : fastRows pm13 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs66 : List (W×W) := [(words5[90]!,words5[113]!),(words5[105]!,words5[148]!),(words5[113]!,words5[90]!),(words5[125]!,words5[99]!),(words5[135]!,words5[105]!),(words5[137]!,words5[146]!),(words5[139]!,words5[125]!),(words5[144]!,words5[152]!)]
set_option maxRecDepth 20000 in
theorem pcert66 : validRow pm66 pm61 pairs66 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert66 : fastRows pm66 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs96 : List (W×W) := [(words5[99]!,words5[90]!),(words5[105]!,words5[141]!),(words5[113]!,words5[99]!),(words5[114]!,words5[144]!),(words5[125]!,words5[113]!),(words5[139]!,words5[125]!)]
set_option maxRecDepth 20000 in
theorem pcert96 : validRow pm96 pm33 pairs96 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert96 : fastRows pm96 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs3 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[99]!),(words5[105]!,words5[105]!),(words5[113]!,words5[125]!),(words5[125]!,words5[139]!),(words5[139]!,words5[113]!),(words5[146]!,words5[120]!)]
set_option maxRecDepth 20000 in
theorem pcert3 : validRow pm3 pm4 pairs3 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert3 : fastRows pm3 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs6 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[113]!),(words5[113]!,words5[99]!),(words5[114]!,words5[105]!),(words5[125]!,words5[125]!),(words5[139]!,words5[139]!)]
set_option maxRecDepth 20000 in
theorem pcert6 : validRow pm6 pm6 pairs6 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert6 : fastRows pm6 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs8 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[113]!),(words5[113]!,words5[125]!),(words5[125]!,words5[99]!),(words5[128]!,words5[105]!),(words5[139]!,words5[139]!)]
set_option maxRecDepth 20000 in
theorem pcert8 : validRow pm8 pm12 pairs8 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert8 : fastRows pm8 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs9 : List (W×W) := [(words5[90]!,words5[90]!),(words5[99]!,words5[113]!),(words5[113]!,words5[125]!),(words5[125]!,words5[139]!),(words5[139]!,words5[99]!),(words5[141]!,words5[105]!)]
set_option maxRecDepth 20000 in
theorem pcert9 : validRow pm9 pm18 pairs9 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert9 : fastRows pm9 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs48 : List (W×W) := [(words5[90]!,words5[113]!),(words5[99]!,words5[90]!),(words5[113]!,words5[99]!),(words5[116]!,words5[105]!),(words5[125]!,words5[125]!),(words5[139]!,words5[139]!)]
set_option maxRecDepth 20000 in
theorem pcert48 : validRow pm48 pm30 pairs48 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert48 : fastRows pm48 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs50 : List (W×W) := [(words5[90]!,words5[113]!),(words5[99]!,words5[90]!),(words5[113]!,words5[125]!),(words5[125]!,words5[99]!),(words5[130]!,words5[105]!),(words5[139]!,words5[139]!)]
set_option maxRecDepth 20000 in
theorem pcert50 : validRow pm50 pm36 pairs50 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert50 : fastRows pm50 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs51 : List (W×W) := [(words5[90]!,words5[113]!),(words5[99]!,words5[90]!),(words5[113]!,words5[125]!),(words5[125]!,words5[139]!),(words5[139]!,words5[99]!),(words5[144]!,words5[105]!)]
set_option maxRecDepth 20000 in
theorem pcert51 : validRow pm51 pm42 pairs51 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert51 : fastRows pm51 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs61 : List (W×W) := [(words5[90]!,words5[113]!),(words5[99]!,words5[125]!),(words5[113]!,words5[90]!),(words5[125]!,words5[139]!),(words5[139]!,words5[99]!),(words5[148]!,words5[105]!)]
set_option maxRecDepth 20000 in
theorem pcert61 : validRow pm61 pm66 pairs61 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert61 : fastRows pm61 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
def pairs64 : List (W×W) := [(words5[90]!,words5[113]!),(words5[99]!,words5[125]!),(words5[113]!,words5[139]!),(words5[125]!,words5[90]!),(words5[139]!,words5[99]!),(words5[152]!,words5[105]!)]
set_option maxRecDepth 20000 in
theorem pcert64 : validRow pm64 pm90 pairs64 = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem gcert64 : fastRows pm64 goal = goal := by decide +kernel
set_option maxRecDepth 20000 in
theorem sym6_0 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 4 r7.toFinset) : ¬live basicOps t 4 (edges6[0]!).toFinset :=
  relink_checked (source := edges6[0]!) (target := r7) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym4_0 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r5.toFinset) : ¬live basicOps t 5 (edges4[0]!).toFinset :=
  relink_checked (source := edges4[0]!) (target := r5) pcert30 (by decide +kernel) (by decide +kernel) gcert30 ht h
set_option maxRecDepth 20000 in
theorem sym4_5 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r6.toFinset) : ¬live basicOps t 5 (edges4[5]!).toFinset :=
  relink_checked (source := edges4[5]!) (target := r6) pcert55 (by decide +kernel) (by decide +kernel) gcert55 ht h
set_option maxRecDepth 20000 in
theorem sym4_16 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r6.toFinset) : ¬live basicOps t 5 (edges4[16]!).toFinset :=
  relink_checked (source := edges4[16]!) (target := r6) pcert12 (by decide +kernel) (by decide +kernel) gcert12 ht h
set_option maxRecDepth 20000 in
theorem sym8_1 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r6.toFinset) : ¬live basicOps t 5 (edges8[1]!).toFinset :=
  relink_checked (source := edges8[1]!) (target := r6) pcert52 (by decide +kernel) (by decide +kernel) gcert52 ht h
set_option maxRecDepth 20000 in
theorem sym8_2 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r6.toFinset) : ¬live basicOps t 5 (edges8[2]!).toFinset :=
  relink_checked (source := edges8[2]!) (target := r6) pcert49 (by decide +kernel) (by decide +kernel) gcert49 ht h
set_option maxRecDepth 20000 in
theorem sym8_5 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r6.toFinset) : ¬live basicOps t 5 (edges8[5]!).toFinset :=
  relink_checked (source := edges8[5]!) (target := r6) pcert10 (by decide +kernel) (by decide +kernel) gcert10 ht h
set_option maxRecDepth 20000 in
theorem sym8_6 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 5 r6.toFinset) : ¬live basicOps t 5 (edges8[6]!).toFinset :=
  relink_checked (source := edges8[6]!) (target := r6) pcert7 (by decide +kernel) (by decide +kernel) gcert7 ht h
set_option maxRecDepth 20000 in
theorem sym2_1 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r3.toFinset) : ¬live basicOps t 6 (edges2[1]!).toFinset :=
  relink_checked (source := edges2[1]!) (target := r3) pcert60 (by decide +kernel) (by decide +kernel) gcert60 ht h
set_option maxRecDepth 20000 in
theorem sym2_10 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges2[10]!).toFinset :=
  relink_checked (source := edges2[10]!) (target := r4) pcert78 (by decide +kernel) (by decide +kernel) gcert78 ht h
set_option maxRecDepth 20000 in
theorem sym2_16 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges2[16]!).toFinset :=
  relink_checked (source := edges2[16]!) (target := r4) pcert80 (by decide +kernel) (by decide +kernel) gcert80 ht h
set_option maxRecDepth 20000 in
theorem sym2_35 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges2[35]!).toFinset :=
  relink_checked (source := edges2[35]!) (target := r4) pcert18 (by decide +kernel) (by decide +kernel) gcert18 ht h
set_option maxRecDepth 20000 in
theorem sym2_41 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges2[41]!).toFinset :=
  relink_checked (source := edges2[41]!) (target := r4) pcert20 (by decide +kernel) (by decide +kernel) gcert20 ht h
set_option maxRecDepth 20000 in
theorem sym2_60 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r8.toFinset) : ¬live basicOps t 6 (edges2[60]!).toFinset :=
  relink_checked (source := edges2[60]!) (target := r8) pcert60 (by decide +kernel) (by decide +kernel) gcert60 ht h
set_option maxRecDepth 20000 in
theorem sym2_65 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges2[65]!).toFinset :=
  relink_checked (source := edges2[65]!) (target := r9) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym2_71 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges2[71]!).toFinset :=
  relink_checked (source := edges2[71]!) (target := r9) pcert24 (by decide +kernel) (by decide +kernel) gcert24 ht h
set_option maxRecDepth 20000 in
theorem sym2_77 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges2[77]!).toFinset :=
  relink_checked (source := edges2[77]!) (target := r9) pcert2 (by decide +kernel) (by decide +kernel) gcert2 ht h
set_option maxRecDepth 20000 in
theorem sym2_83 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges2[83]!).toFinset :=
  relink_checked (source := edges2[83]!) (target := r9) pcert26 (by decide +kernel) (by decide +kernel) gcert26 ht h
set_option maxRecDepth 20000 in
theorem sym11_14 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges11[14]!).toFinset :=
  relink_checked (source := edges11[14]!) (target := r9) pcert98 (by decide +kernel) (by decide +kernel) gcert98 ht h
set_option maxRecDepth 20000 in
theorem sym11_16 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges11[16]!).toFinset :=
  relink_checked (source := edges11[16]!) (target := r9) pcert99 (by decide +kernel) (by decide +kernel) gcert99 ht h
set_option maxRecDepth 20000 in
theorem sym11_27 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges11[27]!).toFinset :=
  relink_checked (source := edges11[27]!) (target := r9) pcert20 (by decide +kernel) (by decide +kernel) gcert20 ht h
set_option maxRecDepth 20000 in
theorem sym11_29 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r9.toFinset) : ¬live basicOps t 6 (edges11[29]!).toFinset :=
  relink_checked (source := edges11[29]!) (target := r9) pcert21 (by decide +kernel) (by decide +kernel) gcert21 ht h
set_option maxRecDepth 20000 in
theorem sym11_45 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r12.toFinset) : ¬live basicOps t 6 (edges11[45]!).toFinset :=
  relink_checked (source := edges11[45]!) (target := r12) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym11_49 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r12.toFinset) : ¬live basicOps t 6 (edges11[49]!).toFinset :=
  relink_checked (source := edges11[49]!) (target := r12) pcert1 (by decide +kernel) (by decide +kernel) gcert1 ht h
set_option maxRecDepth 20000 in
theorem sym11_55 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r13.toFinset) : ¬live basicOps t 6 (edges11[55]!).toFinset :=
  relink_checked (source := edges11[55]!) (target := r13) pcert4 (by decide +kernel) (by decide +kernel) gcert4 ht h
set_option maxRecDepth 20000 in
theorem sym11_57 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r13.toFinset) : ¬live basicOps t 6 (edges11[57]!).toFinset :=
  relink_checked (source := edges11[57]!) (target := r13) pcert5 (by decide +kernel) (by decide +kernel) gcert5 ht h
set_option maxRecDepth 20000 in
theorem sym14_8 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges14[8]!).toFinset :=
  relink_checked (source := edges14[8]!) (target := r4) pcert76 (by decide +kernel) (by decide +kernel) gcert76 ht h
set_option maxRecDepth 20000 in
theorem sym14_13 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges14[13]!).toFinset :=
  relink_checked (source := edges14[13]!) (target := r4) pcert73 (by decide +kernel) (by decide +kernel) gcert73 ht h
set_option maxRecDepth 20000 in
theorem sym14_21 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r13.toFinset) : ¬live basicOps t 6 (edges14[21]!).toFinset :=
  relink_checked (source := edges14[21]!) (target := r13) pcert108 (by decide +kernel) (by decide +kernel) gcert108 ht h
set_option maxRecDepth 20000 in
theorem sym14_26 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r8.toFinset) : ¬live basicOps t 6 (edges14[26]!).toFinset :=
  relink_checked (source := edges14[26]!) (target := r8) pcert108 (by decide +kernel) (by decide +kernel) gcert108 ht h
set_option maxRecDepth 20000 in
theorem sym14_31 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges14[31]!).toFinset :=
  relink_checked (source := edges14[31]!) (target := r4) pcert16 (by decide +kernel) (by decide +kernel) gcert16 ht h
set_option maxRecDepth 20000 in
theorem sym14_36 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r4.toFinset) : ¬live basicOps t 6 (edges14[36]!).toFinset :=
  relink_checked (source := edges14[36]!) (target := r4) pcert13 (by decide +kernel) (by decide +kernel) gcert13 ht h
set_option maxRecDepth 20000 in
theorem sym14_44 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r13.toFinset) : ¬live basicOps t 6 (edges14[44]!).toFinset :=
  relink_checked (source := edges14[44]!) (target := r13) pcert66 (by decide +kernel) (by decide +kernel) gcert66 ht h
set_option maxRecDepth 20000 in
theorem sym14_49 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r8.toFinset) : ¬live basicOps t 6 (edges14[49]!).toFinset :=
  relink_checked (source := edges14[49]!) (target := r8) pcert66 (by decide +kernel) (by decide +kernel) gcert66 ht h
set_option maxRecDepth 20000 in
theorem sym14_53 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r13.toFinset) : ¬live basicOps t 6 (edges14[53]!).toFinset :=
  relink_checked (source := edges14[53]!) (target := r13) pcert4 (by decide +kernel) (by decide +kernel) gcert4 ht h
set_option maxRecDepth 20000 in
theorem sym14_61 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r13.toFinset) : ¬live basicOps t 6 (edges14[61]!).toFinset :=
  relink_checked (source := edges14[61]!) (target := r13) pcert1 (by decide +kernel) (by decide +kernel) gcert1 ht h
set_option maxRecDepth 20000 in
theorem sym14_91 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r8.toFinset) : ¬live basicOps t 6 (edges14[91]!).toFinset :=
  relink_checked (source := edges14[91]!) (target := r8) pcert4 (by decide +kernel) (by decide +kernel) gcert4 ht h
set_option maxRecDepth 20000 in
theorem sym14_96 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 6 r8.toFinset) : ¬live basicOps t 6 (edges14[96]!).toFinset :=
  relink_checked (source := edges14[96]!) (target := r8) pcert1 (by decide +kernel) (by decide +kernel) gcert1 ht h
set_option maxRecDepth 20000 in
theorem sym1_14 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r2.toFinset) : ¬live basicOps t 7 (edges1[14]!).toFinset :=
  relink_checked (source := edges1[14]!) (target := r2) pcert96 (by decide +kernel) (by decide +kernel) gcert96 ht h
set_option maxRecDepth 20000 in
theorem sym1_20 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r2.toFinset) : ¬live basicOps t 7 (edges1[20]!).toFinset :=
  relink_checked (source := edges1[20]!) (target := r2) pcert98 (by decide +kernel) (by decide +kernel) gcert98 ht h
set_option maxRecDepth 20000 in
theorem sym1_26 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r2.toFinset) : ¬live basicOps t 7 (edges1[26]!).toFinset :=
  relink_checked (source := edges1[26]!) (target := r2) pcert99 (by decide +kernel) (by decide +kernel) gcert99 ht h
set_option maxRecDepth 20000 in
theorem sym1_37 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r2.toFinset) : ¬live basicOps t 7 (edges1[37]!).toFinset :=
  relink_checked (source := edges1[37]!) (target := r2) pcert18 (by decide +kernel) (by decide +kernel) gcert18 ht h
set_option maxRecDepth 20000 in
theorem sym1_43 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r2.toFinset) : ¬live basicOps t 7 (edges1[43]!).toFinset :=
  relink_checked (source := edges1[43]!) (target := r2) pcert20 (by decide +kernel) (by decide +kernel) gcert20 ht h
set_option maxRecDepth 20000 in
theorem sym1_49 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r2.toFinset) : ¬live basicOps t 7 (edges1[49]!).toFinset :=
  relink_checked (source := edges1[49]!) (target := r2) pcert21 (by decide +kernel) (by decide +kernel) gcert21 ht h
set_option maxRecDepth 20000 in
theorem sym1_56 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r10.toFinset) : ¬live basicOps t 7 (edges1[56]!).toFinset :=
  relink_checked (source := edges1[56]!) (target := r10) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym1_57 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r11.toFinset) : ¬live basicOps t 7 (edges1[57]!).toFinset :=
  relink_checked (source := edges1[57]!) (target := r11) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym1_64 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r10.toFinset) : ¬live basicOps t 7 (edges1[64]!).toFinset :=
  relink_checked (source := edges1[64]!) (target := r10) pcert2 (by decide +kernel) (by decide +kernel) gcert2 ht h
set_option maxRecDepth 20000 in
theorem sym1_65 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r11.toFinset) : ¬live basicOps t 7 (edges1[65]!).toFinset :=
  relink_checked (source := edges1[65]!) (target := r11) pcert2 (by decide +kernel) (by decide +kernel) gcert2 ht h
set_option maxRecDepth 20000 in
theorem sym1_72 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r10.toFinset) : ¬live basicOps t 7 (edges1[72]!).toFinset :=
  relink_checked (source := edges1[72]!) (target := r10) pcert3 (by decide +kernel) (by decide +kernel) gcert3 ht h
set_option maxRecDepth 20000 in
theorem sym1_73 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r11.toFinset) : ¬live basicOps t 7 (edges1[73]!).toFinset :=
  relink_checked (source := edges1[73]!) (target := r11) pcert3 (by decide +kernel) (by decide +kernel) gcert3 ht h
set_option maxRecDepth 20000 in
theorem sym1_79 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r14.toFinset) : ¬live basicOps t 7 (edges1[79]!).toFinset :=
  relink_checked (source := edges1[79]!) (target := r14) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym1_83 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r14.toFinset) : ¬live basicOps t 7 (edges1[83]!).toFinset :=
  relink_checked (source := edges1[83]!) (target := r14) pcert1 (by decide +kernel) (by decide +kernel) gcert1 ht h
set_option maxRecDepth 20000 in
theorem sym1_87 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 7 r14.toFinset) : ¬live basicOps t 7 (edges1[87]!).toFinset :=
  relink_checked (source := edges1[87]!) (target := r14) pcert4 (by decide +kernel) (by decide +kernel) gcert4 ht h
set_option maxRecDepth 20000 in
theorem sym0_1 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[1]!).toFinset :=
  relink_checked (source := edges0[1]!) (target := r1) pcert0 (by decide +kernel) (by decide +kernel) gcert0 ht h
set_option maxRecDepth 20000 in
theorem sym0_5 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[5]!).toFinset :=
  relink_checked (source := edges0[5]!) (target := r1) pcert6 (by decide +kernel) (by decide +kernel) gcert6 ht h
set_option maxRecDepth 20000 in
theorem sym0_9 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[9]!).toFinset :=
  relink_checked (source := edges0[9]!) (target := r1) pcert8 (by decide +kernel) (by decide +kernel) gcert8 ht h
set_option maxRecDepth 20000 in
theorem sym0_13 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[13]!).toFinset :=
  relink_checked (source := edges0[13]!) (target := r1) pcert9 (by decide +kernel) (by decide +kernel) gcert9 ht h
set_option maxRecDepth 20000 in
theorem sym0_17 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[17]!).toFinset :=
  relink_checked (source := edges0[17]!) (target := r1) pcert48 (by decide +kernel) (by decide +kernel) gcert48 ht h
set_option maxRecDepth 20000 in
theorem sym0_21 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[21]!).toFinset :=
  relink_checked (source := edges0[21]!) (target := r1) pcert50 (by decide +kernel) (by decide +kernel) gcert50 ht h
set_option maxRecDepth 20000 in
theorem sym0_25 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[25]!).toFinset :=
  relink_checked (source := edges0[25]!) (target := r1) pcert51 (by decide +kernel) (by decide +kernel) gcert51 ht h
set_option maxRecDepth 20000 in
theorem sym0_29 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[29]!).toFinset :=
  relink_checked (source := edges0[29]!) (target := r1) pcert60 (by decide +kernel) (by decide +kernel) gcert60 ht h
set_option maxRecDepth 20000 in
theorem sym0_33 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[33]!).toFinset :=
  relink_checked (source := edges0[33]!) (target := r1) pcert61 (by decide +kernel) (by decide +kernel) gcert61 ht h
set_option maxRecDepth 20000 in
theorem sym0_37 {t : W} (ht : t = goal ∨ t = ~~~goal)
    (h : ¬live basicOps t 8 r1.toFinset) : ¬live basicOps t 8 (edges0[37]!).toFinset :=
  relink_checked (source := edges0[37]!) (target := r1) pcert64 (by decide +kernel) (by decide +kernel) gcert64 ht h
end K5Cache

namespace K5Cache
open GThreshold

theorem by_rows_sized {t : W} (tg : t = goal ∨ t = ~~~goal) (k : Nat) (ws : List W)
    (nd : ws.Nodup) (neq : ws.toFinset ≠ {goal} ∧ ws.toFinset ≠ {~~~goal})
    (edges : Array (List W)) (same : follows k ws = edges.toList)
    (n : Nat) (hs : edges.size = n)
    (blocked : ∀ j : Fin n, ¬live basicOps t k edges[j.val]!.toFinset) :
    ¬live basicOps t (k+1) ws.toFinset := by
  apply by_rows tg k ws nd neq edges same
  intro e
  exact blocked ⟨e.val, hs ▸ e.isLt⟩

set_option maxRecDepth 16000 in
theorem block7 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 4 r7.toFinset := by
  apply by_rows_sized h 3 r7 (by decide +kernel) (by decide +kernel) edges7 follow7 0 (by decide +kernel)
  intro e
  fin_cases e
set_option maxRecDepth 16000 in
theorem block5 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 r5.toFinset := by
  apply by_rows_sized h 4 r5 (by decide +kernel) (by decide +kernel) edges5 follow5 18 (by decide +kernel)
  intro e
  fin_cases e
  · exact n5_0 h a
  · exact n5_1 h a
  · exact n5_2 h a
  · exact n5_3 h a
  · exact n5_4 h a
  · exact n5_5 h a
  · exact n5_6 h a
  · exact n5_7 h a
  · exact n5_8 h a
  · exact n5_9 h a
  · exact n5_10 h a
  · exact n5_11 h a
  · exact n5_12 h a
  · exact n5_13 h a
  · exact n5_14 h a
  · exact n5_15 h a
  · exact n5_16 h a
  · exact n5_17 h a
set_option maxRecDepth 16000 in
theorem block6 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 5 r6.toFinset := by
  apply by_rows_sized h 4 r6 (by decide +kernel) (by decide +kernel) edges6 follow6 6 (by decide +kernel)
  intro e
  fin_cases e
  · exact sym6_0 h (block7 h a)
  · exact n6_1 h a
  · exact n6_2 h a
  · exact n6_3 h a
  · exact n6_4 h a
  · exact n6_5 h a
set_option maxRecDepth 16000 in
theorem block3 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 r3.toFinset := by
  apply by_rows_sized h 5 r3 (by decide +kernel) (by decide +kernel) edges3 follow3 67 (by decide +kernel)
  intro e
  fin_cases e
  · exact n3_0 h a
  · exact n3_1 h a
  · exact n3_2 h a
  · exact n3_3 h a
  · exact n3_4 h a
  · exact n3_5 h a
  · exact n3_6 h a
  · exact n3_7 h a
  · exact n3_8 h a
  · exact n3_9 h a
  · exact n3_10 h a
  · exact n3_11 h a
  · exact n3_12 h a
  · exact n3_13 h a
  · exact n3_14 h a
  · exact n3_15 h a
  · exact n3_16 h a
  · exact n3_17 h a
  · exact n3_18 h a
  · exact n3_19 h a
  · exact n3_20 h a
  · exact n3_21 h a
  · exact n3_22 h a
  · exact n3_23 h a
  · exact n3_24 h a
  · exact n3_25 h a
  · exact n3_26 h a
  · exact n3_27 h a
  · exact n3_28 h a
  · exact n3_29 h a
  · exact n3_30 h a
  · exact n3_31 h a
  · exact n3_32 h a
  · exact n3_33 h a
  · exact n3_34 h a
  · exact n3_35 h a
  · exact n3_36 h a
  · exact n3_37 h a
  · exact n3_38 h a
  · exact n3_39 h a
  · exact n3_40 h a
  · exact n3_41 h a
  · exact n3_42 h a
  · exact n3_43 h a
  · exact n3_44 h a
  · exact n3_45 h a
  · exact n3_46 h a
  · exact n3_47 h a
  · exact n3_48 h a
  · exact n3_49 h a
  · exact n3_50 h a
  · exact n3_51 h a
  · exact n3_52 h a
  · exact n3_53 h a
  · exact n3_54 h a
  · exact n3_55 h a
  · exact n3_56 h a
  · exact n3_57 h a
  · exact n3_58 h a
  · exact n3_59 h a
  · exact n3_60 h a
  · exact n3_61 h a
  · exact n3_62 h a
  · exact n3_63 h a
  · exact n3_64 h a
  · exact n3_65 h a
  · exact n3_66 h a
set_option maxRecDepth 16000 in
theorem block4 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 r4.toFinset := by
  apply by_rows_sized h 5 r4 (by decide +kernel) (by decide +kernel) edges4 follow4 42 (by decide +kernel)
  intro e
  fin_cases e
  · exact sym4_0 h (block5 h a)
  · exact n4_1 h a
  · exact n4_2 h a
  · exact n4_3 h a
  · exact n4_4 h a
  · exact sym4_5 h (block6 h a)
  · exact n4_6 h a
  · exact n4_7 h a
  · exact n4_8 h a
  · exact n4_9 h a
  · exact n4_10 h a
  · exact n4_11 h a
  · exact n4_12 h a
  · exact n4_13 h a
  · exact n4_14 h a
  · exact n4_15 h a
  · exact sym4_16 h (block6 h a)
  · exact n4_17 h a
  · exact n4_18 h a
  · exact n4_19 h a
  · exact n4_20 h a
  · exact n4_21 h a
  · exact n4_22 h a
  · exact n4_23 h a
  · exact n4_24 h a
  · exact n4_25 h a
  · exact n4_26 h a
  · exact n4_27 h a
  · exact n4_28 h a
  · exact n4_29 h a
  · exact n4_30 h a
  · exact n4_31 h a
  · exact n4_32 h a
  · exact n4_33 h a
  · exact n4_34 h a
  · exact n4_35 h a
  · exact n4_36 h a
  · exact n4_37 h a
  · exact n4_38 h a
  · exact n4_39 h a
  · exact n4_40 h a
  · exact n4_41 h a
set_option maxRecDepth 16000 in
theorem block8 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 r8.toFinset := by
  apply by_rows_sized h 5 r8 (by decide +kernel) (by decide +kernel) edges8 follow8 21 (by decide +kernel)
  intro e
  fin_cases e
  · exact n8_0 h a
  · exact sym8_1 h (block6 h a)
  · exact sym8_2 h (block6 h a)
  · exact n8_3 h a
  · exact n8_4 h a
  · exact sym8_5 h (block6 h a)
  · exact sym8_6 h (block6 h a)
  · exact n8_7 h a
  · exact n8_8 h a
  · exact n8_9 h a
  · exact n8_10 h a
  · exact n8_11 h a
  · exact n8_12 h a
  · exact n8_13 h a
  · exact n8_14 h a
  · exact n8_15 h a
  · exact n8_16 h a
  · exact n8_17 h a
  · exact n8_18 h a
  · exact n8_19 h a
  · exact n8_20 h a
set_option maxRecDepth 16000 in
theorem block9 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 r9.toFinset := by
  apply by_rows_sized h 5 r9 (by decide +kernel) (by decide +kernel) edges9 follow9 13 (by decide +kernel)
  intro e
  fin_cases e
  · exact n9_0 h a
  · exact n9_1 h a
  · exact n9_2 h a
  · exact n9_3 h a
  · exact n9_4 h a
  · exact n9_5 h a
  · exact n9_6 h a
  · exact n9_7 h a
  · exact n9_8 h a
  · exact n9_9 h a
  · exact n9_10 h a
  · exact n9_11 h a
  · exact n9_12 h a
set_option maxRecDepth 16000 in
theorem block12 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 r12.toFinset := by
  apply by_rows_sized h 5 r12 (by decide +kernel) (by decide +kernel) edges12 follow12 10 (by decide +kernel)
  intro e
  fin_cases e
  · exact n12_0 h a
  · exact n12_1 h a
  · exact n12_2 h a
  · exact n12_3 h a
  · exact n12_4 h a
  · exact n12_5 h a
  · exact n12_6 h a
  · exact n12_7 h a
  · exact n12_8 h a
  · exact n12_9 h a
set_option maxRecDepth 16000 in
theorem block13 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 6 r13.toFinset := by
  apply by_rows_sized h 5 r13 (by decide +kernel) (by decide +kernel) edges13 follow13 12 (by decide +kernel)
  intro e
  fin_cases e
  · exact n13_0 h a
  · exact n13_1 h a
  · exact n13_2 h a
  · exact n13_3 h a
  · exact n13_4 h a
  · exact n13_5 h a
  · exact n13_6 h a
  · exact n13_7 h a
  · exact n13_8 h a
  · exact n13_9 h a
  · exact n13_10 h a
  · exact n13_11 h a
set_option maxRecDepth 16000 in
theorem block2 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 r2.toFinset := by
  apply by_rows_sized h 6 r2 (by decide +kernel) (by decide +kernel) edges2 follow2 96 (by decide +kernel)
  intro e
  fin_cases e
  · exact n2_0 h a
  · exact sym2_1 h (block3 h a)
  · exact n2_2 h a
  · exact n2_3 h a
  · exact n2_4 h a
  · exact n2_5 h a
  · exact n2_6 h a
  · exact n2_7 h a
  · exact n2_8 h a
  · exact n2_9 h a
  · exact sym2_10 h (block4 h a)
  · exact n2_11 h a
  · exact n2_12 h a
  · exact n2_13 h a
  · exact n2_14 h a
  · exact n2_15 h a
  · exact sym2_16 h (block4 h a)
  · exact n2_17 h a
  · exact n2_18 h a
  · exact n2_19 h a
  · exact n2_20 h a
  · exact n2_21 h a
  · exact n2_22 h a
  · exact n2_23 h a
  · exact n2_24 h a
  · exact n2_25 h a
  · exact n2_26 h a
  · exact n2_27 h a
  · exact n2_28 h a
  · exact n2_29 h a
  · exact n2_30 h a
  · exact n2_31 h a
  · exact n2_32 h a
  · exact n2_33 h a
  · exact n2_34 h a
  · exact sym2_35 h (block4 h a)
  · exact n2_36 h a
  · exact n2_37 h a
  · exact n2_38 h a
  · exact n2_39 h a
  · exact n2_40 h a
  · exact sym2_41 h (block4 h a)
  · exact n2_42 h a
  · exact n2_43 h a
  · exact n2_44 h a
  · exact n2_45 h a
  · exact n2_46 h a
  · exact n2_47 h a
  · exact n2_48 h a
  · exact n2_49 h a
  · exact n2_50 h a
  · exact n2_51 h a
  · exact n2_52 h a
  · exact n2_53 h a
  · exact n2_54 h a
  · exact n2_55 h a
  · exact n2_56 h a
  · exact n2_57 h a
  · exact n2_58 h a
  · exact n2_59 h a
  · exact sym2_60 h (block8 h a)
  · exact n2_61 h a
  · exact n2_62 h a
  · exact n2_63 h a
  · exact n2_64 h a
  · exact sym2_65 h (block9 h a)
  · exact n2_66 h a
  · exact n2_67 h a
  · exact n2_68 h a
  · exact n2_69 h a
  · exact n2_70 h a
  · exact sym2_71 h (block9 h a)
  · exact n2_72 h a
  · exact n2_73 h a
  · exact n2_74 h a
  · exact n2_75 h a
  · exact n2_76 h a
  · exact sym2_77 h (block9 h a)
  · exact n2_78 h a
  · exact n2_79 h a
  · exact n2_80 h a
  · exact n2_81 h a
  · exact n2_82 h a
  · exact sym2_83 h (block9 h a)
  · exact n2_84 h a
  · exact n2_85 h a
  · exact n2_86 h a
  · exact n2_87 h a
  · exact n2_88 h a
  · exact n2_89 h a
  · exact n2_90 h a
  · exact n2_91 h a
  · exact n2_92 h a
  · exact n2_93 h a
  · exact n2_94 h a
  · exact n2_95 h a
set_option maxRecDepth 16000 in
theorem block10 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 r10.toFinset := by
  apply by_rows_sized h 6 r10 (by decide +kernel) (by decide +kernel) edges10 follow10 83 (by decide +kernel)
  intro e
  fin_cases e
  · exact n10_0 h a
  · exact n10_1 h a
  · exact n10_2 h a
  · exact n10_3 h a
  · exact n10_4 h a
  · exact n10_5 h a
  · exact n10_6 h a
  · exact n10_7 h a
  · exact n10_8 h a
  · exact n10_9 h a
  · exact n10_10 h a
  · exact n10_11 h a
  · exact n10_12 h a
  · exact n10_13 h a
  · exact n10_14 h a
  · exact n10_15 h a
  · exact n10_16 h a
  · exact n10_17 h a
  · exact n10_18 h a
  · exact n10_19 h a
  · exact n10_20 h a
  · exact n10_21 h a
  · exact n10_22 h a
  · exact n10_23 h a
  · exact n10_24 h a
  · exact n10_25 h a
  · exact n10_26 h a
  · exact n10_27 h a
  · exact n10_28 h a
  · exact n10_29 h a
  · exact n10_30 h a
  · exact n10_31 h a
  · exact n10_32 h a
  · exact n10_33 h a
  · exact n10_34 h a
  · exact n10_35 h a
  · exact n10_36 h a
  · exact n10_37 h a
  · exact n10_38 h a
  · exact n10_39 h a
  · exact n10_40 h a
  · exact n10_41 h a
  · exact n10_42 h a
  · exact n10_43 h a
  · exact n10_44 h a
  · exact n10_45 h a
  · exact n10_46 h a
  · exact n10_47 h a
  · exact n10_48 h a
  · exact n10_49 h a
  · exact n10_50 h a
  · exact n10_51 h a
  · exact n10_52 h a
  · exact n10_53 h a
  · exact n10_54 h a
  · exact n10_55 h a
  · exact n10_56 h a
  · exact n10_57 h a
  · exact n10_58 h a
  · exact n10_59 h a
  · exact n10_60 h a
  · exact n10_61 h a
  · exact n10_62 h a
  · exact n10_63 h a
  · exact n10_64 h a
  · exact n10_65 h a
  · exact n10_66 h a
  · exact n10_67 h a
  · exact n10_68 h a
  · exact n10_69 h a
  · exact n10_70 h a
  · exact n10_71 h a
  · exact n10_72 h a
  · exact n10_73 h a
  · exact n10_74 h a
  · exact n10_75 h a
  · exact n10_76 h a
  · exact n10_77 h a
  · exact n10_78 h a
  · exact n10_79 h a
  · exact n10_80 h a
  · exact n10_81 h a
  · exact n10_82 h a
set_option maxRecDepth 16000 in
theorem block11 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 r11.toFinset := by
  apply by_rows_sized h 6 r11 (by decide +kernel) (by decide +kernel) edges11 follow11 67 (by decide +kernel)
  intro e
  fin_cases e
  · exact n11_0 h a
  · exact n11_1 h a
  · exact n11_2 h a
  · exact n11_3 h a
  · exact n11_4 h a
  · exact n11_5 h a
  · exact n11_6 h a
  · exact n11_7 h a
  · exact n11_8 h a
  · exact n11_9 h a
  · exact n11_10 h a
  · exact n11_11 h a
  · exact n11_12 h a
  · exact n11_13 h a
  · exact sym11_14 h (block9 h a)
  · exact n11_15 h a
  · exact sym11_16 h (block9 h a)
  · exact n11_17 h a
  · exact n11_18 h a
  · exact n11_19 h a
  · exact n11_20 h a
  · exact n11_21 h a
  · exact n11_22 h a
  · exact n11_23 h a
  · exact n11_24 h a
  · exact n11_25 h a
  · exact n11_26 h a
  · exact sym11_27 h (block9 h a)
  · exact n11_28 h a
  · exact sym11_29 h (block9 h a)
  · exact n11_30 h a
  · exact n11_31 h a
  · exact n11_32 h a
  · exact n11_33 h a
  · exact n11_34 h a
  · exact n11_35 h a
  · exact n11_36 h a
  · exact n11_37 h a
  · exact n11_38 h a
  · exact n11_39 h a
  · exact n11_40 h a
  · exact n11_41 h a
  · exact n11_42 h a
  · exact n11_43 h a
  · exact n11_44 h a
  · exact sym11_45 h (block12 h a)
  · exact n11_46 h a
  · exact n11_47 h a
  · exact n11_48 h a
  · exact sym11_49 h (block12 h a)
  · exact n11_50 h a
  · exact n11_51 h a
  · exact n11_52 h a
  · exact n11_53 h a
  · exact n11_54 h a
  · exact sym11_55 h (block13 h a)
  · exact n11_56 h a
  · exact sym11_57 h (block13 h a)
  · exact n11_58 h a
  · exact n11_59 h a
  · exact n11_60 h a
  · exact n11_61 h a
  · exact n11_62 h a
  · exact n11_63 h a
  · exact n11_64 h a
  · exact n11_65 h a
  · exact n11_66 h a
set_option maxRecDepth 16000 in
theorem block14 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 7 r14.toFinset := by
  apply by_rows_sized h 6 r14 (by decide +kernel) (by decide +kernel) edges14 follow14 102 (by decide +kernel)
  intro e
  fin_cases e
  · exact n14_0 h a
  · exact n14_1 h a
  · exact n14_2 h a
  · exact n14_3 h a
  · exact n14_4 h a
  · exact n14_5 h a
  · exact n14_6 h a
  · exact n14_7 h a
  · exact sym14_8 h (block4 h a)
  · exact n14_9 h a
  · exact n14_10 h a
  · exact n14_11 h a
  · exact n14_12 h a
  · exact sym14_13 h (block4 h a)
  · exact n14_14 h a
  · exact n14_15 h a
  · exact n14_16 h a
  · exact n14_17 h a
  · exact n14_18 h a
  · exact n14_19 h a
  · exact n14_20 h a
  · exact sym14_21 h (block13 h a)
  · exact n14_22 h a
  · exact n14_23 h a
  · exact n14_24 h a
  · exact n14_25 h a
  · exact sym14_26 h (block8 h a)
  · exact n14_27 h a
  · exact n14_28 h a
  · exact n14_29 h a
  · exact n14_30 h a
  · exact sym14_31 h (block4 h a)
  · exact n14_32 h a
  · exact n14_33 h a
  · exact n14_34 h a
  · exact n14_35 h a
  · exact sym14_36 h (block4 h a)
  · exact n14_37 h a
  · exact n14_38 h a
  · exact n14_39 h a
  · exact n14_40 h a
  · exact n14_41 h a
  · exact n14_42 h a
  · exact n14_43 h a
  · exact sym14_44 h (block13 h a)
  · exact n14_45 h a
  · exact n14_46 h a
  · exact n14_47 h a
  · exact n14_48 h a
  · exact sym14_49 h (block8 h a)
  · exact n14_50 h a
  · exact n14_51 h a
  · exact n14_52 h a
  · exact sym14_53 h (block13 h a)
  · exact n14_54 h a
  · exact n14_55 h a
  · exact n14_56 h a
  · exact n14_57 h a
  · exact n14_58 h a
  · exact n14_59 h a
  · exact n14_60 h a
  · exact sym14_61 h (block13 h a)
  · exact n14_62 h a
  · exact n14_63 h a
  · exact n14_64 h a
  · exact n14_65 h a
  · exact n14_66 h a
  · exact n14_67 h a
  · exact n14_68 h a
  · exact n14_69 h a
  · exact n14_70 h a
  · exact n14_71 h a
  · exact n14_72 h a
  · exact n14_73 h a
  · exact n14_74 h a
  · exact n14_75 h a
  · exact n14_76 h a
  · exact n14_77 h a
  · exact n14_78 h a
  · exact n14_79 h a
  · exact n14_80 h a
  · exact n14_81 h a
  · exact n14_82 h a
  · exact n14_83 h a
  · exact n14_84 h a
  · exact n14_85 h a
  · exact n14_86 h a
  · exact n14_87 h a
  · exact n14_88 h a
  · exact n14_89 h a
  · exact n14_90 h a
  · exact sym14_91 h (block8 h a)
  · exact n14_92 h a
  · exact n14_93 h a
  · exact n14_94 h a
  · exact n14_95 h a
  · exact sym14_96 h (block8 h a)
  · exact n14_97 h a
  · exact n14_98 h a
  · exact n14_99 h a
  · exact n14_100 h a
  · exact n14_101 h a
set_option maxRecDepth 16000 in
theorem block1 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 8 r1.toFinset := by
  apply by_rows_sized h 7 r1 (by decide +kernel) (by decide +kernel) edges1 follow1 90 (by decide +kernel)
  intro e
  fin_cases e
  · exact n1_0 h a
  · exact n1_1 h a
  · exact n1_2 h a
  · exact n1_3 h a
  · exact n1_4 h a
  · exact n1_5 h a
  · exact n1_6 h a
  · exact n1_7 h a
  · exact n1_8 h a
  · exact n1_9 h a
  · exact n1_10 h a
  · exact n1_11 h a
  · exact n1_12 h a
  · exact n1_13 h a
  · exact sym1_14 h (block2 h a)
  · exact n1_15 h a
  · exact n1_16 h a
  · exact n1_17 h a
  · exact n1_18 h a
  · exact n1_19 h a
  · exact sym1_20 h (block2 h a)
  · exact n1_21 h a
  · exact n1_22 h a
  · exact n1_23 h a
  · exact n1_24 h a
  · exact n1_25 h a
  · exact sym1_26 h (block2 h a)
  · exact n1_27 h a
  · exact n1_28 h a
  · exact n1_29 h a
  · exact n1_30 h a
  · exact n1_31 h a
  · exact n1_32 h a
  · exact n1_33 h a
  · exact n1_34 h a
  · exact n1_35 h a
  · exact n1_36 h a
  · exact sym1_37 h (block2 h a)
  · exact n1_38 h a
  · exact n1_39 h a
  · exact n1_40 h a
  · exact n1_41 h a
  · exact n1_42 h a
  · exact sym1_43 h (block2 h a)
  · exact n1_44 h a
  · exact n1_45 h a
  · exact n1_46 h a
  · exact n1_47 h a
  · exact n1_48 h a
  · exact sym1_49 h (block2 h a)
  · exact n1_50 h a
  · exact n1_51 h a
  · exact n1_52 h a
  · exact n1_53 h a
  · exact n1_54 h a
  · exact n1_55 h a
  · exact sym1_56 h (block10 h a)
  · exact sym1_57 h (block11 h a)
  · exact n1_58 h a
  · exact n1_59 h a
  · exact n1_60 h a
  · exact n1_61 h a
  · exact n1_62 h a
  · exact n1_63 h a
  · exact sym1_64 h (block10 h a)
  · exact sym1_65 h (block11 h a)
  · exact n1_66 h a
  · exact n1_67 h a
  · exact n1_68 h a
  · exact n1_69 h a
  · exact n1_70 h a
  · exact n1_71 h a
  · exact sym1_72 h (block10 h a)
  · exact sym1_73 h (block11 h a)
  · exact n1_74 h a
  · exact n1_75 h a
  · exact n1_76 h a
  · exact n1_77 h a
  · exact n1_78 h a
  · exact sym1_79 h (block14 h a)
  · exact n1_80 h a
  · exact n1_81 h a
  · exact n1_82 h a
  · exact sym1_83 h (block14 h a)
  · exact n1_84 h a
  · exact n1_85 h a
  · exact n1_86 h a
  · exact sym1_87 h (block14 h a)
  · exact n1_88 h a
  · exact n1_89 h a
set_option maxRecDepth 16000 in
theorem block0 {t : W} (h : t = goal ∨ t = ~~~goal) (a : Oracle) : ¬live basicOps t 9 r0.toFinset := by
  apply by_rows_sized h 8 r0 (by decide +kernel) (by decide +kernel) edges0 follow0 40 (by decide +kernel)
  intro e
  fin_cases e
  · exact n0_0 h a
  · exact sym0_1 h (block1 h a)
  · exact n0_2 h a
  · exact n0_3 h a
  · exact n0_4 h a
  · exact sym0_5 h (block1 h a)
  · exact n0_6 h a
  · exact n0_7 h a
  · exact n0_8 h a
  · exact sym0_9 h (block1 h a)
  · exact n0_10 h a
  · exact n0_11 h a
  · exact n0_12 h a
  · exact sym0_13 h (block1 h a)
  · exact n0_14 h a
  · exact n0_15 h a
  · exact n0_16 h a
  · exact sym0_17 h (block1 h a)
  · exact n0_18 h a
  · exact n0_19 h a
  · exact n0_20 h a
  · exact sym0_21 h (block1 h a)
  · exact n0_22 h a
  · exact n0_23 h a
  · exact n0_24 h a
  · exact sym0_25 h (block1 h a)
  · exact n0_26 h a
  · exact n0_27 h a
  · exact n0_28 h a
  · exact sym0_29 h (block1 h a)
  · exact n0_30 h a
  · exact n0_31 h a
  · exact n0_32 h a
  · exact sym0_33 h (block1 h a)
  · exact n0_34 h a
  · exact n0_35 h a
  · exact n0_36 h a
  · exact sym0_37 h (block1 h a)
  · exact n0_38 h a
  · exact n0_39 h a
end K5Cache

namespace K5Cache
open GThreshold

def witnessIdx (i : Fin 5) : Fin 256 := ([2, 1, 7, 25, 67] : List (Fin 256)).get i

theorem every_wire : ∀ i q : Fin 5, differs (witnessIdx i) (vinput q) → i = q := by
  unfold differs
  decide +kernel

theorem impossible_nine {t : W} (ht : t = goal ∨ t = ~~~goal)
    (b : build basicOps t 9 ins_fffefee8.toFinset) : False := by
  obtain ⟨s,sub,path⟩ := compress b
  have all : s = ins_fffefee8.toFinset := by
    apply Finset.Subset.antisymm sub
    intro v hv
    obtain ⟨i,rfl⟩ := input_index _ (List.mem_toFinset.mp hv)
    let r := witnessIdx i
    have hd : differs r t := by
      rcases ht with rfl|rfl
      · exact (goal_changes r).1
      · exact (goal_changes r).2
    obtain ⟨w,ws,diff⟩ := live_separates (differs r) hd (ops_differs r) path
    obtain ⟨j,rfl⟩ := input_index _ (List.mem_toFinset.mp (sub ws))
    exact (every_wire i j diff).symm ▸ ws
  rw [all] at path
  exact block0 ht verifiedOracle path

end K5Cache
namespace GThreshold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def sampleBit (k : Fin 512) (z : W) : Bool := z[k.val]
private def sampleStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem tenBinary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = table x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins_fffefee8, holds ins_fffefee8.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl sampleStep (ins_fffefee8.map (sampleBit k))).getD o false = sampleBit k goal := by
    have same : List.ofFn (fun i : Fin 5 => sampleBit k (ins_fffefee8.getD i.val 0)) =
        ins_fffefee8.map (sampleBit k) := by
      apply List.ext_getElem (by simp [ins_fffefee8])
      intro i hi hj
      have hlt : i < ins_fffefee8.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins_fffefee8.map (sampleBit k)) = sampleBit k goal
    rw [← same, he]
    exact spec_fffefee8 k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins_fffefee8 ins_fffefee8.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins_fffefee8.toFinset) :
      build basicOps t b ins_fffefee8.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact K5Cache.impossible_nine ht (lift low run)

end GThreshold

namespace Finish
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SevenTrack
open GThreshold
theorem base (bound : ∀ gs o, (∀ g ∈ gs, legal g) →
    (∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = table x) → 9 < binaryCost gs)
    (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = GraphPin.clique x) : 10 ≤ BinaryPin.bc C.gates := by
  have eq : ∀ x, GraphPin.clique x = GThreshold.table x := by decide +kernel
  have lb := bound C.gates C.output hg (fun x => (he x).trans (eq x))
  have count (gs : List Gate) : binaryCost gs + (gs.filter ntag).length = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases g with
      | mk op ins => cases op <;> simp [binaryCost,isBinary,ntag,List.filter_cons] at * <;> omega
  have h := count C.gates
  unfold BinaryPin.bc
  omega
end Finish
end PEqualNP.Outside.L_meta_10570_aux

open PEqualNP.Outside.L_meta_10570_aux in
theorem PEqualNP.Outside.L_meta_10570 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  GraphPin.replacement (Finish.base GThreshold.tenBinary)
