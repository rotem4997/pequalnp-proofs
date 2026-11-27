import Mathlib
import PEqualNP.Defs

-- The lemmas from run to build are copied from the merged file L_meta_4342 of this project.
-- The lemmas from scan to wireVal_mono are copied from the merged file L_meta_2970.

namespace PEqualNP.Outside.L_meta_6734

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

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



def AO (n : ℕ) (ds : List Gate) : Prop :=
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < n + j

def Rep (n : ℕ) (ds : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c, ∀ y, f y = c) ∨
    ∃ k < n + ds.length, ∀ y, f y = (run ds (List.ofFn y)).getD k false

theorem rep_app (n : ℕ) (ds : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool)
    (h : Rep n ds f) : Rep n (ds ++ [g]) f := by
  rcases h with h | ⟨k, hk, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
    rw [h y, run_prefix _ _ _ _ (by simpa using hk)]

theorem rep_two (n : ℕ) (ds : List Gate) (hds : AO n ds) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (u v : (Fin n → Bool) → Bool)
    (hu : Rep n ds u) (hv : Rep n ds v) :
    ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
  have triv : ∀ w : (Fin n → Bool) → Bool, Rep n ds w → (∀ y, o.eval [u y, v y] = w y) →
      ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
    intro w hw e
    refine ⟨[], by simp, by simpa using hds, ?_⟩
    rw [List.append_nil, show (fun y => o.eval [u y, v y]) = w from funext e]
    exact hw
  have cst : ∀ c : Bool, Rep n ds fun _ => c := fun c => Or.inl ⟨c, fun _ => rfl⟩
  rcases hu with ⟨c, hc⟩ | ⟨a, ha, hua⟩
  · rcases ho with rfl | rfl <;> cases c
    · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
  · rcases hv with ⟨c, hc⟩ | ⟨b, hb, hvb⟩
    · have hu : Rep n ds u := Or.inr ⟨a, ha, hua⟩
      rcases ho with rfl | rfl <;> cases c
      · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
    · refine ⟨[⟨o, [a, b]⟩], by simp, ⟨?_, ?_⟩, Or.inr ⟨n + ds.length, by simp, fun y => ?_⟩⟩
      · intro g hg
        rcases List.mem_append.1 hg with h | h
        · exact hds.1 g h
        · rw [List.mem_singleton.1 h]; exact ⟨ho, rfl⟩
      · intro j hj i hi
        by_cases h : j < ds.length
        · rw [List.getElem_append_left h] at hi
          exact hds.2 j h i hi
        · have hj' : j = ds.length := by simp at hj; omega
          subst hj'
          simp at hi
          rcases hi with rfl | rfl <;> assumption
      · rw [run_snoc, show n + ds.length = (run ds (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
        simp [hua, hvb]

theorem build (n : ℕ) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ ds : List Gate, AO n ds ∧ ds.length ≤ gs.length ∧
      ∀ w, Rep n ds fun y => (run gs (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], ⟨by simp, by simp⟩, le_rfl, fun w => ?_⟩
    by_cases hw : w < n
    · exact Or.inr ⟨w, by simpa using hw, fun y => rfl⟩
    · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by simp [run]; omega)⟩
  | append_singleton gs g ih =>
    obtain ⟨ds, h1, h2, h3⟩ := ih fun g' h => hops g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hops g (by simp)
    have main : ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧ Rep n (ds ++ hs)
        fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
      match hI : g.inputs, hlen with
      | [], _ =>
        exact ⟨[], by simp, by simpa using h1, Or.inl ⟨g.op.eval [], fun y => rfl⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, by simpa using h1, ?_⟩
        rw [List.append_nil]
        have e : (fun y : Fin n → Bool => g.op.eval ([a].map fun i =>
            (run gs (List.ofFn y)).getD i false)) =
            fun y => (run gs (List.ofFn y)).getD a false := by
          funext y
          rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
        rw [e]
        exact h3 a
      | [a, b], _ => exact rep_two n ds h1 g.op hop _ _ (h3 a) (h3 b)
    obtain ⟨hs, k1, k2, k3⟩ := main
    have k4 : ∀ f : (Fin n → Bool) → Bool, Rep n ds f → Rep n (ds ++ hs) f := by
      intro f hf
      match hs, k1 with
      | [], _ => simpa using hf
      | [g'], _ => exact rep_app n ds g' f hf
    refine ⟨ds ++ hs, k2, by simp; omega, fun w => ?_⟩
    by_cases hw : w = n + gs.length
    · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
          fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
        funext y
        rw [run_snoc, hw, show n + gs.length = (run gs (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
      rw [e]
      exact k3
    · by_cases hw' : w < n + gs.length
      · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
            fun y => (run gs (List.ofFn y)).getD w false := by
          funext y
          exact run_prefix _ _ _ _ (by simpa using hw')
        rw [e]
        exact k4 _ (h3 w)
      · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by
          rw [run_length]; simp; omega)⟩

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma scan_bool_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lx ly : List Bool) (hlen : lx.length = ly.length)
    (hle : ∀ i, lx.getD i false = true → ly.getD i false = true) :
    (scan boolStep gs lx).length = (scan boolStep gs ly).length ∧
      ∀ w, (scan boolStep gs lx).getD w false = true → (scan boolStep gs ly).getD w false = true := by
  induction gs generalizing lx ly with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    have hstep : boolStep lx g = true → boolStep ly g = true := by
      intro h
      rcases hg with hop | hop
      · simp only [boolStep, hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
        intro i hi
        exact hle i (h i hi)
      · simp only [boolStep, hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
        rcases h with ⟨i, hi, hit⟩
        exact ⟨i, hi, hle i hit⟩
    have hlen' : (lx ++ [boolStep lx g]).length = (ly ++ [boolStep ly g]).length := by
      simp [hlen]
    have hle' : ∀ i, (lx ++ [boolStep lx g]).getD i false = true →
        (ly ++ [boolStep ly g]).getD i false = true := by
      intro i hi
      by_cases hil : i < lx.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle i hi
      · by_cases heq : i = lx.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    exact ih hgs (lx ++ [boolStep lx g]) (ly ++ [boolStep ly g]) hlen' hle'

lemma wireVal_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) (w : ℕ) :
    wireVal n C w x = true → wireVal n C w y = true := by
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at hi ⊢
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi
  exact (scan_bool_mono C.gates hAO (List.ofFn x) (List.ofFn y) (by simp) hle).2 w

noncomputable section BS

open Finset Classical

def Clean {n : ℕ} (S : Finset (Fin n)) (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, g x = true → ∃ a ∈ S, x a = true

def single {n : ℕ} (a : Fin n) : Fin n → Bool := fun v => decide (v = a)

def Tset {n : ℕ} (g : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  univ.filter fun a => g (single a) = true

lemma mem_Tset {n : ℕ} {g : (Fin n → Bool) → Bool} {a : Fin n} :
    a ∈ Tset g ↔ g (single a) = true := by
  simp [Tset]

lemma Clean.Tset_subset {n : ℕ} {S : Finset (Fin n)} {g : (Fin n → Bool) → Bool}
    (h : Clean S g) : Tset g ⊆ S := by
  intro a ha
  obtain ⟨b, hb, hx⟩ := h _ (mem_Tset.mp ha)
  have : b = a := by simpa [single] using hx
  exact this ▸ hb

variable {n : ℕ} {C : Circuit}

lemma wv_or (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x = true ↔
      wireVal n C (opnd C j 0) x = true ∨ wireVal n C (opnd C j 1) x = true := by
  rw [wireVal_or hA x hj hop, Bool.or_eq_true]

lemma wv_and (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x = true ↔
      wireVal n C (opnd C j 0) x = true ∧ wireVal n C (opnd C j 1) x = true := by
  rw [wireVal_and hA x hj hop, Bool.and_eq_true]

lemma or_clean (hA : IsAO2 n C) {S : Finset (Fin n)} {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hc : Clean S (wireVal n C (n + j))) :
    Clean S (wireVal n C (opnd C j 0)) ∧ Clean S (wireVal n C (opnd C j 1)) :=
  ⟨fun x hx => hc x ((wv_or hA hj hop x).mpr (Or.inl hx)),
    fun x hx => hc x ((wv_or hA hj hop x).mpr (Or.inr hx))⟩

lemma and_clean (hA : IsAO2 n C) {S : Finset (Fin n)} {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hc : Clean S (wireVal n C (n + j))) :
    Clean S (wireVal n C (opnd C j 0)) ∨ Clean S (wireVal n C (opnd C j 1)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [Clean, not_forall] at h1 h2
  obtain ⟨x1, hx1, n1⟩ := h1
  obtain ⟨x2, hx2, n2⟩ := h2
  have l1 : ∀ i : Fin n, x1 i = true → (fun v => x1 v || x2 v) i = true :=
    fun v hv => by simp [hv]
  have l2 : ∀ i : Fin n, x2 i = true → (fun v => x1 v || x2 v) i = true :=
    fun v hv => by simp [hv]
  obtain ⟨a, ha, hxa⟩ := hc (fun v => x1 v || x2 v) ((wv_and hA hj hop _).mpr
    ⟨wireVal_mono hA.1 l1 _ hx1, wireVal_mono hA.1 l2 _ hx2⟩)
  simp only [Bool.or_eq_true] at hxa
  rcases hxa with h' | h'
  · exact n1 ⟨a, ha, h'⟩
  · exact n2 ⟨a, ha, h'⟩

lemma T_or (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    Tset (wireVal n C (n + j)) ⊆
      Tset (wireVal n C (opnd C j 0)) ∪ Tset (wireVal n C (opnd C j 1)) := by
  intro a ha
  rw [mem_union, mem_Tset, mem_Tset]
  exact (wv_or hA hj hop _).mp (mem_Tset.mp ha)

lemma T_and_left (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    Tset (wireVal n C (n + j)) ⊆ Tset (wireVal n C (opnd C j 0)) :=
  fun _ ha => mem_Tset.mpr ((wv_and hA hj hop _).mp (mem_Tset.mp ha)).1

lemma T_and_right (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    Tset (wireVal n C (n + j)) ⊆ Tset (wireVal n C (opnd C j 1)) :=
  fun _ ha => mem_Tset.mpr ((wv_and hA hj hop _).mp (mem_Tset.mp ha)).2

lemma two_is_gate {w : ℕ} (h2 : 2 ≤ (Tset (wireVal n C w)).card) :
    ∃ j, j < C.gates.length ∧ w = n + j := by
  by_cases h1 : w < n
  · exfalso
    have hsub : Tset (wireVal n C w) ⊆ {⟨w, h1⟩} := by
      intro a ha
      have h := mem_Tset.mp ha
      rw [wireVal_input n C _ w h1] at h
      simp only [single, decide_eq_true_eq] at h
      exact mem_singleton.mpr h.symm
    have := card_le_card hsub
    simp at this
    omega
  · by_cases h3 : n + C.gates.length ≤ w
    · exfalso
      have he : Tset (wireVal n C w) = ∅ := by
        ext a
        simp [mem_Tset, wireVal_ge n C _ w h3]
      rw [he] at h2
      simp at h2
    · exact ⟨w - n, by omega, by omega⟩

def good (n : ℕ) (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (range C.gates.length).filter fun j =>
    Clean S (wireVal n C (n + j)) ∧ 2 ≤ (Tset (wireVal n C (n + j))).card

lemma mem_good {S : Finset (Fin n)} {j : ℕ} :
    j ∈ good n C S ↔ j < C.gates.length ∧ Clean S (wireVal n C (n + j)) ∧
      2 ≤ (Tset (wireVal n C (n + j))).card := by
  simp [good]

def small (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  if (Tset (wireVal n C w)).card ≤ 1 then Tset (wireVal n C w) else ∅

lemma small_card (w : ℕ) : (small n C w).card ≤ 1 := by
  unfold small
  split_ifs with h
  · exact h
  · simp

lemma card_cover_le (hA : IsAO2 n C) (S : Finset (Fin n)) (A : Finset (Fin n))
    (hcov : ∀ a ∈ A, ∃ j ∈ good n C S, a ∈ Tset (wireVal n C (n + j))) :
    A.card ≤ 2 * (good n C S).card := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · simp
  obtain ⟨i0, hi0, _⟩ := hcov a0 ha0
  have hex : ∀ a, a ∈ A →
      ∃ w ∈ good n C S, a ∈ Tset (wireVal n C (n + w)) ∧
        ∀ j ∈ good n C S, a ∈ Tset (wireVal n C (n + j)) → w ≤ j := by
    intro a ha
    have hne : ((good n C S).filter fun j => a ∈ Tset (wireVal n C (n + j))).Nonempty := by
      obtain ⟨i1, hi1, ha1⟩ := hcov a ha
      exact ⟨i1, mem_filter.mpr ⟨hi1, ha1⟩⟩
    obtain ⟨w, hw, hmin⟩ := exists_min_image _ (fun j : ℕ => j) hne
    rw [mem_filter] at hw
    exact ⟨w, hw.1, hw.2, fun j hj haj => hmin j (mem_filter.mpr ⟨hj, haj⟩)⟩
  let first : Fin n → ℕ := fun a => if ha : a ∈ A then Classical.choose (hex a ha) else i0
  have hfirst : ∀ a (ha : a ∈ A), first a ∈ good n C S ∧
      a ∈ Tset (wireVal n C (n + first a)) ∧
      ∀ j ∈ good n C S, a ∈ Tset (wireVal n C (n + j)) → first a ≤ j := by
    intro a ha
    have := Classical.choose_spec (hex a ha)
    simp only [first, ha, dif_pos]
    exact ⟨this.1, this.2.1, this.2.2⟩
  have himg : A.image first ⊆ good n C S := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
    exact (hfirst a ha).1
  have hfib : ∀ w ∈ A.image first, (A.filter fun a => first a = w).card ≤ 2 := by
    intro w hw
    have hwg := himg hw
    obtain ⟨hwl, hwc, hw2⟩ := mem_good.mp hwg
    obtain ⟨hop, _, h0, h1⟩ := ao2_gate_props hA hwl
    have hsub : (A.filter fun a => first a = w) ⊆
        small n C (opnd C w 0) ∪ small n C (opnd C w 1) := by
      intro a ha
      rw [mem_filter] at ha
      obtain ⟨ha0, hfa⟩ := ha
      obtain ⟨_, haw, hmin⟩ := hfirst a ha0
      rw [hfa] at haw hmin
      have key : ∀ o : ℕ, o < n + w → Clean S (wireVal n C o) →
          a ∈ Tset (wireVal n C o) → (Tset (wireVal n C o)).card ≤ 1 := by
        intro o hlt hoc hao
        by_contra hgt
        rw [not_le] at hgt
        obtain ⟨j, hj, rfl⟩ := two_is_gate hgt
        have hjg : j ∈ good n C S := mem_good.mpr ⟨hj, hoc, hgt⟩
        have := hmin j hjg hao
        omega
      rcases hop with hand | hor
      · exfalso
        rcases and_clean hA hwl hand hwc with hcl | hcl
        · have k1 := key _ h0 hcl (T_and_left hA hwl hand haw)
          have k2 := card_le_card (T_and_left hA hwl hand)
          omega
        · have k1 := key _ h1 hcl (T_and_right hA hwl hand haw)
          have k2 := card_le_card (T_and_right hA hwl hand)
          omega
      · obtain ⟨cl, cr⟩ := or_clean hA hwl hor hwc
        rcases mem_union.mp (T_or hA hwl hor haw) with hal | har
        · have k1 := key _ h0 cl hal
          exact mem_union_left _ (by simp [small, k1, hal])
        · have k1 := key _ h1 cr har
          exact mem_union_right _ (by simp [small, k1, har])
    calc _ ≤ (small n C (opnd C w 0) ∪ small n C (opnd C w 1)).card := card_le_card hsub
      _ ≤ (small n C (opnd C w 0)).card + (small n C (opnd C w 1)).card := card_union_le _ _
      _ ≤ 2 := by
        have := small_card (n := n) (C := C) (opnd C w 0)
        have := small_card (n := n) (C := C) (opnd C w 1)
        omega
  calc A.card ≤ 2 * (A.image first).card := card_le_mul_card_image _ 2 hfib
    _ ≤ 2 * (good n C S).card := Nat.mul_le_mul_left 2 (card_le_card himg)

lemma card_T_le (hA : IsAO2 n C) (S : Finset (Fin n)) {i0 : ℕ} (hi0 : i0 ∈ good n C S) :
    (Tset (wireVal n C (n + i0))).card ≤ 2 * (good n C S).card :=
  card_cover_le hA S _ fun _ ha => ⟨i0, hi0, ha⟩

lemma good_disj {κ : Type} [Fintype κ] (Nb : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) :
    ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (good n C (Nb c)) (good n C (Nb c')) := by
  intro c _ c' _ hne
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨_, hc1, h2⟩ := mem_good.mp hi
  obtain ⟨_, hc2, _⟩ := mem_good.mp hi'
  have hsub : Tset (wireVal n C (n + i)) ⊆ Nb c ∩ Nb c' :=
    fun a ha => mem_inter.mpr ⟨hc1.Tset_subset ha, hc2.Tset_subset ha⟩
  have := card_le_card hsub
  have := hdisj c c' hne
  omega

lemma sum_good_le {κ : Type} [Fintype κ] (Nb : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) :
    ∑ c, (good n C (Nb c)).card ≤ C.gates.length := by
  rw [← card_biUnion (good_disj Nb hdisj)]
  calc _ ≤ (range C.gates.length).card := card_le_card (by
        intro j hj
        obtain ⟨c, _, hc⟩ := mem_biUnion.mp hj
        exact mem_range.mpr (mem_good.mp hc).1)
    _ = C.gates.length := card_range _

theorem sum_cover_le (hA : IsAO2 n C) {κ : Type} [Fintype κ] (Nb : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) :
    ∑ c, ((good n C (Nb c)).biUnion fun i => Tset (wireVal n C (n + i))).card ≤
      2 * C.gates.length := by
  have hsum := sum_good_le (C := C) Nb hdisj
  calc ∑ c, ((good n C (Nb c)).biUnion fun i => Tset (wireVal n C (n + i))).card
      ≤ ∑ c, 2 * (good n C (Nb c)).card := sum_le_sum fun c _ =>
        card_cover_le hA (Nb c) _ fun a ha => by
          obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
          exact ⟨i, hi, hai⟩
    _ = 2 * ∑ c, (good n C (Nb c)).card := by rw [mul_sum]
    _ ≤ 2 * C.gates.length := by omega

theorem sum_T_le (hA : IsAO2 n C) {κ : Type} [Fintype κ] (Nb : κ → Finset (Fin n))
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1)
    (h : κ → ℕ) (hclean : ∀ c, Clean (Nb c) (wireVal n C (h c))) :
    ∑ c, (Tset (wireVal n C (h c))).card ≤ 2 * C.gates.length + Fintype.card κ := by
  have hterm : ∀ c, (Tset (wireVal n C (h c))).card ≤ 2 * (good n C (Nb c)).card + 1 := by
    intro c
    by_cases h2 : 2 ≤ (Tset (wireVal n C (h c))).card
    · obtain ⟨j, hj, hjeq⟩ := two_is_gate h2
      have hc' := hclean c
      rw [hjeq] at hc' h2 ⊢
      have := card_T_le hA (Nb c) (mem_good.mpr ⟨hj, hc', h2⟩)
      exact le_trans this (Nat.le_succ _)
    · omega
  have hsum := sum_good_le (C := C) Nb hdisj
  calc ∑ c, (Tset (wireVal n C (h c))).card ≤ ∑ c, (2 * (good n C (Nb c)).card + 1) :=
        sum_le_sum fun c _ => hterm c
    _ = 2 * ∑ c, (good n C (Nb c)).card + Fintype.card κ := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ 2 * C.gates.length + Fintype.card κ := by omega

end BS

lemma ao_isAO2 {n : ℕ} {ds : List Gate} (h1 : AO n ds) : IsAO2 n ⟨ds, 0⟩ := by
  refine ⟨fun g hg => (h1.1 g hg).1, fun j hj i hi => h1.2 j hj i ?_,
    fun g hg => (h1.1 g hg).2⟩
  have hj' : j < ds.length := hj
  simpa [gateAt, hj'] using hi

abbrev Row {m n : ℕ} (R : Fin m → Fin n → Prop) [∀ i j, Decidable (R i j)] : Type :=
  {i : Fin m // 0 < (Finset.filter (R i) Finset.univ).card}

theorem core {m n : ℕ} (R : Fin m → Fin n → Prop) [dR : ∀ i j, Decidable (R i j)]
    (h4 : ∀ (a b : Fin m) (c d : Fin n), R a c → R b c → R a d → R b d → a = b ∨ c = d)
    (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (y : Fin n → Bool), (run gs (List.ofFn y)).getD (out i) false =
      decide (∃ j, R i j ∧ y j = true)) :
    ∑ i, (Finset.filter (R i) Finset.univ).card ≤ 2 * gs.length +
      (Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card).card := by
  classical
  obtain ⟨ds, h1, h2, h3⟩ := build n gs hops
  have hA : IsAO2 n ⟨ds, 0⟩ := ao_isAO2 h1
  have hex : ∀ c : Row R, ∃ k : ℕ,
      ∀ y, wireVal n ⟨ds, 0⟩ k y = decide (∃ j, R c.1 j ∧ y j = true) := by
    intro c
    obtain ⟨a, ha⟩ := Finset.card_pos.mp c.2
    have hRa : R c.1 a := (Finset.mem_filter.mp ha).2
    rcases h3 (out c.1) with ⟨b, hb⟩ | ⟨k, hk, hk'⟩
    · exfalso
      have e1 : decide (∃ j, R c.1 j ∧ (fun _ : Fin n => false) j = true) = b :=
        (hout c.1 _).symm.trans (hb _)
      have e2 : decide (∃ j, R c.1 j ∧ (fun j : Fin n => decide (j = a)) j = true) = b :=
        (hout c.1 _).symm.trans (hb _)
      have f1 : decide (∃ j, R c.1 j ∧ (fun _ : Fin n => false) j = true) = false := by simp
      have f2 : decide (∃ j, R c.1 j ∧ (fun j : Fin n => decide (j = a)) j = true) = true :=
        decide_eq_true ⟨a, hRa, by simp⟩
      exact Bool.false_ne_true ((f1.symm.trans e1).trans (f2.symm.trans e2).symm)
    · exact ⟨k, fun y => (hk' y).symm.trans (hout c.1 y)⟩
  choose h hh using hex
  have hclean : ∀ c : Row R,
      Clean (Finset.filter (R c.1) Finset.univ) (wireVal n ⟨ds, 0⟩ (h c)) := by
    intro c y hy
    rw [hh c y] at hy
    obtain ⟨j, hj, hyj⟩ := of_decide_eq_true hy
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hyj⟩
  have hT : ∀ c : Row R,
      Tset (wireVal n ⟨ds, 0⟩ (h c)) = Finset.filter (R c.1) Finset.univ := by
    intro c
    ext a
    rw [mem_Tset, hh c]
    simp [single]
  have hdisj : ∀ c c' : Row R, c ≠ c' →
      (Finset.filter (R c.1) Finset.univ ∩ Finset.filter (R c'.1) Finset.univ).card ≤ 1 := by
    intro c c' hne
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases h4 c.1 c'.1 a b ha.1 ha.2 hb.1 hb.2 with e | e
    · exact absurd (Subtype.ext e) hne
    · exact e
  have key := sum_T_le hA (fun c : Row R => Finset.filter (R c.1) Finset.univ)
    (by intro c c' hne; convert hdisj c c' hne) h hclean
  simp only [hT] at key
  rw [Fintype.card_subtype] at key
  have e : ∑ i ∈ Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card,
      (Finset.filter (R i) Finset.univ).card =
      ∑ c : Row R, (Finset.filter (R c.1) Finset.univ).card :=
    Finset.sum_subtype _ (by simp) _
  have e' : ∑ i, (Finset.filter (R i) Finset.univ).card =
      ∑ i ∈ Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card,
        (Finset.filter (R i) Finset.univ).card := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simpa using hi
  rw [e', e]
  refine le_trans key ?_
  show 2 * ds.length + _ ≤ _
  omega

theorem main {m n : ℕ} (R : Fin m → Fin n → Prop) [dR : ∀ i j, Decidable (R i j)]
    (h3 : ∀ i : Fin m, (Finset.filter (R i) Finset.univ).card = 0 ∨
      3 ≤ (Finset.filter (R i) Finset.univ).card)
    (h4 : ∀ (a b : Fin m) (c d : Fin n), R a c → R b c → R a d → R b d → a = b ∨ c = d)
    (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (y : Fin n → Bool), (run gs (List.ofFn y)).getD (out i) false =
      decide (∃ j, R i j ∧ y j = true)) :
    ∑ i, (Finset.filter (R i) Finset.univ).card ≤ 3 * gs.length := by
  have hc := core R h4 gs hops out hout
  have hs : (Finset.univ.filter fun i : Fin m =>
      0 < (Finset.filter (R i) Finset.univ).card).card * 3 ≤
      ∑ i, (Finset.filter (R i) Finset.univ).card := by
    calc _ = (Finset.univ.filter fun i : Fin m =>
          0 < (Finset.filter (R i) Finset.univ).card).card • 3 := by simp
      _ ≤ ∑ i ∈ Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card,
          (Finset.filter (R i) Finset.univ).card :=
        Finset.card_nsmul_le_sum _ _ _ (fun i hi => by
          rcases h3 i with h | h
          · have := (Finset.mem_filter.mp hi).2
            omega
          · exact h)
      _ ≤ ∑ i, (Finset.filter (R i) Finset.univ).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

def orBuild {m n : ℕ} : List (Sigma fun _ : Fin m => Fin n) → List Gate × (Fin m → ℕ)
  | [] => ([⟨GateOp.or, []⟩], fun _ => n)
  | p :: P => ((orBuild P).1 ++ [⟨GateOp.or, [p.2.val, (orBuild P).2 p.1]⟩],
      fun i => if i = p.1 then n + (orBuild P).1.length else (orBuild P).2 i)

lemma orBuild_ops {m n : ℕ} (P : List (Sigma fun _ : Fin m => Fin n)) :
    ∀ g ∈ (orBuild P).1, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction P with
  | nil =>
    intro g hg
    have hg' : g = ⟨GateOp.or, []⟩ := List.mem_singleton.mp hg
    subst hg'
    simp
  | cons p P ih =>
    intro g hg
    have hg' : g ∈ (orBuild P).1 ++ [⟨GateOp.or, [p.2.val, (orBuild P).2 p.1]⟩] := hg
    rcases List.mem_append.mp hg' with h | h
    · exact ih g h
    · rw [List.mem_singleton.mp h]
      simp

lemma orBuild_len {m n : ℕ} (P : List (Sigma fun _ : Fin m => Fin n)) :
    (orBuild P).1.length = P.length + 1 := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [orBuild, ih]

lemma or_eval2 (f : ℕ → Bool) (a b : ℕ) : GateOp.or.eval ([a, b].map f) = (f a || f b) := by
  simp [GateOp.eval]

lemma orBuild_spec {m n : ℕ} (P : List (Sigma fun _ : Fin m => Fin n)) (y : Fin n → Bool) :
    ∀ i : Fin m, (orBuild P).2 i < n + (orBuild P).1.length ∧
      ((run (orBuild P).1 (List.ofFn y)).getD ((orBuild P).2 i) false = true ↔
        ∃ p ∈ P, p.1 = i ∧ y p.2 = true) := by
  induction P with
  | nil =>
    intro i
    refine ⟨by simp [orBuild], ?_⟩
    have h0 : (run [⟨GateOp.or, []⟩] (List.ofFn y)).getD (List.ofFn y).length false = false :=
      getD_at (List.ofFn y) _
    rw [List.length_ofFn] at h0
    constructor
    · intro h
      exact absurd (h0.symm.trans h) (by simp)
    · rintro ⟨q, hq, _⟩
      simp at hq
  | cons p P ih =>
    intro i
    have hlen : (run (orBuild P).1 (List.ofFn y)).length = n + (orBuild P).1.length := by
      rw [run_length, List.length_ofFn]
    have e2 : (orBuild (p :: P)).1 =
        (orBuild P).1 ++ [⟨GateOp.or, [p.2.val, (orBuild P).2 p.1]⟩] := rfl
    by_cases hi : i = p.1
    · subst hi
      refine ⟨by simp [orBuild], ?_⟩
      have e : (orBuild (p :: P)).2 p.1 = (run (orBuild P).1 (List.ofFn y)).length := by
        rw [hlen]
        simp [orBuild]
      have hj : (run (orBuild P).1 (List.ofFn y)).getD p.2.val false = y p.2 := by
        rw [run_input _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
      rw [e, e2, run_snoc, getD_at, or_eval2, hj, Bool.or_eq_true, (ih p.1).2]
      constructor
      · rintro (h | ⟨q, hq, h1, h2⟩)
        · exact ⟨p, by simp, rfl, h⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
      · rintro ⟨q, hq, h1, h2⟩
        rcases List.mem_cons.mp hq with hq | hq
        · rw [hq] at h2
          exact Or.inl h2
        · exact Or.inr ⟨q, hq, h1, h2⟩
    · have e : (orBuild (p :: P)).2 i = (orBuild P).2 i := by simp [orBuild, hi]
      obtain ⟨hlt, hiff⟩ := ih i
      refine ⟨by rw [e, e2]; simp; omega, ?_⟩
      rw [e, e2, run_snoc, getD_lt _ _ _ (by rw [hlen]; exact hlt), hiff]
      constructor
      · rintro ⟨q, hq, h1, h2⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
      · rintro ⟨q, hq, h1, h2⟩
        rcases List.mem_cons.mp hq with hq | hq
        · rw [hq] at h1
          exact absurd h1.symm hi
        · exact ⟨q, hq, h1, h2⟩

theorem main2 {m n : ℕ} (R : Fin m → Fin n → Prop) [dR : ∀ i j, Decidable (R i j)]
    (h3 : ∀ i : Fin m, (Finset.filter (R i) Finset.univ).card = 0 ∨
      3 ≤ (Finset.filter (R i) Finset.univ).card)
    (h4 : ∀ (a b : Fin m) (c d : Fin n), R a c → R b c → R a d → R b d → a = b ∨ c = d)
    (s : ℕ)
    (hJ : JointSizeAtMost Set.univ (fun (i : Fin m) (y : Fin n → Bool) =>
      decide (∃ j, R i j ∧ y j = true)) Finset.univ s) :
    ∃ (C : Circuit) (out : Fin m → ℕ),
      (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 3 * (s + 1) ∧
      JointComputes Set.univ (fun (i : Fin m) (y : Fin n → Bool) =>
        decide (∃ j, R i j ∧ y j = true)) Finset.univ C out := by
  obtain ⟨C0, out0, ⟨hmono, hfan⟩, hsize, hcomp⟩ := hJ
  have hsum := main R h3 h4 C0.gates (fun g hg => ⟨hmono g hg, hfan g hg⟩) out0
    (fun i y => hcomp i (Finset.mem_univ _) y (Set.mem_univ _))
  obtain ⟨P, hPdef⟩ : ∃ P : List (Sigma fun _ : Fin m => Fin n),
      P = (Finset.univ.sigma fun i : Fin m => Finset.filter (R i) Finset.univ).toList := ⟨_, rfl⟩
  have hP : P.length = ∑ i, (Finset.filter (R i) Finset.univ).card := by
    rw [hPdef, Finset.length_toList, Finset.card_sigma]
  refine ⟨⟨(orBuild P).1, 0⟩, (orBuild P).2, orBuild_ops P, ?_, ?_⟩
  · show (orBuild P).1.length ≤ 3 * (s + 1)
    rw [orBuild_len, hP]
    have hs : C0.gates.length ≤ s := hsize
    omega
  · intro i _ y _
    show (run (orBuild P).1 (List.ofFn y)).getD ((orBuild P).2 i) false =
      decide (∃ j, R i j ∧ y j = true)
    rw [Bool.eq_iff_iff, (orBuild_spec P y i).2, decide_eq_true_iff]
    constructor
    · rintro ⟨q, hq, h1, h2⟩
      rw [hPdef, Finset.mem_toList, Finset.mem_sigma] at hq
      exact ⟨q.2, by rw [← h1]; exact (Finset.mem_filter.mp hq.2).2, h2⟩
    · rintro ⟨j, hj, hy⟩
      refine ⟨⟨i, j⟩, ?_, rfl, hy⟩
      rw [hPdef, Finset.mem_toList, Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

end PEqualNP.Outside.L_meta_6734

theorem PEqualNP.Outside.L_meta_6734 : ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : ℕ), PEqualNP.CircuitLowerBounds.JointSizeAtMost Set.univ (fun (x10 : Fin x2) (x11 : Fin x3 → Bool) => Decidable.decide (∃ (x12 : Fin x3), x4 x10 x12 ∧ x11 x12 = Bool.true)) Finset.univ x9 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : Fin x2 → ℕ), (∀ x13 ∈ x11.gates, x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x13.inputs.length ≤ (2 : ℕ)) ∧ x11.size ≤ x1 * (x9 + (1 : ℕ)) ∧ PEqualNP.CircuitLowerBounds.JointComputes Set.univ (fun (x13 : Fin x2) (x14 : Fin x3 → Bool) => Decidable.decide (∃ (x15 : Fin x3), x4 x13 x15 ∧ x14 x15 = Bool.true)) Finset.univ x11 x12 := by
  refine ⟨3, ?_⟩
  intro m n R dR h3 _ h4 s hJ
  exact PEqualNP.Outside.L_meta_6734.main2 R h3 h4 s hJ
