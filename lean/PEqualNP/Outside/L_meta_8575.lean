import Mathlib
import PEqualNP.Defs

-- Branch accounting adapts checked L-meta-614, PR 6550.
namespace PEqualNP.Outside.L_meta_8575_aux
namespace Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length  ≤  i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

lemma next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a  ≤  b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

lemma trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a  ≤  b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

lemma live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

lemma trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

lemma align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

lemma difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end Weighted


namespace Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

lemma acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length  ≤  j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

lemma point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

lemma point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

lemma carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

lemma singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

lemma influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b  ≤  j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

lemma next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

lemma mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2  ≤  (readers n C a).card

lemma nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card  ≤  1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

lemma no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end Weighted


namespace Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w, val C (point {v,w}) C.output = true ↔ G.Adj v w

lemma point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

lemma point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

lemma point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

lemma edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n  ≤  C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

lemma two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length  ≤  2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card  ≤  ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

lemma carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

lemma meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n  ≤  j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

lemma covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := by
    apply acts_mono hC (point_mono (s := {v,a₀}) (by simp [S])) C.output
    exact (he v a₀).2 ha₀

  have hZ : val C z C.output = true := by
    apply acts_mono hC (point_mono (s := {w,b₀}) (by simp [S])) C.output
    exact (he w b₀).2 hb₀

  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end Weighted


namespace Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

lemma mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

lemma input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

lemma live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

end Weighted

namespace Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8575_aux.Weighted
open Relation

noncomputable def liveGates (n : Nat) (C : Circuit) : Finset Nat :=
  open Classical in (Finset.range C.gates.length).filter (fun j => Live n C (n+j))

noncomputable def ports (n : Nat) (C : Circuit) : Finset (Nat × Fin 2) :=
  liveGates n C ×ˢ Finset.univ

def portSource (C : Circuit) (t : Nat × Fin 2) : Nat :=
  (NestedCover.gateAt C t.1).inputs.getD t.2.val 0

noncomputable def portCount (n : Nat) (C : Circuit) (a : Nat) : Nat :=
  open Classical in ((ports n C).filter fun t => portSource C t = a).card

def PortBranch (n : Nat) (C : Circuit) (a : Nat) : Prop := 2  ≤  portCount n C a

lemma gate_mem {C : Circuit} {j : Nat} (hj : j < C.gates.length) :
    NestedCover.gateAt C j ∈ C.gates := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs (n : Nat) (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length) :
    (NestedCover.gateAt C j).inputs = [portSource C (j,0), portSource C (j,1)] := by
  have hl := hm.2.2 _ (gate_mem hj)
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hl
  simp [portSource,he]

lemma slot_mem (n : Nat) (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length) (k : Fin 2) :
    portSource C (j,k) ∈ (NestedCover.gateAt C j).inputs := by
  rw [gate_inputs n C hm j hj]
  fin_cases k <;> simp

lemma gate_lookup {C : Circuit} {j : Nat} (hj : j < C.gates.length) :
    C.gates[j]? = some (NestedCover.gateAt C j) := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩

lemma port_next (n : Nat) (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (t : Nat × Fin 2) (ht : t ∈ ports n C) :
    LNext n C (portSource C t) (n+t.1) := by
  classical
  obtain ⟨hj,_⟩ := Finset.mem_product.mp ht
  obtain ⟨hj,hlive⟩ := Finset.mem_filter.mp hj
  have hj := Finset.mem_range.mp hj
  have hs := slot_mem n C hm t.1 hj t.2
  exact ⟨⟨hm.2.1 t.1 hj _ hs, t.1, _, gate_lookup hj, rfl, hs⟩,hlive⟩

lemma port_witness {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    {a b : Nat} (h : LNext n C a b) :
    ∃ t ∈ ports n C, portSource C t = a ∧ n+t.1=b := by
  classical
  obtain ⟨⟨_,j,g,hg,rfl,ha⟩,hb⟩ := h
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  have he : NestedCover.gateAt C j = g := by
    have hlookup := gate_lookup hj
    rw [hg] at hlookup
    exact (Option.some.inj hlookup).symm
  rw [← he,gate_inputs n C hm j hj] at ha
  have hport (k : Fin 2) : (j,k) ∈ ports n C := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hb⟩,Finset.mem_univ _⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with h | h
  · exact ⟨(j,0),hport 0,h.symm,rfl⟩
  · exact ⟨(j,1),hport 1,h.symm,rfl⟩

lemma nonport_unique {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    {a b c : Nat} (hn : ¬ PortBranch n C a) (hb : LNext n C a b) (hc : LNext n C a c) : b=c := by
  classical
  obtain ⟨t,ht,hs,hb'⟩ := port_witness C hm hb
  obtain ⟨u,hu,hs',hc'⟩ := port_witness C hm hc
  have hcard : ((ports n C).filter fun t => portSource C t = a).card  ≤  1 := by
    unfold PortBranch portCount at hn
    omega
  have same := Finset.card_le_one_iff.mp hcard
    (Finset.mem_filter.mpr ⟨ht,hs⟩) (Finset.mem_filter.mpr ⟨hu,hs'⟩)
  exact hb'.symm.trans ((congrArg (fun t : Nat × Fin 2 => n+t.1) same).trans hc')

lemma source_live {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (t : Nat × Fin 2) (ht : t ∈ ports n C) : portSource C t ∈ living n C := by
  have hn := port_next n C hm t ht
  apply mem_living.mpr
  exact ⟨hn.1.1.trans (next_in_range hn.1), live_before hn.1 hn.2⟩

lemma sum_portCount {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C) :
    ∑ a ∈ living n C, portCount n C a = 2*(liveGates n C).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := ports n C) (t := living n C)
    (f := portSource C) (source_live C hm)
  unfold portCount
  rw [← h]
  simp [ports,Nat.mul_comm]

end Port


namespace Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8575_aux.Weighted
open Relation Classical

lemma liveGates_card (n : Nat) (C : Circuit) :
    (liveGates n C).card = ((living n C).filter fun a => ¬a<n).card := by
  classical
  apply Finset.card_bij (fun j _ => n+j)
  · intro j hj
    obtain ⟨hj,hl⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by omega,hl⟩,by omega⟩
  · intro a ha b hb hab
    omega
  · intro a ha
    obtain ⟨ha,hn⟩ := Finset.mem_filter.mp ha
    obtain ⟨hr,hl⟩ := mem_living.mp ha
    refine ⟨a-n,?_,by omega⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega),by simpa only [Nat.add_sub_of_le (by omega : n  ≤  a)] using hl⟩

lemma port_branch_budget {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : PEqualNP.TopForm.IsAO2 n C) (he : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u)
    (ho : C.output ∈ living n C) :
    active.card + ((living n C).filter (PortBranch n C)).card  ≤  C.size+1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a<n)
  let B := W.filter (PortBranch n C)
  let R := W.erase C.output
  have hSub : active.image Fin.val ⊆ W \ S := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_sdiff.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,
      fun h => (Finset.mem_filter.mp h).2 v.isLt⟩
  have hW : active.card + S.card  ≤  W.card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h
    have part := Finset.card_sdiff_add_card_eq_card (show S ⊆ W from Finset.filter_subset _ _)
    omega
  have hR : R.card+1 = W.card := by
    exact Finset.card_erase_add_one ho
  have hS : S.card  ≤  C.gates.length := by
    rw [← liveGates_card n C]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hoNone : ¬ PortBranch n C C.output := by
    intro hb
    have hpos : 0 < ((ports n C).filter fun t => portSource C t = C.output).card := by
      unfold PortBranch portCount at hb
      omega
    obtain ⟨t,ht⟩ := Finset.card_pos.mp hpos
    obtain ⟨ht,hs⟩ := Finset.mem_filter.mp ht
    have hn := port_next n C hm t ht
    rw [hs] at hn
    exact (Nat.not_lt_of_ge (next_le hn.2)) hn.1.1
  have hlow : R.card+B.card  ≤  ∑ a ∈ W, portCount n C a := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : Nat)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : Nat) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if PortBranch n C a then 1 else 0 : Nat)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.mp ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : PortBranch n C a
      · have hb' : 2  ≤  portCount n C a := hb
        simpa [heq,hb] using hb'
      · have hp : 0 < portCount n C a := by
          obtain ⟨b,hb⟩ := live_readers_nonempty hl heq
          obtain ⟨t,ht,hs,_⟩ := port_witness C hm (mem_readers.mp hb)
          exact Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hs⟩⟩
        simpa [heq,hb] using Nat.succ_le_of_lt hp
  have hsum : (∑ a ∈ W, portCount n C a) = 2*S.card := by
    rw [sum_portCount C hm,liveGates_card]
  change active.card+B.card  ≤  C.gates.length+1
  omega

end Port

namespace Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8575_aux.Weighted
open Relation Classical

lemma branch_is_port_branch {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    {a : Nat} (hb : Branch n C a) : PortBranch n C a := by
  by_contra hn
  obtain ⟨b,c,hb,hc,hne⟩ := Finset.one_lt_card_iff.mp hb
  exact hne (nonport_unique C hm hn (mem_readers.mp hb) (mem_readers.mp hc))

end Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8575_aux.Weighted
open PEqualNP.Outside.L_meta_8575_aux.Port
open Relation Classical

def left {n : Nat} : Fin n → Fin (n+n) := Fin.castAdd n
def right {n : Nat} : Fin n → Fin (n+n) := Fin.natAdd n
lemma sides {n : Nat} (a b : Fin n) : left a ≠ right b := by
  intro eq
  have h := congrArg Fin.val eq
  change a.val=n+b.val at h
  have ha := a.isLt
  omega
lemma left_inj {n : Nat} {a b : Fin n} (h : left a=left b) : a=b :=
  Fin.ext (congrArg (fun i : Fin (n+n) => i.val) h)
lemma right_inj {n : Nat} {a b : Fin n} (h : right a=right b) : a=b := by
  have h' := congrArg Fin.val h
  change n+a.val=n+b.val at h'
  exact Fin.ext (by omega)
def graph {n : Nat} (E : Finset (Fin n × Fin n)) : SimpleGraph (Fin (n+n)) :=
  SimpleGraph.fromRel (fun x y => ∃a b,(a,b)∈E ∧ x=left a ∧ y=right b)
lemma graph_adj {n : Nat} (E : Finset (Fin n × Fin n)) (x y : Fin (n+n)) :
    (graph E).Adj x y ↔
      (∃a b,(a,b)∈E ∧ x=left a ∧ y=right b) ∨
      (∃a b,(a,b)∈E ∧ y=left a ∧ x=right b) := by
  rw [graph,SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    rintro rfl
    rcases h with ⟨a,b,_,hl,hr⟩|⟨a,b,_,hl,hr⟩ <;> exact sides a b (hl.symm.trans hr)
lemma graph_lr {n : Nat} (E : Finset (Fin n × Fin n)) (a b : Fin n) :
    (graph E).Adj (left a) (right b) ↔ (a,b)∈E := by
  rw [graph_adj]
  constructor
  · rintro (⟨c,d,mem,hc,hd⟩|⟨c,d,_,_,bad⟩)
    · obtain rfl := left_inj hc
      obtain rfl := right_inj hd
      exact mem
    · exact False.elim (sides a d bad)
  · intro mem
    exact Or.inl ⟨a,b,mem,rfl,rfl⟩
lemma computes_graph {n : Nat} (E : Finset (Fin n × Fin n)) (C : Circuit)
    (computes : ∀x : Fin (n+n) → Bool,circuitFun (n+n) C x=
      decide (∃a b,(a,b)∈E ∧ x (Fin.castAdd n a)=true ∧ x (Fin.natAdd n b)=true)) : GraphEval C (graph E) := by
  intro u v
  have eq := computes (point {u,v})
  change val C (point {u,v}) C.output=decide _ at eq
  rw [eq,decide_eq_true_eq,graph_adj]
  constructor
  · rintro ⟨a,b,mem,ha,hb⟩
    have aa : left a=u ∨ left a=v := by simpa [point,left] using ha
    have bb : right b=u ∨ right b=v := by simpa [point,right] using hb
    rcases aa with au|av <;> rcases bb with bu|bv
    · exact False.elim (sides a b (au.trans bu.symm))
    · exact Or.inl ⟨a,b,mem,au.symm,bv.symm⟩
    · exact Or.inr ⟨a,b,mem,av.symm,bu.symm⟩
    · exact False.elim (sides a b (av.trans bv.symm))
  · rintro (⟨a,b,mem,rfl,rfl⟩|⟨a,b,mem,rfl,rfl⟩)
    · exact ⟨a,b,mem,by simp [point,left],by simp [point,right]⟩
    · exact ⟨a,b,mem,by simp [point,left],by simp [point,right]⟩
lemma matching_extra_lower (n : Nat) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n))
    (C : Circuit) (many : n<E.card)
    (square : ∀a b c d : Fin n,a≠b → c≠d → ¬((a,c)∈E ∧ (a,d)∈E ∧ (b,c)∈E ∧ (b,d)∈E))
    (matching : ∀a,(a,p a)∈E) (ao : PEqualNP.TopForm.IsAO2 (n+n) C)
    (computes : ∀x : Fin (n+n) → Bool,circuitFun (n+n) C x=
      decide (∃a b,(a,b)∈E ∧ x (Fin.castAdd n a)=true ∧ x (Fin.natAdd n b)=true)) : n+n≤C.size := by
  have extra : ∃a b,(a,b)∈E ∧ b≠p a := by
    by_contra! no
    have sub : E⊆Finset.univ.image (fun a : Fin n => (a,p a)) := by
      intro e he
      exact Finset.mem_image.mpr ⟨e.1,Finset.mem_univ _,Prod.ext rfl (no e.1 e.2 he).symm⟩
    have h := (Finset.card_le_card sub).trans (Finset.card_image_le)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    omega
  obtain ⟨a,b,ab,ne⟩ := extra
  let c := p.symm b
  have pcb : p c=b := p.apply_symm_apply b
  have ac : a≠c := by intro eq; apply ne; rw [eq,pcb]
  have missing : (c,p a)∉E := by
    intro bad
    exact square a c b (p a) ac ne ⟨ab,matching a,by simpa only [←pcb] using matching c,bad⟩
  have he := computes_graph E C computes
  have mono : Monotone2 C := by
    intro g hg
    exact ⟨ao.1 g hg,by rw [ao.2.2 g hg]⟩
  have edge : (graph E).Adj (left a) (right b) := (graph_lr E a b).mpr ab
  have al : (graph E).Adj (left a) (right (p a)) := (graph_lr E a (p a)).mpr (matching a)
  have br : (graph E).Adj (right b) (left c) := SimpleGraph.Adj.symm ((graph_lr E c b).mpr (by simpa only [←pcb] using matching c))
  have partners : ¬(graph E).Adj (right (p a)) (left c) := by
    intro h
    exact missing ((graph_lr E c (p a)).mp (SimpleGraph.Adj.symm h))
  have hcover := covers_edge mono he edge al
    (fun h => ne (right_inj h).symm) br (fun h => ac (left_inj h).symm) (Or.inr partners)
  have branch : ∃z,Live (n+n) C z ∧ PortBranch (n+n) C z := by
    rcases hcover with ⟨z,live,_,branch⟩|⟨z,live,_,branch⟩ <;>
      exact ⟨z,live,branch_is_port_branch C ao branch⟩
  have active : ∀v : Fin (n+n),∃u,(graph E).Adj v u := by
    intro v
    refine Fin.addCases ?_ ?_ v
    · intro x
      exact ⟨right (p x),(graph_lr E x (p x)).mpr (matching x)⟩
    · intro y
      refine ⟨left (p.symm y),SimpleGraph.Adj.symm ((graph_lr E (p.symm y) y).mpr ?_)⟩
      simpa only [p.apply_symm_apply] using matching (p.symm y)
  have bound := (edge_at_output he edge).2
  have budget := port_branch_budget C (graph E) ao he Finset.univ (fun v _ => active v)
    (mem_living.mpr ⟨bound,.refl⟩)
  obtain ⟨z,live,bran⟩ := branch
  have zbound := next_le live
  have pos : 0<((living (n+n) C).filter (PortBranch (n+n) C)).card :=
    Finset.card_pos.mpr ⟨z,Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by omega,live⟩,bran⟩⟩
  simp only [Finset.card_univ,Fintype.card_fin] at budget
  omega

end PEqualNP.Outside.L_meta_8575_aux

theorem PEqualNP.Outside.L_meta_8575 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → x1 + x1 ≤ x4.size := by
  exact PEqualNP.Outside.L_meta_8575_aux.matching_extra_lower
