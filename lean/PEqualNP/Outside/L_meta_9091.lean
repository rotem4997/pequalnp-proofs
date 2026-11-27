import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9091.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
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

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
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

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
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

end PEqualNP.Outside.L_meta_9091.GraphProof


namespace PEqualNP.Outside.L_meta_9091.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
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
    by_cases hgt : n + C.gates.length ≤ j
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

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
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

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L_meta_9091.GraphProof


namespace PEqualNP.Outside.L_meta_9091.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

theorem point_contains_edge (hC : Monotone2 C) (he : GraphEval C G)
    {u v : Fin n} {S : Finset (Fin n)} (hu : u ∈ S) (hv : v ∈ S) (edge : G.Adj u v) :
    val C (point S) C.output = true :=
  acts_mono hC (point_mono (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv)))
    C.output ((he u v).mpr edge)

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
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

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
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

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) ∧ val C (point {w}) (n+p) = false := by
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
  have hge : n ≤ j := by
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
    two_inputs ha hb hne hl.2, hs3⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs,_⟩ := meeting_gate hC he hvw
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
  have hY : val C y C.output = true := point_contains_edge hC he (u:=v) (v:=a₀) (by simp) (by simp [S]) ha₀
  have hZ : val C z C.output = true := point_contains_edge hC he (u:=w) (v:=b₀) (by simp) (by simp [S]) hb₀
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

end PEqualNP.Outside.L_meta_9091.GraphProof


namespace PEqualNP.Outside.L_meta_9091.GraphProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
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

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card ≤ C.gates.length+1
  omega

end PEqualNP.Outside.L_meta_9091.GraphProof



namespace PEqualNP.Outside.L_meta_9091.GraphProof
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem size_of_cover {n t : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hdegree : ∀ v : Fin n, ∃ w, G.Adj v w)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w →
      ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    (hpath : ∀ v w : Fin n, G.Adj v w → ∃ a b : Fin n,
      G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b))
    (hcover : ∀ S : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ S ∨ b ∈ S) → t ≤ S.card)
    (hC : Monotone2 C) (hE : GraphEval C G) : n + t ≤ C.size + 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    have ht := hcover ∅ (fun v => Fin.elim0 v)
    simp at ht
    omega
  let i : Fin n := ⟨0,by omega⟩
  obtain ⟨w,edge⟩ := hdegree i
  have hlt := (edge_at_output hE edge).2
  have houtput : C.output ∈ living n C := mem_living.2 ⟨hlt, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter (Eligible C)
  have hS (u : Fin n) : u ∈ S ↔ Eligible C u := by simp [S]
  have htc : t ≤ S.card := by
    apply hcover
    intro v w hvw
    obtain ⟨a,b,hva,haw,hwb,hbv,hab⟩ := hpath v w hvw
    exact (covers_edge hC hE hvw hva haw hwb hbv hab).imp (hS v).mpr (hS w).mpr
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      have hs := (hS u).mp hu
      have hb := firstBranch_spec u hs
      have hw := (next_le hb.1).trans_lt hlt
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hw,hb.1⟩,hb.2.2⟩
    · intro u hu v hv same
      have hsu := (hS u).mp hu
      have hsv := (hS v).mp hv
      rw [hf u hsu,hf v hsv] at same
      exact branch_injective hC hE htwins hsu hsv same
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans (branch_budget hC hE hdegree houtput)

end PEqualNP.Outside.L_meta_9091.GraphProof

namespace PEqualNP.Outside.L_meta_9091.Plane

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem cardL {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

theorem cardR {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

theorem cover {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [cardL, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, smul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [cardR, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, smul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)


theorem left_ne_right {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have := p.isLt
  omega

def graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj u v := ∃ p l : Fin N, I p l ∧ (Fin.castAdd N p = u ∨ Fin.castAdd N p = v) ∧
    (Fin.natAdd N l = u ∨ Fin.natAdd N l = v)
  symm := ⟨by
    rintro u v ⟨p,l,h,hp,hl⟩
    exact ⟨p,l,h,hp.symm,hl.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨p,l,h,hp,hl⟩
    exact left_ne_right p l ((hp.elim id id).trans (hl.elim id id).symm)⟩

theorem adj_ll {N : ℕ} (I : Fin N → Fin N → Prop) (p r : Fin N) :
    ¬ (graph I).Adj (Fin.castAdd N p) (Fin.castAdd N r) := by
  rintro ⟨a,b,_,_,h⟩
  exact h.elim (fun he => left_ne_right p b he.symm) (fun he => left_ne_right r b he.symm)

theorem adj_rr {N : ℕ} (I : Fin N → Fin N → Prop) (l m : Fin N) :
    ¬ (graph I).Adj (Fin.natAdd N l) (Fin.natAdd N m) := by
  rintro ⟨a,b,_,h,_⟩
  exact h.elim (left_ne_right a l) (left_ne_right a m)

theorem adj_lr {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (graph I).Adj (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have hp := Fin.castAdd_inj.mp (ha.resolve_right (left_ne_right a l))
    have hl := (Fin.natAdd_inj N).mp (hb.resolve_left (left_ne_right p b).symm)
    simpa [hp,hl] using hab
  · intro hi
    exact ⟨p,l,hi,Or.inl rfl,Or.inr rfl⟩

theorem adj_rl {N : ℕ} (I : Fin N → Fin N → Prop) (l p : Fin N) :
    (graph I).Adj (Fin.natAdd N l) (Fin.castAdd N p) ↔ I p l :=
  ((graph I).adj_comm _ _).trans (adj_lr I p l)

theorem no_square {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (u v a b : Fin (N+N)) (uv : u ≠ v) (ab : a ≠ b)
    (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
    (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
  have rect {p r l m : Fin N} (pr : p ≠ r) (lm : l ≠ m)
      (pl : I p l) (rl : I r l) (pm : I p m) (rm : I r m) : False :=
    lm ((hu p r pr).unique ⟨pl,rl⟩ ⟨pm,rm⟩)
  induction u using Fin.addCases <;> induction v using Fin.addCases <;>
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    simp_all only [adj_ll,adj_rr,adj_lr,adj_rl]
  all_goals first
    | exact rect (fun e => uv (congrArg (Fin.castAdd N) e)) (fun e => ab (congrArg (Fin.natAdd N) e)) ua va ub vb
    | exact rect (fun e => ab (congrArg (Fin.castAdd N) e)) (fun e => uv (congrArg (Fin.natAdd N) e)) ua ub va vb

theorem other_neighbor {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card=q+1)
    (cols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (v w : Fin (N+N)) : ∃ u : Fin (N+N), (graph I).Adj v u ∧ u ≠ w := by
  have pick {x y : Fin (N+N)} (ne : x≠y) (hx : (graph I).Adj v x) (hy : (graph I).Adj v y) :
      ∃ u, (graph I).Adj v u ∧ u≠w := by
    by_cases he : x=w
    · exact ⟨y,hy,fun ey => ne (he.trans ey.symm)⟩
    · exact ⟨x,hx,he⟩
  suffices distinct : ∃ x y : Fin (N+N), x≠y ∧ (graph I).Adj v x ∧ (graph I).Adj v y by
    obtain ⟨x,y,ne,hx,hy⟩ := distinct
    exact pick ne hx hy
  induction v using Fin.addCases with
  | left p =>
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ.filter (fun l => I p l)).card by rw [rows]; omega)
    exact ⟨Fin.natAdd N a,Fin.natAdd N b,fun e => ne ((Fin.natAdd_inj N).mp e),
      (adj_lr _ _ _).mpr (Finset.mem_filter.mp ha).2,(adj_lr _ _ _).mpr (Finset.mem_filter.mp hb).2⟩
  | right l =>
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ.filter (fun p => I p l)).card by rw [cols]; omega)
    exact ⟨Fin.castAdd N a,Fin.castAdd N b,fun e => ne (Fin.castAdd_inj.mp e),
      (adj_rl _ _ _).mpr (Finset.mem_filter.mp ha).2,(adj_rl _ _ _).mpr (Finset.mem_filter.mp hb).2⟩

theorem vertex_cover {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card=q+1)
    (cols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (T : Finset (Fin (N+N))) (hits : ∀ a b, (graph I).Adj a b → a∈T ∨ b∈T) : N ≤ T.card := by
  classical
  let A := Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)
  let B := Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)
  have cost := cover q I cols rows A B (by
    intro p l hp
    simpa [A,B] using hits _ _ ((adj_lr _ _ _).mpr hp))
  let left : Fin N ↪ Fin (N+N) := ⟨Fin.castAdd N,fun _ _ => Fin.castAdd_inj.mp⟩
  let right : Fin N ↪ Fin (N+N) := ⟨Fin.natAdd N,fun _ _ => (Fin.natAdd_inj N).mp⟩
  have separate : Disjoint (A.map left) (B.map right) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨l,_,he⟩ := Finset.mem_map.mp hz'
    exact left_ne_right p l he.symm
  have sub : A.map left ∪ B.map right ⊆ T := by
    intro z hz
    rcases Finset.mem_union.mp hz with ha|hb
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp ha
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hb
      exact (Finset.mem_filter.mp hl).2
  have hc := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint separate,Finset.card_map,Finset.card_map] at hc
  exact cost.trans hc

end PEqualNP.Outside.L_meta_9091.Plane

namespace PEqualNP.Outside.L_meta_9091.Extra

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9091.GraphProof PEqualNP.Outside.L_meta_9091.Plane
open Relation

lemma cauchy_schwarz_nat {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) ^ 2 ≤ s.card * ∑ x ∈ s, (f x) ^ 2 := by
  have h0 : (0 : ℤ) ≤ ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hexp : ∑ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
      2 * (s.card : ℤ) * (∑ x ∈ s, (f x : ℤ) ^ 2) - 2 * (∑ x ∈ s, (f x : ℤ)) ^ 2 := by
    have h1 : ∀ x ∈ s, ∑ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
        (s.card : ℤ) * (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (∑ y ∈ s, (f y : ℤ)) + ∑ y ∈ s, (f y : ℤ) ^ 2 := by
      intro x _
      have hsq : ∀ y ∈ s, ((f x : ℤ) - (f y : ℤ)) ^ 2 = (f x : ℤ) ^ 2 - 2 * (f x : ℤ) * (f y : ℤ) + (f y : ℤ) ^ 2 :=
        fun y _ => by ring
      rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hint : (∑ x ∈ s, (f x : ℤ)) ^ 2 ≤ (s.card : ℤ) * ∑ x ∈ s, (f x : ℤ) ^ 2 := by linarith
  exact_mod_cast hint

theorem min_cover_one_side {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (cols : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (T : Finset (Fin (N + N))) (hits : ∀ a b, (graph I).Adj a b → a ∈ T ∨ b ∈ T)
    (hcard : T.card = N) :
    (∀ p : Fin N, Fin.castAdd N p ∈ T) ∧ (∀ l : Fin N, Fin.natAdd N l ∉ T) ∨
    (∀ l : Fin N, Fin.natAdd N l ∈ T) ∧ (∀ p : Fin N, Fin.castAdd N p ∉ T) := by
  classical
  let A := Finset.univ.filter (fun p : Fin N => Fin.castAdd N p ∈ T)
  let B := Finset.univ.filter (fun l : Fin N => Fin.natAdd N l ∈ T)
  let leftE : Fin N ↪ Fin (N + N) := ⟨Fin.castAdd N, fun _ _ => Fin.castAdd_inj.mp⟩
  let rightE : Fin N ↪ Fin (N + N) := ⟨Fin.natAdd N, fun _ _ => (Fin.natAdd_inj N).mp⟩
  have hsep : Disjoint (A.map leftE) (B.map rightE) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hz1
    obtain ⟨l, _, h⟩ := Finset.mem_map.mp hz2
    exact left_ne_right p l h.symm
  have hTeq : T = A.map leftE ∪ B.map rightE := by
    ext z
    simp only [Finset.mem_union, Finset.mem_map, A, B, leftE, rightE,
      Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    induction z using Fin.addCases with
    | left p =>
      constructor
      · intro hp; exact Or.inl ⟨p, hp, rfl⟩
      · rintro (⟨p2, hp2, h⟩ | ⟨l2, _, h⟩)
        · exact (Fin.castAdd_inj.mp h) ▸ hp2
        · exact (left_ne_right p l2 h.symm).elim
    | right l =>
      constructor
      · intro hl; exact Or.inr ⟨l, hl, rfl⟩
      · rintro (⟨p2, _, h⟩ | ⟨l2, hl2, h⟩)
        · exact (left_ne_right p2 l h).elim
        · exact ((Fin.natAdd_inj N).mp h) ▸ hl2
  have hAB : A.card + B.card = N := by
    have h1 := congrArg Finset.card hTeq
    rw [Finset.card_union_of_disjoint hsep, Finset.card_map, Finset.card_map] at h1
    omega
  by_cases hA_full : A.card = N
  · left
    have hA_eq : A = Finset.univ := Finset.eq_univ_of_card A (by simpa using hA_full)
    have hB_eq : B = ∅ := Finset.card_eq_zero.mp (by omega)
    constructor
    · intro p
      have hp : p ∈ A := hA_eq ▸ Finset.mem_univ p
      exact (Finset.mem_filter.mp hp).2
    · intro l hl
      have : l ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
      rw [hB_eq] at this
      exact Finset.notMem_empty l this
  by_cases hB_full : B.card = N
  · right
    have hB_eq : B = Finset.univ := Finset.eq_univ_of_card B (by simpa using hB_full)
    have hA_eq : A = ∅ := Finset.card_eq_zero.mp (by omega)
    constructor
    · intro l
      have hl : l ∈ B := hB_eq ▸ Finset.mem_univ l
      exact (Finset.mem_filter.mp hl).2
    · intro p hp
      have : p ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
      rw [hA_eq] at this
      exact Finset.notMem_empty p this
  exfalso
  let A_c := Finset.univ \ A
  have ha_eq : A_c.card = B.card := by
    have h1 : A_c.card + A.card = N := by
      have h2 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
      simpa [A_c] using h2
    omega
  have ha_pos : 0 < A_c.card := by
    have hA_le : A.card ≤ N := by simpa using Finset.card_le_univ A
    omega
  have ha_lt : A_c.card < N := by
    have hB_le : B.card ≤ N := by simpa using Finset.card_le_univ B
    omega
  have hinc_B : ∀ p ∈ A_c, ∀ l : Fin N, I p l → l ∈ B := by
    intro p hp l hpl
    have hpA : Fin.castAdd N p ∉ T := by
      intro hmem
      exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hmem⟩)
    rcases hits (Fin.castAdd N p) (Fin.natAdd N l) ((adj_lr I p l).mpr hpl) with h1 | h2
    · exact (hpA h1).elim
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, h2⟩
  let d : Fin N → ℕ := fun l => (A_c.filter (fun p => I p l)).card
  have hsum1 : ∑ l ∈ B, d l = A_c.card * (q + 1) := by
    have h1 : ∑ l ∈ B, d l = ((A_c ×ˢ B).filter (fun pl : Fin N × Fin N => I pl.1 pl.2)).card :=
      (cardR I A_c B).symm
    rw [h1, cardL]
    have heach : ∀ p ∈ A_c, (B.filter (fun l => I p l)).card = q + 1 := by
      intro p hp
      have heq : B.filter (fun l => I p l) = Finset.univ.filter (fun l => I p l) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨And.right, fun h => ⟨hinc_B p hp l h, h⟩⟩
      rw [heq, rows p]
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
  let P2 : Finset (Fin N × Fin N) := (A_c ×ˢ A_c).filter (fun pr => pr.1 ≠ pr.2)
  have hP2_card : P2.card = A_c.card * (A_c.card - 1) := by
    have hdiag : ((A_c ×ˢ A_c).filter (fun pr => pr.1 = pr.2)).card = A_c.card := by
      have heq : (A_c ×ˢ A_c).filter (fun pr => pr.1 = pr.2) = A_c.image (fun p => (p, p)) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
        · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
      rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
    have hadd : P2.card + ((A_c ×ˢ A_c).filter (fun pr => pr.1 = pr.2)).card = (A_c ×ˢ A_c).card := by
      have hsub : (A_c ×ˢ A_c).filter (fun pr => pr.1 = pr.2) ⊆ A_c ×ˢ A_c := Finset.filter_subset _ _
      have heq : (A_c ×ˢ A_c) \ (A_c ×ˢ A_c).filter (fun pr => pr.1 = pr.2) = P2 := by
        ext pr; simp [P2]; tauto
      rw [← heq]
      exact Finset.card_sdiff_add_card_eq_card hsub
    rw [hdiag, Finset.card_product] at hadd
    have hmul : A_c.card * (A_c.card - 1) + A_c.card = A_c.card * A_c.card := by
      cases hc : A_c.card with
      | zero => omega
      | succ k => simp [Nat.mul_succ, Nat.add_comm]
    omega
  choose! fl hfl using fun (p r : Fin N) (h : p ≠ r) => (hu p r h).exists
  have hfl_u : ∀ p r l, p ≠ r → I p l → I r l → fl p r = l := fun p r l h h1 h2 =>
    (hu p r h).unique (hfl p r h) ⟨h1, h2⟩
  have hsum2 : ∑ l ∈ B, d l * (d l - 1) = A_c.card * (A_c.card - 1) := by
    have hfib : P2.card = ∑ l ∈ B, (P2.filter (fun pr => fl pr.1 pr.2 = l)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro pr hpr
      have hmem := Finset.mem_filter.mp hpr
      have hp1 : pr.1 ∈ A_c := (Finset.mem_product.mp hmem.1).1
      exact hinc_B pr.1 hp1 (fl pr.1 pr.2) (hfl pr.1 pr.2 hmem.2).1
    rw [← hP2_card, hfib]
    apply Finset.sum_congr rfl
    intro l _
    let Sl := A_c.filter (fun p => I p l)
    have hSl_eq : P2.filter (fun pr => fl pr.1 pr.2 = l) = (Sl ×ˢ Sl).filter (fun pr => pr.1 ≠ pr.2) := by
      ext ⟨a, b⟩
      simp only [P2, Sl, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hne⟩, hfeq⟩
        have hI := hfl a b hne
        rw [hfeq] at hI
        exact ⟨⟨⟨ha, hI.1⟩, ⟨hb, hI.2⟩⟩, hne⟩
      · rintro ⟨⟨⟨ha, hIa⟩, ⟨hb, hIb⟩⟩, hne⟩
        exact ⟨⟨⟨ha, hb⟩, hne⟩, hfl_u a b l hne hIa hIb⟩
    rw [hSl_eq]
    have hdiag : ((Sl ×ˢ Sl).filter (fun pr => pr.1 = pr.2)).card = Sl.card := by
      have heq : (Sl ×ˢ Sl).filter (fun pr => pr.1 = pr.2) = Sl.image (fun p => (p, p)) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
        · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
      rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
    have hadd : ((Sl ×ˢ Sl).filter (fun pr => pr.1 ≠ pr.2)).card +
        ((Sl ×ˢ Sl).filter (fun pr => pr.1 = pr.2)).card = (Sl ×ˢ Sl).card := by
      have hsub : (Sl ×ˢ Sl).filter (fun pr => pr.1 = pr.2) ⊆ Sl ×ˢ Sl := Finset.filter_subset _ _
      have heq : (Sl ×ˢ Sl) \ (Sl ×ˢ Sl).filter (fun pr => pr.1 = pr.2) =
          (Sl ×ˢ Sl).filter (fun pr => pr.1 ≠ pr.2) := by
        ext pr; simp; tauto
      rw [← heq]
      exact Finset.card_sdiff_add_card_eq_card hsub
    rw [hdiag, Finset.card_product] at hadd
    have hmul : Sl.card * (Sl.card - 1) + Sl.card = Sl.card * Sl.card := by
      cases hc : Sl.card with
      | zero => omega
      | succ k => simp [Nat.mul_succ, Nat.add_comm]
    change Sl.card * (Sl.card - 1) = ((Sl ×ˢ Sl).filter (fun pr => pr.1 ≠ pr.2)).card
    omega
  have hsum_sq : ∑ l ∈ B, (d l) ^ 2 = A_c.card * (A_c.card + q) := by
    have hpt : ∀ l ∈ B, (d l) ^ 2 = d l * (d l - 1) + d l := by
      intro l _
      cases hc : d l with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hsum2, hsum1]
    cases hc : A_c.card with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  have hcs := cauchy_schwarz_nat B d
  rw [hsum1, hsum_sq, ← ha_eq] at hcs
  have h1 : (A_c.card * (q + 1)) ^ 2 = A_c.card * A_c.card * (q + 1) ^ 2 := by ring
  have h2 : A_c.card * (A_c.card * (A_c.card + q)) = A_c.card * A_c.card * (A_c.card + q) := by ring
  rw [h1, h2] at hcs
  have hpos2 : 0 < A_c.card * A_c.card := Nat.mul_pos ha_pos ha_pos
  have h3 : (q + 1) ^ 2 ≤ A_c.card + q := Nat.le_of_mul_le_mul_left hcs hpos2
  have hsq : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
  omega

lemma trace_split_branch {n : ℕ} {C : Circuit} {w : Fin n} {x m1 m2 : ℕ}
    (Q1 : Trace n C (Carries C w) x m1) (Q2 : Trace n C (Carries C w) x m2)
    (hne : m1 ≠ m2) (h1 : ¬ Carries C w m1) (h2 : ¬ Carries C w m2) :
    ∃ z, x ≤ z ∧ Live n C z ∧ Carries C w z ∧ Branch n C z := by
  induction Q1 using ReflTransGen.head_induction_on with
  | refl =>
    rcases Q2.cases_head with heq | ⟨y, hstep, _⟩
    · exact (hne heq).elim
    · exact (h1 hstep.1).elim
  | @head a b hab Q1' ih =>
    rcases Q2.cases_head with heq | ⟨c, hac, Q2'⟩
    · subst heq
      exact (h2 hab.1).elim
    · by_cases hbc : b = c
      · subst hbc
        obtain ⟨z, hzle, hzlive, hzc, hzb⟩ := ih Q2'
        exact ⟨z, hab.2.1.1.le.trans hzle, hzlive, hzc, hzb⟩
      · refine ⟨a, le_rfl, live_before hab.2.1 hab.2.2, hab.1, ?_⟩
        unfold Branch
        have hsub : ({b, c} : Finset ℕ) ⊆ readers n C a := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact mem_readers.mpr hab.2
          · exact mem_readers.mpr hac.2
        have hc2 : ({b, c} : Finset ℕ).card = 2 := Finset.card_pair hbc
        exact hc2 ▸ Finset.card_le_card hsub

lemma branch_budget_strict {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C)
    (h3 : ∃ b ∈ living n C, Branch n C b ∧ 3 ≤ (readers n C b).card) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  obtain ⟨b0, hb0W, hb0_br, hb0_3⟩ := h3
  have hb0B : b0 ∈ B := Finset.mem_filter.mpr ⟨hb0W, hb0_br⟩
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a, hi⟩
    obtain ⟨u, hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega, input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e, Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := Finset.card_erase_add_one ho
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a - n)
    · intro a ha
      have h : a < n + C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a - n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a - n = b - n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hb0_ne : b0 ≠ C.output := fun h => hoNone (h ▸ (Finset.mem_filter.mp hb0B).2)
  have hlow : R.card + B.card + 1 ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) = R.card := by
      calc _ = ∑ a ∈ W, (if a ≠ C.output then 1 else 0 : ℕ) :=
            Finset.sum_congr rfl (fun a _ => by by_cases h : a = C.output <;> simp [h])
        _ = R.card := by rw [← Finset.sum_filter]; simp [R, Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]; simp [B]
    have hb0W' : b0 ∈ W := hb0W
    have e1 : (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) = 1 := by
      rw [Finset.sum_ite_eq', ite_eq_left hb0W']
    calc R.card + B.card + 1
      _ = (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) +
          (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) +
          (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) := by rw [eR, eB, e1]
      _ = ∑ a ∈ W, ((if a = C.output then 0 else 1) + (if Branch n C a then 1 else 0) + (if a = b0 then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ ≤ ∑ a ∈ W, (readers n C a).card := by
        apply Finset.sum_le_sum
        intro a ha
        have hl := (mem_living.1 ha).2
        by_cases hab0 : a = b0
        · subst hab0
          have hbr : Branch n C a := (Finset.mem_filter.mp hb0B).2
          simp only [hb0_ne, ↓reduceIte, hbr]
          omega
        · by_cases heq : a = C.output
          · subst a; simp [hoNone, hab0]
          · by_cases hb : Branch n C a
            · have hb' : 2 ≤ (readers n C a).card := hb
              simpa [heq, hb, hab0] using hb'
            · simpa [heq, hb, hab0] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm : (∑ a ∈ W, (readers n C a).card) =
      ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2 * S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j < n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j < n then 0 else 2 : ℕ)) = 2 * S.card := by
      simp [S, Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n + B.card ≤ C.gates.length
  omega

theorem main_plane_3N (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hu : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hC : Monotone2 C)
    (hInc : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true)
    (hRej : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) :
    3 * N ≤ C.size := by
  classical
  let G := Plane.graph I
  have cols (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    rw [← Fintype.card_coe]
    refine (Fintype.card_congr (Equiv.subtypeEquivRight ?_)).trans (hline l)
    intro p; simp
  have rows := Plane.lines_through q N I hq hN cols hu
  have other (v w : Fin (N + N)) : ∃ a, G.Adj v a ∧ a ≠ w :=
    Plane.other_neighbor I hq rows cols v w
  have degree (v : Fin (N + N)) : ∃ w, G.Adj v w := by
    obtain ⟨w, hw, _⟩ := other v v; exact ⟨w, hw⟩
  have twins (v w : Fin (N + N)) (ne : v ≠ w) (_ : ¬ G.Adj v w) :
      ∃ u, ¬ (G.Adj v u ↔ G.Adj w u) := by
    obtain ⟨a, va⟩ := degree v
    obtain ⟨b, vb, ba⟩ := other v a
    by_cases wa : G.Adj w a
    · by_cases wb : G.Adj w b
      · exact (Plane.no_square I hu v w a b ne ba.symm va vb wa wb).elim
      · exact ⟨b, fun he => wb (he.mp vb)⟩
    · exact ⟨a, fun he => wa (he.mp va)⟩
  have path (v w : Fin (N + N)) (vw : G.Adj v w) :
      ∃ a b, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b) := by
    obtain ⟨a, va, aw⟩ := other v w
    obtain ⟨b, wb, bv⟩ := other w v
    exact ⟨a, b, va, aw, wb, bv, Or.inr (fun ab =>
      Plane.no_square I hu v b w a bv.symm aw.symm vw va wb.symm ab.symm)⟩
  have eval : GraphEval C G := by
    intro a b
    have hfn : point ({a, b} : Finset (Fin (N + N))) = fun z => decide (z = a ∨ z = b) := by
      funext z; simp [point]
    change circuitFun (N + N) C (point {a, b}) = true ↔ G.Adj a b
    rw [hfn]
    constructor
    · intro ht
      by_contra hnot
      have hcnt : Fintype.card { l : Fin N // decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } ≤ q := by
        have hle2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card ≤ 2 := by
          have hsub : Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b) ⊆
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)) ∪
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)) := by
            intro l hl
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
            exact hl
          have hc1 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro l1 hl1 l2 hl2
            exact (Fin.natAdd_inj N).mp ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
          have hc2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro l1 hl1 l2 hl2
            exact (Fin.natAdd_inj N).mp ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
          exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
        have hceq : Fintype.card { l : Fin N // decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } =
            (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card := by
          rw [← Fintype.card_coe]
          apply Fintype.card_congr
          apply Equiv.subtypeEquivRight
          intro l; simp
        omega
      have hno : ¬ ∃ p l : Fin N, I p l ∧
          decide (Fin.castAdd N p = a ∨ Fin.castAdd N p = b) = true ∧
          decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true := by
        rintro ⟨p, l, hpl, hp, hl⟩
        simp only [decide_eq_true_eq] at hp hl
        exact hnot ⟨p, l, hpl, hp, hl⟩
      have hf := hRej (fun z => decide (z = a ∨ z = b)) hcnt hno
      rw [hf] at ht
      exact Bool.false_ne_true ht
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hset : (fun z : Fin (N + N) => decide (z = a ∨ z = b)) =
          (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) := by
        funext z
        have hne : Fin.castAdd N p ≠ Fin.natAdd N l := left_ne_right p l
        rcases hp with rfl | rfl <;> rcases hl with h2 | h2
        · exact (hne h2.symm).elim
        · subst h2; rfl
        · subst h2; simp [or_comm]
        · exact (hne h2.symm).elim
      rw [hset]
      exact hInc p l hpl
  by_contra hlt3N
  push Not at hlt3N
  have hNpos : 0 < N := by subst hN; nlinarith
  let i0 : Fin (N + N) := ⟨0, by omega⟩
  obtain ⟨w0, hedge0⟩ := degree i0
  have hlt_out := (edge_at_output eval hedge0).2
  have houtput : C.output ∈ living (N + N) C := mem_living.2 ⟨hlt_out, ReflTransGen.refl⟩
  let S : Finset (Fin (N + N)) := Finset.univ.filter (Eligible C)
  have hS (u : Fin (N + N)) : u ∈ S ↔ Eligible C u := by simp [S]
  have hS_hits : ∀ a b, G.Adj a b → a ∈ S ∨ b ∈ S := by
    intro v w hvw
    obtain ⟨a, b, hva, haw, hwb, hbv, hab⟩ := path v w hvw
    exact (covers_edge hC eval hvw hva haw hwb hbv hab).imp (hS v).mpr (hS w).mpr
  have htc : N ≤ S.card := Plane.vertex_cover I rows cols S hS_hits
  let B := (living (N + N) C).filter (Branch (N + N) C)
  let f (u : Fin (N + N)) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin (N + N)) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f, hu]
  have hf_maps : ∀ u ∈ S, f u ∈ B := by
    intro u hu
    have hs := (hS u).mp hu
    have hb := firstBranch_spec u hs
    have hw := (next_le hb.1).trans_lt hlt_out
    rw [hf u hs]
    exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hw, hb.1⟩, hb.2.2⟩
  have hf_inj : Set.InjOn f S := by
    intro u hu v hv same
    have hsu := (hS u).mp hu
    have hsv := (hS v).mp hv
    rw [hf u hsu, hf v hsv] at same
    exact branch_injective hC eval twins hsu hsv same
  have hcap : S.card ≤ B.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hbud_raw := branch_budget hC eval degree houtput
  have hB_card_eq : B.card = (open Classical in ((living (N + N) C).filter (Branch (N + N) C)).card) := by
    congr 1
  have hbud : N + N + B.card ≤ C.size + 1 := by rw [hB_card_eq]; exact hbud_raw
  have hB_eq : B.card = N := by omega
  have hS_eq : S.card = N := by omega
  have hB_img : S.image f = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact hf_maps u hu
    · rw [Finset.card_image_of_injOn hf_inj, hS_eq, hB_eq]
  have hB_deg2 : ∀ b ∈ B, (readers (N + N) C b).card = 2 := by
    intro b hb
    have hge2 : 2 ≤ (readers (N + N) C b).card := (Finset.mem_filter.mp hb).2
    by_contra hne2
    have hge3 : 3 ≤ (readers (N + N) C b).card := by omega
    have hstr_raw := branch_budget_strict hC eval degree houtput
      ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, hge3⟩
    have hstr : N + N + B.card ≤ C.size := by rw [hB_card_eq]; exact hstr_raw
    omega
  have hside := min_cover_one_side I hq hN rows cols hu S hS_hits hS_eq
  have hex_w : ∃ w ∈ S, ∀ v : Fin (N + N), G.Adj w v → v ∉ S := by
    let p0 : Fin N := ⟨0, hNpos⟩
    rcases hside with ⟨hP, hL⟩ | ⟨hL, hP⟩
    · refine ⟨Fin.castAdd N p0, hP p0, ?_⟩
      intro v hv
      induction v using Fin.addCases with
      | left p => exact (adj_ll I p0 p hv).elim
      | right l => exact hL l
    · refine ⟨Fin.natAdd N p0, hL p0, ?_⟩
      intro v hv
      induction v using Fin.addCases with
      | left p => exact hP p
      | right l => exact (adj_rr I p0 l hv).elim
  obtain ⟨w, hwS, hw_nbr_out⟩ := hex_w
  have hwEl : Eligible C w := (hS w).mp hwS
  have h3nbrs : ∃ v1 v2 v3 : Fin (N + N),
      v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧ G.Adj w v1 ∧ G.Adj w v2 ∧ G.Adj w v3 := by
    have hcard3 : 3 ≤ (Finset.univ.filter (fun v : Fin (N + N) => G.Adj w v)).card := by
      induction w using Fin.addCases with
      | left p =>
        have hsub : (Finset.univ.filter (fun l : Fin N => I p l)).image (Fin.natAdd N) ⊆
            Finset.univ.filter (fun v : Fin (N + N) => G.Adj (Fin.castAdd N p) v) := by
          intro v hv
          obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_lr I p l).mpr (Finset.mem_filter.mp hl).2⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ (Fin.natAdd_injective N N), rows p] at h1
        omega
      | right l =>
        have hsub : (Finset.univ.filter (fun p : Fin N => I p l)).image (Fin.castAdd N) ⊆
            Finset.univ.filter (fun v : Fin (N + N) => G.Adj (Fin.natAdd N l) v) := by
          intro v hv
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_rl I l p).mpr (Finset.mem_filter.mp hp).2⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ (Fin.castAdd_injective N N), cols l] at h1
        omega
    let Nw := Finset.univ.filter (fun v : Fin (N + N) => G.Adj w v)
    have hNw3 : 3 ≤ Nw.card := hcard3
    obtain ⟨v1, hv1⟩ := Finset.card_pos.mp (by omega : 0 < Nw.card)
    obtain ⟨v2, hv2⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hv1]; omega : 0 < (Nw.erase v1).card)
    obtain ⟨v3, hv3⟩ := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hv2, Finset.card_erase_of_mem hv1]; omega : 0 < ((Nw.erase v1).erase v2).card)
    have h21 : v2 ≠ v1 := (Finset.mem_erase.mp hv2).1
    have h32 : v3 ≠ v2 := (Finset.mem_erase.mp hv3).1
    have h31 : v3 ≠ v1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hv3).2).1
    exact ⟨v1, v2, v3, h21.symm, h31.symm, h32.symm,
      (Finset.mem_filter.mp hv1).2,
      (Finset.mem_filter.mp (Finset.mem_erase.mp hv2).2).2,
      (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hv3).2).2).2⟩
  obtain ⟨v1, v2, v3, h12, h13, h23, hw1, hw2, hw3⟩ := h3nbrs
  have hmeet : ∀ v : Fin (N + N), G.Adj w v →
      ∃ m a b g, C.gates[m - (N + N)]? = some g ∧ N + N ≤ m ∧
        LNext (N + N) C a m ∧ LNext (N + N) C b m ∧
        Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
        (∀ i ∈ g.inputs, i = a ∨ i = b) ∧ ¬ Carries C w m := by
    intro v hwv
    obtain ⟨p, g, a, b, hg, _, _, ha, hb, hva, hwa, hwb, hvb, h2, hwm⟩ := meeting_gate hC eval (G.adj_symm hwv)
    refine ⟨N + N + p, a, b, g, by simpa using hg, by omega, ha, hb, hva, hwa, hwb, hvb, h2, ?_⟩
    rw [carries_iff hC]
    simp [hwm]
  obtain ⟨m1, a1, b1, g1, hg1, hm1ge, ha1, hb1, hv1a1, hwa1, hwb1, _, h2g1, hwm1⟩ := hmeet v1 hw1
  obtain ⟨m2, a2, b2, g2, hg2, hm2ge, ha2, hb2, hv2a2, hwa2, hwb2, _, h2g2, hwm2⟩ := hmeet v2 hw2
  obtain ⟨m3, a3, b3, g3, hg3, hm3ge, ha3, hb3, hv3a3, hwa3, hwb3, _, h2g3, hwm3⟩ := hmeet v3 hw3
  have hm_ne : ∀ (u1 u2 : Fin (N + N)) (m a b c : ℕ) (g : Gate),
      u1 ≠ u2 → G.Adj w u1 → G.Adj w u2 →
      C.gates[m - (N + N)]? = some g → N + N ≤ m →
      LNext (N + N) C a m → LNext (N + N) C c m →
      Carries C u1 a → ¬ Carries C w a → Carries C w b →
      Carries C u2 c → ¬ Carries C w c →
      (∀ i ∈ g.inputs, i = a ∨ i = b) → False := by
    intro u1 u2 m a b c g hu12 hwu1 hwu2 hgm hmge ham hcm hu1a hwa hwb hu2c hwc h2g
    have hc_in : c ∈ g.inputs := by
      obtain ⟨⟨_, p', g', hg', hm', hmem⟩, _⟩ := hcm
      have hp' : p' = m - (N + N) := by omega
      subst hp'
      rw [hgm] at hg'; cases hg'
      exact hmem
    have hca : c = a := by
      rcases h2g c hc_in with rfl | rfl
      · rfl
      · exact (hwc hwb).elim
    rw [hca] at hu2c
    have hu1_not : ¬ Eligible C u1 := fun h => hw_nbr_out u1 hwu1 ((hS u1).mpr h)
    obtain ⟨w', hu1w', hw'ne⟩ := other u1 w
    have hnot_u2w' : ¬ G.Adj u2 w' := fun h =>
      Plane.no_square I hu u1 u2 w w' hu12 hw'ne.symm hwu1.symm hu1w' hwu2.symm h
    let x := point ({u2, w'} : Finset (Fin (N + N)))
    let y := point (insert u1 ({u2, w'} : Finset (Fin (N + N))))
    have hax : val C x a = true :=
      acts_mono hC (point_mono (by simp)) a ((carries_iff hC).mp hu2c).1
    have hay : val C y a = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) a hax
    have hpath := singleton_path (live_before ham.1 ham.2) hu1a
    have huniq : ∀ k j j', k < a → Carries C u1 k → LNext (N + N) C k j → LNext (N + N) C k j' → j = j' :=
      fun k j j' _ => no_eligible_unique hu1_not k j j'
    have hxy_out : val C x C.output = val C y C.output := by
      by_contra hdiff
      rcases influence hpath huniq (fun _ hi => (point_insert hi).symm) ReflTransGen.refl hdiff with bad | bad
      · exact (Nat.not_lt_of_ge (next_le (live_before ham.1 ham.2))) bad.1
      · exact bad.2 (hax.trans hay.symm)
    have hx0 : val C x C.output = false := point_pair_quiet eval hnot_u2w'
    have hy1 : val C y C.output = true := point_contains_edge hC eval (u := u1) (v := w')
      (by simp) (by simp) hu1w'
    exact Bool.false_ne_true (hx0.symm.trans (hxy_out.trans hy1))
  have hm12 : m1 ≠ m2 := fun h => hm_ne v1 v2 m1 a1 b1 a2 g1 h12 hw1 hw2 hg1 hm1ge ha1 (h ▸ ha2) hv1a1 hwa1 hwb1 hv2a2 hwa2 h2g1
  have hm13 : m1 ≠ m3 := fun h => hm_ne v1 v3 m1 a1 b1 a3 g1 h13 hw1 hw3 hg1 hm1ge ha1 (h ▸ ha3) hv1a1 hwa1 hwb1 hv3a3 hwa3 h2g1
  have hm23 : m2 ≠ m3 := fun h => hm_ne v2 v3 m2 a2 b2 a3 g2 h23 hw2 hw3 hg2 hm2ge ha2 (h ▸ ha3) hv2a2 hwa2 hwb2 hv3a3 hwa3 h2g2
  let bw := firstBranch C w hwEl
  have hbw_spec := firstBranch_spec w hwEl
  have hbw_path : Trace (N + N) C (Carries C w) w.val bw := singleton_path hbw_spec.1 hbw_spec.2.1
  have hstep_from_bw : ∀ (m b : ℕ), LNext (N + N) C b m → Carries C w b → ¬ Carries C w m →
      ∃ r ∈ readers (N + N) C bw, Trace (N + N) C (Carries C w) r m := by
    intro m b hbm hwb hwm
    have hPm : Trace (N + N) C (Carries C w) w.val m :=
      (singleton_path (live_before hbm.1 hbm.2) hwb).tail ⟨hwb, hbm⟩
    rcases align hbw_path (firstBranch_unique w hwEl) m hPm with bad | htail
    · exact (hwm bad.2).elim
    · rcases htail.cases_head with heq | ⟨r, hr, hrest⟩
      · exact (hwm (heq ▸ hbw_spec.2.1)).elim
      · exact ⟨r, mem_readers.mpr hr.2, hrest⟩
  obtain ⟨r1, hr1, hQ1⟩ := hstep_from_bw m1 b1 hb1 hwb1 hwm1
  obtain ⟨r2, hr2, hQ2⟩ := hstep_from_bw m2 b2 hb2 hwb2 hwm2
  obtain ⟨r3, hr3, hQ3⟩ := hstep_from_bw m3 b3 hb3 hwb3 hwm3
  have hbwB : bw ∈ B := by
    have h1 := hf_maps w hwS
    rwa [hf w hwEl] at h1
  have hcard2 : (readers (N + N) C bw).card = 2 := hB_deg2 bw hbwB
  have hpig : r1 = r2 ∨ r1 = r3 ∨ r2 = r3 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨h12', h13', h23'⟩ := hnot
    have hsub : ({r1, r2, r3} : Finset ℕ) ⊆ readers (N + N) C bw := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({r1, r2, r3} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12', h13']), Finset.card_pair h23']
    have hle := Finset.card_le_card hsub
    omega
  have hget_z : ∃ z, bw < z ∧ Live (N + N) C z ∧ Carries C w z ∧ Branch (N + N) C z := by
    rcases hpig with heq | heq | heq
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ2 hm12 hwm1 hwm2
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ3 hm13 hwm1 hwm3
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ2 hQ3 hm23 hwm2 hwm3
      exact ⟨z, (mem_readers.mp hr2).1.1.trans_le hzle, hzl, hzc, hzb⟩
  obtain ⟨z, hbw_lt_z, hzlive, hzcw, hzb⟩ := hget_z
  have hzB : z ∈ B :=
    Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hzlive).trans_lt hlt_out, hzlive⟩, hzb⟩
  rw [← hB_img] at hzB
  obtain ⟨u, huS, hfu⟩ := Finset.mem_image.mp hzB
  have huEl : Eligible C u := (hS u).mp huS
  rw [hf u huEl] at hfu
  have huw_ne : u ≠ w := by
    intro h; subst h
    have : firstBranch C u huEl = bw := rfl
    omega
  have hnot_adj_uw : ¬ G.Adj u w := fun h => hw_nbr_out u h.symm huS
  obtain ⟨a, hua⟩ := degree u
  obtain ⟨b, hub, hba⟩ := other u a
  have hex_vprime : ∃ v', G.Adj u v' ∧ ¬ G.Adj w v' := by
    by_cases hwa : G.Adj w a
    · by_cases hwb : G.Adj w b
      · exact (Plane.no_square I hu u w a b huw_ne hba.symm hua hub hwa hwb).elim
      · exact ⟨b, hub, hwb⟩
    · exact ⟨a, hua, hwa⟩
  obtain ⟨v', huv', hnot_wv'⟩ := hex_vprime
  have hzw : val C (point {w}) z = true := ((carries_iff hC).mp hzcw).1
  have hz1 : val C (point ({w, v'} : Finset (Fin (N + N)))) z = true :=
    acts_mono hC (point_mono (by simp)) z hzw
  have hz2 : val C (point (insert u ({w, v'} : Finset (Fin (N + N))))) z = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) z hz1
  have heq_out := value_at_branch huEl
    (x := point ({w, v'} : Finset (Fin (N + N))))
    (y := point (insert u ({w, v'} : Finset (Fin (N + N)))))
    (fun _ hi => (point_insert hi).symm)
    (by rw [hfu, hz1, hz2])
  have hx0 : val C (point ({w, v'} : Finset (Fin (N + N)))) C.output = false :=
    point_pair_quiet eval hnot_wv'
  have hy1 : val C (point (insert u ({w, v'} : Finset (Fin (N + N))))) C.output = true :=
    point_contains_edge hC eval (u := u) (v := v') (by simp) (by simp) huv'
  exact Bool.false_ne_true (hx0.symm.trans (heq_out.trans hy1))

end PEqualNP.Outside.L_meta_9091.Extra

theorem PEqualNP.Outside.L_meta_9091 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → (3 : ℕ) * x2 ≤ x5.size := by
  intro x1 x2 x3 _ x5 hq hN hline hu hC hInc hRej
  exact PEqualNP.Outside.L_meta_9091.Extra.main_plane_3N x1 x2 x3 x5 hq hN hline hu hC hInc hRej
