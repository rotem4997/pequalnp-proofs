import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The four-input certificate search is adapted from the checked L-meta-1449 proof.

namespace PEqualNP.Outside.L_meta_10586

section ProofPart1
namespace L10586Control
open PEqualNP.CircuitLowerBounds
def edgeData : List ℕ :=
  [0,2,1,3,0,4,1,4,2,4,0,5,2,5,3,5,0,6,1,6,2,6,4,6,5,6]
def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edgeData.length/2, (List.ofFn x).getD (edgeData.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeData.getD (2*i+1) 0) false = true)
private def join (a b : ℕ) : Gate := ⟨.or,[a,b]⟩
private def meet (a b : ℕ) : Gate := ⟨.and,[a,b]⟩
def control : Circuit := ⟨[
  join 0 2, join 4 5, join 8 6, meet 7 9, meet 0 2,
  join 1 5, join 3 6, meet 12 13, join 1 6, meet 4 15,
  join 10 11, join 14 16, join 17 18],19⟩
theorem size : control.gates.length = 13 := rfl
theorem basis : ∀ g ∈ control.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [control,join,meet]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem computes : ∀ x : Fin 7 → Bool, control.eval (List.ofFn x) = target x := by
  decide
theorem replacement_at_thirteen (gs : List Gate) (large : 13 ≤ gs.length) :
    ∃ (gs' : List Gate) (out' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 7 → Bool, (⟨gs',out'⟩ : Circuit).eval (List.ofFn x) = target x :=
  ⟨control.gates,control.output,basis,by simpa only [size] using large,computes⟩
end L10586Control
end ProofPart1

section ProofPart2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace L11022RestrictSupport
namespace BranchGraph
variable {V : Type*} [DecidableEq V]
def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, G.Adj a b
omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w} := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab
lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w} ↔ G.Adj u w := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, by simp, w, by simp, h⟩
def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b
section FiniteGraph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ v ∉ removed)
lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u := by
  intro v membership
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at membership ⊢
  exact ⟨membership.1, fun vIn => membership.2 (h vIn)⟩
lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w := by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B) := by
    ext z
    simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => ⟨⟨hz.1, fun zIn => hz.2 (h zIn)⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [e u, e w, same]
def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group, ∀ w ∈ group, (neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w
def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)
def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed ∧ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed ∧ neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅
def closeIsolates (removed : Finset V) : Finset V := removed ∪ isolates G removed
def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)
lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root := by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty := by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root) := by
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu
theorem dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V, A ∪ Q ⊆ removeClass G B root := by
  classical
  by_cases someActive : ∃ root ∈ Q, root ∉ B ∧ (neighborsAfter G B root).Nonempty
  · obtain ⟨root, rootQ, rootOut, rootLive⟩ := someActive
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU := live.mono (neighborsAfter_subset G smaller u)
      have oldRoot := rootLive.mono (neighborsAfter_subset G smaller root)
      have same := neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root := by simp [maximalClass, rootOut, rootLive, uIn, same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V := Classical.choice inferInstance
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u, hu, uIn, live⟩)
lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty := by
  have uOut : u ∉ removed := fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty := by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v, hv⟩ := old
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨v, ?_⟩
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hv.1, fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v := by
      simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv.1.symm, uOut⟩
    have none : neighborsAfter G removed v = ∅ := by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness
lemma closeIsolates_idempotent (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed := by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live := retained_after_close G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅ := by
      simpa [isolates] using isolated
    simp [noNeighbors] at live
  · exact Finset.subset_union_left
def TwinSteps : Finset V → List (Finset V) → Prop
  | _, [] => True
  | removed, group :: rest => TwinGroup G removed group ∧ TwinSteps (removed ∪ group) rest
def removedThrough : Finset V → List (Finset V) → Finset V
  | removed, [] => removed
  | removed, group :: rest => removedThrough (removed ∪ group) rest
def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0, start, finish => finish = start
  | k + 1, start, finish => ∃ root : V, ClassSteps k (removeClass G start root) finish
theorem dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V, ClassSteps G groups.length B finish ∧ removedThrough A groups ⊆ finish := by
  induction groups generalizing A B with
  | nil => exact ⟨B, rfl, smaller⟩
  | cons group rest ih =>
    obtain ⟨twins, next⟩ := steps
    obtain ⟨root, subset⟩ := dominates_step G smaller twins
    obtain ⟨finish, walk, covered⟩ := ih subset next
    exact ⟨finish, ⟨root, walk⟩, covered⟩
def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v, u ∉ removed → v ∉ removed → ¬ G.Adj u v
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B := by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))
lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ := by
  ext u
  simp only [Finset.mem_univ, iff_true]
  by_contra out
  obtain ⟨v, hv⟩ := retained_after_close G out
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact noEdges u v out hv.2 hv.1
lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V, start = closeIsolates G D) : ∃ D : Finset V, finish = closeIsolates G D := by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root, after⟩ := walk
    exact ih after ⟨_, rfl⟩
theorem covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ := by
  obtain ⟨D, steps, subset⟩ := dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges := edgeless_mono G subset finished
  obtain ⟨A, hD⟩ := classSteps_finish_closed G steps ⟨∅, rfl⟩
  rw [hD] at noEdges
  rwa [hD, closed_edgeless_all G noEdges] at steps
end FiniteGraph
end BranchGraph
namespace BranchGroupsLean
open BranchGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}
def bucket (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v = r)
def below (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v < r)
def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)
omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅ := by
  ext v
  simp [coveredBy]
lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r := by
  ext v
  simp [coveredBy, bucket, List.mem_append]
omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V, label v = out ∨ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r := by
  have facts := List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy, below, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after := (List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim
section Graph
variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots, r < out)
    (twinAt : ∀ r ∈ roots, TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)) := by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots := complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev := covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next := ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_, ?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next
lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending) := by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton, ih]
    simp [List.append_assoc]
omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))) := by
  rw [← coveredBy_nil label, removedThrough_coveredBy, List.nil_append]
  intro u v uNot vNot
  have hu : label u = out := (allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out := (allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket, hu]) v (by simp [bucket, hv])
theorem roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches, r < out)
    (twinAt : ∀ r ∈ branches, TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V), TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card := by
  let roots := branches.sort
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out ∨ label v ∈ roots := by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out := beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)) := by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last := no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last
end Graph
end BranchGroupsLean
namespace CircuitHelpers
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
end CircuitHelpers
namespace CircuitHelpers
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
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
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
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
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
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
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
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
end CircuitHelpers
namespace CircuitHelpers
open PEqualNP.CircuitLowerBounds
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)
def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]
theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]
theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this
end CircuitHelpers
namespace CircuitHelpers
open PEqualNP.CircuitLowerBounds
theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]
theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega
theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false
theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩
theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]
theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1
theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this
end CircuitHelpers
namespace CircuitHelpers
open PEqualNP.CircuitLowerBounds
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)
theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this
theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)
theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]
theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]
theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]
theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)
theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩
theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]
theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)
theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c
end CircuitHelpers
namespace CircuitHelpers
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false
theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩
theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))
theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'
theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]
theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c
theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)
theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm
theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm
theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]
theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩
theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h
end CircuitHelpers
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitHelpers
def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut
theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different
theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches
theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)
def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)
def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs
theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha
private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩
theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di
theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩
end PetersenCutTrace
namespace CircuitHelpers.PermInputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false
theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)
theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this
theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]
theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''
end CircuitHelpers.PermInputs
namespace CircuitHelpers.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers.PermInputs
theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := CircuitHelpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''
end CircuitHelpers.Forest
namespace CircuitHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers
open CircuitHelpers.PermInputs
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x
abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b
def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'
def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)
def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q
structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs
theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩
theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩
theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw
theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1
theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl
theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩
section LocalSection1
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩
theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega
theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
end LocalSection1
theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm
theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _
theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2
section LocalSection2
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  CircuitHelpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS
theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this
theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this
theorem Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this
theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩
theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩
theorem Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega
theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩
end LocalSection2
end CircuitHelpers.Readers
namespace CircuitHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers
theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _
section LocalSection1
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
end LocalSection1
section LocalSection2
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)
theorem Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc
theorem Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc
theorem Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩
theorem Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩
end LocalSection2
end CircuitHelpers.Readers
namespace CircuitHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers
theorem lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp
theorem set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]
theorem set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]
theorem set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]
section LocalSection1
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h
theorem Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩
theorem Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
end LocalSection1
end CircuitHelpers.Readers
namespace CircuitHelpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers
theorem fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf
theorem fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩
end CircuitHelpers.Readers
namespace CircuitHelpers.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHelpers
open CircuitHelpers.Readers CircuitHelpers.PermInputs
open CircuitHelpers.Forest
theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
theorem pq2f_ne_pair {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) : a ≠ b := by
  rcases hin with h | h
  · exact pq2f_nodup L hnc hg hop h
  · exact (pq2f_nodup L hnc hg hop h).symm
end CircuitHelpers.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open CircuitHelpers.RunAsm
theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p, Reads gs p w := by
  by_cases isInput : w < n
  · let v : Fin n := ⟨w, isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p := w - n
    have wire : w = n + p := by dsimp [p]; omega
    have pLt : p < gs.length := by omega
    have notOut : out ≠ n + p := by omega
    obtain ⟨q, _, read⟩ := least.live nonconstant p pLt notOut
    exact ⟨q, wire.symm ▸ read⟩
theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]
theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length := by
  obtain ⟨p, g, hit, reads⟩ := least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound := (List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p, g, hit, reads, by omega⟩
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitHelpers CircuitHelpers.Readers
def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []
theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]
theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]
theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate
theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega
theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact L11022RestrictSupport.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have := b.isLt; omega))
  · simp [predecessors, internal]
end PetersenCutTrace
namespace PetersenScratch
open PEqualNP.MetaComplexity
def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q
def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p
def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k
def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)
def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b
noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q
noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)
private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]
private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]
def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b
private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩
private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩
private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)
private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢
private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl
private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]
private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq
theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all
noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩
private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w, x w = true → w = u ∨ w = v) :
    edgeValue G x = false := by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s, t, es, hs, ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es
private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a && b) := by
  cases a <;> cases b
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u := j) (v := j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput, h.ne.symm])
private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i ≠ j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u ∨ k = v)) a b) = (a || b) := by
  have hu : pairInput i j (fun k => decide (k = u ∨ k = v)) a b u = true := by
    simp [pairInput, hiu.ne.symm, huj]
  have hv : pairInput i j (fun k => decide (k = u ∨ k = v)) a b v = true := by
    simp [pairInput, hvi, hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput, hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu
theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool, ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False := by
  obtain ⟨outerA, ha⟩ := factors (fun _ => false)
  obtain ⟨outerO, ho⟩ := factors (fun k => decide (k = u ∨ k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))
end PetersenScratch
namespace PetersenCutFormula
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitHelpers
open PetersenScratch
def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)
theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]
def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption
theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]
private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]
private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]
private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]
theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl
theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]
theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl
end PetersenCutFormula
namespace PetersenCutIndependent
open PEqualNP.CircuitLowerBounds
open CircuitHelpers
open PetersenCutFormula PetersenCutTrace PetersenScratch
theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]
theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked
theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False := by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f, hf⟩ := cut_factors hcl cut out (fun k => k = i ∨ k = j) base controlled
  refine ⟨f, fun a b => ?_⟩
  have agree : ∀ k, ¬ (k = i ∨ k = j) → pairInput i j base a b k = base k := by
    intro k hk
    simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)
end PetersenCutIndependent
namespace FirstBranchRoute
open Relation
variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)
def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b
def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v
def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v
lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)
variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)
include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩
include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB
noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)
theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1
theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2
theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl
theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)
include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))
lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))
theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩
theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut
lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _
theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after
include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB
theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)
lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩
lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)
section Count
variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)
include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge
include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)
end Count
end FirstBranchRoute
namespace PetersenFirstGroup
open PEqualNP.CircuitLowerBounds
open CircuitHelpers
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch
noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut
theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]
theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w
theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl
theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path
theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j, G.Adj i j → ∃ u v,
      G.Adj i u ∧ G.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adjacent
  obtain ⟨u, v, hiu, hjv, huj, hvi, huv⟩ := witnesses i j adjacent
  have iFirst := (mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst := (mem_firstInputGroup clean out live cut j).mp jIn
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))
end PetersenFirstGroup
namespace PetersenGroupBFS
structure MaskGraph where
  width : Nat
  adjacency : Nat → Nat
def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex
def fullMask (g : MaskGraph) : Nat :=
  bit g.width - 1
def residualNeighbors (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (fullMask g) deleted)
def closeIsolates (g : MaskGraph) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if residualNeighbors g deleted v = 0 then Nat.lor mask (bit v) else mask)
    deleted
def twinClass (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (residualNeighbors g deleted v == residualNeighbors g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0
theorem bit_at (v w : Nat) : (bit v).testBit w = decide (v = w) := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]
theorem full_at (g : MaskGraph) (w : Nat) :
    (fullMask g).testBit w = decide (w < g.width) := by
  simp [fullMask, bit, Nat.shiftLeft_eq]
theorem neighbor_at (g : MaskGraph) (deleted v w : Nat) (hw : w < g.width) :
    (residualNeighbors g deleted v).testBit w =
      ((g.adjacency v).testBit w && !(deleted.testBit w)) := by
  simp [residualNeighbors, Nat.testBit_xor, full_at, hw]
private theorem fold_mask_at (vertices : List Nat) (p : Nat → Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w || (vertices.any fun v => decide (p v) && (v == w))) := by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h, bit_at, Bool.or_assoc, Bool.beq_eq_decide_eq]
private theorem any_mask_at (p : Nat → Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v) && (v == w)) =
      (decide (w < n) && decide (p w)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.and_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨v, hv, hp, rfl⟩
    exact ⟨hv, hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨w, hw, hp, rfl⟩
theorem close_at (g : MaskGraph) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w || (decide (w < g.width) && decide (residualNeighbors g deleted w = 0))) := by
  unfold closeIsolates
  rw [fold_mask_at, any_mask_at]
theorem class_at (g : MaskGraph) (deleted v w : Nat) :
    (twinClass g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w) && (residualNeighbors g deleted w == residualNeighbors g deleted v))) := by
  unfold twinClass
  rw [fold_mask_at, any_mask_at]
  simp [Bool.beq_eq_decide_eq]
theorem bit_eq_power (width : Nat) : bit width = 2 ^ width := by
  simp [bit, Nat.shiftLeft_eq]
theorem lor_bounded {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width := by
  rw [bit_eq_power] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb
theorem high_false {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false := by
  rw [bit_eq_power] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))
theorem mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width, a.testBit w = b.testBit w) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [high_false ha (Nat.le_of_not_gt hw), high_false hb (Nat.le_of_not_gt hw)]
theorem neighbor_bounded (g : MaskGraph) (deleted v : Nat) (hd : deleted < bit g.width) :
    residualNeighbors g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [residualNeighbors, full_at, Nat.not_lt_of_ge hw, high_false hd hw]
theorem close_bounded (g : MaskGraph) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at, Nat.not_lt_of_ge hw, high_false hd hw]
theorem class_bounded (g : MaskGraph) (deleted v : Nat) :
    twinClass g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at, Nat.not_lt_of_ge hw]
def step (g : MaskGraph) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v) && (residualNeighbors g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (twinClass g deleted v)))
    else none
def frontier (g : MaskGraph) : Nat → List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((frontier g depth).flatMap (step g)).eraseDups
theorem advance {g : MaskGraph} {depth deleted next : Nat}
    (hd : deleted ∈ frontier g depth) (hs : next ∈ step g deleted) :
    next ∈ frontier g (depth + 1) := by
  rw [frontier, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨deleted, hd, hs⟩
theorem stay {g : MaskGraph} {depth deleted : Nat} (hd : deleted ∈ frontier g depth) :
    deleted ∈ frontier g (depth + 1) :=
  advance hd (by simp [step])
theorem advance_class {g : MaskGraph} {depth deleted vertex : Nat}
    (hd : deleted ∈ frontier g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : residualNeighbors g deleted vertex ≠ 0) :
    closeIsolates g (Nat.lor deleted (twinClass g deleted vertex)) ∈ frontier g (depth + 1) := by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex, List.mem_range.mpr hv, ?_⟩
  simp [hlive, hne]
end PetersenGroupBFS
namespace PetersenMaskBridge
open PetersenGroupBFS
open BranchGraph
def decode (g : MaskGraph) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)
@[simp] lemma mem_decode (g : MaskGraph) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask ↔ mask.testBit v.val = true := by
  simp [decode]
@[simp] lemma decode_zero (g : MaskGraph) : decode g 0 = ∅ := by
  ext v
  simp
@[simp] lemma decode_full (g : MaskGraph) : decode g (fullMask g) = Finset.univ := by
  ext v
  simp [full_at, v.isLt]
lemma decode_or (g : MaskGraph) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b := by
  ext v
  simp [Bool.or_eq_true]
lemma decode_inj (g : MaskGraph) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b := by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w, hw⟩ : Fin g.width) ∈ decode g a ↔ (⟨w, hw⟩ : Fin g.width) ∈ decode g b := by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm
lemma bit_pos (n : Nat) : 0 < bit n := by
  rw [bit_eq_power]
  exact Nat.two_pow_pos n
lemma full_bounded (g : MaskGraph) : fullMask g < bit g.width := by
  unfold fullMask
  have := bit_pos g.width
  omega
section Graph
variable (g : MaskGraph) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width, G.Adj u v ↔ (g.adjacency u.val).testBit v.val = true)
include adj in
lemma decode_neighbors (deleted : Nat) (u : Fin g.width) :
    decode g (residualNeighbors g deleted u.val) = neighborsAfter G (decode g deleted) u := by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode, neighborsAfter, neighbor_at g deleted u.val v.val v.isLt, adj, h]
include adj in
lemma residual_zero_iff (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    residualNeighbors g deleted u.val = 0 ↔ neighborsAfter G (decode g deleted) u = ∅ := by
  constructor
  · intro h
    rw [← decode_neighbors g G adj, h, decode_zero]
  · intro h
    apply decode_inj g (neighbor_bounded g deleted u.val bound) (bit_pos g.width)
    rw [decode_neighbors g G adj, h, decode_zero]
include adj in
lemma decode_close (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted) := by
  ext v
  simp [close_at, v.isLt, BranchGraph.closeIsolates, isolates, Bool.or_eq_true,
    residual_zero_iff g G adj deleted bound]
include adj in
lemma decode_class (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (twinClass g deleted root.val) = maximalClass G (decode g deleted) root := by
  have same (u : Fin g.width) : residualNeighbors g deleted u.val = residualNeighbors g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root := by
    rw [← decode_neighbors g G adj deleted u, ← decode_neighbors g G adj deleted root]
    exact ⟨congrArg (decode g), decode_inj g (neighbor_bounded g deleted u.val bound)
      (neighbor_bounded g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at, v.isLt, maximalClass, outside, live, h, same, Bool.beq_eq_decide_eq]
def Represented (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m, m ∈ frontier g depth ∧ m < bit g.width ∧ decode g m = removed
include adj in
lemma initial_rep : Represented g 0 (BranchGraph.closeIsolates G ∅) := by
  refine ⟨PetersenGroupBFS.closeIsolates g 0, ?_,
    close_bounded g 0 (bit_pos g.width), ?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [decode_close g G adj _ (bit_pos g.width), decode_zero]
include adj in
lemma advance_rep {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : Represented g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    Represented g (depth + 1) (removeClass G removed root) := by
  obtain ⟨m, hm, bounded, same⟩ := rep
  subst removed
  by_cases active : root ∉ decode g m ∧ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false := by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : residualNeighbors g m root.val ≠ 0 := by
      intro h
      have none := (residual_zero_iff g G adj m bounded root).mp h
      simpa [none] using active.2
    have united := lor_bounded bounded (class_bounded g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (twinClass g m root.val)),
      advance_class hm root.isLt live someNeighbor, close_bounded g _ united, ?_⟩
    rw [decode_close g G adj _ united, decode_or, decode_class g G adj m bounded root active.1 active.2,
      removeClass]
  · have sameRemoval : removeClass G (decode g m) root = decode g m := by
      have emptyClass : maximalClass G (decode g m) root = ∅ := ite_eq_right active
      simp only [removeClass, emptyClass, Finset.union_empty, closed]
    exact ⟨m, stay hm, bounded, sameRemoval.symm⟩
include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : ClassSteps G count start finish) (initial : Represented g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : Represented g (depth + count) finish := by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk, Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root, next⟩ := walk
    have nextClosed : BranchGraph.closeIsolates G (removeClass G start root) = removeClass G start root :=
      closeIsolates_idempotent G _
    have rest := ih next (advance_rep g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using rest
lemma frontier_up {m k r : Nat} (reached : m ∈ frontier g k) (budget : k ≤ r) : m ∈ frontier g r := by
  induction r with
  | zero =>
    have : k = 0 := by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))
include adj in
theorem groups_exceed_budget [Nonempty (Fin g.width)] (k : Nat) (noFinish : fullMask g ∉ frontier g k)
    (groups : List (Finset (Fin g.width))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : k < groups.length := by
  by_contra! budget
  have walk := covering_sequence_reaches_univ G groups twins finished
  obtain ⟨m, reached, bound, allGone⟩ :=
    simulate g G adj walk (initial_rep g G adj) (closeIsolates_idempotent G ∅)
  have equal : m = fullMask g := decode_inj g bound (full_bounded g) (by simpa using allGone)
  rw [equal, Nat.zero_add] at reached
  exact noFinish (frontier_up g reached budget)
end Graph
end PetersenMaskBridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open scoped BigOperators
def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs
def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length
theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩
theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega
theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]
theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound
theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega
theorem one_not_gate_positive {gs : List Gate} (notUsed : ∃ g ∈ gs, g.op = GateOp.not) :
    1 ≤ notGateCount gs := by
  obtain ⟨g, mem, tag⟩ := notUsed
  have kept : g ∈ gs.filter (fun q => isNotGate q.op) :=
    List.mem_filter.mpr ⟨mem, by simp [isNotGate, tag]⟩
  have pos := List.length_pos_of_mem kept
  exact pos
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open PetersenCutTrace
theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length), w ≠ (⟨out, outValid⟩ : Fin (n + gs.length)) → ∃ v, readEdge gs w v := by
  intro w notOutput
  have notSame : w.val ≠ out := fun eq => notOutput (Fin.ext eq)
  obtain ⟨p, g, atSlot, reads, bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p, bound⟩, p, g, atSlot, rfl, reads⟩
theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))
noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w
theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]
def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut
def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut
theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]
theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]
theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds CircuitHelpers
open Relation
theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)
end PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitHelpers
open PetersenCutTrace Relation
def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)
theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]
open PEqualNP.CircuitLowerBounds CircuitHelpers
open PetersenCutTrace
theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n), vl gs (setInput S) out.val = true ↔ BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code, decode, factors⟩ := finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)
end L11022RestrictSupport
end ProofPart2

section ProofPart3
namespace L11022RestrictSupport
open PEqualNP.CircuitLowerBounds
open CircuitHelpers
open PetersenCutTrace Relation
theorem fixed_context_branch_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (fixed : Finset (Fin n)) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool,
      ∀ I J O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) →
        (∀ j ∈ J, label j = cut) →
        (∀ i ∈ O, cut < label i) →
        code I = code J →
        vl gs (setInput ((fixed ∪ I) ∪ O)) out.val =
          vl gs (setInput ((fixed ∪ J) ∪ O)) out.val := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput (fixed ∪ I)) cut.val
  refine ⟨code, ?_⟩
  intro I J O groupI groupJ afterO sameCode
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ j ∈ J, label j = cut) at groupJ
  change (∀ i ∈ O, cut < label i) at afterO
  have stable (K : Finset (Fin n)) :
      vl gs (setInput ((fixed ∪ K) ∪ O)) cut.val = code K := by
    apply agree_on_input_ancestors clean
    intro i ancestral
    have limit : label i ≤ cut :=
      FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
    have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
    simp [setInput, absent]
  have sameCut : vl gs (setInput ((fixed ∪ I) ∪ O)) cut.val =
      vl gs (setInput ((fixed ∪ J) ∪ O)) cut.val :=
    (stable I).trans (sameCode.trans (stable J).symm)
  by_cases atOutput : cut = out
  · simpa only [atOutput] using sameCut
  have before : cut < out := lt_of_le_of_ne prior atOutput
  apply circuit_cut_agreement clean cut out _ _ sameCut
  intro i diff
  have isGroup : label i = cut := by
    by_contra offGroup
    have notI : i ∉ I := fun mem => offGroup (groupI i mem)
    have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
    exact diff (by simp [setInput, notI, notJ])
  intro bypass
  have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
      (inputWire gs i) = cut := isGroup
  have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
    (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
  apply forbid
  have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
    fun _ _ h => ⟨h.1, h.2.1⟩
  have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
    ReflTransGen.mono weaker _ _ bypass
  simpa only [groupLabel] using convert
theorem three_residuals_repeat {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (fixed I J K : Finset (Fin n)) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    let residual (activation O : Finset (Fin n)) :=
      vl gs (setInput ((fixed ∪ activation) ∪ O)) out.val
    (∀ i ∈ I, label i = cut) →
    (∀ j ∈ J, label j = cut) →
    (∀ k ∈ K, label k = cut) →
      ((∀ O : Finset (Fin n), (∀ i ∈ O, cut < label i) → residual I O = residual J O) ∨
       (∀ O : Finset (Fin n), (∀ i ∈ O, cut < label i) → residual I O = residual K O) ∨
       (∀ O : Finset (Fin n), (∀ i ∈ O, cut < label i) → residual J O = residual K O)) := by
  intro label residual hI hJ hK
  obtain ⟨code, factor⟩ := fixed_context_branch_factor clean out live cut prior terminal fixed
  have pair : code I = code J ∨ code I = code K ∨ code J = code K := by
    cases hA : code I <;> cases hB : code J <;> cases hC : code K <;> decide
  rcases pair with eq | eq | eq
  · exact Or.inl (fun O hO => factor I J O hI hJ hO eq)
  · exact Or.inr (Or.inl (fun O hO => factor I K O hI hK hO eq))
  · exact Or.inr (Or.inr (fun O hO => factor J K O hJ hK hO eq))
end L11022RestrictSupport
end ProofPart3

section ProofPart4
namespace L10586Branch
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open PetersenCutTrace PetersenFirstGroup L10586Control
abbrev V := Fin 7
def edges : List (V × V) :=
  [(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(2,5),(3,5),(0,6),(1,6),(2,6),(4,6),(5,6)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem target_eq_edges : ∀ x : V → Bool,
    target x = edges.any (fun e => x e.1 && x e.2) := by decide
theorem loopless : ∀ e ∈ edges, e.1 ≠ e.2 := by decide
def graph : SimpleGraph V where
  Adj a b := (a,b) ∈ edges ∨ (b,a) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => loopless (v,v) he rfl)
    (fun he => loopless (v,v) he rfl)⟩
instance graphDecidable : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ edges ∨ (b,a) ∈ edges))
private def adjB (u v : V) : Bool :=
  ((#[116,88,113,34,71,77,55] : Array Nat)[u.val]?.getD 0).testBit v.val
private theorem adj_spec : ∀ u v : V, adjB u v = true ↔ graph.Adj u v := by decide
private def independentB (s : Finset V) : Bool :=
  (List.finRange 7).all fun u => (List.finRange 7).all fun v =>
    if u ∈ s ∧ v ∈ s then !(adjB u v) else true
private def hasNeighbor (s : Finset V) (u : V) : Bool :=
  (List.finRange 7).any fun v => decide (v ∈ s) && adjB u v
private def twinsB (tail group : Finset V) : Bool :=
  (List.finRange 7).all fun u => (List.finRange 7).all fun v =>
    if u ∈ group ∧ v ∈ group then
      !(hasNeighbor tail u) || !(hasNeighbor tail v) ||
        (List.finRange 7).all (fun w => if w ∈ tail then adjB u w == adjB v w else true)
    else true
private def allowed (rem group : Finset V) : Bool :=
  let tail := rem \ group
  independentB group && twinsB tail group &&
    !decide ((1 ∈ group ∧ 5 ∈ group ∧ 3 ∈ tail) ∨ (6 ∈ group ∧ 3 ∈ group ∧ 5 ∈ tail))
def frontier : ℕ → Finset (Finset V)
  | 0 => {Finset.univ}
  | k+1 => (frontier k).biUnion fun rem =>
      ((rem.powerset.filter fun group => allowed rem group = true).image fun group => rem \ group)
set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem no_four_finished : (frontier 4).filter (fun s => independentB s = true) = ∅ := by
  decide +kernel
private theorem independent_accept {s : Finset V} (h : BranchGraph.Independent graph s) :
    independentB s = true := by
  rw [independentB,List.all_eq_true]
  intro u _
  rw [List.all_eq_true]
  intro v _
  by_cases both : u ∈ s ∧ v ∈ s
  · rw [ite_eq_left both]
    cases bit : adjB u v
    · rfl
    · exact (h u both.1 v both.2 ((adj_spec u v).mp bit)).elim
  · simp [both]
private theorem hasNeighbor_iff (s : Finset V) (u : V) :
    hasNeighbor s u = true ↔ ∃ v ∈ s, graph.Adj u v := by
  simp [hasNeighbor,List.any_eq_true,Bool.and_eq_true,adj_spec]
private theorem twins_accept (tail group : Finset V)
    (twins : ∀ u ∈ group, ∀ v ∈ group,
      (∃ a ∈ tail, graph.Adj u a) → (∃ b ∈ tail, graph.Adj v b) →
      ∀ w ∈ tail, (graph.Adj u w ↔ graph.Adj v w)) :
    twinsB tail group = true := by
  rw [twinsB,List.all_eq_true]
  intro u _
  rw [List.all_eq_true]
  intro v _
  by_cases both : u ∈ group ∧ v ∈ group
  · rw [ite_eq_left both]
    cases hu : hasNeighbor tail u
    · rfl
    · cases hv : hasNeighbor tail v
      · rfl
      · simp only [Bool.not_true,Bool.false_or]
        rw [List.all_eq_true]
        intro w _
        by_cases relevant : w ∈ tail
        · rw [ite_eq_left relevant,beq_iff_eq,Bool.eq_iff_iff,adj_spec,adj_spec]
          exact twins u both.1 v both.2 ((hasNeighbor_iff _ _).mp hu) ((hasNeighbor_iff _ _).mp hv) w relevant
        · simp [relevant]
  · simp [both]
private theorem allowed_of (rem group : Finset V) (independent : BranchGraph.Independent graph group)
    (twins : ∀ u ∈ group, ∀ v ∈ group,
      (∃ a ∈ rem \ group, graph.Adj u a) →
      (∃ b ∈ rem \ group, graph.Adj v b) →
      ∀ w ∈ rem \ group, (graph.Adj u w ↔ graph.Adj v w))
    (safe : ¬ ((1 ∈ group ∧ 5 ∈ group ∧ 3 ∈ rem \ group) ∨
      (6 ∈ group ∧ 3 ∈ group ∧ 5 ∈ rem \ group))) : allowed rem group = true := by
  simp only [allowed,independent_accept independent,twins_accept _ _ twins,decide_eq_false safe,
    Bool.not_false,Bool.and_self]
private theorem frontier_step {k : ℕ} {rem group : Finset V}
    (visited : rem ∈ frontier k) (sub : group ⊆ rem)
    (ok : allowed rem group = true) : rem \ group ∈ frontier (k+1) := by
  rw [frontier]
  exact Finset.mem_biUnion.mpr ⟨rem,visited,Finset.mem_image.mpr
    ⟨group,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,ok⟩,rfl⟩⟩
private theorem frontier_extend {k n : ℕ} {rem : Finset V}
    (bound : k ≤ n) (visited : rem ∈ frontier k) : rem ∈ frontier n := by
  induction bound with
  | refl => exact visited
  | step _ ih =>
    have pad : allowed rem ∅ = true := by simp [allowed,independentB,twinsB,List.all_eq_true]
    simpa using frontier_step ih (Finset.empty_subset rem) pad
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem alternate_neighbors :
    ∀ i j : V, graph.Adj i j →
      ∃ u v, graph.Adj i u ∧ graph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ graph.Adj u v := by decide
theorem target_edges (x : V → Bool) :
    target x = true ↔ ∃ u v : V, graph.Adj u v ∧ x u = true ∧ x v = true := by
  rw [target_eq_edges, List.any_eq_true]
  simp only [Bool.and_eq_true, Prod.exists]
  constructor
  · rintro ⟨a, b, e, ha, hb⟩
    exact ⟨a, b, Or.inl e, ha, hb⟩
  · rintro ⟨a, b, e, ha, hb⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at e
    rcases e with e | e
    · exact ⟨a, b, e, ha, hb⟩
    · exact ⟨b, a, e, hb, ha⟩
theorem marked_edges (S : Finset V) :
    target (setInput S) = true ↔ BranchGraph.containsEdge graph S := by
  rw [target_edges]
  simp only [setInput, decide_eq_true_eq, BranchGraph.containsEdge]
  constructor
  · rintro ⟨u, v, e, hu, hv⟩
    exact ⟨u, hu, v, hv, e⟩
  · rintro ⟨u, hu, v, hv, e⟩
    exact ⟨u, v, e, hu, hv⟩
private theorem dependency_samples : ∀ v : V, ∃ w : V,
    target (Function.update (fun u => decide (u = w)) v
      (!(decide (v = w)))) ≠ target (fun u => decide (u = w)) := by decide
theorem dependent (v : V) : Dep target v := by
  obtain ⟨w, h⟩ := dependency_samples v
  exact ⟨fun u => decide (u = w), h⟩
theorem nonconstant : ∃ x y : V → Bool, target x ≠ target y :=
  ⟨fun _ => false, fun _ => true, by decide⟩
private theorem restrict_samples : ∀ (v : V) (b : Bool),
    target (Function.update (fun _ => false) v b) ≠
      target (Function.update (fun _ => true) v b) := by decide
theorem restrict_nonconstant (v : V) (b : Bool) :
    ∃ x y, target (Function.update x v b) ≠ target (Function.update y v b) :=
  ⟨fun _ => false, fun _ => true, restrict_samples v b⟩
theorem output_valid {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    out < 7 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)
def leastOutputWire {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    Fin (7 + gs.length) :=
  ⟨out, output_valid least⟩
theorem leastReadsLive {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    ∀ w, w ≠ leastOutputWire least → ∃ q, readEdge gs w q :=
  least_read_edge_live least nonconstant dependent restrict_nonconstant (output_valid least)
noncomputable def leastLabel {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    V → Fin (7 + gs.length) :=
  firstInputBoundary least.hcl (leastOutputWire least) (leastReadsLive least)
noncomputable def occupiedBranchWires {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    Finset (Fin (7 + gs.length)) :=
  (Finset.univ.image (leastLabel least)).erase (leastOutputWire least)
theorem occupied_subset {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    occupiedBranchWires least ⊆ circuitBranchWires (n := 7) gs := by
  intro r hr
  obtain ⟨notOut, seen⟩ := Finset.mem_erase.mp hr
  obtain ⟨v, _, chosen⟩ := Finset.mem_image.mp seen
  subst r
  have stopped := FirstBranchRoute.first_stops (readEdge gs) (leastOutputWire least)
    (read_order least.hcl) (leastReadsLive least) (inputWire gs v)
  exact in_circuit_branches.mpr (stopped.resolve_left notOut)
private theorem context_conflict {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (a b probe : V) (same : leastLabel least a = leastLabel least b)
    (later : leastLabel least a < leastLabel least probe)
    (fixed : Finset V)
    (zero : target (setInput fixed) = false)
    (activeA : target (setInput (fixed ∪ {a})) = true)
    (activeB : target (setInput (fixed ∪ {b})) = false)
    (probeAlone : target (setInput (fixed ∪ {probe})) = false)
    (probeB : target (setInput ((fixed ∪ {b}) ∪ {probe})) = true) : False := by
  let cut := leastLabel least a
  let output := leastOutputWire least
  have live := leastReadsLive least
  have stop : FirstBranchRoute.Terminal (readEdge gs) output cut :=
    FirstBranchRoute.first_stops (readEdge gs) output (read_order least.hcl) live (inputWire gs a)
  have agree := three_residuals_repeat least.hcl output live cut
    (wire_le_output least.hcl output live cut) stop fixed ∅ {a} {b}
    (by simp) (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; rfl)
    (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact same.symm)
  rcases agree with ea | eb | ab
  · have eq := ea ∅ (by simp)
    change vl gs (setInput ((fixed ∪ ∅) ∪ ∅)) out =
      vl gs (setInput ((fixed ∪ {a}) ∪ ∅)) out at eq
    rw [least.hev,least.hev] at eq
    simp only [Finset.union_empty,zero,activeA,Bool.false_eq_true] at eq
  · have eq := eb {probe} (by intro i hi; rw [Finset.mem_singleton] at hi; subst i; exact later)
    change vl gs (setInput ((fixed ∪ ∅) ∪ {probe})) out =
      vl gs (setInput ((fixed ∪ {b}) ∪ {probe})) out at eq
    rw [least.hev,least.hev] at eq
    simp only [Finset.union_empty,probeAlone,probeB,Bool.false_eq_true] at eq
  · have eq := ab ∅ (by simp)
    change vl gs (setInput ((fixed ∪ {a}) ∪ ∅)) out =
      vl gs (setInput ((fixed ∪ {b}) ∪ ∅)) out at eq
    rw [least.hev,least.hev] at eq
    simp only [Finset.union_empty,activeA,activeB,Bool.true_eq_false] at eq
private theorem no_finish (states : Finset (Finset V))
    (empty : states.filter (fun s => independentB s = true) = ∅)
    (s : Finset V) (seen : s ∈ states) (independent : independentB s = true) : False := by
  have member := (Finset.mem_filter (s := states) (p := fun s => independentB s = true)).mpr
    ⟨seen,independent⟩
  rw [empty] at member
  exact Finset.notMem_empty _ member
set_option maxRecDepth 16384 in
theorem least_five_occupied_branches {gs : List Gate} {out : ℕ} (least : Least 7 target gs out) :
    5 ≤ (occupiedBranchWires least).card := by
  classical
  by_contra! few
  let outWire := leastOutputWire least
  let live := leastReadsLive least
  let label := leastLabel least
  let branches := occupiedBranchWires least
  let roots := branches.sort
  let remains (done : List (Fin (7 + gs.length))) := (BranchGroupsLean.coveredBy label done)ᶜ
  have computes (x : V → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue graph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, target_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (s : Finset V) : vl gs (setInput s) outWire.val = true ↔ BranchGraph.containsEdge graph s := by
    change vl gs (setInput s) out = true ↔ _
    rw [least.hev]
    exact marked_edges s
  have independent (r) : BranchGraph.Independent graph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least nonconstant)
      graph computes alternate_neighbors r
  have labels (v : V) : label v = outWire ∨ label v ∈ roots := by
    by_cases same : label v = outWire
    · exact Or.inl same
    · apply Or.inr
      have member : label v ∈ branches := Finset.mem_erase.mpr
        ⟨same,Finset.mem_image.mpr ⟨v,Finset.mem_univ v,rfl⟩⟩
      simpa [roots] using member
  have before (r) (member : r ∈ roots) : r < outWire := by
    have inBranches : r ∈ branches := by simpa [roots] using member
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp (occupied_subset least inBranches)
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ roots) : BranchGraph.TwinGroup graph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) := by
    have inBranches : r ∈ branches := by simpa [roots] using member
    exact circuit_branch_class_twins least.hcl outWire live graph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp (occupied_subset least inBranches)))
      (independent r)
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have scan : ∀ pending done, done ++ pending = roots → remains done ∈ frontier done.length →
      remains roots ∈ frontier roots.length := by
    intro pending
    induction pending with
    | nil =>
      intro done complete visited
      simp only [List.append_nil] at complete
      exact complete ▸ visited
    | cons r tail ih =>
      intro done complete visited
      have member : r ∈ roots := complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
      have covered : BranchGroupsLean.coveredBy label done = BranchGroupsLean.below label r :=
        BranchGroupsLean.covered_before_of_sorted label outWire done tail r
          (by simpa only [complete] using sorted)
          (fun v => by simpa only [complete] using labels v) (before r member)
      let group := BranchGroupsLean.bucket label r
      have atCut (u : V) (hu : u ∈ group) : label u = r := by
        simpa [group,BranchGroupsLean.bucket] using hu
      have sub : group ⊆ remains done := by
        intro u hu
        change u ∈ (BranchGroupsLean.coveredBy label done)ᶜ
        rw [covered]
        simp [BranchGroupsLean.below,atCut u hu]
      have after (w : V) : w ∈ remains done \ group ↔ r < label w := by
        unfold remains
        rw [covered]
        simp only [group,BranchGroupsLean.bucket,BranchGroupsLean.below,Finset.mem_sdiff,
          Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨fun ⟨h,e⟩ => lt_of_le_of_ne (le_of_not_gt h) (Ne.symm e),
          fun h => ⟨not_lt_of_ge h.le,ne_of_gt h⟩⟩
      have noPairs : ¬ ((1 ∈ group ∧ 5 ∈ group ∧ 3 ∈ remains done \ group) ∨
          (6 ∈ group ∧ 3 ∈ group ∧ 5 ∈ remains done \ group)) := by
        rintro (⟨ha,hb,hp⟩ | ⟨ha,hb,hp⟩)
        · exact context_conflict least 1 5 3 ((atCut 1 ha).trans (atCut 5 hb).symm)
            ((atCut 1 ha).trans_lt ((after 3).mp hp)) {4}
            (by decide) (by decide) (by decide) (by decide) (by decide)
        · exact context_conflict least 6 3 5 ((atCut 6 ha).trans (atCut 3 hb).symm)
            ((atCut 6 ha).trans_lt ((after 5).mp hp)) {4}
            (by decide) (by decide) (by decide) (by decide) (by decide)
      have laterTwins : ∀ u ∈ group, ∀ v ∈ group,
          (∃ a ∈ remains done \ group, graph.Adj u a) →
          (∃ b ∈ remains done \ group, graph.Adj v b) →
          ∀ w ∈ remains done \ group, (graph.Adj u w ↔ graph.Adj v w) := by
        intro u hu v hv ua va w hw
        have toNear (k : V) (active : ∃ a ∈ remains done \ group, graph.Adj k a) :
            (BranchGraph.neighborsAfter graph (BranchGroupsLean.below label r) k).Nonempty := by
          obtain ⟨a,ha,edge⟩ := active
          refine ⟨a,?_⟩
          simp only [BranchGraph.neighborsAfter,BranchGroupsLean.below,Finset.mem_filter,
            Finset.mem_univ,true_and]
          exact ⟨edge,not_lt_of_ge ((after a).mp ha).le⟩
        have equal := twins r member u hu v hv (toNear u ua) (toNear v va)
        have test := Finset.ext_iff.mp equal w
        have noEarlier : ¬ label w < r := not_lt_of_ge ((after w).mp hw).le
        simpa only [BranchGraph.neighborsAfter,BranchGroupsLean.below,Finset.mem_filter,
          Finset.mem_univ,true_and,noEarlier,not_false_eq_true,and_true] using test
      have pass := allowed_of (remains done) group (independent r) laterTwins noPairs
      have add : remains (done ++ [r]) = remains done \ group := by
        unfold remains
        rw [BranchGroupsLean.coveredBy_append_singleton]
        ext v
        simp [group]
      have next := frontier_step visited sub pass
      apply ih (done ++ [r])
      · simpa [List.append_assoc] using complete
      · simpa [add] using next
  have start : remains [] ∈ frontier 0 := by simp [remains,frontier]
  have member := scan roots [] rfl start
  have short : roots.length ≤ 4 := by
    change branches.card < 5 at few
    change branches.sort.length ≤ 4
    rw [Finset.length_sort]
    omega
  have final : BranchGraph.Independent graph (remains roots) := by
    have atOut (v : V) (member : v ∈ remains roots) : label v = outWire := by
      have outOnly : label v ∉ roots := by simpa [remains,BranchGroupsLean.coveredBy] using member
      exact (labels v).resolve_right outOnly
    intro u hu v hv
    exact independent outWire u (by simp [BranchGroupsLean.bucket,atOut u hu]) v
      (by simp [BranchGroupsLean.bucket,atOut v hv])
  exact no_finish (frontier 4) no_four_finished (remains roots)
    (frontier_extend (k := roots.length) (n := 4) (rem := remains roots) short member)
    (independent_accept final)
theorem least_five_branches {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    5 ≤ (circuitBranchWires (n := 7) gs).card :=
  (least_five_occupied_branches least).trans (Finset.card_le_card (occupied_subset least))
theorem least_branch_budget {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    (circuitBranchWires (n := 7) gs).card + 6 + notGateCount gs ≤ gs.length := by
  classical
  let branches := circuitBranchWires (n := 7) gs
  let emb : Fin (7 + gs.length) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let natBranches := branches.map emb
  have card : natBranches.card = (circuitBranchWires (n := 7) gs).card :=
    Finset.card_map emb
  have every (w : Nat) (hw : w < 7 + gs.length) (hne : w ≠ out) : ∃ p, Reads gs p w :=
    least_wire_used least nonconstant dependent restrict_nonconstant w hw hne
  have twice (w : ℕ) (hw : w ∈ natBranches) :
      ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w := by
    obtain ⟨v, hv, eq⟩ := Finset.mem_map.mp hw
    have readers := branch_slots_of_read_edges (in_circuit_branches.mp hv)
    exact (show v.val = w from eq) ▸ readers
  have budget := branching_budget least.hcl (output_valid least) every natBranches twice
  rw [card] at budget
  omega
theorem least_binary_budget {gs : List Gate} {out : Nat} (least : Least 7 target gs out) :
    11 + notGateCount gs ≤ gs.length := by
  have branches := least_five_branches least
  have budget := least_branch_budget least
  omega
theorem size_lower (s : Nat) (h : HasCircuitSize 7 target s) : 11 ≤ s := by
  obtain ⟨gs, out, least, size⟩ := exists_least 7 target s nonconstant h
  have budget := least_binary_budget least
  omega
theorem replacement_at_eleven (s : ℕ) (small : s ≤ 11) (fit : HasCircuitSize 7 target s) :
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧
      g.inputs.length ≤ 2) ∧ gs.length ≤ s ∧
      ∀ x : V → Bool, (⟨gs,out⟩ : Circuit).eval (List.ofFn x) = target x := by
  obtain ⟨gs,out,least,size⟩ := exists_least 7 target s nonconstant fit
  have budget := least_binary_budget least
  have noNot : notGateCount gs = 0 := by omega
  refine ⟨gs,out,?_,size,least.hev⟩
  intro g member
  obtain ⟨slot,hit⟩ := List.mem_iff_getElem?.mp member
  rcases least.hcl slot g hit with ⟨tag,_⟩ | ⟨tags,a,b,_,_,args⟩
  · have := one_not_gate_positive (gs := gs) ⟨g,member,tag⟩
    omega
  · exact ⟨tags,by simp [args]⟩
end L10586Branch
end ProofPart4

section ProofPart5
namespace L10586OffThree
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open PetersenCutTrace PetersenFirstGroup
open CircuitHelpers.PermInputs
abbrev V := Fin 6
def edges : List (V × V) :=
  [(0,2),(0,3),(1,3),(2,3),(0,4),(2,4),(0,5),(1,5),(2,5),(3,5),(4,5)]
def target (x : V → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)
theorem target_eq_edges (x : V → Bool) :
    target x = edges.any (fun e => x e.1 && x e.2) := rfl
theorem loopless : ∀ e ∈ edges, e.1 ≠ e.2 := by decide
def graph : SimpleGraph V where
  Adj a b := (a, b) ∈ edges ∨ (b, a) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => loopless (v, v) he rfl)
    (fun he => loopless (v, v) he rfl)⟩
instance graphDecidable : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))
def maskGraph : PetersenGroupBFS.MaskGraph :=
  ⟨6, fun u => (#[60,40,57,39,37,31] : Array Nat)[u]?.getD 0⟩
theorem graph_matches_mask :
    ∀ u v : V, graph.Adj u v ↔ (maskGraph.adjacency u.val).testBit v.val = true := by
  decide
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem no_three : PetersenGroupBFS.fullMask maskGraph ∉ PetersenGroupBFS.frontier maskGraph 3 := by
  decide
theorem groups_need_four (groups : List (Finset V))
    (twins : BranchGraph.TwinSteps graph ∅ groups)
    (finished : BranchGraph.EdgelessAfter graph (BranchGraph.removedThrough ∅ groups)) :
    4 ≤ groups.length :=
  @PetersenMaskBridge.groups_exceed_budget maskGraph graph graphDecidable graph_matches_mask
    (inferInstance : Nonempty V) 3 no_three groups twins finished
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem alternate_neighbors :
    ∀ i j : V, graph.Adj i j →
      ∃ u v, graph.Adj i u ∧ graph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ graph.Adj u v := by decide
theorem target_edges (x : V → Bool) :
    target x = true ↔ ∃ u v : V, graph.Adj u v ∧ x u = true ∧ x v = true := by
  rw [target_eq_edges, List.any_eq_true]
  simp only [Bool.and_eq_true, Prod.exists]
  constructor
  · rintro ⟨a, b, e, ha, hb⟩
    exact ⟨a, b, Or.inl e, ha, hb⟩
  · rintro ⟨a, b, e, ha, hb⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at e
    rcases e with e | e
    · exact ⟨a, b, e, ha, hb⟩
    · exact ⟨b, a, e, hb, ha⟩
theorem marked_edges (S : Finset V) :
    target (setInput S) = true ↔ BranchGraph.containsEdge graph S := by
  rw [target_edges]
  simp only [setInput, decide_eq_true_eq, BranchGraph.containsEdge]
  constructor
  · rintro ⟨u, v, e, hu, hv⟩
    exact ⟨u, hu, v, hv, e⟩
  · rintro ⟨u, hu, v, hv, e⟩
    exact ⟨u, v, e, hu, hv⟩
private theorem dependency_samples : ∀ v : V, ∃ w : V,
    target (Function.update (fun u => decide (u = w)) v
      (!(decide (v = w)))) ≠ target (fun u => decide (u = w)) := by decide
theorem dependent (v : V) : Dep target v := by
  obtain ⟨w, h⟩ := dependency_samples v
  exact ⟨fun u => decide (u = w), h⟩
theorem nonconstant : ∃ x y : V → Bool, target x ≠ target y :=
  ⟨fun _ => false, fun _ => true, by decide⟩
private theorem restrict_samples : ∀ (v : V) (b : Bool),
    target (Function.update (fun _ => false) v b) ≠
      target (Function.update (fun _ => true) v b) := by decide
theorem restrict_nonconstant (v : V) (b : Bool) :
    ∃ x y, target (Function.update x v b) ≠ target (Function.update y v b) :=
  ⟨fun _ => false, fun _ => true, restrict_samples v b⟩
theorem output_valid {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    out < 6 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)
def leastOutputWire {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    Fin (6 + gs.length) :=
  ⟨out, output_valid least⟩
theorem leastReadsLive {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    ∀ w, w ≠ leastOutputWire least → ∃ q, readEdge gs w q :=
  least_read_edge_live least nonconstant dependent restrict_nonconstant (output_valid least)
noncomputable def leastLabel {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    V → Fin (6 + gs.length) :=
  firstInputBoundary least.hcl (leastOutputWire least) (leastReadsLive least)
noncomputable def occupiedBranchWires {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    Finset (Fin (6 + gs.length)) :=
  (Finset.univ.image (leastLabel least)).erase (leastOutputWire least)
theorem occupied_subset {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    occupiedBranchWires least ⊆ circuitBranchWires (n := 6) gs := by
  intro r hr
  obtain ⟨notOut, seen⟩ := Finset.mem_erase.mp hr
  obtain ⟨v, _, chosen⟩ := Finset.mem_image.mp seen
  subst r
  have stopped := FirstBranchRoute.first_stops (readEdge gs) (leastOutputWire least)
    (read_order least.hcl) (leastReadsLive least) (inputWire gs v)
  exact in_circuit_branches.mpr (stopped.resolve_left notOut)
theorem least_four_occupied_branches {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    4 ≤ (occupiedBranchWires least).card := by
  let outWire := leastOutputWire least
  have live := leastReadsLive least
  let label := leastLabel least
  let branches := occupiedBranchWires least
  have computes (x : V → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue graph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, target_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset V) : vl gs (setInput S) outWire.val = true ↔ BranchGraph.containsEdge graph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact marked_edges S
  have independent (r) : BranchGraph.Independent graph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least nonconstant)
      graph computes alternate_neighbors r
  have labels (v : V) : label v = outWire ∨ label v ∈ branches := by
    by_cases same : label v = outWire
    · exact Or.inl same
    · exact Or.inr (Finset.mem_erase.mpr ⟨same, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp (occupied_subset least member)
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup graph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live graph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp (occupied_subset least member))) (independent r)
  exact BranchGroupsLean.roots_required graph label outWire branches 4 labels before twins
    (independent outWire) groups_need_four
theorem least_four_branches {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    4 ≤ (circuitBranchWires (n := 6) gs).card :=
  (least_four_occupied_branches least).trans (Finset.card_le_card (occupied_subset least))
theorem least_branch_budget {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    (circuitBranchWires (n := 6) gs).card + 5 + notGateCount gs ≤ gs.length := by
  classical
  let branches := circuitBranchWires (n := 6) gs
  let emb : Fin (6 + gs.length) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let natBranches := branches.map emb
  have card : natBranches.card = (circuitBranchWires (n := 6) gs).card :=
    Finset.card_map emb
  have every (w : Nat) (hw : w < 6 + gs.length) (hne : w ≠ out) : ∃ p, Reads gs p w :=
    least_wire_used least nonconstant dependent restrict_nonconstant w hw hne
  have twice (w : ℕ) (hw : w ∈ natBranches) :
      ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w := by
    obtain ⟨v, hv, eq⟩ := Finset.mem_map.mp hw
    have readers := branch_slots_of_read_edges (in_circuit_branches.mp hv)
    exact (show v.val = w from eq) ▸ readers
  have budget := branching_budget least.hcl (output_valid least) every natBranches twice
  rw [card] at budget
  omega
theorem least_binary_budget {gs : List Gate} {out : Nat} (least : Least 6 target gs out) :
    9 + notGateCount gs ≤ gs.length := by
  have branches := least_four_branches least
  have budget := least_branch_budget least
  omega
theorem size_lower (s : Nat) (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  obtain ⟨gs, out, least, size⟩ := exists_least 6 target s nonconstant h
  have budget := least_binary_budget least
  omega
def compact (i : Fin 7) : Fin 6 :=
  ([0,1,2,0,3,4,5] : List (Fin 6)).getD i.val 0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem compact_pin : ∀ x : V → Bool,
    L10586Control.target (Function.update (x ∘ compact) 3 false) = target x := by
  decide
theorem pin_false_lower (s : ℕ)
    (fit : HasCircuitSize 7 (fun x => L10586Control.target (Function.update x 3 false)) s) :
    9 ≤ s := by
  have reduced := relabel_size compact _ s fit
  have eq : (fun x => L10586Control.target (Function.update (x ∘ compact) 3 false)) = target :=
    funext compact_pin
  rw [eq] at reduced
  exact size_lower _ reduced
private def join (a b : ℕ) : Gate := ⟨.or,[a,b]⟩
private def meet (a b : ℕ) : Gate := ⟨.and,[a,b]⟩
def control : Circuit := ⟨[
  join 0 1, join 3 5, join 3 4, join 0 5, join 8 9,
  meet 6 7, meet 8 9, meet 2 10, join 11 12, join 14 13],15⟩
theorem control_size : control.gates.length = 10 := rfl
theorem control_basis : ∀ g ∈ control.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [control,join,meet]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem control_computes : ∀ x : V → Bool, control.eval (List.ofFn x) = target x := by
  decide
end L10586OffThree
end ProofPart5

section ProofPart6
namespace LineDegTest
open PEqualNP.CircuitLowerBounds
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]
theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega
theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true
theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
    · rw [ite_eq_right h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [ite_eq_left h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [ite_eq_right h2] at ht; simp at ht
theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]
end LineDegTest
end ProofPart6

section ProofPart7
namespace L11022Rewire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open L11022RestrictSupport
open CircuitHelpers
def redirect (cut source wire : ℕ) : ℕ :=
  if wire < cut then wire else if wire = cut then source else wire - 1
def rewire (cut source : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (redirect cut source)⟩
def splice (n : ℕ) (pre post : List Gate) (source output : ℕ) : Circuit :=
  ⟨pre ++ post.map (rewire (n+pre.length) source),redirect (n+pre.length) source output⟩
private theorem redirect_below (cut source wire : ℕ) (below : wire < cut) :
    redirect cut source wire = wire := by simp [redirect,below]
private theorem redirect_above (cut source wire : ℕ) (above : cut < wire) :
    redirect cut source wire = wire-1 := by
  simp [redirect,show ¬ wire < cut by omega,show wire ≠ cut by omega]
private theorem redirect_exact (cut source : ℕ) : redirect cut source cut = source := by
  simp [redirect]
private theorem redirect_lt {cut source rank wire : ℕ} (earlier : source < cut)
    (after : cut < rank) (before : wire < rank) : redirect cut source wire < rank-1 := by
  rcases lt_trichotomy wire cut with below | equal | above
  · rw [redirect_below _ _ _ below]
    omega
  · rw [equal,redirect_exact]
    omega
  · rw [redirect_above _ _ _ above]
    omega
theorem splice_clean (n : ℕ) (pre post : List Gate) (g : Gate) (source output : ℕ)
    (clean : CleanL n (pre ++ g :: post)) (earlier : source < n+pre.length) :
    CleanL n (splice n pre post source output).gates := by
  intro p gate atGate
  change (pre ++ post.map (rewire (n+pre.length) source))[p]? = some gate at atGate
  by_cases before : p < pre.length
  · rw [List.getElem?_append_left before] at atGate
    exact clean p gate (by rw [List.getElem?_append_left before,atGate])
  let j := p-pre.length
  rw [List.getElem?_append_right (by omega),List.getElem?_map] at atGate
  change (post[j]?).map (rewire (n+pre.length) source) = some gate at atGate
  cases found : post[j]? with
  | none => rw [found] at atGate; cases atGate
  | some old =>
    have eq : rewire (n+pre.length) source old = gate := by simpa [found] using atGate
    subst gate
    have oldAt : (pre ++ g :: post)[p+1]? = some old := by
      rw [List.getElem?_append_right (by omega)]
      have idx : p+1-pre.length = j+1 := by dsimp [j]; omega
      rw [idx]
      exact found
    have oldClean := clean (p+1) old oldAt
    have smaller (w : ℕ) (h : w < n+(p+1)) : redirect (n+pre.length) source w < n+p := by
      have bound := redirect_lt earlier (show n+pre.length < n+(p+1) by omega) h
      omega
    rcases oldClean with ⟨op,a,small,input⟩ | ⟨op,a,b,smallA,smallB,input⟩
    · exact Or.inl ⟨op,_,smaller a small,by simp [rewire,input]⟩
    · exact Or.inr ⟨op,_,_,smaller a smallA,smaller b smallB,by simp [rewire,input]⟩
private def Aligned (cut source : ℕ) (old new : List Bool) : Prop :=
  old.length = new.length + 1 ∧ cut ≤ new.length ∧
    ∀ w, old.getD w false = new.getD (redirect cut source w) false
private theorem at_cut (cut source : ℕ) (prefixBits : List Bool)
    (length : prefixBits.length = cut) :
    Aligned cut source (prefixBits ++ [prefixBits.getD source false]) prefixBits := by
  refine ⟨by simp,by omega,?_⟩
  intro w
  rcases lt_trichotomy w cut with below | equal | above
  · rw [redirect_below _ _ _ below, List.getD_append _ _ _ _ (by omega)]
  · subst w
    rw [redirect_exact,← length,getD_snoc_eq]
  · rw [redirect_above _ _ _ above,List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]
private theorem append_same {cut source : ℕ} {old new : List Bool} (earlier : source < cut)
    (aligned : Aligned cut source old new) (bit : Bool) :
    Aligned cut source (old ++ [bit]) (new ++ [bit]) := by
  obtain ⟨length,bound,entries⟩ := aligned
  refine ⟨by simp [length],by simp; omega,?_⟩
  intro w
  by_cases isNew : w = old.length
  · subst w
    have mapped : redirect cut source old.length = new.length := by
      rw [redirect_above _ _ _ (by omega)]
      omega
    rw [mapped,getD_snoc_eq,getD_snoc_eq]
  · have notNew : redirect cut source w ≠ new.length := by
      rcases lt_trichotomy w cut with below | equal | above
      · rw [redirect_below _ _ _ below]
        omega
      · rw [equal,redirect_exact]
        omega
      · rw [redirect_above _ _ _ above]
        omega
    rw [getD_snoc_ne _ _ _ _ isNew,getD_snoc_ne _ _ _ _ notNew,entries]
private theorem after_suffix (cut source : ℕ) (earlier : source < cut)
    (post : List Gate) (old new : List Bool) (aligned : Aligned cut source old new) :
    Aligned cut source (wiresFrom post old) (wiresFrom (post.map (rewire cut source)) new) := by
  induction post generalizing old new with
  | nil => exact aligned
  | cons g tail ih =>
    let bit := g.op.eval (g.inputs.map (fun w => old.getD w false))
    have eq : g.op.eval (g.inputs.map (fun w => new.getD (redirect cut source w) false)) = bit := by
      congr 1
      apply List.map_congr_left
      intro w _
      exact (aligned.2.2 w).symm
    change Aligned cut source (wiresFrom tail (old ++ [bit]))
      (wiresFrom (tail.map (rewire cut source)) (new ++
        [g.op.eval (((rewire cut source g).inputs).map (fun w => new.getD w false))]))
    rw [show ((rewire cut source g).inputs.map (fun w => new.getD w false)) =
      g.inputs.map (fun w => new.getD (redirect cut source w) false) by simp [rewire,List.map_map],eq]
    exact ih _ _ (append_same earlier aligned bit)
theorem splice_agrees (n : ℕ) (x : Fin n → Bool) (pre : List Gate) (g : Gate) (post : List Gate)
    (source output : ℕ) (earlier : source < n + pre.length)
    (atGate : let wires := wiresFrom pre (List.ofFn x)
      g.op.eval (g.inputs.map (fun w => wires.getD w false)) = wires.getD source false) :
    ∀ w, ((splice n pre post source output).wires (List.ofFn x)).getD
      (redirect (n+pre.length) source w) false =
      ((⟨pre ++ g :: post, output⟩ : Circuit).wires (List.ofFn x)).getD w false := by
  intro w
  let wires := wiresFrom pre (List.ofFn x)
  have length : wires.length = n + pre.length := by
    simp [wires,length_wiresFrom]
  have initial := at_cut (n+pre.length) source wires length
  have result := after_suffix (n+pre.length) source earlier post
    (wires ++ [wires.getD source false]) wires initial
  change (wiresFrom (pre ++ post.map (rewire (n+pre.length) source)) (List.ofFn x)).getD
      (redirect (n+pre.length) source w) false =
    (wiresFrom (pre ++ g :: post) (List.ofFn x)).getD w false
  rw [wiresFrom_append,wiresFrom_append]
  change (wiresFrom (post.map (rewire (n+pre.length) source)) wires).getD
      (redirect (n+pre.length) source w) false =
    (wiresFrom post (wires ++ [g.op.eval (g.inputs.map (fun w => wires.getD w false))])).getD w false
  rw [show g.op.eval (g.inputs.map (fun w => wires.getD w false)) =
    wires.getD source false from atGate]
  exact (result.2.2 w).symm
theorem splice_eval (n : ℕ) (x : Fin n → Bool) (pre : List Gate) (g : Gate) (post : List Gate)
    (source output : ℕ) (earlier : source < n + pre.length)
    (atGate : let wires := wiresFrom pre (List.ofFn x)
      g.op.eval (g.inputs.map (fun w => wires.getD w false)) = wires.getD source false) :
    (splice n pre post source output).eval (List.ofFn x) =
      (⟨pre ++ g :: post, output⟩ : Circuit).eval (List.ofFn x) :=
  splice_agrees n x pre g post source output earlier atGate output
theorem splice_size (n : ℕ) (pre post : List Gate) (source output : ℕ) :
    (splice n pre post source output).size = pre.length + post.length := by
  simp [splice,Circuit.size]
theorem splice_increases (n : ℕ) (x : Fin n → Bool) (pre : List Gate) (g : Gate) (post : List Gate)
    (source output : ℕ) (earlier : source < n + pre.length)
    (monotone : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or)
    (atGate : let wires := wiresFrom pre (List.ofFn x)
      g.op.eval (g.inputs.map (fun w => wires.getD w false)) = true → wires.getD source false = true)
    (on : (⟨pre ++ g :: post, output⟩ : Circuit).eval (List.ofFn x) = true) :
    (splice n pre post source output).eval (List.ofFn x) = true := by
  let wires := wiresFrom pre (List.ofFn x)
  let bit := g.op.eval (g.inputs.map (fun w => wires.getD w false))
  have length : wires.length = n+pre.length := by simp [wires,length_wiresFrom]
  have before : ∀ j, (wires ++ [bit]).getD j false = true →
      (wires ++ [wires.getD source false]).getD j false = true := by
    intro j h
    by_cases isLast : j = wires.length
    · subst j
      rw [getD_snoc_eq] at h ⊢
      exact atGate h
    · rw [getD_snoc_ne _ _ _ _ isLast] at h ⊢
      exact h
  have oldValue : (wiresFrom post (wires ++ [bit])).getD output false = true := by
    change (wiresFrom (pre ++ g :: post) (List.ofFn x)).getD output false = true at on
    rw [wiresFrom_append] at on
    exact on
  have up : (wiresFrom post (wires ++ [wires.getD source false])).getD output false = true :=
    LineDegTest.W_mono post monotone _ _ (by simp) before output oldValue
  have aligned := after_suffix (n+pre.length) source earlier post _ _ (at_cut _ source wires length)
  change (wiresFrom (pre ++ post.map (rewire (n+pre.length) source)) (List.ofFn x)).getD
    (redirect (n+pre.length) source output) false = true
  rw [wiresFrom_append]
  exact (aligned.2.2 output).symm.trans up
def appendOr (n : ℕ) (C : Circuit) (other : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or,[C.output,other]⟩],n+C.gates.length⟩
theorem promote_clean (n : ℕ) (pre post : List Gate) (source other output : ℕ)
    (clean : CleanL n (pre ++ ⟨.or,[source,other]⟩ :: post))
    (sourceEarlier : source < n+pre.length) (otherEarlier : other < n+pre.length)
    (outputValid : output < n+(pre ++ ⟨.or,[source,other]⟩ :: post).length) :
    CleanL n (appendOr n (splice n pre post source output) other).gates := by
  let reduced := splice n pre post source output
  have reducedClean : CleanL n reduced.gates := splice_clean n pre post _ source output clean sourceEarlier
  have size : reduced.gates.length = pre.length+post.length := splice_size n pre post source output
  have reducedOutput : reduced.output < n+reduced.gates.length := by
    change redirect (n+pre.length) source output < n+reduced.gates.length
    simp only [List.length_append,List.length_cons] at outputValid
    have smaller := redirect_lt sourceEarlier (show n+pre.length < n+(pre.length+(post.length+1)) by omega)
      outputValid
    omega
  intro p g atGate
  change (reduced.gates ++ [⟨.or,[reduced.output,other]⟩])[p]? = some g at atGate
  by_cases before : p < reduced.gates.length
  · rw [List.getElem?_append_left before] at atGate
    exact reducedClean p g atGate
  · rw [List.getElem?_append_right (by omega)] at atGate
    have atEnd : p = reduced.gates.length := by
      by_contra diff
      rw [List.getElem?_eq_none (by simp; omega)] at atGate
      cases atGate
    subst p
    have eq : (⟨.or,[reduced.output,other]⟩ : Gate) = g := by simpa using atGate
    subst g
    exact Or.inr ⟨Or.inr rfl,_,_,reducedOutput,by omega,rfl⟩
private theorem appendOr_eval (n : ℕ) (C : Circuit) (other : ℕ) (x : Fin n → Bool) :
    (appendOr n C other).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || (C.wires (List.ofFn x)).getD other false) := by
  let data := wiresFrom C.gates (List.ofFn x)
  have length : data.length = n+C.gates.length := by simp [data,length_wiresFrom]
  change (wiresFrom (C.gates ++ [⟨.or,[C.output,other]⟩]) (List.ofFn x)).getD
    (n+C.gates.length) false = (data.getD C.output false || data.getD other false)
  rw [wiresFrom_append]
  change (data ++ [GateOp.or.eval [data.getD C.output false,data.getD other false]]).getD
    (n+C.gates.length) false = _
  rw [← length,getD_snoc_eq]
  simp [GateOp.eval]
private theorem splice_earlier (n : ℕ) (pre post : List Gate) (source output h : ℕ)
    (before : h < n+pre.length) (x : Fin n → Bool) :
    ((splice n pre post source output).wires (List.ofFn x)).getD h false =
      (wiresFrom pre (List.ofFn x)).getD h false := by
  change (wiresFrom (pre ++ post.map (rewire (n+pre.length) source)) (List.ofFn x)).getD h false = _
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using before)]
theorem promote_eval (n : ℕ) (pre post : List Gate) (source other output : ℕ)
    (sourceEarlier : source < n + pre.length) (otherEarlier : other < n + pre.length)
    (x : Fin n → Bool)
    (safe : (wiresFrom pre (List.ofFn x)).getD other false = true →
      (⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩ : Circuit).eval (List.ofFn x) = true) :
    (appendOr n (splice n pre post source output) other).eval (List.ofFn x) =
      (⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩ : Circuit).eval (List.ofFn x) := by
  rw [appendOr_eval, splice_earlier n pre post source output other otherEarlier x]
  cases value : (wiresFrom pre (List.ofFn x)).getD other false with
  | false =>
    simp only [Bool.or_false]
    apply splice_eval n x pre _ post source output sourceEarlier
    have evalOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
      cases a <;> cases b <;> rfl
    change GateOp.or.eval [(wiresFrom pre (List.ofFn x)).getD source false,
      (wiresFrom pre (List.ofFn x)).getD other false] =
        (wiresFrom pre (List.ofFn x)).getD source false
    rw [evalOr,value,Bool.or_false]
  | true =>
    rw [safe value]
    simp
theorem promote_size (n : ℕ) (pre post : List Gate) (source other output : ℕ) :
    (appendOr n (splice n pre post source output) other).size = (pre ++ post).length + 1 := by
  simp [appendOr,splice,Circuit.size,Nat.add_assoc]
def badReads (dirty : ℕ → Bool) (rank : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: rest => (if dirty rank then g.inputs.countP (fun w => !(dirty w)) else 0) +
      badReads dirty (rank+1) rest
private theorem badReads_append (dirty : ℕ → Bool) (rank : ℕ) (pre post : List Gate) :
    badReads dirty rank (pre ++ post) =
      badReads dirty rank pre + badReads dirty (rank+pre.length) post := by
  induction pre generalizing rank with
  | nil => simp [badReads]
  | cons g pre ih =>
    simp only [List.cons_append,badReads,List.length_cons,ih]
    rw [show rank+1+pre.length = rank+(pre.length+1) by omega]
    omega
private theorem badReads_past {old fresh : ℕ → Bool} (cut source : ℕ)
    (same : ∀ w, fresh (redirect cut source w) = old w)
    (post : List Gate) (rank : ℕ) (after : cut < rank) :
    badReads fresh (rank-1) (post.map (rewire cut source)) = badReads old rank post := by
  induction post generalizing rank with
  | nil => rfl
  | cons g post ih =>
    have rankMark : fresh (rank-1) = old rank := by
      simpa only [redirect_above cut source rank after] using same rank
    have inputs : (rewire cut source g).inputs.countP (fun w => !(fresh w)) =
        g.inputs.countP (fun w => !(old w)) := by
      change (g.inputs.map (redirect cut source)).countP (fun w => !(fresh w)) = _
      rw [List.countP_map]
      apply List.countP_congr
      intro w _
      simp only [Function.comp_apply,same]
    have advance : (rank-1)+1 = (rank+1)-1 := by omega
    simp only [List.map_cons,badReads,rankMark,inputs,advance,ih (rank+1) (by omega : cut < rank+1)]
private theorem badReads_before {old fresh : ℕ → Bool} (cut source : ℕ)
    (same : ∀ w, fresh (redirect cut source w) = old w)
    (pre : List Gate) (rank : ℕ) (before : rank+pre.length ≤ cut)
    (reads : ∀ g ∈ pre, ∀ w ∈ g.inputs, w < cut) :
    badReads fresh rank pre = badReads old rank pre := by
  induction pre generalizing rank with
  | nil => rfl
  | cons g pre ih =>
    have rankMark : fresh rank = old rank := by
      have lt : rank < cut := by simp only [List.length_cons] at before; omega
      simpa only [redirect_below cut source rank lt] using same rank
    have inputs : g.inputs.countP (fun w => !(fresh w)) = g.inputs.countP (fun w => !(old w)) := by
      apply List.countP_congr
      intro w hw
      have mark : fresh w = old w := by
        simpa only [redirect_below cut source w (reads g (by simp) w hw)] using same w
      rw [mark]
    have bound : rank+1+pre.length ≤ cut := by simp only [List.length_cons] at before; omega
    simp only [badReads,rankMark,inputs,ih (rank+1) bound (fun t ht => reads t (by simp [ht]))]
theorem promotion_removes_one_bad_read (n : ℕ) (pre post : List Gate) (source other output : ℕ)
    (old fresh : ℕ → Bool)
    (same : ∀ w, fresh (redirect (n+pre.length) source w) = old w)
    (reads : ∀ g ∈ pre, ∀ w ∈ g.inputs, w < n+pre.length)
    (dirtyGate : old (n+pre.length) = true) (dirtySource : old source = true) (safeOther : old other = false)
    (safeNewOutput : fresh (n+(splice n pre post source output).gates.length) = false) :
    badReads fresh n (appendOr n (splice n pre post source output) other).gates + 1 =
      badReads old n (pre ++ ⟨.or,[source,other]⟩ :: post) := by
  change badReads fresh n ((splice n pre post source output).gates ++ _) + 1 = _
  rw [badReads_append]
  rw [show badReads fresh (n+(splice n pre post source output).gates.length)
      [⟨.or,[(splice n pre post source output).output,other]⟩] = 0 by simp [badReads,safeNewOutput],Nat.add_zero]
  change badReads fresh n (pre ++ post.map (rewire (n+pre.length) source)) + 1 = _
  rw [badReads_append,badReads_append]
  rw [badReads_before (n+pre.length) source same pre n (le_refl _) reads]
  have suffix := badReads_past (n+pre.length) source same post (n+pre.length+1) (by omega)
  rw [show n+pre.length+1-1 = n+pre.length by omega] at suffix
  rw [suffix]
  simp only [badReads,dirtyGate,ite_true,List.countP_cons,dirtySource,safeOther,
    Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,List.countP_nil]
  omega
noncomputable def dirty (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (wire : ℕ) : Bool := by
  classical
  exact decide (∃ x : Fin n → Bool, f x = false ∧ (C.wires (List.ofFn x)).getD wire false = true)
private theorem dirty_iff (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (wire : ℕ) :
    dirty n f C wire = true ↔
      ∃ x : Fin n → Bool, f x = false ∧ (C.wires (List.ofFn x)).getD wire false = true := by
  classical
  simp only [dirty,decide_eq_true_eq]
private theorem getD_snoc_false (bits : List Bool) (wire : ℕ) :
    (bits ++ [false]).getD wire false = bits.getD wire false := by
  by_cases eq : wire = bits.length
  · subst wire
    rw [getD_snoc_eq, List.getD_eq_default _ _ (le_refl _)]
  · exact getD_snoc_ne _ _ _ _ eq
theorem promotion_reduces_dirty_reads (n : ℕ) (f : (Fin n → Bool) → Bool)
    (pre post : List Gate) (source other output : ℕ)
    (sourceEarlier : source < n+pre.length) (otherEarlier : other < n+pre.length)
    (reads : ∀ g ∈ pre, ∀ w ∈ g.inputs, w < n+pre.length)
    (safe : ∀ x : Fin n → Bool, f x = false →
      (wiresFrom pre (List.ofFn x)).getD other false = false)
    (fit : ∀ x : Fin n → Bool,
      (⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩ : Circuit).eval (List.ofFn x) = f x)
    (dirtyGate : dirty n f ⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩ (n+pre.length) = true)
    (dirtySource : dirty n f ⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩ source = true) :
    let old : Circuit := ⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩
    let fresh := appendOr n (splice n pre post source output) other
    (∀ x : Fin n → Bool, fresh.eval (List.ofFn x) = f x) ∧
      badReads (dirty n f fresh) n fresh.gates + 1 = badReads (dirty n f old) n old.gates := by
  let old : Circuit := ⟨pre ++ ⟨.or,[source,other]⟩ :: post,output⟩
  let reduced := splice n pre post source output
  let fresh := appendOr n reduced other
  have computes (x : Fin n → Bool) : fresh.eval (List.ofFn x) = f x := by
    rw [← fit x]
    apply promote_eval n pre post source other output sourceEarlier otherEarlier x
    intro value
    rw [fit x]
    cases eq : f x
    · rw [safe x eq] at value
      cases value
    · rfl
  refine ⟨computes,?_⟩
  have equalWire (x : Fin n → Bool) (neg : f x = false) (w : ℕ) :
      (fresh.wires (List.ofFn x)).getD (redirect (n+pre.length) source w) false =
        (old.wires (List.ofFn x)).getD w false := by
    let bits := wiresFrom reduced.gates (List.ofFn x)
    let appended := GateOp.or.eval [bits.getD reduced.output false,bits.getD other false]
    have len : bits.length = n+reduced.gates.length := by
      simp [bits,length_wiresFrom]
    have evaluate : (bits ++ [appended]).getD bits.length false = f x := by
      rw [len]
      have eval := computes x
      change (wiresFrom (reduced.gates ++ [⟨.or,[reduced.output,other]⟩]) (List.ofFn x)).getD
        (n+reduced.gates.length) false = f x at eval
      rw [wiresFrom_append] at eval
      exact eval
    have off : appended = false := by
      rw [getD_snoc_eq,neg] at evaluate
      exact evaluate
    change (wiresFrom (reduced.gates ++ [⟨.or,[reduced.output,other]⟩]) (List.ofFn x)).getD _ false = _
    rw [wiresFrom_append]
    change (bits ++ [appended]).getD _ false = _
    rw [off,getD_snoc_false]
    apply splice_agrees n x pre ⟨.or,[source,other]⟩ post source output sourceEarlier
    have offOther := safe x neg
    change GateOp.or.eval [(wiresFrom pre (List.ofFn x)).getD source false,
      (wiresFrom pre (List.ofFn x)).getD other false] = (wiresFrom pre (List.ofFn x)).getD source false
    generalize (wiresFrom pre (List.ofFn x)).getD source false = bit
    rw [offOther]
    cases bit <;> rfl
  have same (w : ℕ) : dirty n f fresh (redirect (n+pre.length) source w) = dirty n f old w := by
    apply Bool.eq_iff_iff.mpr
    rw [dirty_iff,dirty_iff]
    constructor
    · rintro ⟨x,neg,value⟩
      exact ⟨x,neg,by rwa [equalWire x neg w] at value⟩
    · rintro ⟨x,neg,value⟩
      exact ⟨x,neg,by rwa [equalWire x neg w]⟩
  have safeOther : dirty n f old other = false := by
    cases mark : dirty n f old other
    · rfl
    obtain ⟨x,neg,value⟩ := (dirty_iff n f old other).mp mark
    change (wiresFrom (pre ++ _) (List.ofFn x)).getD other false = true at value
    rw [wiresFrom_append, getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using otherEarlier), safe x neg] at value
    cases value
  have safeOutput : dirty n f fresh (n+reduced.gates.length) = false := by
    cases mark : dirty n f fresh (n+reduced.gates.length)
    · rfl
    obtain ⟨x,neg,value⟩ := (dirty_iff n f fresh _).mp mark
    change fresh.eval (List.ofFn x) = true at value
    rw [computes x,neg] at value
    cases value
  exact promotion_removes_one_bad_read n pre post source other output _ _ same reads
    dirtyGate dirtySource safeOther safeOutput
theorem bypass_neutral_and (n : ℕ) (f : (Fin n → Bool) → Bool)
    (pre post : List Gate) (source other output : ℕ)
    (sourceEarlier : source < n+pre.length)
    (zeroRejects : f (fun _ => false) = false)
    (neutral : ∀ x : Fin n → Bool, f x = false →
      (wiresFrom pre (List.ofFn x)).getD other false = true)
    (oneSide : (∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) ∨
      ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (fit : ∀ x : Fin n → Bool,
      (⟨pre ++ ⟨.and,[source,other]⟩ :: post,output⟩ : Circuit).eval (List.ofFn x) = f x) :
    ∀ x : Fin n → Bool, (splice n pre post source output).eval (List.ofFn x) = f x := by
  intro x
  let gate : Gate := ⟨.and,[source,other]⟩
  have agrees (peer : (wiresFrom pre (List.ofFn x)).getD other false = true) :
      (splice n pre post source output).eval (List.ofFn x) = f x := by
    rw [← fit x]
    apply splice_eval n x pre gate post source output sourceEarlier
    change GateOp.and.eval [(wiresFrom pre (List.ofFn x)).getD source false,
      (wiresFrom pre (List.ofFn x)).getD other false] = (wiresFrom pre (List.ofFn x)).getD source false
    rw [peer]
    cases (wiresFrom pre (List.ofFn x)).getD source false <;> rfl
  rcases oneSide with before | after
  · apply agrees
    refine LineDegTest.W_mono pre before
      (List.ofFn (fun _ : Fin n => false)) (List.ofFn x) (by simp) ?_ other (neutral _ zeroRejects)
    intro i h
    rw [LineDegTest.ofFn_getD] at h
    split at h <;> cases h
  · by_cases no : f x = false
    · exact agrees (neutral x no)
    have yes : f x = true := by cases bit : f x <;> simp_all
    rw [yes]
    apply splice_increases n x pre gate post source output sourceEarlier after _ (by rw [fit x,yes])
    change GateOp.and.eval [(wiresFrom pre (List.ofFn x)).getD source false,
      (wiresFrom pre (List.ofFn x)).getD other false] = true → (wiresFrom pre (List.ofFn x)).getD source false = true
    cases (wiresFrom pre (List.ofFn x)).getD source false <;>
      cases (wiresFrom pre (List.ofFn x)).getD other false <;> decide
private theorem monotone_except (gs : List Gate) (ignored : ℕ) (x y : List Bool)
    (hlen : x.length = y.length)
    (gates : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ignored ∉ g.inputs)
    (before : ∀ i, i ≠ ignored → x.getD i false = true → y.getD i false = true) :
    ∀ i, i ≠ ignored → (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact before
  | cons g tail ih =>
    let bx := g.op.eval (g.inputs.map (fun w => x.getD w false))
    let by' := g.op.eval (g.inputs.map (fun w => y.getD w false))
    have step : ∀ i, i ≠ ignored → (x ++ [bx]).getD i false = true → (y ++ [by']).getD i false = true := by
      intro i apart h
      by_cases atEnd : i = x.length
      · rw [atEnd,getD_snoc_eq] at h
        rw [atEnd,hlen,getD_snoc_eq]
        have gate := gates g (by simp)
        apply LineDegTest.eval_mono g gate.1 x y _ h
        intro w mem
        apply before w
        exact fun eq => gate.2 (eq ▸ mem)
      · rw [getD_snoc_ne _ _ _ _ atEnd] at h
        rw [getD_snoc_ne _ _ _ _ (by simpa only [hlen] using atEnd)]
        exact before i apart h
    exact ih (x ++ [bx]) (y ++ [by']) (by simp [hlen]) (fun g mem => gates g (by simp [mem])) step
theorem sole_not_reader_antitone (n : ℕ) (p : Fin n) (pre post : List Gate) (output : ℕ)
    (gates : ∀ g ∈ pre ++ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ p.val ∉ g.inputs)
    (outApart : output ≠ p.val) (x y : Fin n → Bool)
    (off : x p = false) (on : y p = true) (same : ∀ q, q ≠ p → x q = y q) :
    let C : Circuit := ⟨pre ++ ⟨.not,[p.val]⟩ :: post,output⟩
    C.eval (List.ofFn y) = true → C.eval (List.ofFn x) = true := by
  dsimp only
  intro trueOn
  let low := wiresFrom pre (List.ofFn y)
  let high := wiresFrom pre (List.ofFn x)
  have sameLen : low.length = high.length := by simp [low,high,length_wiresFrom]
  have before : ∀ i, i ≠ p.val → low.getD i false = true → high.getD i false = true := by
    apply monotone_except pre p.val (List.ofFn y) (List.ofFn x) (by simp)
      (fun g mem => gates g (List.mem_append_left _ mem))
    intro i apart h
    rw [LineDegTest.ofFn_getD] at h ⊢
    by_cases valid : i < n
    · rw [dite_eq_left valid] at h ⊢
      rw [same ⟨i,valid⟩ (fun eq => apart (congrArg Fin.val eq))]
      exact h
    · rw [dite_eq_right valid] at h
      cases h
  have bitLow : low.getD p.val false = true := by
    change vl pre y p.val = true
    rw [vl_input pre y p.val p.isLt]
    exact on
  have bitHigh : high.getD p.val false = false := by
    change vl pre x p.val = false
    rw [vl_input pre x p.val p.isLt]
    exact off
  have step : ∀ i, i ≠ p.val → (low ++ [false]).getD i false = true →
      (high ++ [true]).getD i false = true := by
    intro i apart h
    by_cases last : i = low.length
    · rw [last,getD_snoc_eq] at h
      cases h
    · rw [getD_snoc_ne _ _ _ _ last] at h
      rw [getD_snoc_ne _ _ _ _ (by simpa only [sameLen] using last)]
      exact before i apart h
  have old : (wiresFrom post (low ++ [false])).getD output false = true := by
    change (wiresFrom (pre ++ ⟨.not,[p.val]⟩ :: post) (List.ofFn y)).getD output false = true at trueOn
    rw [wiresFrom_append] at trueOn
    change (wiresFrom post (low ++ [!low.getD p.val false])).getD output false = true at trueOn
    simpa only [bitLow,Bool.not_true] using trueOn
  have fresh := monotone_except post p.val (low ++ [false]) (high ++ [true]) (by simp [sameLen])
    (fun g mem => gates g (List.mem_append_right _ mem)) step output outApart old
  change (wiresFrom (pre ++ ⟨.not,[p.val]⟩ :: post) (List.ofFn x)).getD output false = true
  rw [wiresFrom_append]
  change (wiresFrom post (high ++ [!high.getD p.val false])).getD output false = true
  simpa only [bitHigh,Bool.not_false] using fresh
open CircuitHelpers.Readers
noncomputable def dirtyReads (n : ℕ) (f : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  badReads (dirty n f ⟨gs,0⟩) n gs
theorem exists_least_fewest_dirty_reads (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (nonconstant : ∃ x y, f x ≠ f y) (fit : HasCircuitSize n f s) :
    ∃ (gs : List Gate) (out : ℕ), Least n f gs out ∧ gs.length ≤ s ∧
      ∀ (gs' : List Gate) (out' : ℕ), CleanL n gs' →
        (∀ x : Fin n → Bool, vl gs' x out' = f x) → gs'.length = gs.length →
        dirtyReads n f gs ≤ dirtyReads n f gs' := by
  classical
  obtain ⟨gs, out, least, size⟩ := exists_least n f s nonconstant fit
  let correct (ys : List Gate) (o : ℕ) := CleanL n ys ∧ (∀ x : Fin n → Bool, vl ys x o = f x) ∧
    ys.length = gs.length
  have existsCost : ∃ k, ∃ ys o, correct ys o ∧ dirtyReads n f ys = k :=
    ⟨dirtyReads n f gs,gs,out,⟨least.hcl,least.hev,rfl⟩,rfl⟩
  obtain ⟨ys, o, ⟨clean, evaluate, sameSize⟩, cost⟩ := Nat.find_spec existsCost
  refine ⟨ys,o,⟨clean,evaluate,?_⟩,by simpa only [sameSize] using size,?_⟩
  · intro zs zOut zClean zFit
    rw [sameSize]
    exact least.hmin zs zOut zClean zFit
  intro zs zOut zClean zFit zSize
  rw [cost]
  exact Nat.find_min' existsCost ⟨zs,zOut,⟨zClean,zFit,zSize.trans sameSize⟩,rfl⟩
end L11022Rewire
end ProofPart7

section ProofPart8
namespace L11022ReaderSwap
open L11022RestrictSupport L11022Rewire
open PEqualNP.CircuitLowerBounds CircuitHelpers
private theorem swap_clean (n : ℕ) (pre post : List Gate) (op : GateOp) (a b : ℕ)
    (binary : op = .and ∨ op = .or)
    (clean : CleanL n (pre ++ ⟨op,[b,a]⟩ :: post)) :
    CleanL n (pre ++ ⟨op,[a,b]⟩ :: post) := by
  intro i g hit
  by_cases before : i < pre.length
  · rw [List.getElem?_append_left before] at hit
    exact clean i g (by rw [List.getElem?_append_left before,hit])
  have reaching : pre.length ≤ i := Nat.le_of_not_gt before
  by_cases middle : i = pre.length
  · subst i
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero] at hit
    have eq := Option.some.inj hit
    subst g
    have old : CleanGate (n + pre.length) ⟨op,[b,a]⟩ := by
      apply clean
      rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]
    exact Or.inr ⟨binary,a,b,old.lt a (by simp),old.lt b (by simp),rfl⟩
  have offset : i - pre.length = (i - pre.length - 1) + 1 := by omega
  apply clean i g
  rw [List.getElem?_append_right reaching,offset,List.getElem?_cons_succ] at hit ⊢
  exact hit
private theorem swap_wires (pre post : List Gate) (op : GateOp) (a b : ℕ)
    (binary : op = .and ∨ op = .or) (input : List Bool) :
    wiresFrom (pre ++ ⟨op,[a,b]⟩ :: post) input =
      wiresFrom (pre ++ ⟨op,[b,a]⟩ :: post) input := by
  rw [wiresFrom_append,wiresFrom_append]
  let bits := wiresFrom pre input
  change wiresFrom post (bits ++ [op.eval [bits.getD a false,bits.getD b false]]) =
    wiresFrom post (bits ++ [op.eval [bits.getD b false,bits.getD a false]])
  have commute (x y : Bool) : op.eval [x,y] = op.eval [y,x] := by
    rcases binary with rfl | rfl <;> cases x <;> cases y <;> rfl
  rw [commute]
private theorem swap_bad_reads (mark : ℕ → Bool) (rank : ℕ) (pre post : List Gate)
    (op : GateOp) (a b : ℕ) :
    badReads mark rank (pre ++ ⟨op,[a,b]⟩ :: post) =
      badReads mark rank (pre ++ ⟨op,[b,a]⟩ :: post) := by
  induction pre generalizing rank with
  | nil =>
    have counts : ([a,b] : List ℕ).countP (fun w => !(mark w)) =
        ([b,a] : List ℕ).countP (fun w => !(mark w)) := by
      simp only [List.countP_cons,List.countP_nil,Nat.zero_add,Nat.add_comm]
    simp only [List.nil_append,badReads,counts]
  | cons h pre ih => simp only [List.cons_append,badReads,ih]
theorem swap_middle (n : ℕ) (f : (Fin n → Bool) → Bool) (pre post : List Gate)
    (op : GateOp) (a b : ℕ) (binary : op = .and ∨ op = .or)
    (clean : CleanL n (pre ++ ⟨op,[b,a]⟩ :: post)) :
    CleanL n (pre ++ ⟨op,[a,b]⟩ :: post) ∧
      (∀ (x : Fin n → Bool) (w : ℕ),
        vl (pre ++ ⟨op,[a,b]⟩ :: post) x w = vl (pre ++ ⟨op,[b,a]⟩ :: post) x w) ∧
      dirtyReads n f (pre ++ ⟨op,[a,b]⟩ :: post) = dirtyReads n f (pre ++ ⟨op,[b,a]⟩ :: post) := by
  have values (x : Fin n → Bool) (w : ℕ) :
      vl (pre ++ ⟨op,[a,b]⟩ :: post) x w = vl (pre ++ ⟨op,[b,a]⟩ :: post) x w :=
    congrArg (fun bits : List Bool => bits.getD w false)
      (swap_wires pre post op a b binary (List.ofFn x))
  refine ⟨swap_clean n pre post op a b binary clean,values,?_⟩
  have marks : dirty n f ⟨pre ++ ⟨op,[a,b]⟩ :: post,0⟩ =
      dirty n f ⟨pre ++ ⟨op,[b,a]⟩ :: post,0⟩ := by
    funext w
    apply Bool.eq_iff_iff.mpr
    simp only [dirty,decide_eq_true_eq]
    constructor
    · rintro ⟨x,no,yes⟩
      exact ⟨x,no,(values x w).symm.trans yes⟩
    · rintro ⟨x,no,yes⟩
      exact ⟨x,no,(values x w).trans yes⟩
  unfold dirtyReads
  rw [marks]
  exact swap_bad_reads _ n pre post op a b
end L11022ReaderSwap
end ProofPart8

section ProofPart9
namespace L8703Lower
section LivePart1
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
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
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]
theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)
def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> (cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> (cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]
theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)
theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this
theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩
end LivePart1
section LivePart2
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)
theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]
theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih
abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false
theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp
theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]
def shift (K a : ℕ) : ℕ := if a < K then a else a - 1
def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩
def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false
theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
def readLater (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs
open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (readLater gs o p a))
theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ readLater gs o p a := by
  simp [liveList]
theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range
abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x
theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → readLater gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩
open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (readLater gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (readLater gs o (p + 1) j)) j
              (kept (decide (readLater gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)
end LivePart2
section LivePart3
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)
theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)
def diff (k w : Nat) : Nat := w ^^^ (w >>> k)
def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t
theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k
theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]
theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p
def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat
def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat
def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))
theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]
theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])
theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _
theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp
theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf
end LivePart3
section LivePart4
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i
def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)
theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]
theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]
theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl
theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl
theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih
end LivePart4
section LivePart5
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def barrierOK (k : Nat) : Nat → List Nat → Bool
  | 0, ws => decide (ws = [goal k])
  | s+1, ws =>
    decide (ws.length ≤ s+2) && decide ((cov k ws &&& lo k) = lo k) &&
    next (mask k) (s+2-ws.length) ws (fun _ ys => barrierOK k s ys)
theorem barrierOK_of_run {k s : Nat} {ws : List Nat}
    (h : NatRun (mask k) (goal k) s ws) : barrierOK k s ws = true := by
  induction s generalizing ws with
  | zero => simpa [barrierOK] using zero_done h rfl
  | succ s ih =>
    simp only [barrierOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_,required h⟩,?_⟩
    · have := run_len h
      omega
    · exact next_complete h s rfl ws (List.Perm.refl _) _ (fun _ _ hey => ih hey)
theorem none_from_barrier {k b a : Nat} {rest : List Nat}
    (bad : barrierOK k b (a::rest) = false) :
    ∀ s ≤ b, ¬ NatRun (mask k) (goal k) s (a::rest) := by
  intro s hs h
  have impossible := barrierOK_of_run (extend_run h hs)
  simp [bad] at impossible
end LivePart5
section LivePart6
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def targetFour (T : Nat) (x : Fin 4 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 4, if x i then 2 ^ (i : ℕ) else 0)
theorem size_from_fourBarrier
    (T k bound : Nat) (rows : List ℕ) (xHead : Nat) (xTail : List ℕ)
    (differs : targetFour T (fun _ => false) ≠ targetFour T (fun _ => true))
    (rowsLen : mask k = 2 ^ rows.length - 1)
    (inputs : (List.ofFn fun i : Fin 4 => fun x : Fin 4 → Bool => x i).map
      (fun a => encL a rows) = xHead :: xTail)
    (output : encL (targetFour T) rows = goal k)
    (essential : ∀ zs ∈ (xHead :: xTail).sublists, zs ≠ xHead :: xTail →
      (cov k zs &&& lo k) ≠ lo k)
    (none : ∀ s ≤ bound, ¬ NatRun (mask k) (goal k) s (xHead :: xTail))
    {s : Nat} (circuit : HasCircuitSize 4 (targetFour T) s) : bound < s := by
  by_contra! hlt
  obtain ⟨t,ht,ws,sub,h⟩ := exists_run _ ⟨_,_,differs⟩ s circuit
  have hr : NatRun (mask k) (encL (targetFour T) rows) t (ws.map (fun a => encL a rows)) :=
    Run.map (fun a : BFn 4 => encL a rows)
      (fun a => by rw [rowsLen]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) h
  rw [output] at hr
  have hsub : (ws.map (fun a => encL a rows)).Sublist (xHead :: xTail) := inputs ▸ sub.map _
  by_cases heq : ws.map (fun a => encL a rows) = xHead :: xTail
  · rw [heq] at hr
    exact none t (ht.trans hlt) hr
  · exact essential _ (List.mem_sublists.2 hsub) heq (required hr)
def fourRows2 : List Nat := [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x2,0x2,0x2,0x2,0x2,0x2,0x2,0x2,0x2,0x2,0x2,0x4,0x4,0x4,0x4,0x4,0x4,0x4,0x4,0x4,0x4,0x4,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x8,0x3,0x5,0x6,0x7,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x3,0x5,0x6,0x7,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x3,0x5,0x6,0x7,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x3,0x5,0x6,0x7,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x3,0x5,0x6,0x7,0x9,0xa,0xb,0xc,0xd,0xe,0xf]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
theorem fourLower2 (s : Nat) (h : HasCircuitSize 4 (targetFour 0xfee8) s) : 6 < s := by
  apply size_from_fourBarrier 0xfee8 55 6 fourRows2 0x2add5bab756ead800000003ff800 [0x336e6dcdb9b736800001ffc00000,0x3c778ef1de3bc7000ffe00000000,0x3f87f0fe1fc3f87ff00000000000] (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) _ h
  apply none_from_barrier
  decide +kernel
end LivePart6
end L8703Lower
end ProofPart9

section ProofPart10
namespace L10586OffThreeLower
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open CircuitHelpers.PermInputs CircuitHelpers.Forest
open L10586OffThree (V target)
open L11022Rewire
private def leafTarget (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)
private def dropLeaf (i : Fin 5) : Fin 4 := ([0,1,2,3,0] : List (Fin 4)).getD i.val 0
private theorem leaf_pin : ∀ x : Fin 4 → Bool,
    leafTarget (Function.update (x ∘ dropLeaf) 4 false) = L8703Lower.targetFour 0xfee8 x := by
  decide
private theorem leaf_lower (s : ℕ) (h : HasCircuitSize 5 leafTarget s) : 8 ≤ s := by
  by_contra! small
  obtain ⟨C,fan,size,value⟩ := h
  have smaller : HasCircuitSize 5 leafTarget (6+1) := ⟨C,fan,by omega,value⟩
  have pinned := one_gate_at 4 leafTarget 4 false 6
    ⟨fun i => decide (i=0),by decide⟩ ⟨fun _ => false,fun _ => true,by decide⟩ smaller
  have compact := relabel_size dropLeaf _ 6 pinned
  rw [funext leaf_pin] at compact
  exact (Nat.lt_irrefl 6) (L8703Lower.fourLower2 6 compact)
private def offFourMap (i : V) : Fin 5 := ([1,4,2,0,3,0] : List (Fin 5)).getD i.val 0
private theorem off_four_table : ∀ x : Fin 5 → Bool,
    target (Function.update (x ∘ offFourMap) 3 false) = leafTarget x := by
  decide
theorem pin_four_false_lower (s : ℕ) (fit : HasCircuitSize 6
    (fun x => target (Function.update x 3 false)) s) : 8 ≤ s := by
  have reindexed := relabel_size offFourMap _ s fit
  rw [funext off_four_table] at reindexed
  exact leaf_lower _ reindexed
private theorem short_drop_impossible {gs : List Gate} (short : gs.length ≤ 9)
    (drop : Drop target (3 : V) false 2 gs.length) : False := by
  obtain ⟨s,save,fit⟩ := drop
  have floor := pin_four_false_lower s fit
  omega
private theorem only_binary {gs : List Gate} (clean : CleanL 6 gs)
    (zero : notGateCount gs = 0) : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
  intro g mem
  obtain ⟨p,hit⟩ := List.mem_iff_getElem?.mp mem
  rcases clean p g hit with ⟨tag,_⟩ | ⟨tags,_⟩
  · have := one_not_gate_positive (gs := gs) ⟨g,mem,tag⟩
    omega
  · exact tags
private theorem raw_agree {x y : V → Bool} (same : ∀ i, i ≠ (3:V) → x i = y i) :
    ∀ j : ℕ, j ≠ 3 → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
  intro j apart
  by_cases valid : j < 6
  · let i : V := ⟨j,valid⟩
    have h : i ≠ (3 : V) := fun eq => apart (congrArg Fin.val eq)
    rw [show (List.ofFn x).getD j false = x i from getD_ofFn 6 x false i,
      show (List.ofFn y).getD j false = y i from getD_ofFn 6 y false i]
    exact same i h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
private theorem prefix_agree (pre : List Gate) (peer : ℕ)
    (ignored : ∀ g ∈ pre, 3 ∉ g.inputs) (other : peer ≠ 3) (x y : V → Bool)
    (same : ∀ i, i ≠ (3:V) → x i = y i) :
    (wiresFrom pre (List.ofFn x)).getD peer false =
      (wiresFrom pre (List.ofFn y)).getD peer false :=
  agree_except 3 pre _ _ ignored (by simp) (raw_agree same) peer other
private theorem pivotal_peer (pre post : List Gate) (peer out : ℕ)
    (ignoredPre : ∀ g ∈ pre, 3 ∉ g.inputs) (ignoredPost : ∀ g ∈ post, 3 ∉ g.inputs)
    (other : peer ≠ 3) (internal : out ≠ 3)
    (fit : ∀ x : V → Bool, (⟨pre ++ ⟨.or,[3,peer]⟩ :: post,out⟩ : Circuit).eval
      (List.ofFn x) = target x)
    (x : V → Bool) (off : target x = false) (on : target (Function.update x 3 true) = true) :
    (wiresFrom pre (List.ofFn x)).getD peer false = false := by
  let y := Function.update x (3:V) true
  let wx := wiresFrom pre (List.ofFn x)
  let wy := wiresFrom pre (List.ofFn y)
  have same (i : V) (different : i ≠ 3) : x i = y i := by
    simp [y, Function.update_of_ne different]
  have agree : ∀ j, j ≠ 3 → wx.getD j false = wy.getD j false :=
    agree_except 3 pre _ _ ignoredPre (by simp) (raw_agree same)
  have len : wx.length = wy.length := by simp [wx,wy,length_wiresFrom]
  cases yes : wx.getD peer false with
  | false => rfl
  | true =>
    have yes' : wy.getD peer false = true := (agree peer other).symm.trans yes
    have step : ∀ j, j ≠ 3 → (wx ++ [true]).getD j false = (wy ++ [true]).getD j false := by
      intro j different
      by_cases ending : j = wx.length
      · rw [ending,getD_snoc_eq,len,getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ ending,
          getD_snoc_ne _ _ _ _ (by simpa only [len] using ending)]
        exact agree j different
    have eval (z : V → Bool) (hit : (wiresFrom pre (List.ofFn z)).getD peer false = true) :
        target z = (wiresFrom post (wiresFrom pre (List.ofFn z) ++ [true])).getD out false := by
      rw [← fit z]
      change (wiresFrom (pre ++ ⟨.or,[3,peer]⟩ :: post) (List.ofFn z)).getD out false = _
      rw [wiresFrom_append]
      let bits := wiresFrom pre (List.ofFn z)
      change (wiresFrom post (bits ++ [GateOp.or.eval [bits.getD 3 false,bits.getD peer false]])).getD out false = _
      change bits.getD peer false = true at hit
      rw [hit]
      cases bits.getD 3 false <;> rfl
    have outEqual := agree_except 3 post _ _ ignoredPost (by simp [len]) step out internal
    exact (Bool.false_ne_true (off.symm.trans ((eval x yes).trans (outEqual.trans ((eval y yes').symm.trans on))))).elim
private def pivotalCover (x : V → Bool) : V → Bool :=
  let y := Function.update x 3 false
  if target (Function.update y 3 true) then y else Function.update y 1 true
set_option maxRecDepth 16384 in
private theorem pivotal_cover_spec : ∀ x : V → Bool, target x = false →
    target (pivotalCover x) = false ∧ target (Function.update (pivotalCover x) 3 true) = true ∧
    ∀ i, Function.update x 3 false i = true → pivotalCover x i = true := by
  decide
private theorem peer_sound (pre post : List Gate) (peer out : ℕ)
    (mono : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (ignoredPre : ∀ g ∈ pre, 3 ∉ g.inputs) (ignoredPost : ∀ g ∈ post, 3 ∉ g.inputs)
    (other : peer ≠ 3) (internal : out ≠ 3)
    (fit : ∀ x : V → Bool, (⟨pre ++ ⟨.or,[3,peer]⟩ :: post,out⟩ : Circuit).eval
      (List.ofFn x) = target x)
    (x : V → Bool) (off : target x = false) :
    (wiresFrom pre (List.ofFn x)).getD peer false = false := by
  let x0 := Function.update x (3:V) false
  let y := pivotalCover x
  have ⟨no,yes,dominates⟩ := pivotal_cover_spec x off
  have rejected := pivotal_peer pre post peer out ignoredPre ignoredPost other internal fit y no yes
  have same : ∀ i : V, i ≠ 3 → x i = x0 i := by
    intro i different
    simp [x0,Function.update_of_ne different]
  rw [prefix_agree pre peer ignoredPre other x x0 same]
  cases value : (wiresFrom pre (List.ofFn x0)).getD peer false with
  | false => rfl
  | true =>
    have pos := LineDegTest.W_mono pre mono
      (List.ofFn x0) (List.ofFn y) (by simp) (by
        intro j positive
        by_cases valid : j < 6
        · let i : V := ⟨j,valid⟩
          rw [show (List.ofFn x0).getD j false = x0 i from getD_ofFn 6 x0 false i] at positive
          rw [show (List.ofFn y).getD j false = y i from getD_ofFn 6 y false i]
          exact dominates i positive
        · rw [List.getD_eq_default _ _ (by simp; omega)] at positive
          cases positive) peer value
    exact (Bool.false_ne_true (rejected.symm.trans pos)).elim
private theorem rejecting_singleton : target (fun i => decide (i = (3:V))) = false := by decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 600000 in
theorem size_lower_ten (s : ℕ) (fit : HasCircuitSize 6 target s) : 10 ≤ s := by
  by_contra! small
  obtain ⟨gs,out,least,lengthBound,measure⟩ := exists_least_fewest_dirty_reads 6 s target
    L10586OffThree.nonconstant fit
  have short : gs.length ≤ 9 := by omega
  have budget := L10586OffThree.least_binary_budget least
  have noNot : notGateCount gs = 0 := by omega
  have mono := only_binary least.hcl noNot
  have remains := L10586OffThree.restrict_nonconstant (3:V)
  obtain ⟨r,reads⟩ := least.dep_read (3:V) (L10586OffThree.dependent 3) remains
  have unique (q) (read : Reads gs q 3) : q = r := by
    by_contra different
    exact short_drop_impossible short (least.save2 (3:V) false (remains false) q r different
      (rc_input false read) (rc_input false reads))
  obtain ⟨g,hit,source⟩ := reads
  have gmem : g ∈ gs := List.mem_iff_getElem?.mpr ⟨r,hit⟩
  have tag : g.op = .or := by
    rcases mono g gmem with isAnd | isOr
    · have constant : IsC 5 gs (3:V) false (6+r) :=
        isC_reader least.hcl (3:V) r g hit source false (Or.inr (by simp [fixBit,isAnd]))
      obtain ⟨q,after,_,lost⟩ := least.next (3:V) false (remains false) r
        ((List.getElem?_eq_some_iff.mp hit).1) constant
      exact False.elim (short_drop_impossible short (least.save2 (3:V) false (remains false) r q
        (ne_of_lt after) (rc_input false ⟨g,hit,source⟩) lost))
    · exact isOr
  have shape : ∃ peer : ℕ, peer ≠ 3 ∧ (g.inputs = [3,peer] ∨ g.inputs = [peer,3]) := by
    rcases least.hcl r g hit with ⟨isNot,_⟩ | ⟨_,a,b,_,_,args⟩
    · rw [tag] at isNot
      cases isNot
    · have distinct := least_gate_inputs_nodup least L10586OffThree.nonconstant g gmem
      have apart : a ≠ b := by simpa [args] using distinct
      simp only [args,List.mem_cons,List.not_mem_nil,or_false] at source
      rcases source with first | second
      · subst a
        exact ⟨b,apart.symm,Or.inl args⟩
      · subst b
        exact ⟨a,apart,Or.inr args⟩
  obtain ⟨peer,apart,args⟩ := shape
  have peerMem : peer ∈ g.inputs := by rcases args with eq | eq <;> simp [eq]
  have peerBound := (least.hcl r g hit).lt peer peerMem
  obtain ⟨pre,post,listEq,idxEq⟩ := split_at gs r g hit
  have peerEarlier : peer < 6+pre.length := by rwa [idxEq]
  have sourceEarlier : 3 < 6+pre.length := by omega
  have ignoredPre : ∀ a ∈ pre, 3 ∉ a.inputs := by
    intro g mem bad
    obtain ⟨q,atQ⟩ := List.mem_iff_getElem?.mp mem
    have bound := (List.getElem?_eq_some_iff.mp atQ).1
    have oldHit : gs[q]? = some g := by rw [listEq,List.getElem?_append_left bound,atQ]
    have := unique q ⟨g,oldHit,bad⟩
    omega
  have ignoredPost : ∀ a ∈ post, 3 ∉ a.inputs := by
    intro g mem bad
    obtain ⟨q,atQ⟩ := List.mem_iff_getElem?.mp mem
    have oldHit : gs[pre.length+1+q]? = some g := by
      rw [listEq,List.getElem?_append_right (by omega)]
      rw [show pre.length+1+q-pre.length = q+1 by omega]
      exact atQ
    have := unique (pre.length+1+q) ⟨g,oldHit,bad⟩
    omega
  have prefixMono : ∀ g ∈ pre, g.op = .and ∨ g.op = .or := by
    intro g mem
    apply mono g
    rw [listEq]
    exact List.mem_append_left _ mem
  have readsPre : ∀ g ∈ pre, ∀ w ∈ g.inputs, w < 6+pre.length := by
    intro g mem w port
    obtain ⟨q,atQ⟩ := List.mem_iff_getElem?.mp mem
    have bound := (List.getElem?_eq_some_iff.mp atQ).1
    have found : gs[q]? = some g := by rw [listEq,List.getElem?_append_left bound,atQ]
    have := (least.hcl q g found).lt w port
    omega
  have internal : out ≠ 3 := by
    intro eq
    have value := least.hev (fun i => decide (i = (3:V)))
    rw [eq,vl_input gs _ 3 (by decide),rejecting_singleton] at value
    simp at value
  let old : Circuit := ⟨pre ++ ⟨.or,[3,peer]⟩ :: post,out⟩
  have update : CleanL 6 old.gates ∧
      (∀ (x : V → Bool) (w : ℕ), vl old.gates x w = vl gs x w) ∧
      dirtyReads 6 target old.gates = dirtyReads 6 target gs := by
    rcases args with args | args
    · have gate : g = ⟨.or,[3,peer]⟩ :=
        (congrArg (fun ins => (⟨g.op,ins⟩ : Gate)) args).trans
          (congrArg (fun op => (⟨op,[3,peer]⟩ : Gate)) tag)
      have equal : gs = old.gates := listEq.trans (congrArg (fun a => pre ++ a :: post) gate)
      rw [← equal]
      exact ⟨least.hcl,fun _ _ => rfl,rfl⟩
    · have gate : g = ⟨.or,[peer,3]⟩ :=
        (congrArg (fun ins => (⟨g.op,ins⟩ : Gate)) args).trans
          (congrArg (fun op => (⟨op,[peer,3]⟩ : Gate)) tag)
      have equal : gs = pre ++ ⟨.or,[peer,3]⟩ :: post :=
        listEq.trans (congrArg (fun a => pre ++ a :: post) gate)
      have clean : CleanL 6 (pre ++ ⟨.or,[peer,3]⟩ :: post) := by
        rw [← equal]
        exact least.hcl
      rw [equal]
      exact L11022ReaderSwap.swap_middle 6 target pre post .or 3 peer (Or.inr rfl) clean
  have oldSize : old.gates.length = gs.length := by
    rw [listEq]
    simp [old]
  have computes (x : V → Bool) : old.eval (List.ofFn x) = target x :=
    (update.2.1 x out).trans (least.hev x)
  have sound := peer_sound pre post peer out prefixMono ignoredPre ignoredPost apart internal computes
  let row : V → Bool := fun i => decide (i = (3:V))
  have dirtySource : dirty 6 target old 3 = true := by
    classical
    unfold dirty
    apply decide_eq_true
    refine ⟨row,rejecting_singleton,?_⟩
    change vl old.gates row 3 = true
    rw [vl_input old.gates row 3 (by decide)]
    decide
  have dirtyGate : dirty 6 target old (6+pre.length) = true := by
    classical
    unfold dirty
    apply decide_eq_true
    refine ⟨row,rejecting_singleton,?_⟩
    change vl old.gates row (6+pre.length) = true
    have atGate : old.gates[pre.length]? = some ⟨.or,[3,peer]⟩ := by simp [old]
    rw [vl_gate old.gates update.1 row pre.length _ atGate]
    change GateOp.or.eval [vl old.gates row 3,vl old.gates row peer] = true
    rw [vl_input old.gates row 3 (by decide)]
    change GateOp.or.eval [true,vl old.gates row peer] = true
    rfl
  let fresh := appendOr 6 (splice 6 pre post 3 out) peer
  have result := promotion_reduces_dirty_reads 6 target pre post 3 peer out
    sourceEarlier peerEarlier readsPre sound computes dirtyGate dirtySource
  have ⟨newFit,counts⟩ := result
  have valid : out < 6+old.gates.length := by rw [oldSize]; exact L10586OffThree.output_valid least
  have newClean := promote_clean 6 pre post 3 peer out update.1 sourceEarlier peerEarlier valid
  have newSize : fresh.gates.length = gs.length := by
    rw [← oldSize]
    change fresh.size = old.size
    rw [promote_size]
    simp [old,Circuit.size,Nat.add_assoc]
  have minimal := measure fresh.gates fresh.output newClean newFit newSize
  change dirtyReads 6 target fresh.gates + 1 = dirtyReads 6 target old.gates at counts
  rw [update.2.2] at counts
  omega
theorem pin_three_false_lower_ten (s : ℕ)
    (fit : HasCircuitSize 7 (fun x => L10586Control.target (Function.update x 3 false)) s) :
    10 ≤ s := by
  have compact := relabel_size L10586OffThree.compact _ s fit
  rw [funext L10586OffThree.compact_pin] at compact
  exact size_lower_ten _ compact
end L10586OffThreeLower
end ProofPart10

section ProofPart11
namespace L10586EarCofactors
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open CircuitHelpers.PermInputs CircuitHelpers.Forest
open L10586Control (target)
abbrev Input := Fin 7 → Bool
private def onThree (x : Input) : Bool := target (Function.update x 3 true)
private def dropOne (x : Input) : Bool := onThree (Function.update x 1 false)
private def dropOneFive (x : Input) : Bool := dropOne (Function.update x 5 false)
private def cliqueProjection (i : Fin 7) : Fin 4 :=
  ([0,0,1,0,2,0,3] : List (Fin 4)).getD i.val 0
private theorem clique_table : ∀ x : Fin 4 → Bool,
    dropOneFive (x ∘ cliqueProjection) = L8703Lower.targetFour 0xfee8 x := by
  decide
theorem pin_three_true_lower (s : ℕ)
    (fit : HasCircuitSize 7 (fun x => target (Function.update x 3 true)) s) : 9 ≤ s := by
  by_contra! small
  obtain ⟨C,fan,size,value⟩ := fit
  have exactEight : HasCircuitSize 7 onThree (7+1) := ⟨C,fan,by omega,value⟩
  have first : HasCircuitSize 7 dropOne 7 :=
    one_gate_at 6 onThree 1 false 7 ⟨fun _ => false,by decide⟩
      ⟨fun _ => false,fun _ => true,by decide⟩ exactEight
  have second : HasCircuitSize 7 dropOneFive 6 :=
    one_gate_at 6 dropOne 5 false 6 ⟨fun _ => false,by decide⟩
      ⟨fun _ => false,fun _ => true,by decide⟩ first
  have compact := relabel_size cliqueProjection _ 6 second
  rw [funext clique_table] at compact
  exact (Nat.lt_irrefl 6) (L8703Lower.fourLower2 6 compact)
theorem three_unique_reader {gs : List Gate} {out : ℕ}
    (least : Least 7 target gs out) (small : gs.length ≤ 12) :
    ∃ r, Reads gs r 3 ∧ ∀ q, Reads gs q 3 → q = r := by
  have nonconstant := L10586Branch.restrict_nonconstant 3
  obtain ⟨r,reads⟩ := least.dep_read (3 : Fin 7) (L10586Branch.dependent 3) nonconstant
  refine ⟨r,reads,?_⟩
  intro q read
  by_contra different
  have costs := least.two_readers (3 : Fin 7) nonconstant q r different read reads
  rcases costs with ⟨⟨s,save,fit⟩,_⟩ | ⟨⟨s,save,fit⟩,_⟩ | ⟨_,⟨s,save,fit⟩⟩
  · have := L10586OffThreeLower.pin_three_false_lower_ten s fit
    omega
  · have := L10586OffThreeLower.pin_three_false_lower_ten s fit
    omega
  · have := pin_three_true_lower s fit
    omega
end L10586EarCofactors
end ProofPart11

section ProofPart12
namespace L10586EarShape
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control (target)
private theorem binary_of_no_not {gs sub : List Gate} (clean : CleanL 7 gs)
    (part : ∀ g ∈ sub, g ∈ gs) (count : notGateCount sub = 0) :
    ∀ g ∈ sub, g.op = .and ∨ g.op = .or := by
  intro g mem
  obtain ⟨i,hit⟩ := List.mem_iff_getElem?.mp (part g mem)
  rcases clean i g hit with ⟨notTag,_⟩ | ⟨binary,_⟩
  · have := one_not_gate_positive (gs := sub) ⟨g,mem,notTag⟩
    omega
  · exact binary
private theorem sole_not_impossible (pre post : List Gate) (out : ℕ)
    (least : Least 7 target (pre ++ ⟨.not,[3]⟩ :: post) out)
    (budget : notGateCount (pre ++ ⟨.not,[3]⟩ :: post) ≤ 1)
    (unique : ∀ q, Reads (pre ++ ⟨.not,[3]⟩ :: post) q 3 → q = pre.length) : False := by
  let gs : List Gate := pre ++ ⟨.not,[3]⟩ :: post
  have counts : notGateCount (pre ++ (⟨.not,[3]⟩ : Gate) :: post) =
      notGateCount pre + 1 + notGateCount post := by
    simp [notGateCount,isNotGate,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have countPre : notGateCount pre = 0 := by omega
  have countPost : notGateCount post = 0 := by omega
  have before := binary_of_no_not least.hcl (fun g mem => List.mem_append_left _ mem) countPre
  have after := binary_of_no_not least.hcl (fun g mem =>
    List.mem_append_right _ (List.mem_cons_of_mem _ mem)) countPost
  have pure : ∀ g ∈ pre ++ post, (g.op = .and ∨ g.op = .or) ∧ 3 ∉ g.inputs := by
    intro g mem
    rcases List.mem_append.mp mem with left | right
    · refine ⟨before g left,?_⟩
      intro used
      obtain ⟨r,hit⟩ := List.mem_iff_getElem?.mp left
      have shorter := (List.getElem?_eq_some_iff.mp hit).1
      have oldHit : gs[r]? = some g := by simp [gs,List.getElem?_append_left shorter,hit]
      have eq := unique r ⟨g,oldHit,used⟩
      omega
    · refine ⟨after g right,?_⟩
      intro used
      obtain ⟨r,hit⟩ := List.mem_iff_getElem?.mp right
      have oldHit : gs[pre.length+1+r]? = some g := by
        change (pre ++ ⟨.not,[3]⟩ :: post)[pre.length+1+r]? = some g
        rw [List.getElem?_append_right (by omega)]
        rw [show pre.length+1+r-pre.length = r+1 by omega]
        exact hit
      have eq := unique (pre.length+1+r) ⟨g,oldHit,used⟩
      omega
  let x : Fin 7 → Bool := fun i => decide (i = 1)
  let y : Fin 7 → Bool := Function.update x 3 true
  have outApart : out ≠ 3 := by
    intro eq
    have singleton := least.hev (fun i => decide (i = 3))
    rw [eq,vl_input _ _ 3 (by decide)] at singleton
    revert singleton
    decide
  have same : ∀ i, i ≠ (3 : Fin 7) → x i = y i := by
    intro i different
    simp [y,Function.update_of_ne different]
  have reject : target x = false := by decide
  have accept : target y = true := by decide
  have contradiction := L11022Rewire.sole_not_reader_antitone 7 3 pre post out pure
    outApart x y (by decide) (by decide) same ((least.hev y).trans accept)
  have impossible := (least.hev x).symm.trans contradiction
  exact Bool.false_ne_true (reject.symm.trans impossible)
theorem unique_readers_binary {gs : List Gate} {out r : ℕ} {g : Gate}
    (least : Least 7 target gs out) (budget : notGateCount gs ≤ 1)
    (hit : gs[r]? = some g) (read : 3 ∈ g.inputs)
    (unique : ∀ q, Reads gs q 3 → q = r) : g.op = .and ∨ g.op = .or := by
  rcases least.hcl r g hit with ⟨notTag,a,_,args⟩ | ⟨binary,_⟩
  · exfalso
    have eq : a = 3 := by simpa [args,eq_comm] using read
    subst a
    have repr : g = ⟨.not,[3]⟩ := by
      cases g
      simp_all
    subst g
    obtain ⟨pre,post,rfl,rfl⟩ := split_at gs r _ hit
    exact sole_not_impossible pre post out least budget unique
  · exact binary
private theorem no_three_low_losses {s : ℕ} (cap : s ≤ 12) :
    ¬ Drop target (3 : Fin 7) false 3 s := by
  rintro ⟨cost,saved,exactness⟩
  have := L10586OffThreeLower.pin_three_false_lower_ten cost exactness
  omega
private theorem and_const_false {gs : List Gate} (clean : CleanL 7 gs)
    {r : ℕ} {g : Gate} (hit : gs[r]? = some g) (tag : g.op = .and)
    (read : 3 ∈ g.inputs) : stF 6 gs (3 : Fin 7) false (7+r) = Stat.const false := by
  obtain ⟨b,hb⟩ := isC_reader clean (3 : Fin 7) r g hit read false
    (Or.inr (by simp [fixBit,tag]))
  have evaluated := st_val_const 6 gs clean (3 : Fin 7) false (7+r) b hb (fun _ => false)
  rw [vl_gate gs clean _ r g hit,tag] at evaluated
  have rawFalse : vl gs (ins (3 : Fin 7) false (fun _ => false)) 3 = false := by
    rw [vl_input gs _ 3 (by decide)]
    decide
  rcases clean r g hit with ⟨bad,_⟩ | ⟨_,a,c,_,_,args⟩
  · rw [tag] at bad
    cases bad
  · rw [args] at read evaluated
    simp only [List.mem_cons, List.not_mem_nil, or_false] at read
    rcases read with rfl | rfl
    · simp only [List.map_cons, List.map_nil, GateOp.eval, rawFalse, List.all_cons, id_eq,
        Bool.false_and] at evaluated
      simpa only [← evaluated] using hb
    · simp only [List.map_cons, List.map_nil, GateOp.eval, rawFalse, List.all_cons, id_eq,
        Bool.false_and, Bool.and_false] at evaluated
      simpa only [← evaluated] using hb
theorem and_reader_next_or {gs : List Gate} {out r : ℕ} {g : Gate}
    (least : Least 7 target gs out) (cap : gs.length ≤ 12)
    (hit : gs[r]? = some g) (tag : g.op = .and) (read : 3 ∈ g.inputs) :
    ∃ q h, r < q ∧ gs[q]? = some h ∧ h.op = .or ∧ (7+r) ∈ h.inputs ∧
      ∀ v, Reads gs v (7+r) → v = q := by
  have nc := L10586Branch.restrict_nonconstant (3 : Fin 7) false
  have rawRC : RC 6 gs (3 : Fin 7) false r := rc_input false ⟨g,hit,read⟩
  have status := and_const_false least.hcl hit tag read
  have constant : IsC 6 gs (3 : Fin 7) false (7+r) := ⟨false,status⟩
  obtain ⟨q,rq,reader,qRC⟩ := least.next (3 : Fin 7) false nc r (reads_len ⟨g,hit,read⟩) constant
  have qUnique (v : ℕ) (readerV : Reads gs v (7+r)) : v = q := by
    by_contra different
    have rv := reads_lt least.hcl readerV
    exact no_three_low_losses cap <| least.save3 (3 : Fin 7) false nc r q v
      (by omega) (by omega) (Ne.symm different) rawRC qRC (rc_of_reads readerV constant)
  obtain ⟨h,hitQ,hread⟩ := reader
  refine ⟨q,h,rq,hitQ,?_,hread,qUnique⟩
  by_contra notOr
  have second : IsC 6 gs (3 : Fin 7) false (7+q) := by
    rcases least.hcl q h hitQ with ⟨_,a,_,args⟩ | ⟨ha | ho,_⟩
    · have eq : a = 7+r := by simpa [args,eq_comm] using hread
      subst a
      apply st_allconst 6 gs least.hcl (3 : Fin 7) false q h hitQ
      intro a mem
      have eq : a = 7+r := by simpa [args] using mem
      subst a
      exact constant
    · exact const_read 6 gs least.hcl (3 : Fin 7) false q h hitQ (7+r) hread
        (by simpa [fixBit,ha] using status)
    · exact (notOr ho).elim
  obtain ⟨v,qv,_,vRC⟩ := least.next (3 : Fin 7) false nc q
    (reads_len ⟨h,hitQ,hread⟩) second
  exact no_three_low_losses cap <| least.save3 (3 : Fin 7) false nc r q v
    (by omega) (by omega) (by omega) rawRC qRC vRC
end L10586EarShape
end ProofPart12

section ProofPart13
namespace L10586WeightedRestriction
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)
abbrev binaryCount (gs : List Gate) : ℕ := opCount (fun op => !isNotGate op) gs
private theorem simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; rfl
  · simp at hg
  · simp at hg
private theorem simplify_count_le (test : GateOp → Bool) (op : GateOp)
    (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases choice : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have mem : g ∈ (simplify op m ins).1 := by simp [choice]
    have same := simplify_same_op op m ins g mem
    simp [opCount,same]
theorem elim_count_selected (test : GateOp → Bool) (n : ℕ)
    (acc : List Stat × List Gate) (gs : List Gate) (good : ∀ g ∈ gs, NOk g)
    (S : Finset ℕ) (lost : ∀ p ∈ S, ∃ g, gs[p]? = some g ∧ test g.op = true ∧
      ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (.const false) = .const c) :
    opCount test (elim n gs acc).2 + S.card ≤ opCount test acc.2 + opCount test gs := by
  induction gs using List.reverseRecOn generalizing S with
  | nil =>
    have empty : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p mem
      obtain ⟨g,hit,_⟩ := lost p mem
      simp at hit
    simp [empty,elim,opCount]
  | append_singleton gs g ih =>
    have step : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]
      rfl
    have prior (a : ℕ) (d : Stat) (older : a < acc.1.length + gs.length) :
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      elim_split_getD_lt n gs g [] acc a d older
    have inductionBound := ih (fun g hg => good g (List.mem_append_left _ hg)) (S.erase gs.length) (by
      intro p mem
      obtain ⟨apart,inS⟩ := Finset.mem_erase.mp mem
      obtain ⟨h,hit,mark,a,used,earlier,c,constant⟩ := lost p inS
      have older : p < gs.length := by
        have hlen := (List.getElem?_eq_some_iff.mp hit).1
        simp only [List.length_append,List.length_singleton] at hlen
        omega
      rw [List.getElem?_append_left older] at hit
      rw [prior a _ (by omega)] at constant
      exact ⟨h,hit,mark,a,used,earlier,c,constant⟩)
    rw [step]
    by_cases last : gs.length ∈ S
    · obtain ⟨h,hit,mark,a,used,earlier,c,constant⟩ := lost _ last
      rw [List.getElem?_concat_length] at hit
      have eq := Option.some.inj hit
      subst h
      rw [prior a _ earlier] at constant
      have none : (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (.const false))).1 = none := by
        have ok := good g (by simp)
        exact simplify_count _ _ _ ok.1.1 (by simpa using ok.1.2)
          (fun h => by simpa using ok.2 h) ⟨c,List.mem_map.mpr ⟨a,used,constant⟩⟩
      have erased := Finset.card_erase_of_mem last
      have chosen : 1 ≤ S.card := Finset.card_pos.mpr ⟨_,last⟩
      have unchanged : (elimStep n (elim n gs acc) g).2 = (elim n gs acc).2 := by
        unfold elimStep
        rw [none]
        simp
      rw [unchanged]
      simp [opCount,mark] at inductionBound ⊢
      omega
    · rw [Finset.erase_eq_of_notMem last] at inductionBound
      have added := simplify_count_le test g.op (n + (elim n gs acc).2.length)
        (g.inputs.map fun i => (elim n gs acc).1.getD i (.const false))
      simp only [elimStep,opCount,List.countP_append,List.countP_cons,List.countP_nil,
        zero_add] at inductionBound added ⊢
      omega
theorem restrict_selected {n : ℕ} {gs : List Gate} (clean : CleanL (n+1) gs)
    (i : Fin (n+1)) (b : Bool) (test : GateOp → Bool) (S : Finset ℕ)
    (lost : ∀ p ∈ S, ∃ g, gs[p]? = some g ∧ test g.op = true ∧
      ∃ a ∈ g.inputs, IsC n gs i b a) :
    opCount test (passG n gs i b) + S.card ≤ opCount test gs := by
  have cnt := elim_count_selected test n (statAt n i b,[]) gs (clean_nok _ gs clean) S (by
    intro p mem
    obtain ⟨g,hit,mark,a,used,c,constant⟩ := lost p mem
    refine ⟨g,hit,mark,a,used,?_,c,constant⟩
    rw [show (statAt n i b, ([] : List Gate)).1.length = n+1 from statAt_length n i b]
    exact (clean p g hit).lt a used)
  simpa [passG,opCount] using cnt
theorem not_count_le {n : ℕ} {gs : List Gate} (clean : CleanL (n+1) gs)
    (i : Fin (n+1)) (b : Bool) : notGateCount (passG n gs i b) ≤ notGateCount gs := by
  simpa [opCount,notGateCount,List.countP_eq_length_filter] using
    restrict_selected clean i b isNotGate ∅ (by simp)
theorem binary_count_losses {n : ℕ} {gs : List Gate} (clean : CleanL (n+1) gs)
    (i : Fin (n+1)) (b : Bool) (S : Finset ℕ)
    (lost : ∀ p ∈ S, ∃ g, gs[p]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧
      ∃ a ∈ g.inputs, IsC n gs i b a) :
    binaryCount (passG n gs i b) + S.card ≤ binaryCount gs := by
  apply restrict_selected clean i b _ S
  intro p mem
  obtain ⟨g,hit,tag,a,used,constant⟩ := lost p mem
  exact ⟨g,hit,tag.elim (fun h => by simp [h,isNotGate]) (fun h => by simp [h,isNotGate]),
    a,used,constant⟩
theorem binary_add_not (gs : List Gate) : binaryCount gs + notGateCount gs = gs.length := by
  rw [notGateCount,← List.countP_eq_length_filter]
  rw [Nat.add_comm]
  exact (gs.length_eq_countP_add_countP (fun g => isNotGate g.op)).symm
theorem restrict_eval {n : ℕ} {gs : List Gate} {out : ℕ}
    {f : (Fin (n+1) → Bool) → Bool} (clean : CleanL (n+1) gs)
    (exactness : ∀ x, vl gs x out = f x) (i : Fin (n+1)) (b : Bool)
    (nonconstant : ∃ x y : Fin n → Bool, f (ins i b x) ≠ f (ins i b y)) :
    ∃ o, CleanL n (passG n gs i b) ∧ ∀ x : Fin n → Bool,
      vl (passG n gs i b) x o = f (ins i b x) := by
  cases status : stF n gs i b out with
  | const c =>
    obtain ⟨x,y,apart⟩ := nonconstant
    have fixed (z : Fin n → Bool) : f (ins i b z) = c :=
      (exactness _).symm.trans (st_val_const n gs clean i b out c status z)
    exact (apart ((fixed x).trans (fixed y).symm)).elim
  | wire o =>
    have strict : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs clean g hg).1) (inv_at n i b _)
        (by intro p g hp; simp at hp)
    exact ⟨o,strict,fun x => (st_val_wire n gs clean i b out o status x).symm.trans (exactness _)⟩
theorem binary_reader_of_pivot {m : ℕ} {gs : List Gate} {out : ℕ}
    (clean : CleanL m gs) (budget : notGateCount gs ≤ 1) (p : Fin m) (outApart : out ≠ p.val)
    (x y : Fin m → Bool) (off : x p = false) (on : y p = true)
    (same : ∀ q, q ≠ p → x q = y q) (reject : vl gs x out = false) (accept : vl gs y out = true) :
    ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧ p.val ∈ g.inputs := by
  classical
  by_contra missing
  have noBinary (q : ℕ) (g : Gate) (hit : gs[q]? = some g)
      (tag : g.op = .and ∨ g.op = .or) : p.val ∉ g.inputs :=
    fun mem => missing ⟨q,g,hit,tag,mem⟩
  have isRead : ∃ q, Reads gs q p.val := by
    by_contra none
    have ignored : ∀ g ∈ gs, p.val ∉ g.inputs := by
      intro g mem reads
      obtain ⟨q,hit⟩ := List.mem_iff_getElem?.mp mem
      exact none ⟨q,g,hit,reads⟩
    have equal : vl gs x out = vl gs y out := by
      apply agree_except p.val gs _ _ ignored (by simp) _ out outApart
      intro i apart
      by_cases hi : i < m
      · rw [show (List.ofFn x).getD i false = x ⟨i,hi⟩ from getD_ofFn m x false ⟨i,hi⟩,
          show (List.ofFn y).getD i false = y ⟨i,hi⟩ from getD_ofFn m y false ⟨i,hi⟩]
        exact same ⟨i,hi⟩ (fun eq => apart (congrArg Fin.val eq))
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    exact Bool.false_ne_true (reject.symm.trans (equal.trans accept))
  obtain ⟨q,g,hit,read⟩ := isRead
  have repr : g = ⟨.not,[p.val]⟩ := by
    rcases clean q g hit with ⟨tag,r,_,args⟩ | ⟨tag,_⟩
    · have eq : r = p.val := by simpa [args,eq_comm] using read
      subst r
      cases g
      simp_all
    · exact (noBinary q g hit tag read).elim
  subst g
  obtain ⟨pre,post,rfl,rfl⟩ := split_at gs q _ hit
  have counts : notGateCount (pre ++ (⟨.not,[p.val]⟩ : Gate) :: post) =
      notGateCount (pre ++ post) + 1 := by
    simp [notGateCount,isNotGate,Nat.add_comm,Nat.add_left_comm]
  have none : notGateCount (pre ++ post) = 0 := by omega
  have rest : ∀ g ∈ pre ++ post, (g.op = .and ∨ g.op = .or) ∧ p.val ∉ g.inputs := by
    intro g mem
    have located : ∃ t, (pre ++ ⟨.not,[p.val]⟩ :: post)[t]? = some g :=
      List.mem_iff_getElem?.mp (by
        rcases List.mem_append.mp mem with left | right
        · exact List.mem_append_left _ left
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ right))
    obtain ⟨t,atT⟩ := located
    rcases clean t g atT with ⟨tag,_⟩ | ⟨tag,_⟩
    · have := one_not_gate_positive ⟨g,mem,tag⟩
      omega
    · exact ⟨tag,noBinary t g atT tag⟩
  have contradiction := L11022Rewire.sole_not_reader_antitone m p pre post out rest
    outApart x y off on same accept
  exact Bool.false_ne_true (reject.symm.trans contradiction)
end L10586WeightedRestriction
end ProofPart13

section ProofPart14
namespace L10586BinaryCofactors
open L11022RestrictSupport L10586WeightedRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control (target)
abbrev cliqueTarget := L8703Lower.targetFour 0xfee8
def K4BinaryLower : Prop := ∀ (gs : List Gate) (out : ℕ), CleanL 4 gs →
  (∀ x, vl gs x out = cliqueTarget x) → 7 ≤ binaryCount gs
def highFive (x : Fin 5 → Bool) : Bool :=
  cliqueTarget (x ∘ Fin.succAbove (3 : Fin 5)) || x 3
def highSix (x : Fin 6 → Bool) : Bool := highFive (x ∘ Fin.succAbove (1 : Fin 6)) || x 1
private theorem high_table : ∀ x : Fin 6 → Bool,
    target (ins (3 : Fin 7) true x) = highSix x := by decide
private theorem five_table : ∀ x : Fin 5 → Bool,
    highSix (ins (1 : Fin 6) false x) = highFive x := by decide
private theorem four_table : ∀ x : Fin 4 → Bool,
    highFive (ins (3 : Fin 5) false x) = cliqueTarget x := by decide
theorem remove_pivotal_binary {n : ℕ} {gs : List Gate} {out : ℕ}
    {f : (Fin (n+1) → Bool) → Bool} {pinned : (Fin n → Bool) → Bool}
    (clean : CleanL (n+1) gs) (oneNot : notGateCount gs ≤ 1)
    (exactness : ∀ x, vl gs x out = f x) (p : Fin (n+1))
    (pinExact : ∀ x, f (ins p false x) = pinned x)
    (posPivot : ∃ x y : Fin (n+1) → Bool, x p = false ∧ y p = true ∧
      (∀ q, q ≠ p → x q = y q) ∧ f x = false ∧ f y = true)
    (pinNC : ∃ x y : Fin n → Bool, pinned x ≠ pinned y) :
    ∃ o, CleanL n (passG n gs p false) ∧
      (∀ x, vl (passG n gs p false) x o = pinned x) ∧
      binaryCount (passG n gs p false) + 1 ≤ binaryCount gs ∧
      notGateCount (passG n gs p false) ≤ 1 := by
  have pinnedNC : ∃ x y : Fin n → Bool, f (ins p false x) ≠ f (ins p false y) := by
    obtain ⟨x,y,apart⟩ := pinNC
    exact ⟨x,y,by simpa only [pinExact] using apart⟩
  have outApart : out ≠ p.val := by
    intro eq
    obtain ⟨x,y,apart⟩ := pinnedNC
    have fixed (z : Fin n → Bool) : f (ins p false z) = false := by
      rw [← exactness,eq,vl_input _ _ _ p.isLt]
      exact Fin.insertNth_apply_same _ _ _
    exact apart ((fixed x).trans (fixed y).symm)
  obtain ⟨x,y,off,on,same,reject,accept⟩ := posPivot
  obtain ⟨q,g,hit,tag,read⟩ := binary_reader_of_pivot clean oneNot p outApart x y off on same
    ((exactness x).trans reject) ((exactness y).trans accept)
  obtain ⟨o,strict,ev⟩ := restrict_eval clean exactness p false pinnedNC
  have cut := binary_count_losses clean p false {q} (by
    intro k mem
    rw [Finset.mem_singleton] at mem
    subst k
    exact ⟨g,hit,tag,p.val,read,false,stF_self n gs p false⟩)
  exact ⟨o,strict,fun z => (ev z).trans (pinExact z),by simpa using cut,
    (not_count_le clean p false).trans oneNot⟩
theorem high_six_binary_lower (clique : K4BinaryLower) {gs : List Gate} {out : ℕ} (clean : CleanL 6 gs)
    (oneNot : notGateCount gs ≤ 1) (ev : ∀ x, vl gs x out = highSix x) :
    9 ≤ binaryCount gs := by
  let five := passG 5 gs (1 : Fin 6) false
  obtain ⟨o5,h5,v5,c5,n5⟩ := remove_pivotal_binary clean oneNot ev (1 : Fin 6) five_table
    ⟨fun _ => false,fun j => decide (j=1),by decide,by decide,by decide,by decide,by decide⟩
    ⟨fun _ => false,fun _ => true,by decide⟩
  let four := passG 4 five (3 : Fin 5) false
  obtain ⟨o4,h4,v4,c4,_⟩ := remove_pivotal_binary h5 n5 v5 (3 : Fin 5) four_table
    ⟨fun _ => false,fun j => decide (j=3),by decide,by decide,by decide,by decide,by decide⟩
    ⟨fun _ => false,fun _ => true,by decide⟩
  have k4 := clique _ o4 h4 v4
  change binaryCount five + 1 ≤ binaryCount gs at c5
  change binaryCount four + 1 ≤ binaryCount five at c4
  change 7 ≤ binaryCount four at k4
  omega
theorem pin_three_true_binary (clique : K4BinaryLower) {gs : List Gate} {out : ℕ} (clean : CleanL 7 gs)
    (oneNot : notGateCount gs ≤ 1) (ev : ∀ x, vl gs x out = target x) :
    9 ≤ binaryCount (passG 6 gs (3 : Fin 7) true) := by
  have nc : ∃ x y : Fin 6 → Bool,
      target (ins (3 : Fin 7) true x) ≠ target (ins (3 : Fin 7) true y) :=
    ⟨fun _ => false,fun _ => true,by decide⟩
  obtain ⟨o,strict,compute⟩ := restrict_eval clean ev (3 : Fin 7) true nc
  exact high_six_binary_lower clique strict ((not_count_le clean (3 : Fin 7) true).trans oneNot)
    (fun x => (compute x).trans (high_table x))
end L10586BinaryCofactors
end ProofPart14

section ProofPart15
namespace L10586EarOrShape
open L11022RestrictSupport L10586WeightedRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control (target)
private def BinaryConstReader (gs : List Gate) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧
    ∃ a ∈ g.inputs, IsC 6 gs (3 : Fin 7) true a
private theorem no_three_high {gs : List Gate} {out a b c : ℕ}
    (clique : L10586BinaryCofactors.K4BinaryLower)
    (least : Least 7 target gs out) (budget : binaryCount gs ≤ 11)
    (oneNot : notGateCount gs ≤ 1) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (ha : BinaryConstReader gs a) (hb : BinaryConstReader gs b)
    (hc : BinaryConstReader gs c) : False := by
  have upper := binary_count_losses least.hcl (3 : Fin 7) true {a,b,c} (by
    intro p mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with rfl | rfl | rfl <;> assumption)
  rw [Finset.card_eq_three.mpr ⟨a,b,c,ab,ac,bc,rfl⟩] at upper
  have lower := L10586BinaryCofactors.pin_three_true_binary clique least.hcl oneNot least.hev
  omega
private theorem later_not_impossible {gs : List Gate} (oneNot : notGateCount gs ≤ 1)
    {p q : ℕ} {g h : Gate} (lt : p < q) (hit : gs[p]? = some g)
    (second : gs[q]? = some h) (tag : g.op = .not) (other : h.op = .not) : False := by
  obtain ⟨pre,post,rfl,rfl⟩ := split_at gs p g hit
  have inside : post[q-pre.length-1]? = some h := by
    rw [List.getElem?_append_right (by omega)] at second
    rw [show q-pre.length = (q-pre.length-1)+1 by omega] at second
    exact second
  have positive := one_not_gate_positive (gs := post) ⟨h,List.mem_iff_getElem?.mpr ⟨_,inside⟩,other⟩
  have cost : notGateCount (pre ++ g :: post) = notGateCount pre + 1 + notGateCount post := by
    simp [notGateCount,isNotGate,tag,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  omega
private theorem not_constant {gs : List Gate} (strict : CleanL 7 gs)
    {p a : ℕ} {g : Gate} (hit : gs[p]? = some g) (tag : g.op = .not)
    (reads : a ∈ g.inputs) (constant : IsC 6 gs (3 : Fin 7) true a) :
    IsC 6 gs (3 : Fin 7) true (7+p) := by
  rcases strict p g hit with ⟨_,j,_,args⟩ | ⟨bad | bad,_⟩
  · have eq : j = a := by simpa [args,eq_comm] using reads
    subst j
    apply st_allconst 6 gs strict (3 : Fin 7) true p g hit
    intro w mem
    have eq : w = a := by simpa [args] using mem
    subst w
    exact constant
  · rw [tag] at bad
    cases bad
  · rw [tag] at bad
    cases bad
private theorem binary_after_const_not {gs : List Gate} {out p : ℕ} {g : Gate}
    (least : Least 7 target gs out) (oneNot : notGateCount gs ≤ 1)
    (hit : gs[p]? = some g) (tag : g.op = .not)
    (constant : IsC 6 gs (3 : Fin 7) true (7+p)) :
    ∃ q, p < q ∧ Reads gs q (7+p) ∧ BinaryConstReader gs q := by
  have nc := L10586Branch.restrict_nonconstant (3 : Fin 7) true
  obtain ⟨q,lt,⟨h,hq,read⟩,_⟩ := least.next (3 : Fin 7) true nc p
    (List.getElem?_eq_some_iff.mp hit).1 constant
  have binary : h.op = .and ∨ h.op = .or := by
    rcases least.hcl q h hq with ⟨other,_⟩ | ⟨both,_⟩
    · exact (later_not_impossible oneNot lt hit hq tag other).elim
    · exact both
  exact ⟨q,lt,⟨h,hq,read⟩,⟨h,hq,binary,7+p,read,constant⟩⟩
private theorem binary_after_const {gs : List Gate} {out p : ℕ}
    (least : Least 7 target gs out) (oneNot : notGateCount gs ≤ 1)
    (valid : p < gs.length) (constant : IsC 6 gs (3 : Fin 7) true (7+p)) :
    ∃ q, p < q ∧ BinaryConstReader gs q := by
  have nc := L10586Branch.restrict_nonconstant (3 : Fin 7) true
  obtain ⟨q,lt,⟨h,hq,read⟩,_⟩ := least.next (3 : Fin 7) true nc p valid constant
  rcases least.hcl q h hq with ⟨notTag,_⟩ | ⟨binary,_⟩
  · have qConstant := not_constant least.hcl hq notTag read constant
    obtain ⟨t,qt,_,trc⟩ := binary_after_const_not least oneNot hq notTag qConstant
    exact ⟨t,lt.trans qt,trc⟩
  · exact ⟨q,lt,h,hq,binary,7+p,read,constant⟩
private theorem or_const_true {gs : List Gate} (strict : CleanL 7 gs)
    {r : ℕ} {g : Gate} (hit : gs[r]? = some g) (tag : g.op = .or)
    (read : 3 ∈ g.inputs) : stF 6 gs (3 : Fin 7) true (7+r) = .const true := by
  obtain ⟨bit,constant⟩ := isC_reader strict (3 : Fin 7) r g hit read true
    (Or.inr (by simp [fixBit,tag]))
  have evaluated := st_val_const 6 gs strict (3 : Fin 7) true (7+r) bit constant (fun _ => false)
  rw [vl_gate gs strict _ r g hit,tag] at evaluated
  have rawTrue : vl gs (ins (3 : Fin 7) true (fun _ => false)) 3 = true := by
    rw [vl_input gs _ 3 (by decide)]
    decide
  rcases strict r g hit with ⟨bad,_⟩ | ⟨_,a,b,_,_,args⟩
  · rw [tag] at bad
    cases bad
  · rw [args] at read evaluated
    simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with rfl | rfl
    · simp only [List.map_cons,List.map_nil,GateOp.eval,rawTrue,List.any_cons,id_eq,
        Bool.true_or] at evaluated
      simpa only [← evaluated] using constant
    · simp only [List.map_cons,List.map_nil,GateOp.eval,rawTrue,List.any_cons,id_eq,
        Bool.true_or,Bool.or_true] at evaluated
      simpa only [← evaluated] using constant
theorem or_reader_next_and {gs : List Gate} {out r q : ℕ} {g h : Gate}
    (clique : L10586BinaryCofactors.K4BinaryLower)
    (least : Least 7 target gs out) (budget : binaryCount gs ≤ 11)
    (oneNot : notGateCount gs ≤ 1) (hit : gs[r]? = some g) (tag : g.op = .or)
    (rawRead : 3 ∈ g.inputs) (hitQ : gs[q]? = some h) (hBin : h.op = .and ∨ h.op = .or)
    (srcRead : 7+r ∈ h.inputs) :
    r < q ∧ h.op = .and ∧ ∀ v, Reads gs v (7+r) → v = q := by
  have gStatus := or_const_true least.hcl hit tag rawRead
  have gConst : IsC 6 gs (3 : Fin 7) true (7+r) := ⟨true,gStatus⟩
  have gRC : BinaryConstReader gs r :=
    ⟨g,hit,Or.inr tag,3,rawRead,true,stF_self 6 gs (3 : Fin 7) true⟩
  have qRC : BinaryConstReader gs q := ⟨h,hitQ,hBin,7+r,srcRead,gConst⟩
  have rq : r < q := by
    have := reads_lt least.hcl ⟨h,hitQ,srcRead⟩
    omega
  have sole (v : ℕ) (read : Reads gs v (7+r)) : v = q := by
    by_contra apart
    have rv : r < v := by
      have := reads_lt least.hcl read
      omega
    obtain ⟨j,hitV,readV⟩ := read
    rcases least.hcl v j hitV with ⟨notTag,_⟩ | ⟨binary,_⟩
    · have vConst := not_constant least.hcl hitV notTag readV gConst
      obtain ⟨k,vk,readK,kRC⟩ := binary_after_const_not least oneNot hitV notTag vConst
      have qk : q ≠ k := by
        intro eq
        subst k
        exact least.no_tri L10586Branch.nonconstant v q (7+r) ⟨j,hitV,readV⟩
          ⟨h,hitQ,srcRead⟩ readK
      exact no_three_high clique least budget oneNot (by omega) (by omega) qk gRC qRC kRC
    · exact no_three_high clique least budget oneNot (by omega) (by omega) (Ne.symm apart) gRC qRC
        ⟨j,hitV,binary,7+r,readV,gConst⟩
  refine ⟨rq,?_,sole⟩
  rcases hBin with andTag | orTag
  · exact andTag
  · have qConstant := const_read 6 gs least.hcl (3 : Fin 7) true q h hitQ (7+r) srcRead
      (by simpa [fixBit,orTag] using gStatus)
    obtain ⟨t,qt,tRC⟩ := binary_after_const least oneNot (List.getElem?_eq_some_iff.mp hitQ).1 qConstant
    exact (no_three_high clique least budget oneNot (by omega) (by omega) (by omega) gRC qRC tRC).elim
end L10586EarOrShape
end ProofPart15

section ProofPart16
namespace L10586Tight
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch
open PetersenCutTrace
open scoped BigOperators
theorem one_not_occupied_eq_all {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (small : gs.length ≤ 12) (one : 1 ≤ notGateCount gs) :
    occupiedBranchWires least = circuitBranchWires (n := 7) gs ∧
      (circuitBranchWires (n := 7) gs).card = 5 := by
  have lower := least_five_occupied_branches least
  have allLower := least_five_branches least
  have budget := least_branch_budget least
  exact ⟨Finset.eq_of_subset_of_card_le (occupied_subset least) (by omega), by omega⟩
theorem exact_operand_multiplicity {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (size : gs.length = 12) (one : notGateCount gs = 1)
    (w : Fin (7 + gs.length)) (notOutput : w ≠ leastOutputWire least) :
    (operands gs).count w.val = if w ∈ circuitBranchWires (n := 7) gs then 2 else 1 := by
  classical
  let branches := circuitBranchWires (n := 7) gs
  let emb : Fin (7 + gs.length) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let branchNats := branches.map emb
  let wires := (operands gs).toFinset
  let required := (Finset.range (7 + gs.length)).erase out
  have branchCard : branchNats.card = 5 := by
    rw [Finset.card_map]
    exact (one_not_occupied_eq_all least size.le (by omega)).2
  have requiredCard : required.card = 18 := by
    dsimp only [required]
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (output_valid least)), Finset.card_range]
    omega
  have requiredUsed : required ⊆ wires := by
    intro u hu
    have spec := Finset.mem_erase.mp hu
    obtain ⟨_,reads⟩ := least_wire_used least nonconstant dependent restrict_nonconstant u
      (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read reads)
  have twice (u : ℕ) (hu : u ∈ branchNats) : 2 ≤ (operands gs).count u := by
    obtain ⟨v,hv,eq⟩ := Finset.mem_map.mp hu
    obtain ⟨p,q,different,hp,hq⟩ := branch_slots_of_read_edges (in_circuit_branches.mp hv)
    rw [← eq]
    exact two_readers_operand_count different hp hq
  have branchesUsed : branchNats ⊆ wires := by
    intro u hu
    have h := twice u hu
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have operandLength : (operands gs).length = 23 := by
    have len := operands_count_length gs (clean_gate_arity least.hcl)
    omega
  have wiresCard : wires.card = 18 := by
    have low := Finset.card_le_card requiredUsed
    have high := branch_card_add_wire_card_le_operands gs branchNats twice
    change branchNats.card + wires.card ≤ (operands gs).length at high
    omega
  let expected (u : ℕ) := (if u ∈ branchNats then 1 else 0) + 1
  have point (u : ℕ) (hu : u ∈ wires) : expected u ≤ (operands gs).count u := by
    by_cases b : u ∈ branchNats
    · simpa [expected,b] using twice u b
    · have pos : 0 < (operands gs).count u := List.count_pos_iff.mpr (List.mem_toFinset.mp hu)
      simpa [expected,b] using pos
  have countBranches : (∑ u ∈ wires, if u ∈ branchNats then (1 : ℕ) else 0) = 5 := by
    have same : (∑ u ∈ branchNats, if u ∈ branchNats then (1 : ℕ) else 0) =
        ∑ u ∈ wires, if u ∈ branchNats then (1 : ℕ) else 0 := by
      apply Finset.sum_subset branchesUsed
      intro u _ outside
      simp [outside]
    rw [← same]
    simpa using branchCard
  have sumExpected : (∑ u ∈ wires, expected u) = 23 := by
    simp only [expected,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one]
    omega
  have sumCount : (∑ u ∈ wires, (operands gs).count u) = 23 := by
    change (∑ u ∈ (operands gs).toFinset, (operands gs).count u) = 23
    rw [List.sum_toFinset_count_eq_length]
    exact operandLength
  have wIn : w.val ∈ wires := requiredUsed (Finset.mem_erase.mpr
    ⟨fun eq => notOutput (Fin.ext eq),Finset.mem_range.mpr w.isLt⟩)
  have exactCount : (operands gs).count w.val = expected w.val := by
    apply Nat.le_antisymm _ (point w.val wIn)
    by_contra! large
    have strict := Finset.sum_lt_sum (fun u hu => point u hu) ⟨w.val,wIn,large⟩
    omega
  have mem_iff : w.val ∈ branchNats ↔ w ∈ branches := by
    constructor
    · intro h
      obtain ⟨v,hv,eq⟩ := Finset.mem_map.mp h
      exact (Fin.ext eq : v = w) ▸ hv
    · intro h
      exact Finset.mem_map.mpr ⟨w,h,rfl⟩
  rw [exactCount]
  change expected w.val = if w ∈ branches then 2 else 1
  by_cases b : w ∈ branches
  · simp [expected,b,mem_iff]
  · simp [expected,b,mem_iff]
def Replacement (s : ℕ) : Prop :=
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧
      g.inputs.length ≤ 2) ∧ gs.length ≤ s ∧
      ∀ x : Fin 7 → Bool, (⟨gs,out⟩ : Circuit).eval (List.ofFn x) = target x
theorem from_critical_case
    (critical : ∀ (gs : List Gate) (out : ℕ), Least 7 target gs out →
      gs.length = 12 → notGateCount gs = 1 → False)
    (s : ℕ) (fit : HasCircuitSize 7 target s) : Replacement s := by
  by_cases small : s ≤ 11
  · exact replacement_at_eleven s small fit
  by_cases large : 13 ≤ s
  · exact ⟨control.gates,control.output,basis,by rw [size]; exact large,computes⟩
  obtain ⟨gs,out,least,size⟩ := exists_least 7 target s nonconstant fit
  have lower := least_binary_budget least
  have zero : notGateCount gs = 0 := by
    by_contra! someNot
    exact critical gs out least (by omega) (by omega)
  refine ⟨gs,out,?_,size,least.hev⟩
  intro g mem
  obtain ⟨slot,hit⟩ := List.mem_iff_getElem?.mp mem
  rcases least.hcl slot g hit with ⟨tag,_⟩ | ⟨tags,a,b,_,_,args⟩
  · have nonzero := one_not_gate_positive (gs := gs) ⟨g,mem,tag⟩
    omega
  · exact ⟨tags,by simp [args]⟩
end L10586Tight
end ProofPart16

section ProofPart17
namespace L10586SignedInfluence
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch PetersenCutTrace Relation
def NotWire {n : ℕ} (gs : List Gate) (w : Fin (n + gs.length)) : Prop :=
  ∃ (p : ℕ) (g : Gate), gs[p]? = some g ∧ w.val = n + p ∧ g.op = .not
theorem grows_if_negations_stable {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (ascending : ∀ i, x i = true → y i = true)
    (w : Fin (n + gs.length))
    (stable : ∀ v, ReflTransGen (readEdge gs) v w → NotWire gs v → vl gs x v.val = vl gs y v.val) :
    vl gs x w.val = true → vl gs y w.val = true := by
  revert stable
  induction w using (measure (fun w : Fin (n + gs.length) => w.val)).wf.induction with
  | h w earlier =>
    intro stable atX
    by_cases input : w.val < n
    · rw [vl_input gs x _ input] at atX
      rw [vl_input gs y _ input]
      exact ascending _ atX
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have index : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have hit : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rcases clean p g hit with ⟨neg,a,aLt,ins⟩ | ⟨binary,a,b,aLt,bLt,ins⟩
      · have same := stable w ReflTransGen.refl ⟨p,g,hit,index,neg⟩
        exact same.symm.trans atX
      · have previous (a : ℕ) (aLt : a < n + p) (arg : a ∈ g.inputs) :
            vl gs x a = true → vl gs y a = true := by
          let v : Fin (n + gs.length) := ⟨a,by have := w.isLt; omega⟩
          have before : v.val < w.val := by change a < w.val; omega
          exact earlier v before (fun z path neg => stable z (path.tail ⟨p,g,hit,index,arg⟩) neg)
        have aMem : a ∈ g.inputs := by simp [ins]
        have bMem : b ∈ g.inputs := by simp [ins]
        rw [index,vl_gate gs clean x p g hit,ins] at atX
        rw [index,vl_gate gs clean y p g hit,ins]
        rcases binary with andGate | orGate
        · have both : vl gs x a = true ∧ vl gs x b = true := by
            simpa [andGate,GateOp.eval] using atX
          simp [andGate,GateOp.eval,previous a aLt aMem both.1,previous b bLt bMem both.2]
        · have either : vl gs x a = true ∨ vl gs x b = true := by
            simpa [orGate,GateOp.eval] using atX
          rcases either with first | second
          · simp [orGate,GateOp.eval,previous a aLt aMem first]
          · simp [orGate,GateOp.eval,previous b bLt bMem second]
theorem update_keeps_true_of_no_negand_ancestry {n : ℕ} {gs : List Gate}
    (clean : CleanL n gs) (raw : Fin n)
    (avoids : ∀ v, NotWire gs v → ¬ ReflTransGen (readEdge gs) (inputWire gs raw) v) :
    ∀ (x : Fin n → Bool) (w : Fin (n + gs.length)),
      vl gs x w.val = true → vl gs (Function.update x raw true) w.val = true := by
  intro x w
  apply grows_if_negations_stable clean
  · intro i on
    by_cases hit : i = raw
    · simp [hit]
    · simpa [Function.update_of_ne hit] using on
  · intro v _ neg
    apply agree_on_input_ancestors clean
    intro i path
    by_cases hit : i = raw
    · subst i
      exact False.elim (avoids v neg path)
    · simp [Function.update_of_ne hit]
theorem false_at_zero_without_negation {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (w : Fin (n+gs.length)) (without : ∀ v, ReflTransGen (readEdge gs) v w → ¬ NotWire gs v) :
    vl gs (fun _ : Fin n => false) w.val = false := by
  let zero : Fin n → Bool := fun _ => false
  change vl gs zero w.val = false
  revert without
  induction w using (measure (fun w : Fin (n+gs.length) => w.val)).wf.induction with
  | h w earlier =>
    intro without
    by_cases raw : w.val < n
    · simpa [zero] using (vl_input gs zero w.val raw)
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have index : w.val = n+p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have hit : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rcases clean p g hit with ⟨tag,_,_,_⟩ | ⟨binary,a,b,aLt,bLt,ports⟩
      · exact False.elim (without w ReflTransGen.refl ⟨p,g,hit,index,tag⟩)
      · have zeroEarlier (q : ℕ) (earlierThan : q < n+p) (used : q ∈ g.inputs) :
            vl gs zero q = false := by
          let pred : Fin (n+gs.length) := ⟨q,by have := w.isLt; omega⟩
          have earlierVal : pred.val < w.val := by change q < w.val; omega
          exact earlier pred earlierVal (fun v path => without v (path.tail ⟨p,g,hit,index,used⟩))
        rw [index,vl_gate gs clean zero p g hit,ports]
        rcases binary with op | op <;>
          simp [GateOp.eval,op,zeroEarlier a aLt (by simp [ports]),zeroEarlier b bLt (by simp [ports])]
theorem not_wire_cannot_rise {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    {neg : Fin (n + gs.length)} (isNegation : NotWire gs neg)
    (unique : ∀ w, NotWire gs w → w = neg)
    (x y : Fin n → Bool) (ascending : ∀ i, x i = true → y i = true) :
    ¬ (vl gs x neg.val = false ∧ vl gs y neg.val = true) := by
  intro ⟨off,on⟩
  obtain ⟨p,g,hit,index,tag⟩ := isNegation
  rcases clean p g hit with ⟨_,a,aLt,inputs⟩ | ⟨binary,_,_,_,_,_⟩
  · let source : Fin (n + gs.length) := ⟨a,by have := neg.isLt; omega⟩
    have before : source.val < neg.val := by change a < neg.val; omega
    have grows : vl gs x a = true → vl gs y a = true :=
      grows_if_negations_stable clean x y ascending source (fun w reaches isNot => by
        have comesBefore := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) reaches
        rw [unique w isNot] at comesBefore
        exact False.elim ((not_le_of_gt before) comesBefore))
    rw [index,vl_gate gs clean x p g hit,tag,inputs] at off
    rw [index,vl_gate gs clean y p g hit,tag,inputs] at on
    have beforeTrue : vl gs x a = true := by simpa [GateOp.eval] using off
    have afterFalse : vl gs y a = false := by simpa [GateOp.eval] using on
    rw [grows beforeTrue] at afterFalse
    cases afterFalse
  · rcases binary with h | h <;> rw [h] at tag <;> cases tag
private theorem binary_rises
    (op : GateOp) (bin : op = .and ∨ op = .or)
    (xa xb ya yb : Bool)
    (off : op.eval [xa,xb] = false) (on : op.eval [ya,yb] = true) :
    (xa = false ∧ ya = true) ∨ (xb = false ∧ yb = true) := by
  rcases bin with rfl | rfl <;> cases xa <;> cases xb <;> cases ya <;> cases yb <;>
    simp_all [GateOp.eval]
theorem rising_path_avoids_negation {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    {neg : Fin (n + gs.length)} (isNegation : NotWire gs neg)
    (unique : ∀ w, NotWire gs w → w = neg)
    (raw : Fin n) (x y : Fin n → Bool) (ascending : ∀ i, x i = true → y i = true)
    (agrees : ∀ i, i ≠ raw → x i = y i)
    (w : Fin (n + gs.length)) (off : vl gs x w.val = false) (on : vl gs y w.val = true) :
    ReflTransGen (avoid (readEdge gs) neg) (inputWire gs raw) w := by
  have riseApart {v : Fin (n+gs.length)} (vx : vl gs x v.val = false) (vy : vl gs y v.val = true) :
      v ≠ neg := by
    rintro rfl
    exact not_wire_cannot_rise clean isNegation unique x y ascending ⟨vx,vy⟩
  revert off on
  induction w using (measure (fun w : Fin (n + gs.length) => w.val)).wf.induction with
  | h w earlier =>
    intro off on
    by_cases input : w.val < n
    · let v : Fin n := ⟨w.val,input⟩
      have same : inputWire gs v = w := Fin.ext rfl
      have rawDiff : x v ≠ y v := by
        intro eq
        rw [vl_input gs x _ input,eq,← vl_input gs y _ input,on] at off
        cases off
      have vIsRaw : v = raw := by by_contra apart; exact rawDiff (agrees _ apart)
      rw [← same,vIsRaw]
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have index : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have hit : gs[p]? = some g := List.getElem?_eq_getElem pLt
      have wApart := riseApart off on
      rcases clean p g hit with ⟨tag,_,_,_⟩ | ⟨bin,a,b,aLt,bLt,ins⟩
      · exact False.elim (wApart (unique w ⟨p,g,hit,index,tag⟩))
      · rw [index,vl_gate gs clean x p g hit,ins] at off
        rw [index,vl_gate gs clean y p g hit,ins] at on
        have atXY := binary_rises g.op bin (vl gs x a) (vl gs x b) (vl gs y a) (vl gs y b) off on
        have go (q : ℕ) (lt : q < n+p) (used : q ∈ g.inputs)
            (qoff : vl gs x q = false) (qon : vl gs y q = true) :
            ReflTransGen (avoid (readEdge gs) neg) (inputWire gs raw) w := by
          let pred : Fin (n+gs.length) := ⟨q,by have := w.isLt; omega⟩
          have before : pred.val < w.val := by change q < w.val; omega
          exact (earlier pred before qoff qon).tail ⟨⟨p,g,hit,index,used⟩,riseApart qoff qon,wApart⟩
        rcases atXY with first | second
        · exact go a aLt (by simp [ins]) first.1 first.2
        · exact go b bLt (by simp [ins]) second.1 second.2
private theorem not_slots_unique {gs : List Gate} (one : notGateCount gs = 1)
    {p q : ℕ} {g h : Gate} (first : gs[p]? = some g) (second : gs[q]? = some h)
    (isFirst : g.op = .not) (isSecond : h.op = .not) : p = q := by
  induction gs generalizing p q with
  | nil => simp at first
  | cons a rest ih =>
    have cost : notGateCount (a :: rest) = (if isNotGate a.op then 1 else 0) + notGateCount rest := by
      cases test : isNotGate a.op <;> simp [notGateCount,test,Nat.add_comm]
    rw [cost] at one
    cases p <;> cases q
    · rfl
    · rename_i q
      have same : a = g := Option.some.inj (by simpa using first)
      have aIs : a.op = .not := by rw [same]; exact isFirst
      have atQ : rest[q]? = some h := by simpa using second
      have restNot := one_not_gate_positive ⟨h,List.mem_iff_getElem?.mpr ⟨q,atQ⟩,isSecond⟩
      simp [aIs,isNotGate] at one
      omega
    · rename_i p
      have same : a = h := Option.some.inj (by simpa using second)
      have aIs : a.op = .not := by rw [same]; exact isSecond
      have atP : rest[p]? = some g := by simpa using first
      have restNot := one_not_gate_positive ⟨g,List.mem_iff_getElem?.mpr ⟨p,atP⟩,isFirst⟩
      simp [aIs,isNotGate] at one
      omega
    · rename_i p q
      have atP : rest[p]? = some g := by simpa using first
      have atQ : rest[q]? = some h := by simpa using second
      have restNot := one_not_gate_positive ⟨g,List.mem_iff_getElem?.mpr ⟨p,atP⟩,isFirst⟩
      have restOne : notGateCount rest = 1 := by
        cases test : isNotGate a.op <;> simp [test] at one <;> omega
      exact congrArg Nat.succ (ih restOne atP atQ)
theorem unique_negation {n : ℕ} {gs : List Gate} (one : notGateCount gs = 1) :
    ∃ neg : Fin (n+gs.length), NotWire gs neg ∧ ∀ w, NotWire gs w → w = neg := by
  cases eq : gs.filter (fun g => isNotGate g.op) with
  | nil => simp [notGateCount,eq] at one
  | cons g tail =>
    have member : g ∈ gs.filter (fun g => isNotGate g.op) := by simp [eq]
    have spec := List.mem_filter.mp member
    have tag : g.op = .not := by
      cases law : g.op <;> simp [isNotGate,law] at spec ⊢
    obtain ⟨p,hit⟩ := List.mem_iff_getElem?.mp spec.1
    have pLt := (List.getElem?_eq_some_iff.mp hit).1
    let neg : Fin (n+gs.length) := ⟨n+p,by omega⟩
    refine ⟨neg,⟨p,g,hit,rfl,tag⟩,?_⟩
    rintro w ⟨q,h,atQ,index,isNot⟩
    have same := not_slots_unique one atQ hit isNot tag
    apply Fin.ext
    simpa [neg,same] using index
end L10586SignedInfluence
end ProofPart17

section ProofPart18
namespace L10586OrPeers
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch PetersenCutTrace Relation
def single (v : Fin 7) : Fin 7 → Bool := fun i => decide (i = v)
def PeerTest (owner other : Fin 7) : Prop :=
  (∀ x : Fin 7 → Bool, target x = false → target (Function.update x owner false) = false) ∧
  ∀ x : Fin 7 → Bool, target x = false → x owner = false → x ≠ single other →
    target (Function.update x owner true) = true ∨
      target (Function.update x 3 true) = false ∧
        target (Function.update (Function.update x 3 true) owner true) = true
set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem test_one : PeerTest 1 5 := by
  unfold PeerTest
  decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem test_five : PeerTest 5 1 := by
  unfold PeerTest
  decide
def OnlyOrReader (gs : List Gate) (owner : Fin 7) (reader peer : Fin (7 + gs.length)) : Prop :=
  (∀ w, readEdge gs (inputWire gs owner) w → w = reader) ∧
  peer ≠ inputWire gs owner ∧ readEdge gs peer reader ∧
  ∀ x : Fin 7 → Bool, vl gs x reader.val = (x owner || vl gs x peer.val)
theorem only_reader_le_of_change {gs : List Gate} (clean : CleanL 7 gs)
    {owner : Fin 7} {reader w : Fin (7 + gs.length)}
    (one : ∀ v, readEdge gs (inputWire gs owner) v → v = reader)
    (other : w ≠ inputWire gs owner) {x y : Fin 7 → Bool}
    (agree : ∀ i, i ≠ owner → x i = y i) (difference : vl gs x w.val ≠ vl gs y w.val) :
    reader ≤ w := by
  by_contra! early
  apply difference
  apply agree_on_input_ancestors clean x y w
  intro i route
  by_cases apart : i ≠ owner
  · exact agree i apart
  · have same : i = owner := not_ne_iff.mp apart
    subst i
    rcases route.cases_head with here | ⟨first,edge,tail⟩
    · exact False.elim (other here.symm)
    · rw [one first edge] at tail
      have later := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) tail
      exact False.elim ((not_le_of_gt early) later)
private theorem only_reader_blocks {gs : List Gate} {owner : Fin 7}
    {reader out : Fin (7 + gs.length)}
    (one : ∀ v, readEdge gs (inputWire gs owner) v → v = reader)
    (outputApart : out ≠ inputWire gs owner) :
    ¬ ReflTransGen (avoid (readEdge gs) reader) (inputWire gs owner) out := by
  intro route
  rcases route.cases_head with here | ⟨first,edge,_⟩
  · exact outputApart here.symm
  · exact edge.2.2 (one first edge.1)
private theorem single_negative : ∀ i : Fin 7, target (single i) = false := by decide
theorem output_apart {gs : List Gate} {out : Fin (7 + gs.length)}
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x) (i : Fin 7) :
    out ≠ inputWire gs i := by
  rintro rfl
  have h := computes (single i)
  change vl gs (single i) i.val = _ at h
  rw [vl_input gs (single i) i.val i.isLt, single_negative] at h
  simp [single] at h
theorem peer_blocking {gs : List Gate} (clean : CleanL 7 gs) {out : Fin (7 + gs.length)}
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x) {owner : Fin 7}
    {reader peer : Fin (7 + gs.length)} (shape : OnlyOrReader gs owner reader peer)
    (x : Fin 7 → Bool) (lit : vl gs x peer.val = true) :
    target x = target (Function.update x owner true) := by
  let y := Function.update x owner true
  have equals : vl gs x reader.val = vl gs y reader.val := by
    rw [shape.2.2.2,shape.2.2.2,lit]
    simp [y]
  have result := circuit_cut_agreement clean reader out x y equals (fun i diff => by
    have same : i = owner := by
      by_contra apart
      apply diff
      simp [y,Function.update_of_ne apart]
    subst i
    exact only_reader_blocks shape.1 (output_apart computes owner))
  simpa only [computes] using result
theorem dirty_peer_accepts_opposite {gs : List Gate} (clean : CleanL 7 gs)
    {out : Fin (7 + gs.length)} (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x)
    {owner other : Fin 7} (test : PeerTest owner other)
    {reader peer : Fin (7 + gs.length)} (shape : OnlyOrReader gs owner reader peer)
    (grow : ∀ x : Fin 7 → Bool, vl gs x peer.val = true →
      vl gs (Function.update x 3 true) peer.val = true)
    (dirty : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer.val = true) :
    vl gs (single other) peer.val = true := by
  obtain ⟨x,bad,present⟩ := dirty
  let off := Function.update x owner false
  have offBad : target off = false := test.1 _ bad
  have offLit : off owner = false := by simp [off]
  have samePeer : vl gs off peer.val = vl gs x peer.val := by
    by_contra diff
    have now := only_reader_le_of_change clean shape.1 shape.2.1
      (x := off) (y := x) (fun i h => by simp [off,Function.update_of_ne h]) diff
    have before := read_order clean shape.2.2.1
    exact (not_le_of_gt before) now
  have offPeer : vl gs off peer.val = true := samePeer.trans present
  by_cases same : off = single other
  · simpa only [same] using offPeer
  rcases test.2 off offBad offLit same with up | ⟨threeBad,threeUp⟩
  · rw [← peer_blocking clean computes shape off offPeer,offBad] at up
    cases up
  · have later := peer_blocking clean computes shape (Function.update off 3 true) (grow off offPeer)
    rw [← later,threeBad] at threeUp
    cases threeUp
private def compareOne : Fin 7 → Bool := fun i => decide (i = 1 ∨ i = 4)
private def compareFive : Fin 7 → Bool := fun i => decide (i = 5 ∨ i = 4)
private theorem compare_other_inputs : ∀ v : Fin 7, v ≠ 1 → v ≠ 5 →
    compareOne v = compareFive v := by decide
private theorem readers_apart {gs : List Gate} (clean : CleanL 7 gs) {out : Fin (7 + gs.length)}
    (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x)
    {reader1 reader5 peer1 peer5 : Fin (7 + gs.length)}
    (one : OnlyOrReader gs 1 reader1 peer1) (five : OnlyOrReader gs 5 reader5 peer5) :
    reader1 ≠ reader5 := by
  intro same
  subst reader5
  have first : vl gs compareOne reader1.val = true := by
    rw [one.2.2.2]
    simp [compareOne]
  have second : vl gs compareFive reader1.val = true := by
    rw [five.2.2.2]
    simp [compareFive]
  have equal := circuit_cut_agreement clean reader1 out compareOne compareFive (first.trans second.symm)
    (fun i diff => by
      by_cases a : i = 1
      · subst i
        exact only_reader_blocks one.1 (output_apart computes 1)
      by_cases b : i = 5
      · subst i
        exact only_reader_blocks five.1 (output_apart computes 5)
      exact False.elim (diff (compare_other_inputs i a b)))
  rw [computes,computes] at equal
  have mismatch : target compareOne ≠ target compareFive := by decide
  exact mismatch equal
theorem two_dirty_or_readers_impossible {gs : List Gate} (clean : CleanL 7 gs)
    {out : Fin (7 + gs.length)} (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x)
    {reader1 reader5 peer1 peer5 : Fin (7 + gs.length)}
    (one : OnlyOrReader gs 1 reader1 peer1) (five : OnlyOrReader gs 5 reader5 peer5)
    (grow1 : ∀ x : Fin 7 → Bool, vl gs x peer1.val = true →
      vl gs (Function.update x 3 true) peer1.val = true)
    (grow5 : ∀ x : Fin 7 → Bool, vl gs x peer5.val = true →
      vl gs (Function.update x 3 true) peer5.val = true)
    (dirty1 : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer1.val = true)
    (dirty5 : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer5.val = true) : False := by
  have apart := readers_apart clean computes one five
  have at5 := dirty_peer_accepts_opposite clean computes test_one one grow1 dirty1
  have at1 := dirty_peer_accepts_opposite clean computes test_five five grow5 dirty5
  let empty : Fin 7 → Bool := fun _ => false
  have noEmpty1 : vl gs empty peer1.val = false := by
    by_contra! yes
    have lit : vl gs empty peer1.val = true := by cases h : vl gs empty peer1.val <;> simp_all
    have equal := peer_blocking clean computes one (Function.update empty 3 true) (grow1 empty lit)
    have diff : target (Function.update empty 3 true) ≠
        target (Function.update (Function.update empty 3 true) 1 true) := by decide
    exact diff equal
  have noEmpty5 : vl gs empty peer5.val = false := by
    by_contra! yes
    have lit : vl gs empty peer5.val = true := by cases h : vl gs empty peer5.val <;> simp_all
    have equal := peer_blocking clean computes five (Function.update empty 3 true) (grow5 empty lit)
    have diff : target (Function.update empty 3 true) ≠
        target (Function.update (Function.update empty 3 true) 5 true) := by decide
    exact diff equal
  have not5 : peer1 ≠ inputWire gs (5 : Fin 7) := by
    intro h
    apply apart
    apply five.1
    simpa only [h] using one.2.2.1
  have not1 : peer5 ≠ inputWire gs (1 : Fin 7) := by
    intro h
    apply apart.symm
    apply one.1
    simpa only [h] using five.2.2.1
  have reader5Before : reader5 ≤ peer1 := only_reader_le_of_change clean five.1 not5
    (x := empty) (y := single 5) (fun i different => by simp [empty,single,different]) (by simp [noEmpty1,at5])
  have reader1Before : reader1 ≤ peer5 := only_reader_le_of_change clean one.1 not1
    (x := empty) (y := single 1) (fun i different => by simp [empty,single,different]) (by simp [noEmpty5,at1])
  have peer1Before := read_order clean one.2.2.1
  have peer5Before := read_order clean five.2.2.1
  change reader5.val ≤ peer1.val at reader5Before
  change reader1.val ≤ peer5.val at reader1Before
  omega
end L10586OrPeers
end ProofPart18

section ProofPart19
namespace L10586OrPeerAncestry
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586OrPeers L10586SignedInfluence PetersenCutTrace Relation
def ExtendsToPositivePivot (owner : Fin 7) : Prop :=
  ∀ x : Fin 7 → Bool, target x = false → x owner = false →
    ∃ y : Fin 7 → Bool, (∀ i, x i = true → y i = true) ∧
      target y = false ∧ target (Function.update y owner true) = true
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem one_extends : ExtendsToPositivePivot 1 := by
  unfold ExtendsToPositivePivot
  decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem five_extends : ExtendsToPositivePivot 5 := by
  unfold ExtendsToPositivePivot
  decide
theorem dirty_peer_has_negation {gs : List Gate} (clean : CleanL 7 gs)
    {out : Fin (7 + gs.length)} (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x)
    {owner other : Fin 7} {reader peer : Fin (7 + gs.length)}
    (shape : OnlyOrReader gs owner reader peer) (rows : PeerTest owner other)
    (extension : ExtendsToPositivePivot owner)
    (dirty : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer.val = true) :
    ∃ neg, NotWire gs neg ∧ ReflTransGen (readEdge gs) neg peer := by
  classical
  by_contra noNegation
  obtain ⟨x,bad,xPeer⟩ := dirty
  let off : Fin 7 → Bool := Function.update x owner false
  have different : vl gs off peer.val = vl gs x peer.val := by
    by_contra changed
    have le := only_reader_le_of_change clean shape.1 shape.2.1
      (x := off) (y := x) (fun i h => by simp [off,Function.update_of_ne h]) changed
    exact (not_le_of_gt (read_order clean shape.2.2.1)) le
  have offPeer := different.trans xPeer
  have offBad : target off = false := rows.1 _ bad
  have noOwner : off owner = false := by simp [off]
  obtain ⟨y,larger,yBad,yPivot⟩ := extension off offBad noOwner
  have keep : vl gs y peer.val = true := by
    apply grows_if_negations_stable clean off y larger peer ?_ offPeer
    intro v path isNot
    exact False.elim (noNegation ⟨v,isNot,path⟩)
  have blocks := peer_blocking clean computes shape y keep
  rw [yBad,yPivot] at blocks
  cases blocks
theorem path_passes_unique_reader {n : ℕ} {gs : List Gate}
    {source reader output : Fin (n+gs.length)}
    (one : ∀ next, readEdge gs source next → next = reader)
    (different : output ≠ source) (path : ReflTransGen (readEdge gs) source output) :
    ReflTransGen (readEdge gs) reader output := by
  rcases path.cases_head with here | ⟨next,edge,tail⟩
  · exact False.elim (different here.symm)
  · rwa [one next edge] at tail
theorem early_wire_rejects_single_one {gs : List Gate} (clean : CleanL 7 gs)
    {out : Fin (7+gs.length)} (computes : ∀ x : Fin 7 → Bool, vl gs x out.val = target x)
    {reader1 peer1 wire neg : Fin (7+gs.length)}
    (one : OnlyOrReader gs 1 reader1 peer1)
    (dirty : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer1.val = true)
    (unique : ∀ w, NotWire gs w → w = neg)
    (beforeNot : wire < neg) (notRawOne : wire ≠ inputWire gs (1 : Fin 7)) :
    vl gs (single 1) wire.val = false := by
  obtain ⟨actual,notAt,reach⟩ := dirty_peer_has_negation clean computes one test_one one_extends dirty
  rw [unique actual notAt] at reach
  have afterNot : neg < reader1 := lt_of_le_of_lt
    (FirstBranchRoute.path_forward (readEdge gs) (read_order clean) reach)
    (read_order clean one.2.2.1)
  have fromOne : ¬ ReflTransGen (readEdge gs) (inputWire gs (1 : Fin 7)) wire := by
    intro yes
    have toPeer := path_passes_unique_reader one.1 notRawOne yes
    have beforeReader := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) toPeer
    exact (not_le_of_gt (lt_trans beforeNot afterNot)) beforeReader
  have none (v : Fin (7+gs.length)) (route : ReflTransGen (readEdge gs) v wire) : ¬ NotWire gs v := by
    intro tag
    have cannot := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) route
    rw [unique v tag] at cannot
    exact (not_le_of_gt beforeNot) cannot
  have same : vl gs (single 1) wire.val = vl gs (fun _ : Fin 7 => false) wire.val := by
    apply agree_on_input_ancestors clean
    intro i route
    by_cases hit : i = (1 : Fin 7)
    · subst i
      exact False.elim (fromOne route)
    · simp [single,hit]
  exact same.trans (false_at_zero_without_negation clean wire none)
end L10586OrPeerAncestry
end ProofPart19

section ProofPart20
namespace L10586RawRoute
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586OrPeers L10586OrPeerAncestry PetersenCutTrace Relation
def soleReader {n : ℕ} (gs : List Gate) (source reader : Fin (n+gs.length)) : Prop :=
  ∀ other, readEdge gs source other → other = reader
theorem away_from_raw_reader {gs : List Gate} (clean : CleanL 7 gs)
    {raw : Fin 7} {first : Fin (7+gs.length)}
    (reads : soleReader gs (inputWire gs raw) first)
    (out : Fin (7+gs.length)) (notRaw : out ≠ inputWire gs raw)
    (x y : Fin 7 → Bool) (agree : ∀ i, i ≠ raw → x i = y i)
    (atReader : vl gs x first.val = vl gs y first.val) :
    vl gs x out.val = vl gs y out.val := by
  apply circuit_cut_agreement clean first out x y atReader
  intro i different path
  have same : i = raw := by by_contra apart; exact different (agree i apart)
  subst i
  rcases path.cases_head with here | ⟨next,edge,_⟩
  · exact notRaw here.symm
  · exact edge.2.2 (reads next edge.1)
theorem away_from_second_reader {gs : List Gate} (clean : CleanL 7 gs)
    {raw : Fin 7} {first second : Fin (7+gs.length)}
    (reads : soleReader gs (inputWire gs raw) first) (next : soleReader gs first second)
    (out : Fin (7+gs.length)) (notRaw : out ≠ inputWire gs raw) (notFirst : out ≠ first)
    (x y : Fin 7 → Bool) (agree : ∀ i, i ≠ raw → x i = y i)
    (atReader : vl gs x second.val = vl gs y second.val) :
    vl gs x out.val = vl gs y out.val := by
  apply circuit_cut_agreement clean second out x y atReader
  intro i diff path
  have same : i = raw := by by_contra apart; exact diff (agree i apart)
  subst i
  rcases path.cases_head with here | ⟨r,edge,tail⟩
  · exact notRaw here.symm
  · rw [reads r edge.1] at tail
    rcases tail.cases_head with here | ⟨r',edge',_⟩
    · exact notFirst here.symm
    · exact edge'.2.2 (next r' edge'.1)
def Bin (andGate : Bool) (a b : Bool) : Bool := if andGate then a && b else a || b
private theorem bin_pivotal : ∀ andGate peer : Bool,
    Bin andGate false peer ≠ Bin andGate true peer → peer = andGate := by decide
theorem reader_peer_pivotal {gs : List Gate} (clean : CleanL 7 gs)
    {raw : Fin 7} {first peer out : Fin (7+gs.length)}
    (one : soleReader gs (inputWire gs raw) first)
    (peerEdge : readEdge gs peer first) (peerApart : peer ≠ inputWire gs raw)
    (outApart : out ≠ inputWire gs raw) (andGate : Bool)
    (gateEval : ∀ x : Fin 7 → Bool, vl gs x first.val = Bin andGate (x raw) (vl gs x peer.val))
    (x : Fin 7 → Bool) (off : x raw = false)
    (pivotal : vl gs x out.val ≠ vl gs (Function.update x raw true) out.val) :
    vl gs x peer.val = andGate := by
  let y := Function.update x raw true
  have agree (i : Fin 7) (h : i ≠ raw) : x i = y i := by simp [y,Function.update_of_ne h]
  have samePeer : vl gs x peer.val = vl gs y peer.val := by
    by_contra changed
    have le := only_reader_le_of_change clean one peerApart agree changed
    exact (not_le_of_gt (read_order clean peerEdge)) le
  have changeGate : vl gs x first.val ≠ vl gs y first.val :=
    fun same => pivotal (away_from_raw_reader clean one out outApart x y agree same)
  rw [gateEval,gateEval,off,← samePeer] at changeGate
  have high : y raw = true := by simp [y]
  rw [high] at changeGate
  exact bin_pivotal _ _ changeGate
theorem second_peer_pivotal {gs : List Gate} (clean : CleanL 7 gs)
    {raw : Fin 7} {first second peer out : Fin (7+gs.length)}
    (one : soleReader gs (inputWire gs raw) first) (two : soleReader gs first second)
    (firstEdge : readEdge gs first second)
    (peerEdge : readEdge gs peer second) (apart : peer ≠ first)
    (outApart : out ≠ inputWire gs raw) (outNotFirst : out ≠ first) (andGate : Bool)
    (gateEval : ∀ x : Fin 7 → Bool, vl gs x second.val = Bin andGate (vl gs x first.val) (vl gs x peer.val))
    (x : Fin 7 → Bool) (pivotal : vl gs x out.val ≠ vl gs (Function.update x raw true) out.val) :
    vl gs x peer.val = andGate := by
  let y := Function.update x raw true
  have agree (i : Fin 7) (h : i ≠ raw) : x i = y i := by simp [y,Function.update_of_ne h]
  have peerNotRaw : peer ≠ inputWire gs raw := by
    intro hit
    have eq : second = first := one second (hit ▸ peerEdge)
    exact (ne_of_lt (read_order clean firstEdge)) (congrArg Fin.val eq.symm)
  have unchanged : vl gs x peer.val = vl gs y peer.val := by
    apply agree_on_input_ancestors clean x y peer
    intro i path
    by_cases same : i = raw
    · subst i
      have firstPath := path_passes_unique_reader one peerNotRaw path
      have secondPath := path_passes_unique_reader two apart firstPath
      have comesBefore := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) secondPath
      exact False.elim ((not_le_of_gt (read_order clean peerEdge)) comesBefore)
    · exact agree i same
  have differ : vl gs x second.val ≠ vl gs y second.val := fun same =>
    pivotal (away_from_second_reader clean one two out outApart outNotFirst x y agree same)
  rw [gateEval,gateEval,← unchanged] at differ
  by_contra wrong
  cases andGate <;> cases value : vl gs x peer.val <;> simp_all [Bin]
end L10586RawRoute
end ProofPart20

section ProofPart21
namespace L10586EarLocal
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch L10586RawRoute L10586OrPeers PetersenCutTrace
def slotWire {gs : List Gate} {p : ℕ} {g : Gate} (hit : gs[p]? = some g) : Fin (7+gs.length) :=
  ⟨7+p,by have := (List.getElem?_eq_some_iff.mp hit).1; omega⟩
theorem sole_reader_of_slots {gs : List Gate} {source : Fin (7+gs.length)} {p : ℕ} {g : Gate}
    (hit : gs[p]? = some g) (only : ∀ k, Reads gs k source.val → k = p) :
    soleReader gs source (slotWire hit) := by
  rintro dest ⟨q,h,found,destVal,used⟩
  have eq := only q ⟨h,found,used⟩
  apply Fin.ext
  simpa [slotWire,eq] using destVal
theorem binary_gate_peer {gs : List Gate} {out p : ℕ} {g : Gate}
    (least : Least 7 target gs out) (hit : gs[p]? = some g)
    (andGate : Bool) (op : g.op = (if andGate then .and else .or))
    (source : Fin (7+gs.length)) (used : source.val ∈ g.inputs) :
    ∃ peer : Fin (7+gs.length), peer ≠ source ∧
      readEdge gs peer (slotWire hit) ∧
      (∀ w ∈ g.inputs, w = source.val ∨ w = peer.val) ∧
      ∀ x : Fin 7 → Bool, vl gs x (7+p) = Bin andGate (vl gs x source.val) (vl gs x peer.val) := by
  have mem : g ∈ gs := List.mem_iff_getElem?.mpr ⟨p,hit⟩
  have nodup := least_gate_inputs_nodup least nonconstant g mem
  have pLt := (List.getElem?_eq_some_iff.mp hit).1
  rcases least.hcl p g hit with ⟨neg,_,_,_⟩ | ⟨_,a,b,aLt,bLt,args⟩
  · rw [neg] at op
    cases andGate <;> cases op
  · have diff : a ≠ b := by simpa [args] using nodup
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with first | second
    · subst a
      let peer : Fin (7+gs.length) := ⟨b,by omega⟩
      have peerUsed : peer.val ∈ g.inputs := by
        change b ∈ g.inputs
        simp [args]
      refine ⟨peer,(fun h => diff (congrArg Fin.val h).symm),⟨p,g,hit,rfl,peerUsed⟩,?_,?_⟩
      · intro w inside
        simpa [args,peer] using inside
      · intro x
        rw [vl_gate gs least.hcl x p g hit,op,args]
        cases andGate <;> simp [Bin,GateOp.eval,peer]
    · subst b
      let peer : Fin (7+gs.length) := ⟨a,by omega⟩
      have peerUsed : peer.val ∈ g.inputs := by
        change a ∈ g.inputs
        simp [args]
      refine ⟨peer,(fun h => diff (congrArg Fin.val h)),⟨p,g,hit,rfl,peerUsed⟩,?_,?_⟩
      · intro w inside
        have either : w = a ∨ w = source.val := by simpa [args] using inside
        exact either.symm
      · intro x
        rw [vl_gate gs least.hcl x p g hit,op,args]
        cases andGate <;> simp [Bin,GateOp.eval,peer,Bool.or_comm,Bool.and_comm]
private def opposite (u : Fin 7) : Fin 7 := if u = 1 then 5 else 1
private theorem ear_input_facts : ∀ u : Fin 7, u = 1 ∨ u = 5 →
    (single u) u = true ∧ (single (opposite u)) u = false ∧ u ≠ 3 ∧
    (Function.update (single 3) u true) u = true ∧ (single 3) u = false ∧
    target (single 3) ≠ target (Function.update (single 3) u true) ∧
    (∀ i, i ≠ 3 → Function.update (single 3) u true i = (single u) i) := by
  decide
private theorem three_pivots_on_ears : ∀ u : Fin 7, u = 1 ∨ u = 5 →
    ((single u) 3 = false ∧ target (single u) ≠ target (Function.update (single u) 3 true)) ∧
    ((single (opposite u)) 3 = false ∧ target (single (opposite u)) ≠
      target (Function.update (single (opposite u)) 3 true)) := by
  decide
theorem local_clearance {gs : List Gate} {out r q : ℕ} {g h : Gate}
    (least : Least 7 target gs out) (u : Fin 7) (side : u = 1 ∨ u = 5) (high : Bool)
    (hitG : gs[r]? = some g) (tagG : g.op = (if high then .or else .and)) (rawG : 3 ∈ g.inputs)
    (hitH : gs[q]? = some h) (tagH : h.op = (if high then .and else .or)) (wireH : 7+r ∈ h.inputs)
    (only3 : ∀ k, Reads gs k 3 → k = r) (onlyG : ∀ k, Reads gs k (7+r) → k = q) :
    (u.val ∉ g.inputs) ∧ (u.val ∉ h.inputs) ∧
    (∀ p N, gs[p]? = some N → N.op = .not → u.val ∈ N.inputs →
      7+p ∉ g.inputs ∧ 7+p ∉ h.inputs) ∧
    (∀ p D, gs[p]? = some D → D.op = .and → u.val ∈ D.inputs →
      (∀ k, Reads gs k u.val → k = p) → 7+p ∉ g.inputs) := by
  let raw3 := inputWire gs (3 : Fin 7)
  let first := slotWire hitG
  let second := slotWire hitH
  let output := leastOutputWire least
  have computes (x : Fin 7 → Bool) : vl gs x output.val = target x := least.hev x
  have tagFirst : g.op = (if !high then .and else .or) := by cases high <;> simpa using tagG
  have linked : readEdge gs first second := ⟨q,h,hitH,rfl,wireH⟩
  have firstNotOut : output ≠ first := ne_of_gt (lt_of_lt_of_le (read_order least.hcl linked)
    (PetersenFirstGroup.wire_le_output least.hcl output (leastReadsLive least) second))
  obtain ⟨a,aApart,ea,gPorts,valueG⟩ := binary_gate_peer least hitG (!high) tagFirst raw3 rawG
  obtain ⟨b,bApart,eb,hPorts,valueH⟩ := binary_gate_peer least hitH high tagH first wireH
  have rawOnly : soleReader gs raw3 first := sole_reader_of_slots hitG only3
  have firstOnly : soleReader gs first second := sole_reader_of_slots hitH onlyG
  have evalG (x : Fin 7 → Bool) : vl gs x first.val = Bin (!high) (x 3) (vl gs x a.val) := by
    change vl gs x (7+r) = _
    rw [valueG]
    change Bin (!high) (vl gs x 3) (vl gs x a.val) = _
    have atThree : vl gs x 3 = x 3 := vl_input gs x 3 (by decide)
    rw [atThree]
  have info := ear_input_facts u side
  have pivots (x : Fin 7 → Bool) (off : x 3 = false)
      (diff : target x ≠ target (Function.update x 3 true)) :
      vl gs x a.val = !high ∧ vl gs x b.val = high := by
    have realDiff : vl gs x output.val ≠ vl gs (Function.update x 3 true) output.val := by
      simpa only [computes] using diff
    exact ⟨reader_peer_pivotal least.hcl rawOnly ea aApart (output_apart computes 3) _ evalG x off realDiff,
      second_peer_pivotal least.hcl rawOnly firstOnly linked eb bApart (output_apart computes 3)
        firstNotOut high valueH x realDiff⟩
  have firstTest := (three_pivots_on_ears u side).1
  have secondTest := (three_pivots_on_ears u side).2
  have v1 := pivots (single u) firstTest.1 firstTest.2
  have v2 := pivots (single (opposite u)) secondTest.1 secondTest.2
  have rawPos : u.val ≠ 3 := fun eq => info.2.2.1 (Fin.ext eq)
  have gClear : u.val ∉ g.inputs := by
    intro inside
    have eq := (gPorts _ inside).resolve_left rawPos
    rw [← eq,vl_input gs (single u) u.val u.isLt,info.1] at v1
    rw [← eq,vl_input gs (single (opposite u)) u.val u.isLt,info.2.1] at v2
    cases high
    · exact Bool.noConfusion v2.1
    · exact Bool.noConfusion v1.1
  have hClear : u.val ∉ h.inputs := by
    intro inside
    have ne : u.val ≠ first.val := by change u.val ≠ 7+r; have := u.isLt; omega
    have eq := (hPorts _ inside).resolve_left ne
    rw [← eq,vl_input gs (single u) u.val u.isLt,info.1] at v1
    rw [← eq,vl_input gs (single (opposite u)) u.val u.isLt,info.2.1] at v2
    cases high
    · exact Bool.noConfusion v1.2
    · exact Bool.noConfusion v2.2
  refine ⟨gClear,hClear,?_,?_⟩
  · intro p N hit neg inside
    have inputs : N.inputs = [u.val] := by
      rcases least.hcl p N hit with ⟨_,a,_,args⟩ | ⟨binary,_,_,_,_,_⟩
      · have ha : u.val = a := by simpa [args] using inside
        simpa [ha] using args
      · rcases binary with ht | ht <;> rw [ht] at neg <;> cases neg
    have evaluate (x : Fin 7 → Bool) : vl gs x (7+p) = !x u := by
      rw [vl_gate gs least.hcl x p N hit,neg,inputs]
      simp [GateOp.eval,vl_input gs x u.val u.isLt]
    have gNo : 7+p ∉ g.inputs := by
      intro uses
      have ne : 7+p ≠ raw3.val := by change 7+p ≠ 3; omega
      have eq := (gPorts _ uses).resolve_left ne
      rw [← eq,evaluate,info.1] at v1
      rw [← eq,evaluate,info.2.1] at v2
      cases high
      · exact Bool.noConfusion v1.1
      · exact Bool.noConfusion v2.1
    have hNo : 7+p ∉ h.inputs := by
      intro uses
      have ne : 7+p ≠ first.val := by
        intro eq
        have slots : p = r := by change 7+p = 7+r at eq; omega
        subst p
        have same := Option.some.inj (hitG.symm.trans hit)
        subst N
        rw [tagG] at neg
        cases high <;> cases neg
      have eq := (hPorts _ uses).resolve_left ne
      rw [← eq,evaluate,info.1] at v1
      rw [← eq,evaluate,info.2.1] at v2
      cases high
      · exact Bool.noConfusion v2.2
      · exact Bool.noConfusion v1.2
    exact ⟨gNo,hNo⟩
  · intro p D hit tag inside onlyU uses
    have ne : 7+p ≠ raw3.val := by change 7+p ≠ 3; omega
    have eq := (gPorts _ uses).resolve_left ne
    have reject (x : Fin 7 → Bool) (notU : x u = false) : vl gs x (7+p) = false := by
      rw [vl_gate gs least.hcl x p D hit,tag]
      rcases least.hcl p D hit with ⟨neg,_,_,_⟩ | ⟨_,a,b,_,_,args⟩
      · rw [tag] at neg
        cases neg
      · have port : u.val = a ∨ u.val = b := by simpa [args] using inside
        rcases port with first | second
        · simp [GateOp.eval,args,← first,vl_input gs x u.val u.isLt,notU]
        · simp [GateOp.eval,args,← second,vl_input gs x u.val u.isLt,notU]
    cases high
    · have absent := reject (single (opposite u)) info.2.1
      rw [eq,v2.1] at absent
      cases absent
    · let d := slotWire hit
      let y := Function.update (single 3) u true
      have only : soleReader gs (inputWire gs u) d := sole_reader_of_slots hit onlyU
      have earlier : d < first := read_order least.hcl (show readEdge gs d first from ⟨r,g,hitG,rfl,uses⟩)
      have differ : vl gs (single 3) output.val ≠ vl gs y output.val := by
        simpa only [computes] using info.2.2.2.2.2.1
      have agreeU (i : Fin 7) (hne : i ≠ u) : (single 3) i = y i := by simp [y,Function.update_of_ne hne]
      have dAtY : vl gs y d.val = true := by
        cases bit : vl gs y d.val
        · exfalso
          exact differ (away_from_raw_reader least.hcl only output (output_apart computes u)
            (single 3) y agreeU ((reject (single 3) info.2.2.2.2.1).trans bit.symm))
        · rfl
      have dNotRaw : d ≠ raw3 := fun h => ne (congrArg Fin.val h)
      have sameD : vl gs y d.val = vl gs (single u) d.val := by
        by_contra changeD
        have later := only_reader_le_of_change least.hcl rawOnly dNotRaw info.2.2.2.2.2.2 changeD
        exact (not_le_of_gt earlier) later
      have valEq : d.val = a.val := eq
      rw [dAtY,valEq,v1.1] at sameD
      cases sameD
end L10586EarLocal
end ProofPart21

section ProofPart22
namespace L10586DoublePin
open L11022RestrictSupport L10586WeightedRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
def pin (a : Fin 7) (b : Fin 6) (high : Bool) (x : Fin 5 → Bool) : Fin 7 → Bool :=
  ins a high (ins b false x)
private def init (a : Fin 7) (b : Fin 6) (high : Bool) : List Stat × List Gate :=
  (List.ofFn (Fin.insertNth a (.const high)
    (Fin.insertNth b (.const false) (fun i : Fin 5 => Stat.wire i.val))), [])
private theorem init_length (a : Fin 7) (b : Fin 6) (high : Bool) : (init a b high).1.length = 7 := by
  simp [init]
def status (gs : List Gate) (a : Fin 7) (b : Fin 6) (high : Bool) (w : ℕ) : Stat :=
  (elim 5 gs (init a b high)).1.getD w (.const false)
def gates (gs : List Gate) (a : Fin 7) (b : Fin 6) (high : Bool) : List Gate :=
  (elim 5 gs (init a b high)).2
private theorem init_inv (a : Fin 7) (b : Fin 6) (high : Bool) (x : Fin 5 → Bool) :
    Inv 5 (List.ofFn x) (List.ofFn (pin a b high x)) (init a b high) := by
  refine ⟨by simp [init],?_⟩
  intro i
  by_cases valid : i < 7
  · let j : Fin 7 := ⟨i,valid⟩
    let assigned : Fin 7 → Stat := Fin.insertNth a (Stat.const high)
      (Fin.insertNth b (Stat.const false) (fun i : Fin 5 => Stat.wire i.val))
    change ((init a b high).1.getD j.val (.const false)).Valid 5 ∧
      ((init a b high).1.getD j.val (.const false)).val (List.ofFn x) =
        (List.ofFn (pin a b high x)).getD j.val false
    have lookup : (init a b high).1.getD j.val (.const false) = assigned j :=
      getD_ofFn 7 assigned (Stat.const false) j
    rw [lookup,getD_ofFn _ _ _ j]
    dsimp only [assigned]
    rcases Fin.eq_self_or_eq_succAbove a j with same | ⟨k,above⟩
    · rw [same]
      simp [pin,Stat.Valid,Stat.val]
    · rw [above,Fin.insertNth_apply_succAbove]
      rcases Fin.eq_self_or_eq_succAbove b k with rfl | ⟨l,rfl⟩
      · simp [pin,Stat.Valid,Stat.val]
      · simp only [pin,Fin.insertNth_apply_succAbove,Stat.Valid,Stat.val]
        exact ⟨l.isLt,getD_ofFn _ _ _ l⟩
  · rw [List.getD_eq_default _ _ (by simp [init]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩
theorem first_status (gs : List Gate) (a : Fin 7) (b : Fin 6) (high : Bool) :
    status gs a b high a.val = .const high := by
  unfold status
  rw [elim_getD _ _ _ _ _ (by simp [init_length])]
  rw [init,getD_ofFn _ _ _ a,Fin.insertNth_apply_same]
theorem second_status (gs : List Gate) (a : Fin 7) (b : Fin 6) (high : Bool) :
    status gs a b high (a.succAbove b).val = .const false := by
  unfold status
  rw [elim_getD _ _ _ _ _ (by simp [init_length])]
  rw [init,getD_ofFn _ _ _ (a.succAbove b),Fin.insertNth_apply_succAbove,Fin.insertNth_apply_same]
private theorem gate_status {gs : List Gate} (clean : CleanL 7 gs)
    (a : Fin 7) (b : Fin 6) (high : Bool) {p : ℕ} {g : Gate} (hit : gs[p]? = some g) :
    ∃ t, status gs a b high (7+p) = (simplify g.op (5+t) (g.inputs.map (status gs a b high))).2 := by
  have earlier := (clean p g hit).lt
  obtain ⟨pre,post,rfl,rfl⟩ := split_at gs p g hit
  let acc := init a b high
  refine ⟨(elim 5 pre acc).2.length,?_⟩
  have step : status (pre ++ g :: post) a b high (7+pre.length) =
      (elimStep 5 (elim 5 pre acc) g).1.getD (7+pre.length) (.const false) := by
    unfold status
    exact elim_split_getD 5 pre g post acc _ _ (by simp [acc,init_length])
  have next : (elimStep 5 (elim 5 pre acc) g).1.getD (7+pre.length) (.const false) =
      (simplify g.op (5+(elim 5 pre acc).2.length)
        (g.inputs.map fun w => (elim 5 pre acc).1.getD w (.const false))).2 := by
    unfold elimStep
    apply getD_snoc_len
    rw [elim_fst_len,show acc.1.length = 7 from init_length a b high]
  have operands : (g.inputs.map fun w => (elim 5 pre acc).1.getD w (.const false)) =
      g.inputs.map (status (pre ++ g :: post) a b high) := by
    apply List.map_congr_left
    intro w mem
    exact (elim_split_getD_lt 5 pre g post acc w _ (by
      simpa [acc,init_length] using earlier w mem)).symm
  rw [step,next,operands]
theorem and_status_false {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    {p w : ℕ} {g : Gate} (hit : gs[p]? = some g) (tag : g.op = .and)
    (read : w ∈ g.inputs) (value : status gs a b high w = .const false) :
    status gs a b high (7+p) = .const false := by
  obtain ⟨t,formula⟩ := gate_status clean a b high hit
  rw [formula,tag]
  rcases clean p g hit with ⟨bad,_⟩ | ⟨_,i,j,_,_,args⟩
  · rw [tag] at bad
    cases bad
  · rw [args] at read ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with rfl | rfl
    · simp only [List.map_cons,List.map_nil,value]
      cases status gs a b high j <;> simp [simplify,simpAnd]
    · simp only [List.map_cons,List.map_nil,value]
      cases status gs a b high i <;> simp [simplify,simpAnd]
theorem and_status_true {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    {p : ℕ} {g : Gate} (hit : gs[p]? = some g) (tag : g.op = .and)
    (allTrue : ∀ w ∈ g.inputs, status gs a b high w = .const true) :
    status gs a b high (7+p) = .const true := by
  obtain ⟨t,formula⟩ := gate_status clean a b high hit
  rw [formula,tag]
  rcases clean p g hit with ⟨bad,_⟩ | ⟨_,i,j,_,_,args⟩
  · rw [tag] at bad
    cases bad
  · have vi := allTrue i (by simp [args])
    have vj := allTrue j (by simp [args])
    simp [args,vi,vj,simplify,simpAnd]
theorem or_status_false {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    {p : ℕ} {g : Gate} (hit : gs[p]? = some g) (tag : g.op = .or)
    (allFalse : ∀ w ∈ g.inputs, status gs a b high w = .const false) :
    status gs a b high (7+p) = .const false := by
  obtain ⟨t,formula⟩ := gate_status clean a b high hit
  rw [formula,tag]
  rcases clean p g hit with ⟨bad,_⟩ | ⟨_,i,j,_,_,args⟩
  · rw [tag] at bad
    cases bad
  · have vi := allFalse i (by simp [args])
    have vj := allFalse j (by simp [args])
    simp [args,vi,vj,simplify,simpOr]
theorem or_status_true {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    {p w : ℕ} {g : Gate} (hit : gs[p]? = some g) (tag : g.op = .or)
    (read : w ∈ g.inputs) (value : status gs a b high w = .const true) :
    status gs a b high (7+p) = .const true := by
  obtain ⟨t,formula⟩ := gate_status clean a b high hit
  rw [formula,tag]
  rcases clean p g hit with ⟨bad,_⟩ | ⟨_,i,j,_,_,args⟩
  · rw [tag] at bad
    cases bad
  · rw [args] at read ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with rfl | rfl
    · simp only [List.map_cons,List.map_nil,value]
      cases status gs a b high j <;> simp [simplify,simpOr]
    · simp only [List.map_cons,List.map_nil,value]
      cases status gs a b high i <;> simp [simplify,simpOr]
theorem not_status {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    {p w : ℕ} {g : Gate} {c : Bool} (hit : gs[p]? = some g) (tag : g.op = .not)
    (read : w ∈ g.inputs) (value : status gs a b high w = .const c) :
    status gs a b high (7+p) = .const (!c) := by
  obtain ⟨t,formula⟩ := gate_status clean a b high hit
  rw [formula,tag]
  rcases clean p g hit with ⟨_,i,_,args⟩ | ⟨bad | bad,_⟩
  · have eq : w = i := by simpa [args] using read
    subst i
    simp [args,value,simplify,simpNot]
  · rw [tag] at bad
    cases bad
  · rw [tag] at bad
    cases bad
theorem weighted_losses {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    (test : GateOp → Bool) (S : Finset ℕ)
    (lost : ∀ p ∈ S, ∃ g, gs[p]? = some g ∧ test g.op = true ∧
      ∃ w ∈ g.inputs, ∃ c, status gs a b high w = .const c) :
    opCount test (gates gs a b high) + S.card ≤ opCount test gs := by
  have cnt := elim_count_selected test 5 (init a b high) gs (clean_nok _ gs clean) S (by
    intro p mem
    obtain ⟨g,hit,mark,w,read,c,constant⟩ := lost p mem
    refine ⟨g,hit,mark,w,read,?_,c,constant⟩
    rw [init_length]
    exact (clean p g hit).lt w read)
  simpa [gates,init,opCount] using cnt
theorem not_count_le {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool) :
    notGateCount (gates gs a b high) ≤ notGateCount gs := by
  simpa [opCount,notGateCount,List.countP_eq_length_filter] using
    weighted_losses clean a b high isNotGate ∅ (by simp)
theorem constant_eval {gs : List Gate} (clean : CleanL 7 gs) (a : Fin 7) (b : Fin 6) (high : Bool)
    {w : ℕ} {c : Bool} (value : status gs a b high w = .const c) (x : Fin 5 → Bool) :
    vl gs (pin a b high x) w = c := by
  have eval := ((inv_elim 5 (List.ofFn x) (by simp) gs _ _
    (fun g mem => (clean_nok _ gs clean g mem).1) (init_inv a b high x)).2 w).2
  change (status gs a b high w).val (wiresFrom (gates gs a b high) (List.ofFn x)) = _ at eval
  rw [value] at eval
  exact eval.symm
theorem next_of_const {gs : List Gate} {out p : ℕ} {f : (Fin 7 → Bool) → Bool}
    (least : Least 7 f gs out) (a : Fin 7) (b : Fin 6) (high : Bool) (valid : p < gs.length)
    {c : Bool} (constant : status gs a b high (7+p) = .const c)
    (nonconstant : ∃ x y : Fin 5 → Bool, f (pin a b high x) ≠ f (pin a b high y)) :
    ∃ q, p < q ∧ Reads gs q (7+p) := by
  obtain ⟨x,y,apart⟩ := nonconstant
  apply least.live ⟨pin a b high x,pin a b high y,apart⟩ p valid
  intro eq
  apply apart
  rw [← least.hev,← least.hev,eq]
  exact (constant_eval least.hcl a b high constant x).trans
    (constant_eval least.hcl a b high constant y).symm
theorem clean_and_exact {gs : List Gate} {out : ℕ} {f : (Fin 7 → Bool) → Bool}
    (clean : CleanL 7 gs) (exactness : ∀ x, vl gs x out = f x) (a : Fin 7) (b : Fin 6) (high : Bool)
    (nonconstant : ∃ x y : Fin 5 → Bool, f (pin a b high x) ≠ f (pin a b high y)) :
    ∃ o, CleanL 5 (gates gs a b high) ∧ ∀ x, vl (gates gs a b high) x o = f (pin a b high x) := by
  have ev (x : Fin 5 → Bool) := ((inv_elim 5 (List.ofFn x) (by simp) gs _ _
    (fun g mem => (clean_nok _ gs clean g mem).1) (init_inv a b high x)).2 out).2
  cases result : status gs a b high out with
  | const c =>
    obtain ⟨x,y,apart⟩ := nonconstant
    have value (z : Fin 5 → Bool) : c = f (pin a b high z) := by
      have h := ev z
      change (status gs a b high out).val (wiresFrom (gates gs a b high) (List.ofFn z)) = _ at h
      rw [result] at h
      exact h.trans (exactness _)
    exact (apart ((value x).symm.trans (value y))).elim
  | wire o =>
    have strict : CleanL 5 (gates gs a b high) :=
      clean_elim 5 (List.ofFn fun _ : Fin 5 => false) (by simp) gs _ _
        (fun g mem => (clean_nok _ gs clean g mem).1) (init_inv a b high _) (by
          intro p g hit
          simp [init] at hit)
    refine ⟨o,strict,fun x => ?_⟩
    have h := ev x
    change (status gs a b high out).val (wiresFrom (gates gs a b high) (List.ofFn x)) = _ at h
    rw [result] at h
    exact h.trans (exactness _)
end L10586DoublePin
end ProofPart22

section ProofPart23
namespace L10586DoubleLower
open L11022RestrictSupport L10586WeightedRestriction L10586DoublePin
open L10586BinaryCofactors
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control (target)
private def offOne (high : Bool) (x : Fin 5 → Bool) : Bool := target (pin 3 1 high x)
private def offFive (high : Bool) (x : Fin 5 → Bool) : Bool := target (pin 3 4 high x)
private theorem offOne_table : ∀ (high : Bool) (x : Fin 4 → Bool),
    offOne high (ins (3 : Fin 5) false x) = cliqueTarget x := by decide
private theorem offFive_table : ∀ (high : Bool) (x : Fin 4 → Bool),
    offFive high (ins (1 : Fin 5) false x) = cliqueTarget x := by decide
private theorem offOne_lower (clique : K4BinaryLower) {gs : List Gate} {o : ℕ} (clean : CleanL 5 gs)
    (oneNot : notGateCount gs ≤ 1) (high : Bool) (ev : ∀ x, vl gs x o = offOne high x) :
    8 ≤ binaryCount gs := by
  obtain ⟨out,strict,exactness,lost,_⟩ := remove_pivotal_binary clean oneNot ev 3 (offOne_table high)
    ⟨fun i => decide (i=0),fun i => decide (i=0 ∨ i=3),by decide,by decide,by decide,
      by cases high <;> decide,by cases high <;> decide⟩
    ⟨fun _ => false,fun _ => true,by decide⟩
  have := clique _ out strict exactness
  omega
private theorem offFive_lower (clique : K4BinaryLower) {gs : List Gate} {o : ℕ} (clean : CleanL 5 gs)
    (oneNot : notGateCount gs ≤ 1) (high : Bool) (ev : ∀ x, vl gs x o = offFive high x) :
    8 ≤ binaryCount gs := by
  obtain ⟨out,strict,exactness,lost,_⟩ := remove_pivotal_binary clean oneNot ev 1 (offFive_table high)
    ⟨fun i => decide (i=3),fun i => decide (i=3 ∨ i=1),by decide,by decide,by decide,
      by cases high <;> decide,by cases high <;> decide⟩
    ⟨fun _ => false,fun _ => true,by decide⟩
  have := clique _ out strict exactness
  omega
theorem double_cofactor_binary (clique : K4BinaryLower) {gs : List Gate} {o : ℕ} (clean : CleanL 7 gs)
    (oneNot : notGateCount gs ≤ 1) (ev : ∀ x, vl gs x o = target x)
    {ear : Fin 6} (side : ear = 1 ∨ ear = 4) (high : Bool) : 8 ≤ binaryCount (gates gs 3 ear high) := by
  rcases side with rfl | rfl
  · obtain ⟨out,strict,value⟩ := clean_and_exact clean ev 3 1 high
      ⟨fun _ => false,fun _ => true,by cases high <;> decide⟩
    exact offOne_lower clique (o := out) strict ((L10586DoublePin.not_count_le clean 3 1 high).trans oneNot) high value
  · obtain ⟨out,strict,value⟩ := clean_and_exact clean ev 3 4 high
      ⟨fun _ => false,fun _ => true,by cases high <;> decide⟩
    exact offFive_lower clique (o := out) strict ((L10586DoublePin.not_count_le clean 3 4 high).trans oneNot) high value
def Charged (gs : List Gate) (ear : Fin 6) (high : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧
    ∃ w ∈ g.inputs, ∃ c, status gs 3 ear high w = .const c
theorem charged_of_read {gs : List Gate} {ear : Fin 6} {high : Bool} {p w : ℕ} {g : Gate} {c : Bool}
    (atP : gs[p]? = some g) (tag : g.op = .and ∨ g.op = .or)
    (used : w ∈ g.inputs) (constant : status gs 3 ear high w = .const c) :
    Charged gs ear high p := ⟨g,atP,tag,w,used,c,constant⟩
theorem double_pin_charges_le_three (clique : K4BinaryLower) {gs : List Gate} {o : ℕ} (clean : CleanL 7 gs)
    (oneNot : notGateCount gs ≤ 1) (budget : binaryCount gs ≤ 11)
    (ev : ∀ x, vl gs x o = target x) {ear : Fin 6} (side : ear = 1 ∨ ear = 4) (high : Bool)
    (S : Finset ℕ) (lost : ∀ p ∈ S, Charged gs ear high p) :
    S.card ≤ 3 := by
  have lower := double_cofactor_binary clique clean oneNot ev side high
  have upper := weighted_losses clean 3 ear high (fun op => !isNotGate op) S (by
    intro p mem
    obtain ⟨g,hit,tag,charge⟩ := lost p mem
    refine ⟨g,hit,?_,charge⟩
    rcases tag with tag | tag <;> simp [tag,isNotGate])
  change binaryCount (gates gs 3 ear high) + S.card ≤ binaryCount gs at upper
  omega
theorem no_four_charges (clique : K4BinaryLower) {gs : List Gate} {out : ℕ}
    (least : Least 7 target gs out) (oneNot : notGateCount gs ≤ 1) (budget : binaryCount gs ≤ 11)
    {ear : Fin 6} (side : ear = 1 ∨ ear = 4) (high : Bool) {a b c d : ℕ}
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    (ha : Charged gs ear high a) (hb : Charged gs ear high b)
    (hc : Charged gs ear high c) (hd : Charged gs ear high d) : False := by
  have atMost := double_pin_charges_le_three clique least.hcl oneNot budget least.hev side high
    {a,b,c,d} (by
      intro p mem
      simp only [Finset.mem_insert,Finset.mem_singleton] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> assumption)
  have card : ({a,b,c,d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [ab,ac,ad]),
      Finset.card_eq_three.mpr ⟨b,c,d,bc,bd,cd,rfl⟩]
  omega
end L10586DoubleLower
end ProofPart23

section ProofPart24
namespace L10586RawReaderProof
open L11022RestrictSupport L10586WeightedRestriction L10586DoublePin
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control (target)
open L10586SignedInfluence PetersenCutTrace Relation
abbrev raw (ear : Fin 6) : ℕ := ((3 : Fin 7).succAbove ear).val
def BinaryReader (gs : List Gate) (slot w : ℕ) : Prop :=
  ∃ g, gs[slot]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧ w ∈ g.inputs
private theorem binary_of_avoiding_edge {gs : List Gate} (clean : CleanL 7 gs)
    {neg w v : Fin (7+gs.length)} (unique : ∀ a, NotWire gs a → a = neg)
    (edge : avoid (readEdge gs) neg w v) :
    ∃ p, v.val = 7+p ∧ BinaryReader gs p w.val := by
  obtain ⟨p,g,hit,index,used⟩ := edge.1
  rcases clean p g hit with ⟨tag,_⟩ | ⟨binary,_⟩
  · exact (edge.2.2 (unique v ⟨p,g,hit,index,tag⟩)).elim
  · exact ⟨p,index,g,hit,binary,used⟩
private theorem positive_ear_path {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (one : notGateCount gs = 1) {ear : Fin 6} (side : ear = 1 ∨ ear = 4) :
    ∃ neg : Fin (7+gs.length), (∀ w, NotWire gs w → w = neg) ∧
      ReflTransGen (avoid (readEdge gs) neg) (inputWire gs ((3 : Fin 7).succAbove ear))
        (L10586Branch.leastOutputWire least) := by
  let u := (3 : Fin 7).succAbove ear
  let x := L10586OrPeers.single (3 : Fin 7)
  let y := Function.update x u true
  have off : target x = false := by decide
  have on : target y = true := by rcases side with rfl | rfl <;> decide
  have ascending (i : Fin 7) (old : x i = true) : y i = true := by
    by_cases atEar : i = u
    · simp [y,atEar]
    · simpa [y,Function.update_of_ne atEar] using old
  have agrees (i : Fin 7) (apart : i ≠ u) : x i = y i := by
    simp [y,Function.update_of_ne apart]
  obtain ⟨neg,tag,unique⟩ := unique_negation (n := 7) one
  exact ⟨neg,unique,rising_path_avoids_negation least.hcl tag unique u x y ascending agrees _
    ((least.hev x).trans off) ((least.hev y).trans on)⟩
theorem ear_has_binary_reader {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (one : notGateCount gs = 1) {ear : Fin 6} (side : ear = 1 ∨ ear = 4) :
    ∃ p, BinaryReader gs p (raw ear) := by
  obtain ⟨neg,unique,route⟩ := positive_ear_path least one side
  rcases route.cases_head with same | ⟨w,edge,_⟩
  · exact (L10586OrPeers.output_apart (fun x => least.hev x) ((3 : Fin 7).succAbove ear) same.symm).elim
  · obtain ⟨p,_,bin⟩ := binary_of_avoiding_edge least.hcl unique edge
    exact ⟨p,bin⟩
private theorem raw_and_not_output {gs : List Gate} {out p : ℕ} (least : Least 7 target gs out)
    {ear : Fin 6} (side : ear = 1 ∨ ear = 4) {D : Gate} (hit : gs[p]? = some D)
    (andTag : D.op = .and) (used : raw ear ∈ D.inputs) : out ≠ 7+p := by
  intro eq
  let x : Fin 7 → Bool := fun i => decide (i = 0 ∨ i = 2)
  have accepts : target x = true := by decide
  have zero : vl gs x (raw ear) = false := by
    rw [vl_input gs x (raw ear) ((3 : Fin 7).succAbove ear).isLt]
    rcases side with rfl | rfl <;> decide
  have value := least.hev x
  rcases gate_cases gs least.hcl p D hit (raw ear) used with ⟨tag,_⟩ | ⟨_,_,law⟩
  · rw [andTag] at tag
    cases tag
  · rcases law with ⟨_,formula⟩ | ⟨tag,_⟩
    · rw [eq,formula,zero,accepts] at value
      simp at value
    · rw [andTag] at tag
      cases tag
theorem ear_and_has_binary_next {gs : List Gate} {out p : ℕ} (least : Least 7 target gs out)
    (one : notGateCount gs = 1) {ear : Fin 6} (side : ear = 1 ∨ ear = 4) {D : Gate}
    (hit : gs[p]? = some D) (andTag : D.op = .and) (used : raw ear ∈ D.inputs)
    (sole : ∀ k, Reads gs k (raw ear) → k = p) : ∃ k, p < k ∧ BinaryReader gs k (7+p) := by
  obtain ⟨neg,unique,route⟩ := positive_ear_path least one side
  rcases route.cases_head with same | ⟨first,edge,tail⟩
  · exact (L10586OrPeers.output_apart (fun x => least.hev x) ((3 : Fin 7).succAbove ear) same.symm).elim
  · obtain ⟨k,g,atK,index,rawRead⟩ := edge.1
    have whereP : k = p := sole k ⟨g,atK,rawRead⟩
    subst k
    rcases tail.cases_head with same | ⟨next,after,_⟩
    · have sameOut : out = 7+p := (congrArg Fin.val same.symm).trans index
      exact (raw_and_not_output least side hit andTag used sameOut).elim
    · obtain ⟨k,which,bin⟩ := binary_of_avoiding_edge least.hcl unique after
      have earlier := read_order least.hcl after.1
      rw [index,which] at earlier
      exact ⟨k,by omega,by simpa only [index] using bin⟩
def Loss (gs : List Gate) (ear : Fin 6) (high : Bool) (slot : ℕ) : Prop :=
  ∃ g, gs[slot]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧
    ∃ w ∈ g.inputs, ∃ c, status gs 3 ear high w = .const c
theorem no_four (clique : L10586BinaryCofactors.K4BinaryLower)
    {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (oneNot : notGateCount gs ≤ 1) (budget : binaryCount gs ≤ 11)
    {ear : Fin 6} (side : ear = 1 ∨ ear = 4) (high : Bool)
    {r q p k : ℕ} (rq : r ≠ q) (rp : r ≠ p) (rk : r ≠ k)
    (qp : q ≠ p) (qk : q ≠ k) (pk : p ≠ k)
    (hr : Loss gs ear high r) (hq : Loss gs ear high q)
    (hp : Loss gs ear high p) (hk : Loss gs ear high k) : False := by
  have limit := L10586DoubleLower.double_pin_charges_le_three clique least.hcl oneNot budget least.hev
    side high {r,q,p,k} (by
      intro n mem
      simp only [Finset.mem_insert,Finset.mem_singleton] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> assumption)
  have card : ({r,q,p,k} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [rq,rp,rk]),
      Finset.card_eq_three.2 ⟨q,p,k,qp,qk,pk,rfl⟩]
  omega
private theorem no_later_not {gs : List Gate} (oneNot : notGateCount gs ≤ 1)
    {p q : ℕ} {g h : Gate} (lt : p < q) (hit : gs[p]? = some g)
    (later : gs[q]? = some h) (gNot : g.op = .not) (hNot : h.op = .not) : False := by
  obtain ⟨pre,post,rfl,rfl⟩ := split_at gs p g hit
  have inside : post[q-pre.length-1]? = some h := by
    rw [List.getElem?_append_right (by omega)] at later
    rw [show q-pre.length = (q-pre.length-1)+1 by omega] at later
    exact later
  have positive := one_not_gate_positive (gs := post)
    ⟨h,List.mem_iff_getElem?.mpr ⟨_,inside⟩,hNot⟩
  have cost : notGateCount (pre ++ g :: post) = notGateCount pre + 1 + notGateCount post := by
    simp [notGateCount,isNotGate,gNot,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  omega
def ViaNot (gs : List Gate) (p w : ℕ) : Prop :=
  w = 7+p ∨ ∃ j g, gs[j]? = some g ∧ g.op = .not ∧ 7+p ∈ g.inputs ∧ w = 7+j
theorem next_binary_of_const {gs : List Gate} {out p : ℕ}
    (least : Least 7 target gs out) (oneNot : notGateCount gs ≤ 1)
    (ear : Fin 6) (high : Bool) (valid : p < gs.length)
    {c : Bool} (constant : status gs 3 ear high (7+p) = .const c)
    (nonconstant : ∃ x y : Fin 5 → Bool, target (pin 3 ear high x) ≠ target (pin 3 ear high y)) :
    ∃ k g w b, p < k ∧ gs[k]? = some g ∧ (g.op = .and ∨ g.op = .or) ∧
      w ∈ g.inputs ∧ ViaNot gs p w ∧ status gs 3 ear high w = .const b := by
  obtain ⟨q,pq,h,hit,read⟩ := next_of_const least 3 ear high valid constant nonconstant
  rcases least.hcl q h hit with ⟨neg,_⟩ | ⟨binary,_⟩
  · have qConst := not_status least.hcl 3 ear high hit neg read constant
    obtain ⟨k,qk,g,atK,used⟩ := next_of_const least 3 ear high
      (reads_len (show Reads gs q (7+p) from ⟨h,hit,read⟩)) qConst nonconstant
    have binary : g.op = .and ∨ g.op = .or := by
      rcases least.hcl k g atK with ⟨also,_⟩ | ⟨binary,_⟩
      · exact (no_later_not oneNot qk hit atK neg also).elim
      · exact binary
    exact ⟨k,g,7+q,!c,pq.trans qk,atK,binary,used,Or.inr ⟨q,h,hit,neg,read,rfl⟩,qConst⟩
  · exact ⟨q,h,7+p,c,pq,hit,binary,read,Or.inl rfl,constant⟩
private theorem neutral_follower_constant {gs : List Gate} (clean : CleanL 7 gs)
    (ear : Fin 6) (high : Bool) {q w z : ℕ} {h : Gate} {c : Bool}
    (hit : gs[q]? = some h) (tag : h.op = (if high then .and else .or))
    (left : w ∈ h.inputs) (right : z ∈ h.inputs) (apart : w ≠ z)
    (first : status gs 3 ear high w = .const high)
    (second : status gs 3 ear high z = .const c) :
    status gs 3 ear high (7+q) = .const c := by
  have all (u : ℕ) (mem : u ∈ h.inputs) : u = w ∨ u = z :=
    two_inputs (clean q h hit) w z u left right apart mem
  cases high <;> cases c
  · apply or_status_false clean 3 ear false hit (by simpa using tag)
    intro u mem
    rcases all u mem with rfl | rfl <;> assumption
  · exact or_status_true clean 3 ear false hit (by simpa using tag) right second
  · exact and_status_false clean 3 ear true hit (by simpa using tag) right second
  · apply and_status_true clean 3 ear true hit (by simpa using tag)
    intro u mem
    rcases all u mem with rfl | rfl <;> assumption
private theorem pin_nonconstant {ear : Fin 6} (side : ear = 1 ∨ ear = 4) (high : Bool) :
    ∃ x y : Fin 5 → Bool, target (pin 3 ear high x) ≠ target (pin 3 ear high y) := by
  rcases side with rfl | rfl <;> cases high <;>
    exact ⟨fun _ => false,fun _ => true,by decide⟩
private theorem read_loss {gs : List Gate} {ear : Fin 6} {high : Bool} {p w : ℕ} {c : Bool}
    (reader : BinaryReader gs p w) (constant : status gs 3 ear high w = .const c) :
    Loss gs ear high p := by
  obtain ⟨g,hit,binary,used⟩ := reader
  exact ⟨g,hit,binary,w,used,c,constant⟩
private theorem tag_of_read {gs : List Gate} (clean : CleanL 7 gs)
    {p w : ℕ} (reader : Reads gs p w) :
    BinaryReader gs p w ∨ ∃ g, gs[p]? = some g ∧ g.op = .not ∧ w ∈ g.inputs := by
  obtain ⟨g,hit,used⟩ := reader
  rcases clean p g hit with ⟨neg,_⟩ | ⟨binary,_⟩
  · exact Or.inr ⟨g,hit,neg,used⟩
  · exact Or.inl ⟨g,hit,binary,used⟩
theorem sole_or_of_local_exclusions (clique : L10586BinaryCofactors.K4BinaryLower)
    {gs : List Gate} {out r q : ℕ} {g h : Gate}
    (least : Least 7 target gs out) (oneNot : notGateCount gs ≤ 1)
    (budget : binaryCount gs ≤ 11) {ear : Fin 6} (side : ear = 1 ∨ ear = 4) (high : Bool)
    (hitG : gs[r]? = some g) (tagG : g.op = (if high then .or else .and)) (rawG : 3 ∈ g.inputs)
    (hitH : gs[q]? = some h) (tagH : h.op = (if high then .and else .or)) (wireH : 7+r ∈ h.inputs)
    (clearG : raw ear ∉ g.inputs) (clearH : raw ear ∉ h.inputs)
    (binaryReader : ∃ p, BinaryReader gs p (raw ear))
    (notClear : ∀ p N, gs[p]? = some N → N.op = .not → raw ear ∈ N.inputs →
      7+p ∉ g.inputs ∧ 7+p ∉ h.inputs)
    (andClear : ∀ p D, gs[p]? = some D → D.op = .and → raw ear ∈ D.inputs →
      (∀ k, Reads gs k (raw ear) → k = p) → 7+p ∉ g.inputs)
    (andNext : ∀ p D, gs[p]? = some D → D.op = .and → raw ear ∈ D.inputs →
      (∀ k, Reads gs k (raw ear) → k = p) →
      ∃ k, p < k ∧ BinaryReader gs k (7+p)) :
    ∃ p D, gs[p]? = some D ∧ D.op = .or ∧ raw ear ∈ D.inputs ∧
      ∀ k, Reads gs k (raw ear) → k = p := by
  have rq : r < q := by
    have earlier := reads_lt least.hcl (show Reads gs q (7+r) from ⟨h,hitH,wireH⟩)
    omega
  have gBinary : g.op = .and ∨ g.op = .or := by cases high <;> simp [tagG]
  have hBinary : h.op = .and ∨ h.op = .or := by cases high <;> simp [tagH]
  have pin3 : status gs 3 ear high 3 = .const high := first_status gs 3 ear high
  have pinEar : status gs 3 ear high (raw ear) = .const false := second_status gs 3 ear high
  have gConst : status gs 3 ear high (7+r) = .const high := by
    cases high
    · exact and_status_false least.hcl 3 ear false hitG (by simpa using tagG) rawG pin3
    · exact or_status_true least.hcl 3 ear true hitG (by simpa using tagG) rawG pin3
  have lossG : Loss gs ear high r := read_loss ⟨g,hitG,gBinary,rawG⟩ pin3
  have lossH : Loss gs ear high q := read_loss ⟨h,hitH,hBinary,wireH⟩ gConst
  obtain ⟨p,D,hitD,tagD,rawD⟩ := binaryReader
  have lossD : Loss gs ear high p := read_loss ⟨D,hitD,tagD,rawD⟩ pinEar
  have rp : r ≠ p := by
    rintro rfl
    rw [hitG] at hitD
    have := Option.some.inj hitD
    subst D
    exact clearG rawD
  have qp : q ≠ p := by
    rintro rfl
    rw [hitH] at hitD
    have := Option.some.inj hitD
    subst D
    exact clearH rawD
  have noExtra {k : ℕ} (rk : r ≠ k) (qk : q ≠ k) (pk : p ≠ k)
      (lost : Loss gs ear high k) : False :=
    no_four clique least oneNot budget side high rq.ne rp rk qp qk pk lossG lossH lossD lost
  have unique (k : ℕ) (reader : Reads gs k (raw ear)) : k = p := by
    by_contra distinct
    rcases tag_of_read least.hcl reader with bin | ⟨N,hitN,tagN,rawN⟩
    · obtain ⟨J,hitJ,tagJ,rawJ⟩ := bin
      have rk : r ≠ k := by
        rintro rfl
        rw [hitG] at hitJ
        have := Option.some.inj hitJ
        subst J
        exact clearG rawJ
      have qk : q ≠ k := by
        rintro rfl
        rw [hitH] at hitJ
        have := Option.some.inj hitJ
        subst J
        exact clearH rawJ
      exact noExtra rk qk (Ne.symm distinct) (read_loss ⟨J,hitJ,tagJ,rawJ⟩ pinEar)
    · have constN := not_status least.hcl 3 ear high hitN tagN rawN pinEar
      obtain ⟨j,lt,N',hitJ,wireJ⟩ := next_of_const least 3 ear high
        (reads_len (show Reads gs k (raw ear) from ⟨N,hitN,rawN⟩)) constN (pin_nonconstant side high)
      have tags : N'.op = .and ∨ N'.op = .or := by
        rcases least.hcl j N' hitJ with ⟨neg,_⟩ | ⟨binary,_⟩
        · exact (no_later_not oneNot lt hitN hitJ tagN neg).elim
        · exact binary
      obtain ⟨notG,notH⟩ := notClear k N hitN tagN rawN
      have rj : r ≠ j := by
        rintro rfl
        rw [hitG] at hitJ
        have := Option.some.inj hitJ
        subst N'
        exact notG wireJ
      have qj : q ≠ j := by
        rintro rfl
        rw [hitH] at hitJ
        have := Option.some.inj hitJ
        subst N'
        exact notH wireJ
      have pj : p ≠ j := by
        intro eq
        subst j
        exact least.no_tri L10586Branch.nonconstant k p (raw ear)
          ⟨N,hitN,rawN⟩ ⟨D,hitD,rawD⟩ ⟨N',hitJ,wireJ⟩
      exact noExtra rj qj pj (read_loss ⟨N',hitJ,tags,wireJ⟩ constN)
  refine ⟨p,D,hitD,?_,rawD,unique⟩
  rcases tagD with isAnd | isOr
  · exfalso
    have pConst := and_status_false least.hcl 3 ear high hitD isAnd rawD pinEar
    obtain ⟨k,pk,J,hitJ,tagJ,used⟩ := andNext p D hitD isAnd rawD unique
    have rk : r ≠ k := by
      rintro rfl
      rw [hitG] at hitJ
      have := Option.some.inj hitJ
      subst J
      exact andClear p D hitD isAnd rawD unique used
    by_cases hq : q = k
    · subst k
      rw [hitH] at hitJ
      have := Option.some.inj hitJ
      subst J
      have qConst := neutral_follower_constant least.hcl ear high hitH tagH wireH used
        (by omega) gConst pConst
      obtain ⟨j,L,v,b,qj,hitL,tagL,usesL,_,constL⟩ := next_binary_of_const least oneNot ear high
        (reads_len (show Reads gs q (7+r) from ⟨h,hitH,wireH⟩)) qConst (pin_nonconstant side high)
      exact noExtra (rq.trans qj).ne qj.ne (pk.trans qj).ne (read_loss ⟨L,hitL,tagL,usesL⟩ constL)
    · exact noExtra rk hq pk.ne (read_loss ⟨J,hitJ,tagJ,used⟩ pConst)
  · exact isOr
end L10586RawReaderProof
end ProofPart24

section ProofPart25
namespace L10586EarAndClose
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch L10586OrPeers L10586SignedInfluence
open L10586OrPeerAncestry L10586RawRoute PetersenCutTrace Relation
private theorem raw_three_pivots : ∀ i : Fin 7, i = 1 ∨ i = 5 →
    (single i) 3 = false ∧ target (single i) ≠ target (Function.update (single i) 3 true) := by
  decide
theorem no_ear_path_to_not_of_and_peer {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    {first peer reader1 peer1 neg : Fin (7+gs.length)}
    (reader : soleReader gs (inputWire gs (3 : Fin 7)) first)
    (readsPeer : readEdge gs peer first) (peerApart : peer ≠ inputWire gs (3 : Fin 7))
    (gateEval : ∀ x : Fin 7 → Bool, vl gs x first.val = (x 3 && vl gs x peer.val))
    (one : OnlyOrReader gs 1 reader1 peer1)
    (dirty : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer1.val = true)
    (isNot : NotWire gs neg) (unique : ∀ w, NotWire gs w → w = neg) :
    ¬ ReflTransGen (readEdge gs) (inputWire gs (3 : Fin 7)) neg := by
  let output := leastOutputWire least
  have computes (x : Fin 7 → Bool) : vl gs x output.val = target x := least.hev x
  have peerOn (i : Fin 7) (allowed : i = 1 ∨ i = 5) : vl gs (single i) peer.val = true := by
    have spec := raw_three_pivots i allowed
    apply reader_peer_pivotal least.hcl reader readsPeer peerApart (output_apart computes 3) true
      (fun x => by simpa [Bin] using gateEval x) (single i) spec.1
    simpa only [computes] using spec.2
  have notOne : peer ≠ inputWire gs (1 : Fin 7) := by
    intro eq
    have on := peerOn 5 (Or.inr rfl)
    rw [eq] at on
    change vl gs (single 5) 1 = true at on
    rw [vl_input gs (single 5) 1 (by decide)] at on
    exact (by decide : (single 5) 1 ≠ true) on
  have notRaw : neg ≠ inputWire gs (3 : Fin 7) := by
    obtain ⟨p,g,_,idx,_⟩ := isNot
    intro same
    have val := congrArg Fin.val same
    change neg.val = 3 at val
    omega
  intro path
  have later := path_passes_unique_reader reader notRaw path
  have beforeNot : peer < neg := lt_of_lt_of_le (read_order least.hcl readsPeer)
    (FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl) later)
  have absent := early_wire_rejects_single_one least.hcl computes one dirty unique beforeNot notOne
  rw [peerOn 1 (Or.inl rfl)] at absent
  cases absent
end L10586EarAndClose
end ProofPart25

section ProofPart26
namespace L10586EarOrClose
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch L10586OrPeers L10586SignedInfluence
open L10586OrPeerAncestry L10586RawRoute PetersenCutTrace PetersenFirstGroup Relation
private theorem compare_single_one : target (single 1) ≠
    target (Function.update (single 1) 3 true) := by decide
theorem no_ear_path_to_not {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    {first second peer reader1 peer1 neg : Fin (7+gs.length)}
    (readThree : soleReader gs (inputWire gs (3 : Fin 7)) first)
    (readFirst : soleReader gs first second)
    (firstEdge : readEdge gs first second) (peerEdge : readEdge gs peer second)
    (peerApart : peer ≠ first) (firstNotNeg : first ≠ neg)
    (gateEval : ∀ x : Fin 7 → Bool,
      vl gs x second.val = (vl gs x first.val && vl gs x peer.val))
    (one : OnlyOrReader gs 1 reader1 peer1)
    (dirty : ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer1.val = true)
    (isNot : NotWire gs neg) (unique : ∀ w, NotWire gs w → w = neg) :
    ¬ ReflTransGen (readEdge gs) (inputWire gs (3 : Fin 7)) neg := by
  let output := leastOutputWire least
  have computes (x : Fin 7 → Bool) : vl gs x output.val = target x := least.hev x
  have firstBefore : first < output := lt_of_lt_of_le (read_order least.hcl firstEdge)
    (wire_le_output least.hcl output (leastReadsLive least) second)
  have pivot : vl gs (single 1) output.val ≠
      vl gs (Function.update (single 1) 3 true) output.val := by
    rw [computes,computes]
    exact compare_single_one
  have peerOn : vl gs (single 1) peer.val = true :=
    second_peer_pivotal least.hcl readThree readFirst firstEdge peerEdge peerApart
      (output_apart computes 3) (ne_of_gt firstBefore) true
      (fun x => by simpa [Bin] using gateEval x) (single 1) pivot
  obtain ⟨neg1,actual,reach⟩ := dirty_peer_has_negation least.hcl computes one test_one one_extends dirty
  rw [unique neg1 actual] at reach
  have afterNot : neg < reader1 := lt_of_le_of_lt
    (FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl) reach)
    (read_order least.hcl one.2.2.1)
  intro inputPath
  have notRaw : neg ≠ inputWire gs (3 : Fin 7) := by
    obtain ⟨p,g,_,idx,_⟩ := isNot
    intro same
    have val := congrArg Fin.val same
    change neg.val = 3 at val
    omega
  have readPath := path_passes_unique_reader readThree notRaw inputPath
  have nextPath := path_passes_unique_reader readFirst firstNotNeg.symm readPath
  have secondLe := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl) nextPath
  have beforeNot : peer < neg := lt_of_lt_of_le (read_order least.hcl peerEdge) secondLe
  have notOne : peer ≠ inputWire gs (1 : Fin 7) := by
    intro same
    have slot : second = reader1 := one.1 second (same ▸ peerEdge)
    rw [← slot] at afterNot
    exact (not_le_of_gt afterNot) secondLe
  have fromOne : ¬ ReflTransGen (readEdge gs) (inputWire gs (1 : Fin 7)) peer := by
    intro yes
    have toPeer := path_passes_unique_reader one.1 notOne yes
    have beforeReader := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl) toPeer
    exact (not_le_of_gt (lt_trans beforeNot afterNot)) beforeReader
  have peerZero := false_at_zero_without_negation least.hcl peer (fun v route tag => by
    have cannot := FirstBranchRoute.path_forward (readEdge gs) (read_order least.hcl) route
    rw [unique v tag] at cannot
    exact (not_le_of_gt beforeNot) cannot)
  have samePeer : vl gs (single 1) peer.val = vl gs (fun _ : Fin 7 => false) peer.val := by
    apply agree_on_input_ancestors least.hcl
    intro i route
    by_cases hit : i = (1 : Fin 7)
    · subst i
      exact False.elim (fromOne route)
    · simp [single,hit]
  rw [peerOn,peerZero] at samePeer
  cases samePeer
end L10586EarOrClose
end ProofPart26

section ProofPart27
namespace L10586OrPromotion
open L11022RestrictSupport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch L10586OrPeers L11022Rewire PetersenCutTrace
theorem dirty_peer_of_sole_or {gs : List Gate} {out : ℕ} (least : Least 7 target gs out)
    (fewest : ∀ (ys : List Gate) (o : ℕ), CleanL 7 ys →
      (∀ x : Fin 7 → Bool, vl ys x o = target x) → ys.length = gs.length →
      dirtyReads 7 target gs ≤ dirtyReads 7 target ys)
    (raw : Fin 7) (slot : ℕ) (gate : Gate) (atGate : gs[slot]? = some gate)
    (tag : gate.op = .or) (inside : raw.val ∈ gate.inputs)
    (unique : ∀ q, Reads gs q raw.val → q = slot) :
    ∃ (reader peer : Fin (7 + gs.length)), OnlyOrReader gs raw reader peer ∧
      ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer.val = true := by
  have member : gate ∈ gs := List.mem_iff_getElem?.mpr ⟨slot,atGate⟩
  have slotLt := (List.getElem?_eq_some_iff.mp atGate).1
  have ports : ∃ a : ℕ, a ≠ raw.val ∧ (gate.inputs = [raw.val,a] ∨ gate.inputs = [a,raw.val]) := by
    rcases least.hcl slot gate atGate with ⟨neg,_,_,_⟩ | ⟨_,a,b,_,_,args⟩
    · rw [tag] at neg
      cases neg
    · have nodup := least_gate_inputs_nodup least nonconstant gate member
      have diff : a ≠ b := by simpa [args] using nodup
      simp only [args,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with first | second
      · subst a
        exact ⟨b,diff.symm,Or.inl args⟩
      · subst b
        exact ⟨a,diff,Or.inr args⟩
  obtain ⟨peer,apart,args⟩ := ports
  have inPeer : peer ∈ gate.inputs := by rcases args with args | args <;> simp [args]
  have peerBound := (least.hcl slot gate atGate).lt peer inPeer
  let reader : Fin (7+gs.length) := ⟨7+slot,by omega⟩
  let peerWire : Fin (7+gs.length) := ⟨peer,by omega⟩
  have shape : OnlyOrReader gs raw reader peerWire := by
    refine ⟨?_,?_,⟨slot,gate,atGate,rfl,inPeer⟩,?_⟩
    · intro dest reads
      obtain ⟨q,g,seen,value,used⟩ := reads
      exact Fin.ext (value.trans (congrArg (7 + ·) (unique q ⟨g,seen,used⟩)))
    · exact fun eq => apart (congrArg Fin.val eq)
    · intro x
      change vl gs x (7+slot) = (x raw || vl gs x peer)
      rw [vl_gate gs least.hcl x slot gate atGate,tag]
      rcases args with args | args
      · simp [args,GateOp.eval,vl_input gs x raw.val raw.isLt]
      · simp [args,GateOp.eval,vl_input gs x raw.val raw.isLt,Bool.or_comm]
  refine ⟨reader,peerWire,shape,?_⟩
  by_contra! alwaysFalse
  have safe (x : Fin 7 → Bool) (bad : target x = false) : vl gs x peer = false := by
    cases bit : vl gs x peer
    · rfl
    · exact False.elim (alwaysFalse x bad bit)
  obtain ⟨pre,post,listEq,indexEq⟩ := split_at gs slot gate atGate
  have sourceEarlier : raw.val < 7 + pre.length := by omega
  have peerEarlier : peer < 7 + pre.length := by rwa [indexEq]
  have preReads : ∀ g ∈ pre, ∀ w ∈ g.inputs, w < 7+pre.length := by
    intro g mem w used
    obtain ⟨q,found⟩ := List.mem_iff_getElem?.mp mem
    have before := (List.getElem?_eq_some_iff.mp found).1
    have seen : gs[q]? = some g := by rw [listEq,List.getElem?_append_left before,found]
    have bound := (least.hcl q g seen).lt w used
    omega
  let old : Circuit := ⟨pre ++ ⟨.or,[raw.val,peer]⟩ :: post, out⟩
  have update : CleanL 7 old.gates ∧
      (∀ (x : Fin 7 → Bool) (w : ℕ), vl old.gates x w = vl gs x w) ∧
      dirtyReads 7 target old.gates = dirtyReads 7 target gs := by
    rcases args with args | args
    · have gateEq : gate = ⟨.or,[raw.val,peer]⟩ := by cases gate; simp_all
      have equal : gs = old.gates := listEq.trans (congrArg (fun g => pre ++ g :: post) gateEq)
      rw [← equal]
      exact ⟨least.hcl,fun _ _ => rfl,rfl⟩
    · have gateEq : gate = ⟨.or,[peer,raw.val]⟩ := by cases gate; simp_all
      have equal : gs = pre ++ ⟨.or,[peer,raw.val]⟩ :: post :=
        listEq.trans (congrArg (fun g => pre ++ g :: post) gateEq)
      have clean : CleanL 7 (pre ++ ⟨.or,[peer,raw.val]⟩ :: post) := by rw [← equal]; exact least.hcl
      rw [equal]
      exact L11022ReaderSwap.swap_middle 7 target pre post .or raw.val peer (Or.inr rfl) clean
  have oldSize : old.gates.length = gs.length := by rw [listEq]; simp [old]
  have computes (x : Fin 7 → Bool) : old.eval (List.ofFn x) = target x :=
    (update.2.1 x out).trans (least.hev x)
  have silentPrefix (x : Fin 7 → Bool) (negative : target x = false) :
      (wiresFrom pre (List.ofFn x)).getD peer false = false := by
    have flat : vl old.gates x peer = (wiresFrom pre (List.ofFn x)).getD peer false := by
      change (wiresFrom (pre ++ ⟨.or,[raw.val,peer]⟩ :: post) (List.ofFn x)).getD peer false = _
      rw [wiresFrom_append,getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using peerEarlier)]
    rw [← flat,update.2.1]
    exact safe x negative
  let row := single raw
  have negative : target row = false := by
    have check : ∀ i : Fin 7, target (single i) = false := by decide
    exact check raw
  have on : row raw = true := by simp [row,single]
  have sourceDirty : dirty 7 target old raw.val = true := by
    classical
    unfold dirty
    apply decide_eq_true
    refine ⟨row,negative,?_⟩
    change vl old.gates row raw.val = true
    simpa only [vl_input old.gates row raw.val raw.isLt] using on
  have gateDirty : dirty 7 target old (7+pre.length) = true := by
    classical
    unfold dirty
    apply decide_eq_true
    refine ⟨row,negative,?_⟩
    change vl old.gates row (7+pre.length) = true
    rw [update.2.1,indexEq]
    change vl gs row reader.val = true
    rw [shape.2.2.2,on]
    rfl
  let fresh := appendOr 7 (splice 7 pre post raw.val out) peer
  obtain ⟨newFit,counts⟩ := promotion_reduces_dirty_reads 7 target pre post raw.val peer out
    sourceEarlier peerEarlier preReads silentPrefix computes gateDirty sourceDirty
  have valid : out < 7+old.gates.length := by rw [oldSize]; exact output_valid least
  have newClean := promote_clean 7 pre post raw.val peer out update.1 sourceEarlier peerEarlier valid
  have newSize : fresh.gates.length = gs.length := by
    rw [← oldSize]
    change fresh.size = old.size
    rw [promote_size]
    simp [old,Circuit.size,Nat.add_assoc]
  have minimal := fewest fresh.gates fresh.output newClean newFit newSize
  change dirtyReads 7 target fresh.gates + 1 = dirtyReads 7 target old.gates at counts
  rw [update.2.2] at counts
  omega
end L10586OrPromotion
end ProofPart27

section ProofPart28
namespace L10586Closure
open L11022RestrictSupport L10586WeightedRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
open L10586Control L10586Branch L10586OrPeers L10586SignedInfluence
open L10586RawRoute L10586EarLocal L10586RawReaderProof L10586OrPromotion
open L10586BinaryCofactors L11022Rewire PetersenCutTrace Relation
def Fewest (gs : List Gate) : Prop :=
  ∀ (ys : List Gate) (o : ℕ), CleanL 7 ys →
    (∀ x : Fin 7 → Bool, vl ys x o = target x) → ys.length = gs.length →
    dirtyReads 7 target gs ≤ dirtyReads 7 target ys
private theorem positive_reader_after_raw_three_or {gs : List Gate} {out r : ℕ} {g : Gate}
    (least : Least 7 target gs out) (notCount : notGateCount gs = 1)
    (hit : gs[r]? = some g) (tag : g.op = .or) (rawG : 3 ∈ g.inputs)
    (only : ∀ v, Reads gs v 3 → v = r) : ∃ q, BinaryReader gs q (7+r) := by
  obtain ⟨neg,isNot,unique⟩ := unique_negation (n := 7) notCount
  let x := single (1 : Fin 7)
  let y := Function.update x 3 true
  let output := leastOutputWire least
  have off : target x = false := by decide
  have on : target y = true := by decide
  have ascend (i : Fin 7) (hi : x i = true) : y i = true := by
    by_cases same : i = 3
    · simp [y,same]
    · simpa [y,Function.update_of_ne same] using hi
  have agree (i : Fin 7) (apart : i ≠ 3) : x i = y i := by simp [y,Function.update_of_ne apart]
  have route := rising_path_avoids_negation least.hcl isNot unique 3 x y ascend agree output
    ((least.hev x).trans off) ((least.hev y).trans on)
  rcases route.cases_head with zero | ⟨first,edge,rest⟩
  · exact (output_apart (fun x => least.hev x) 3 zero.symm).elim
  · obtain ⟨p,H,found,idx,used⟩ := edge.1
    have eq := only p ⟨H,found,used⟩
    subst p
    rcases rest.cases_head with zero | ⟨second,next,_⟩
    · have outEq : out = 7+r := (congrArg Fin.val zero.symm).trans idx
      obtain ⟨a,_,_,_,reads⟩ := binary_gate_peer least hit false tag (inputWire gs (3 : Fin 7)) rawG
      have claim := least.hev (single 3)
      rw [outEq,reads] at claim
      change Bin false (vl gs (single 3) 3) (vl gs (single 3) a.val) = target (single 3) at claim
      rw [vl_input gs (single 3) 3 (by decide),show target (single 3) = false by decide] at claim
      simp [Bin,single] at claim
    · obtain ⟨q,H,found,idxQ,used⟩ := next.1
      have bin : H.op = .and ∨ H.op = .or := by
        rcases least.hcl q H found with ⟨notTag,_⟩ | ⟨k,_⟩
        · exact False.elim (next.2.2 (unique second ⟨q,H,found,idxQ,notTag⟩))
        · exact k
      exact ⟨q,H,found,bin,by simpa only [idx] using used⟩
theorem exclude_typed_chain (clique : K4BinaryLower) {gs : List Gate} {out r q : ℕ} {g h : Gate}
    (least : Least 7 target gs out) (size : gs.length = 12) (notCount : notGateCount gs = 1)
    (measure : Fewest gs) (high : Bool)
    (hitG : gs[r]? = some g) (tagG : g.op = (if high then .or else .and)) (rawG : 3 ∈ g.inputs)
    (hitH : gs[q]? = some h) (tagH : h.op = (if high then .and else .or)) (wireH : 7+r ∈ h.inputs)
    (only3 : ∀ k, Reads gs k 3 → k = r) (onlyG : ∀ k, Reads gs k (7+r) → k = q) : False := by
  have count := binary_add_not gs
  have budget : binaryCount gs ≤ 11 := by omega
  have earOR (ear : Fin 6) (side : ear = 1 ∨ ear = 4) :
      ∃ (reader peer : Fin (7+gs.length)), OnlyOrReader gs ((3 : Fin 7).succAbove ear) reader peer ∧
        ∃ x : Fin 7 → Bool, target x = false ∧ vl gs x peer.val = true := by
    let u := (3 : Fin 7).succAbove ear
    have which : u = 1 ∨ u = 5 := by rcases side with rfl | rfl <;> decide
    obtain ⟨clearG,clearH,negative,directAnd⟩ := local_clearance least u which high
      hitG tagG rawG hitH tagH wireH only3 onlyG
    obtain ⟨slot,reader,found,tag,reads,unique⟩ := sole_or_of_local_exclusions clique least (by omega)
      budget side high hitG tagG rawG hitH tagH wireH clearG clearH
      (ear_has_binary_reader least notCount side) negative directAnd
      (fun p D hit tag used sole => ear_and_has_binary_next least notCount side hit tag used sole)
    exact dirty_peer_of_sole_or least measure u slot reader found tag reads unique
  obtain ⟨reader1,peer1,one,dirty1⟩ := earOR 1 (Or.inl rfl)
  obtain ⟨reader5,peer5,five,dirty5⟩ := earOR 4 (Or.inr rfl)
  have oneShape : OnlyOrReader gs 1 reader1 peer1 := one
  have fiveShape : OnlyOrReader gs 5 reader5 peer5 := five
  obtain ⟨neg,isNot,uniqueNeg⟩ := unique_negation (n := 7) notCount
  let first := slotWire hitG
  let second := slotWire hitH
  let ear := inputWire gs (3 : Fin 7)
  have readRaw : soleReader gs ear first := sole_reader_of_slots hitG only3
  have readG : soleReader gs first second := sole_reader_of_slots hitH onlyG
  have noPath : ¬ ReflTransGen (readEdge gs) ear neg := by
    cases high
    · obtain ⟨peer,apart,reads,_,eval⟩ := binary_gate_peer least hitG true (by simpa using tagG) ear rawG
      refine L10586EarAndClose.no_ear_path_to_not_of_and_peer least readRaw reads apart ?_
        oneShape dirty1 isNot uniqueNeg
      intro x
      change vl gs x (7+r) = _
      rw [eval]
      change (vl gs x 3 && vl gs x peer.val) = _
      rw [vl_input gs x 3 (by decide)]
      rw [show (⟨3,by decide⟩ : Fin 7) = 3 by decide]
    · have firstNotNeg : first ≠ neg := by
        intro same
        obtain ⟨p,N,hitN,idx,tag⟩ := isNot
        have eq := congrArg Fin.val same
        change 7+r = neg.val at eq
        have slots : p = r := by omega
        subst p
        have gateEq := Option.some.inj (hitG.symm.trans hitN)
        subst N
        rw [tagG] at tag
        cases tag
      obtain ⟨peer,apart,reads,_,eval⟩ := binary_gate_peer least hitH true (by simpa using tagH) first wireH
      have joins : readEdge gs first second := ⟨q,h,hitH,rfl,wireH⟩
      exact L10586EarOrClose.no_ear_path_to_not least readRaw readG joins reads apart firstNotNeg
        (fun x => by
          change vl gs x (7+q) = _
          simpa [Bin] using eval x) oneShape dirty1 isNot uniqueNeg
  have growth := update_keeps_true_of_no_negand_ancestry least.hcl (3 : Fin 7)
    (fun w tag => by rw [uniqueNeg w tag]; exact noPath)
  exact two_dirty_or_readers_impossible least.hcl (out := leastOutputWire least)
    (fun x => least.hev x) oneShape fiveShape
    (fun x => growth x peer1) (fun x => growth x peer5) dirty1 dirty5
theorem no_normal_twelve (clique : K4BinaryLower) {gs : List Gate} {out : ℕ}
    (least : Least 7 target gs out) (size : gs.length = 12) (one : notGateCount gs = 1)
    (fewest : Fewest gs) : False := by
  have cost := binary_add_not gs
  obtain ⟨r,reads,only⟩ := L10586EarCofactors.three_unique_reader least size.le
  obtain ⟨g,hit,used⟩ := reads
  rcases L10586EarShape.unique_readers_binary least (by omega) hit used only with isAnd | isOr
  · obtain ⟨q,h,_,atQ,tag,src,reader⟩ := L10586EarShape.and_reader_next_or least size.le hit isAnd used
    exact exclude_typed_chain clique least size one fewest false hit isAnd used atQ tag src only reader
  · obtain ⟨q,h,atQ,bin,src⟩ := positive_reader_after_raw_three_or least one hit isOr used only
    obtain ⟨_,tag,reader⟩ := L10586EarOrShape.or_reader_next_and clique least (by omega)
      (by omega) hit isOr used atQ bin src
    exact exclude_typed_chain clique least size one fewest true hit isOr used atQ tag src only reader
theorem replacement (clique : K4BinaryLower) (s : ℕ) (fit : HasCircuitSize 7 target s) :
    L10586Tight.Replacement s := by
  by_cases large : 13 ≤ s
  · exact ⟨control.gates,control.output,basis,by rw [L10586Control.size]; exact large,computes⟩
  obtain ⟨gs,out,least,size,fewest⟩ := exists_least_fewest_dirty_reads 7 s target nonconstant fit
  have lower := least_binary_budget least
  have zero : notGateCount gs = 0 := by
    by_contra! someNot
    exact no_normal_twelve clique least (by omega) (by omega) fewest
  refine ⟨gs,out,?_,size,least.hev⟩
  intro g member
  obtain ⟨slot,hit⟩ := List.mem_iff_getElem?.mp member
  rcases least.hcl slot g hit with ⟨tag,_⟩ | ⟨tags,a,b,_,_,args⟩
  · have notFree := one_not_gate_positive ⟨g,member,tag⟩
    omega
  · exact ⟨tags,by simp [args]⟩
end L10586Closure
end ProofPart28

section ProofPart29
namespace L10586K4Core
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
abbrev W := BitVec 64
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
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
def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val
theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]
theorem cuts_spec (ws : List W) (i : Fin 32) :
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
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
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
    decide (w ∉ a :: b :: r) &&
      (((v == -1) && next extra (w :: r)) ||
       ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                        ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
       ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (fresh : z ∉ a :: b :: r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  change (decide (z ∉ a :: b :: r) && _) = true
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fresh, ?_⟩
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
        have fresh : z ∉ a :: b :: r := fun mem =>
          hout (List.mem_toFinset.mpr (perm.mem_iff.mpr mem))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk fresh
          (by omega) (by omega) (cuts_full hg hl)
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
open PEqualNP.CircuitLowerBounds
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)
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
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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
private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
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
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
private abbrev k4x0 : W := 0xcb2cb2cb00000fc0
private abbrev k4x1 : W := 0xd55555550003f000
private abbrev k4x2 : W := 0x269a69a600fc0000
private abbrev k4x3 : W := 0x38e38e383f000000
def k4inputs : List W := [k4x0, k4x1, k4x2, k4x3]
private theorem full_of_cut :
    ∀ ws ∈ k4inputs.sublists, cuts ws = -1 → ws = k4inputs := by
  decide +kernel
private theorem initial_pairs :
    pairs k4inputs =
      [(k4x0, k4x1, [k4x2, k4x3]), (k4x0, k4x2, [k4x1, k4x3]),
       (k4x0, k4x3, [k4x1, k4x2]), (k4x1, k4x2, [k4x0, k4x3]),
       (k4x1, k4x3, [k4x0, k4x2]), (k4x2, k4x3, [k4x0, k4x1])] := rfl
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem no01 :
    dispatch 3 (optimized 5) k4x0 k4x1 [k4x2, k4x3] = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem no02 :
    dispatch 3 (optimized 5) k4x0 k4x2 [k4x1, k4x3] = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem no03 :
    dispatch 3 (optimized 5) k4x0 k4x3 [k4x1, k4x2] = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem no12 :
    dispatch 3 (optimized 5) k4x1 k4x2 [k4x0, k4x3] = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem no13 :
    dispatch 3 (optimized 5) k4x1 k4x3 [k4x0, k4x2] = false := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
private theorem no23 :
    dispatch 3 (optimized 5) k4x2 k4x3 [k4x0, k4x1] = false := by
  decide +kernel
private theorem reject_initial :
    optimized 6 3 k4inputs = false := by
  have not_done : (k4inputs == [goal] || k4inputs == [~~~goal]) = false := by
    decide +kernel
  change ((k4inputs == [goal] || k4inputs == [~~~goal]) ||
    (pairs k4inputs).any (fun (a, b, rest) => dispatch 3 (optimized 5) a b rest)) = false
  simp only [not_done, initial_pairs, List.any_cons, List.any_nil,
    no01, no02, no03, no12, no13, no23, Bool.false_or]
theorem k4exact : search 6 k4inputs = false := by
  unfold search
  apply List.any_eq_false.mpr
  intro ws mem accepted
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  obtain ⟨⟨_, covered⟩, reached⟩ := accepted
  have full := full_of_cut ws mem covered
  subst ws
  change optimized 6 3 k4inputs = true at reached
  exact Bool.noConfusion (reject_initial.symm.trans reached)
end L10586K4Core
namespace L10586K4Binary
open PEqualNP.CircuitLowerBounds
open L10586K4Core
open scoped BigOperators
def target (x : Fin 4 → Bool) : Bool :=
  Nat.testBit 0xfee8 (∑ i : Fin 4, if x i then 2 ^ (i : ℕ) else 0)
private def wordBit (k : Fin 64) (w : W) : Bool := w[k.val]
private def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
set_option maxRecDepth 8000 in
theorem table_matches_target : ∀ k : Fin 64,
    target (fun i => wordBit k (k4inputs.getD i.val 0)) = wordBit k goal := by
  decide +kernel
set_option maxRecDepth 8000 in
theorem table_inputs_nodup : k4inputs.Nodup := by decide +kernel
theorem target_edges : ∀ x : Fin 4 → Bool,
    target x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
      (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)) := by
  decide +kernel
theorem binary_at_least_seven (gs : List Gate) (out : ℕ)
    (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin 4 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    7 ≤ binaryCost gs := by
  by_contra! short
  have low : binaryCost gs ≤ 6 := by omega
  have width : k4inputs.length = 4 := rfl
  have init : ∀ w ∈ k4inputs, holds k4inputs.toFinset w := fun w hw =>
    .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl boolStep (k4inputs.map (wordBit k))).getD out false = wordBit k goal := by
    let x (i : Fin 4) : Bool := wordBit k (k4inputs.getD i.val 0)
    have same : List.ofFn x = k4inputs.map (wordBit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < k4inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, out⟩ (k4inputs.map (wordBit k)) = wordBit k goal
    rw [← same, computes]
    exact table_matches_target k
  obtain ⟨t, ht, run⟩ := compile gs out legalGates k4inputs k4inputs.toFinset init evaluate
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a k4inputs.toFinset) :
      build basicOps t b k4inputs.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have found := search_complete ht 6 k4inputs table_inputs_nodup (lift low run)
  exact Bool.noConfusion (k4exact.symm.trans found)
def countNOT (gs : List Gate) : ℕ :=
  (gs.filter fun g => match g.op with
    | .not => true
    | _ => false).length
theorem binary_and_not_count (gs : List Gate) :
    binaryCost gs + countNOT gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
      cases hop : g.op <;> simp [binaryCost, countNOT, isBinary, hop] at * <;> omega
theorem total_at_least_seven_add_not (gs : List Gate) (out : ℕ)
    (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin 4 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    7 + countNOT gs ≤ gs.length := by
  have lower := binary_at_least_seven gs out legalGates computes
  have count := binary_and_not_count gs
  omega
end L10586K4Binary
end ProofPart29

section ProofPart30
namespace L10586K4Bridge
open L11022RestrictSupport L10586WeightedRestriction L10586BinaryCofactors
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitHelpers CircuitHelpers.Readers
theorem clique_binary_lower : K4BinaryLower := by
  intro gs out strict ev
  have legal : ∀ g ∈ gs, L10586K4Core.legal g := by
    intro g mem
    obtain ⟨p,hit⟩ := List.mem_iff_getElem?.mp mem
    rcases strict p g hit with ⟨tag,_,_,args⟩ | ⟨tag,_,_,_,_,args⟩
    · exact ⟨Or.inr (Or.inr tag),by simp [args]⟩
    · exact ⟨tag.elim Or.inl (fun h => Or.inr (Or.inl h)),by simp [args]⟩
  have cost : L10586K4Core.binaryCost gs = binaryCount gs := by
    rw [L10586K4Core.binaryCost,← List.countP_eq_length_filter]
    unfold binaryCount opCount
    congr 1
    funext g
    cases tag : g.op <;> simp [L10586K4Core.isBinary,isNotGate,tag]
  rw [← cost]
  exact L10586K4Binary.binary_at_least_seven gs out legal ev
end L10586K4Bridge
end ProofPart30

end PEqualNP.Outside.L_meta_10586

theorem PEqualNP.Outside.L_meta_10586 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal _oneNot evaluates
  have fit : PEqualNP.MetaComplexity.HasCircuitSize 7 PEqualNP.Outside.L_meta_10586.L10586Control.target gates.length := by
    refine ⟨⟨gates,out⟩,?_,le_rfl,?_⟩
    · intro gate member
      have ok := legal gate member
      refine ⟨?_,ok.2⟩
      rcases ok.1 with andGate | orGate | notGate <;> simp_all
    · intro x
      simpa [PEqualNP.Outside.L_meta_10586.L10586Control.target,PEqualNP.Outside.L_meta_10586.L10586Control.edgeData] using evaluates x
  obtain ⟨fresh,output,monotone,size,same⟩ :=
    PEqualNP.Outside.L_meta_10586.L10586Closure.replacement PEqualNP.Outside.L_meta_10586.L10586K4Bridge.clique_binary_lower gates.length fit
  exact ⟨fresh,output,monotone,size,fun x => by
    simpa [PEqualNP.Outside.L_meta_10586.L10586Control.target,PEqualNP.Outside.L_meta_10586.L10586Control.edgeData] using same x⟩
