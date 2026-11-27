import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2940


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The normalization, fork bound, and pair invariant below are adapted from
-- L-meta-2165 by copsrlpond and its predecessor L-meta-1549.


-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

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
    simpa [noNeighbors] using live
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

omit [Fintype V] [DecidableRel G.Adj] in
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

namespace CircuitProof

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

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

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
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
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
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
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

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Stat.const false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

namespace CircuitProof

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


end CircuitProof

namespace CircuitProof

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

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
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
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
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


end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

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

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
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
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
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
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
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

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

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


end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm

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
open CircuitProof CircuitProof.Readers

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
    exact PEqualNP.Outside.L_meta_2940.least_gate_inputs_nodup least nonnull _
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
open CircuitProof
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
open CircuitProof
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
open CircuitProof
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

namespace PetersenNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)


def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)


lemma noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true ↔ ∃ a b, (a, b) ∈ es ∧ x a = true ∧ x b = true := by
  simp only [edgeFun, List.any_eq_true, Bool.and_eq_true, Prod.exists]


def graph (es : Edges) (noSelf : ∀ e ∈ es, e.1 ≠ e.2) : SimpleGraph Vertex where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => noSelf (v, v) he rfl) (fun he => noSelf (v, v) he rfl)⟩

end PetersenNine

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

def petersenNine : MaskGraph :=
  ⟨9, fun v => (#[50, 69, 138, 276, 9, 385, 258, 36, 104] : Array Nat)[v]?.getD 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem petersen_nine_no_four : fullMask petersenNine ∉ frontier petersenNine 4 := by
  decide +kernel

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

theorem petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9, G.Adj u v ↔ (petersenNine.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 9))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : 5 ≤ groups.length :=
  @groups_exceed_budget petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 petersen_nine_no_four groups twins finished

end PetersenMaskBridge

open PetersenNine

def petersenGraph : SimpleGraph Vertex := graph edges noLoops

def petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S := by
  constructor
  · intro h
    obtain ⟨a, b, edge, ha, hb⟩ := (edgeFun_true edges _).mp h
    exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, Or.inl edge⟩
  · rintro ⟨a, ha, b, hb, adjacent⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, decide_eq_true ha, decide_eq_true hb⟩
    · exact ⟨b, a, edge, decide_eq_true hb, decide_eq_true ha⟩

theorem petersen_graph_matches_mask :
    ∀ a b : Vertex, petersenGraph.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val = true := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide

theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex, petersenGraph.Adj i j →
      ∃ u v, petersenGraph.Adj i u ∧ petersenGraph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ petersenGraph.Adj u v := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
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

open PEqualNP.CircuitLowerBounds CircuitProof
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
open CircuitProof
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
  change (_ ↔ decode (code I) O)
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

open PEqualNP.CircuitLowerBounds CircuitProof
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

abbrev petersenF := edgeFun edges

private theorem petersen_dependency_samples : ∀ v : Vertex, ∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w)))) ≠ petersenF (fun i => decide (i = w)) := by
  decide +kernel

theorem petersen_depends (v : Vertex) : Dep petersenF v := by
  obtain ⟨w, hw⟩ := petersen_dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

theorem petersen_nonconstant : ∃ x y : Vertex → Bool, petersenF x ≠ petersenF y :=
  dep_nc (petersen_depends 0)

private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true := by
  decide +kernel

theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y, petersenF (Function.update x v b) ≠ petersenF (Function.update y v b) := by
  obtain ⟨no, yes⟩ := petersen_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩


lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9, petersenGraph.Adj u v ∧ x u = true ∧ x v = true := by
  change PetersenNine.edgeFun PetersenNine.edges x = true ↔ _
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, adjacent, ha, hb⟩
    change (a, b) ∈ PetersenNine.edges ∨ (b, a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem least_petersen_five_branches (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n := 9) gs).card := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  have outValid := least_petersen_output_valid least
  let outWire : Fin (9 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant outValid
  let label : Fin 9 → Fin (9 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have labels (v : Fin 9) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup petersenGraph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required petersenGraph label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five petersenGraph petersen_graph_matches_mask)

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]

lemma nonNotCount_three_not (gs : List Gate) (i j k : Fin gs.length)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not)
    (hk : (gs.get k).op = .not) : nonNotCount gs + 3 ≤ gs.length := by
  let g : Gate := ⟨.and, []⟩
  let gs' := gs.set i.val g
  let gs'' := gs'.set j.val g
  let gs''' := gs''.set k.val g
  have hj' : j.val < gs'.length := by simpa [gs'] using j.isLt
  have hk' : k.val < gs'.length := by simpa [gs'] using k.isLt
  have hk'' : k.val < gs''.length := by simpa [gs''] using hk'
  have cmp_i := nonNotCount_replace_not gs i.val i.isLt hi
  have cmp_j := nonNotCount_replace_not gs' j.val hj' (by
    rw [show gs'[j.val] = gs[j.val] from List.getElem_set_ne (fun h => hij (Fin.ext h)) hj']
    exact hj)
  have cmp_k := nonNotCount_replace_not gs'' k.val hk'' (by
    rw [show gs''[k.val] = gs'[k.val] from List.getElem_set_ne (fun h => hjk (Fin.ext h)) hk'',
        show gs'[k.val] = gs[k.val] from List.getElem_set_ne (fun h => hik (Fin.ext h)) hk']
    exact hk)
  change nonNotCount gs' = nonNotCount gs + 1 at cmp_i
  change nonNotCount gs'' = nonNotCount gs' + 1 at cmp_j
  change nonNotCount gs''' = nonNotCount gs'' + 1 at cmp_k
  have hbound : nonNotCount gs''' ≤ gs.length := by
    simpa [nonNotCount, gs''', gs'', gs', g] using
      (List.countP_le_length (p := fun q : Gate => !(isNotGate q.op)) (l := gs'''))
  omega

theorem petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex → Bool, C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates := by
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C hfan he petersen_nonconstant
  have valid := least_petersen_output_valid least
  have live := least_read_edge_live least petersen_nonconstant petersen_depends
    petersen_restrict_nonconstant valid
  let branches := circuitBranchWires (n := 9) gs
  have branchLower : 5 ≤ branches.card := least_petersen_five_branches gs o least
  have branchBudget := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  omega




open PEqualNP.CircuitLowerBounds CircuitProof CircuitProof.Readers

open PEqualNP.CircuitLowerBounds CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

theorem forksOfBudget {n K : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (budget : nonNotCount gs + 1 ≤ n + K) : (circuitBranchWires (n := n) gs).card ≤ K := by
  classical
  let branches := circuitBranchWires (n := n) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
      let wire : Fin (n + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at count
  change branches.card ≤ K
  omega

theorem normalizedCutsK {n K : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ K) :
    ∃ label : Fin n → Fin (K + 1),
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ i, label i = Fin.last K ↔ firstInputBoundary clean out live i = out) ∧
      (∀ k : Fin (K + 1), ∃ code : (Fin n → Bool) → Bool,
        (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
        (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → vl gs x out.val = vl gs y out.val)) := by
  classical
  let branches := circuitBranchWires (n := n) gs
  change branches.card ≤ K at hcard
  let cuts := insert out branches
  have hpos : 0 < cuts.card := Finset.card_pos.mpr ⟨out, Finset.mem_insert_self out branches⟩
  have small : cuts.card ≤ K + 1 := (Finset.card_insert_le ..).trans (by omega)
  let boundary := firstInputBoundary clean out live
  have mem (i : Fin n) : boundary i ∈ cuts := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let embed := (cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin (K + 1) :=
    ⟨(K + 1) - cuts.card + (embed c).val, by have := (embed c).isLt; omega⟩
  have strict : StrictMono rank := by
    intro c d hcd
    have he := embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change (K + 1) - cuts.card + (embed c).val < (K + 1) - cuts.card + (embed d).val
    omega
  let outC : cuts := ⟨out, Finset.mem_insert_self out branches⟩
  have houtRank : rank outC = Fin.last K := by
    have hmax : ∀ c : cuts, c ≤ outC := fun c => wire_le_output clean out live c.val
    let topC : cuts := (cuts.orderIsoOfFin rfl) ⟨cuts.card - 1, by omega⟩
    have hle1 : (embed topC).val ≤ (embed outC).val := embed.monotone (hmax topC)
    have htop : (embed topC).val = cuts.card - 1 := by
      simp [embed, topC]
    have hlt2 : (embed outC).val < cuts.card := (embed outC).isLt
    have heq : (embed outC).val = cuts.card - 1 := by omega
    apply Fin.ext
    change (K + 1) - cuts.card + (embed outC).val = K
    omega
  let loc (i : Fin n) : cuts := ⟨boundary i, mem i⟩
  let label (i : Fin n) := rank (loc i)
  have eqv (i j : Fin n) : label i = label j ↔ boundary i = boundary j := by
    change rank (loc i) = rank (loc j) ↔ (loc i).val = (loc j).val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  have isLast (i : Fin n) : label i = Fin.last K ↔ boundary i = out := by
    rw [← houtRank]
    change rank (loc i) = rank outC ↔ (loc i).val = outC.val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  refine ⟨label, eqv, isLast, ?_⟩
  intro k
  by_cases used : ∃ z, label z = k
  · obtain ⟨z, rfl⟩ := used
    let c := boundary z
    have term : FirstBranchRoute.Terminal (readEdge gs) out c :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs z)
    refine ⟨fun x => vl gs x c.val, ?_, ?_⟩
    · intro x y hxy
      apply agree_on_input_ancestors clean
      intro i path
      apply hxy i
      exact strict.monotone (show loc i ≤ loc z from
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path term)
    · intro x y hxy heq
      have blocked := firstInputGroup_controlled clean out live c
      rcases blocked with atOut | apart
      · simpa only [atOut] using heq
      · apply circuit_cut_agreement clean c out x y heq
        intro i hi
        apply apart i
        apply (mem_firstInputGroup clean out live c i).mpr
        exact (eqv i z).mp (by_contra fun ne => hi (hxy i ne))
  · refine ⟨fun _ => false, fun _ _ _ => rfl, ?_⟩
    intro x y hxy _
    have : x = y := funext (fun i => hxy i (fun h => used ⟨i, h⟩))
    rw [this]


lemma conf_guard {K : ℕ} {a b : Fin K} (h : a ≠ b) : (a.val != b.val) = true :=
  bne_iff_ne.mpr (fun e => h (Fin.ext e))

lemma cube_guard {K : ℕ} {a b c : Fin K} (h : a = b → c ≤ a) :
    (!(a.val == b.val) || decide (c.val ≤ a.val)) = true := by
  by_cases he : a = b
  · have hle : c.val ≤ a.val := h he
    simp [hle]
  · have hne : a.val ≠ b.val := fun e => he (Fin.ext e)
    simp [hne]

namespace SignedCompile2940

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def wire (i : ℕ) : ℕ :=
  if i < 10 then i else if i = 10 then 11 else 14 + 3 * (i - 11)

def pin (p : ℕ × Bool) (neg : ℕ) : ℕ :=
  if p.2 then neg else wire p.1

def negate (i : ℕ) : Gate := ⟨.not, [i]⟩

def constants : List Gate := [⟨.not, []⟩, negate 10]

def block (j : ℕ) (a b : ℕ × Bool) : List Gate :=
  [negate (wire a.1), negate (wire b.1),
    ⟨.and, [pin a (12 + 3 * j), pin b (13 + 3 * j)]⟩]

def blocks {n : ℕ} (a b : Fin n → ℕ × Bool) (j : ℕ) : List Gate :=
  if hj : j < n then block j (a ⟨j, hj⟩) (b ⟨j, hj⟩) else []

def schedule (gates : ℕ → List Gate) : ℕ → List Gate
  | 0 => constants
  | k + 1 => schedule gates k ++ gates k

def run (gs : List Gate) (x : Fin 10 → Bool) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma run_append (gs hs : List Gate) (x : Fin 10 → Bool) :
    run (gs ++ hs) x = hs.foldl step (run gs x) := by
  change (gs ++ hs).foldl step (List.ofFn x) = hs.foldl step (gs.foldl step (List.ofFn x))
  rw [List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_old {w : List Bool} (g : Gate) {i : ℕ} (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma step_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma wire_lt {i k : ℕ} (hi : i < 11 + k) : wire i < 12 + 3 * k := by
  unfold wire
  split
  · omega
  split <;> omega

lemma run_constants (x : Fin 10 → Bool) :
    run constants x = List.ofFn x ++ [true, false] := by
  let v : List Bool := List.ofFn x
  have hv : v.length = 10 := List.length_ofFn
  have h := step_new v (⟨.not, []⟩ : Gate)
  rw [hv] at h
  change (v ++ [true]).getD 10 false = true at h
  change (v ++ [true]) ++ [!((v ++ [true]).getD 10 false)] = v ++ [true, false]
  rw [h, List.append_assoc]
  rfl

lemma step_pin {w : List Bool} {p : ℕ × Bool} (hp : wire p.1 < w.length) :
    (step w (negate (wire p.1))).getD (pin p w.length) false =
      (w.getD (wire p.1) false ^^ p.2) := by
  cases hs : p.2
  · simpa [pin, hs] using step_old (negate (wire p.1)) hp
  · simpa [pin, hs, negate, GateOp.eval] using step_new w (negate (wire p.1))

lemma block_run {w : List Bool} {j : ℕ} {a b : ℕ × Bool}
    (hw : w.length = 12 + 3 * j) (ha : a.1 < 11 + j) (hb : b.1 < 11 + j) :
    let w' := (block j a b).foldl step w
    w'.length = 12 + 3 * (j + 1) ∧
      (∀ i < w.length, w'.getD i false = w.getD i false) ∧
      w'.getD (wire (11 + j)) false =
        ((w.getD (wire a.1) false ^^ a.2) && (w.getD (wire b.1) false ^^ b.2)) := by
  let ga := negate (wire a.1)
  let gb := negate (wire b.1)
  let wa := step w ga
  let wb := step wa gb
  let g : Gate := ⟨.and, [pin a (12 + 3 * j), pin b (13 + 3 * j)]⟩
  have hwa : wa.length = 13 + 3 * j := by
    change (step w ga).length = _; rw [step_length, hw]; omega
  have hwb : wb.length = 14 + 3 * j := by
    change (step wa gb).length = _; rw [step_length, hwa]; omega
  change (step wb g).length = _ ∧ _ ∧ _
  refine ⟨by rw [step_length, hwb]; omega, ?_, ?_⟩
  · intro i hi
    change (step wb g).getD i false = w.getD i false
    rw [step_old g (by omega : i < wb.length)]
    change (step wa gb).getD i false = _
    rw [step_old gb (by omega : i < wa.length)]
    exact step_old ga hi
  · have hap := wire_lt ha
    have hbp := wire_lt hb
    have hpin : pin a (12 + 3 * j) < wa.length := by
      simp only [pin, hwa]; split <;> omega
    have hva : wb.getD (pin a (12 + 3 * j)) false = (w.getD (wire a.1) false ^^ a.2) := by
      change (step wa gb).getD _ false = _
      rw [step_old gb hpin]
      simpa only [hw] using step_pin (w := w) (p := a) (by omega)
    have hvb : wb.getD (pin b (13 + 3 * j)) false = (w.getD (wire b.1) false ^^ b.2) := by
      have h := step_pin (w := wa) (p := b) (by omega)
      rw [hwa, step_old ga (by omega : wire b.1 < w.length)] at h
      exact h
    have hout : wire (11 + j) = wb.length := by
      simp [wire, show ¬ 11 + j < 10 by omega, show 11 + j ≠ 10 by omega, hwb]
    change (step wb g).getD (wire (11 + j)) false = _
    rw [hout, step_new]
    simp only [List.getD_eq_getElem?_getD] at hva hvb
    simp [g, GateOp.eval, hva, hvb]

def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma negate_allowed (i : ℕ) : allowed (negate i) := by simp [allowed, negate]

lemma sched_budget {n : ℕ} (a b : Fin n → ℕ × Bool) (k : ℕ) (hk : k ≤ n) :
    nonNotCount (schedule (blocks a b) k) = k := by
  induction k with
  | zero => simp [schedule, constants, negate, nonNotCount, isNotGate]
  | succ k ih =>
    have hj : k < n := by omega
    have h := ih (by omega)
    unfold nonNotCount at h ⊢
    simp only [schedule, blocks, dite_eq_left hj, List.countP_append, h]
    simp [block, negate, isNotGate]

lemma sched_allowed {n : ℕ} (a b : Fin n → ℕ × Bool) (k : ℕ) (hk : k ≤ n) :
    ∀ g ∈ schedule (blocks a b) k, allowed g := by
  induction k with
  | zero =>
    intro g hg
    simp only [schedule, constants, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp [allowed]
    · exact negate_allowed 10
  | succ k ih =>
    have hj : k < n := by omega
    intro g hg
    simp only [schedule, blocks, dite_eq_left hj, List.mem_append] at hg
    rcases hg with h | h
    · exact ih (by omega) g h
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact negate_allowed _
    · exact negate_allowed _
    · simp [allowed]

def binStep (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

lemma binStep_length (w : List Bool) (g : BinaryGate) : (binStep w g).length = w.length + 1 := by
  simp [binStep]

lemma binStep_old {w : List Bool} (g : BinaryGate) {i : ℕ} (hi : i < w.length) :
    (binStep w g).getD i false = w.getD i false := by
  simp only [binStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma binStep_new (w : List Bool) (g : BinaryGate) :
    (binStep w g).getD w.length false = g.op (w.getD g.left false) (w.getD g.right false) := by
  simp only [binStep, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma bin_wires_take_succ (gs : List BinaryGate) (init : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.take (k + 1)).foldl binStep init = binStep ((gs.take k).foldl binStep init) gs[k] := by
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma bin_wires_len (gs : List BinaryGate) (init : List Bool) :
    (gs.foldl binStep init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih, binStep_length]; omega

theorem compile_binary (B : BinaryCircuit) (p : Bool)
    (hsigned : ∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun u v => (u == a) && (v == b)) :
    ∃ D : Circuit, FanInTwo D ∧ nonNotCount D.gates = B.size ∧
      ∀ x : Fin 10 → Bool, circuitFun 10 D x = (B.eval (List.ofFn x ++ [false]) != p) := by
  classical
  let n := B.gates.length
  have hex : ∀ j : Fin n, ∃ ab : Bool × Bool, B.gates[j.val].op = fun u v => (u == ab.1) && (v == ab.2) := fun j =>
    let ⟨a, b, h⟩ := hsigned B.gates[j.val] (List.getElem_mem j.isLt); ⟨(a, b), h⟩
  let clamp (j i : ℕ) : ℕ := if i < 11 + j then i else 10
  let ab (j : Fin n) : Bool × Bool := Classical.choose (hex j)
  let aPin (j : Fin n) : ℕ × Bool := (clamp j.val B.gates[j.val].left, !(ab j).1)
  let bPin (j : Fin n) : ℕ × Bool := (clamp j.val B.gates[j.val].right, !(ab j).2)
  have hop (j : Fin n) (u v : Bool) :
      B.gates[j.val].op u v = ((u ^^ (aPin j).2) && (v ^^ (bPin j).2)) := by
    have h : B.gates[j.val].op = fun u v => (u == (ab j).1) && (v == (ab j).2) := Classical.choose_spec (hex j)
    rw [h]
    dsimp only [aPin, bPin]
    cases (ab j).1 <;> cases (ab j).2 <;> cases u <;> cases v <;> rfl
  have hreads (j : Fin n) : (aPin j).1 < 11 + j.val ∧ (bPin j).1 < 11 + j.val := by
    simp only [aPin, bPin, clamp]; constructor <;> split <;> omega
  let outPin : ℕ × Bool := (if B.output < 11 + n then B.output else 10, p)
  have hout : outPin.1 < 11 + n := by simp only [outPin]; split <;> omega
  let gs := schedule (blocks aPin bPin) n
  let last := negate (wire outPin.1)
  refine ⟨⟨gs ++ [last], pin outPin (12 + 3 * n)⟩, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ gs ++ [last] at hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact sched_allowed aPin bPin n le_rfl _ h
    · exact negate_allowed _
  · change nonNotCount (gs ++ [last]) = n
    have h := sched_budget aPin bPin n le_rfl
    simpa [gs, last, nonNotCount, List.countP_append, negate, isNotGate] using h
  · intro x
    let init : List Bool := List.ofFn x ++ [false]
    have hinitLen : init.length = 11 := by simp [init]
    have hrun : ∀ k ≤ n,
        let w := run (schedule (blocks aPin bPin) k) x
        let bw := (B.gates.take k).foldl binStep init
        w.length = 12 + 3 * k ∧ bw.length = 11 + k ∧
          ∀ i < 11 + k, w.getD (wire i) false = bw.getD i false := by
      intro k hk
      induction k with
      | zero =>
        change (run constants x).length = 12 ∧ init.length = 11 ∧
          ∀ i < 11, (run constants x).getD (wire i) false = init.getD i false
        rw [run_constants]
        refine ⟨by simp, hinitLen, ?_⟩
        intro i hi
        by_cases h10 : i < 10
        · rw [show wire i = i by simp [wire, h10]]
          have hi' : i < (List.ofFn x).length := by simpa using h10
          simp only [init, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
        · have h10' : i = 10 := by omega
          subst i
          change (List.ofFn x ++ [true, false]).getD 11 false = (List.ofFn x ++ [false]).getD 10 false
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
          simp
      | succ k ih =>
        have hj : k < n := by omega
        let j : Fin n := ⟨k, hj⟩
        obtain ⟨hlen, hblen, hw⟩ := ih (by omega)
        let w := run (schedule (blocks aPin bPin) k) x
        let bw := (B.gates.take k).foldl binStep init
        have hblock := block_run (w := w) (a := aPin j) (b := bPin j) hlen (hreads j).1 (hreads j).2
        have hbw1 : (B.gates.take (k + 1)).foldl binStep init = binStep bw B.gates[k] :=
          bin_wires_take_succ B.gates init k hj
        change (run (schedule (blocks aPin bPin) k ++ blocks aPin bPin k) x).length = _ ∧
          ((B.gates.take (k + 1)).foldl binStep init).length = _ ∧
          ∀ i < 11 + (k + 1), (run (schedule (blocks aPin bPin) k ++ blocks aPin bPin k) x).getD (wire i) false =
            ((B.gates.take (k + 1)).foldl binStep init).getD i false
        rw [run_append, blocks, dite_eq_left hj, hbw1]
        obtain ⟨hsize, hold, hnew⟩ := hblock
        refine ⟨hsize, by rw [binStep_length, hblen]; omega, ?_⟩
        have h10f : bw.getD 10 false = false := by
          have h0 : init.getD 10 false = false := by
            simp only [init, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by simp)]; simp
          have hkeep : ∀ m ≤ k, ((B.gates.take m).foldl binStep init).getD 10 false = false := by
            intro m hm
            induction m with
            | zero => simpa using h0
            | succ m ihm =>
              rw [bin_wires_take_succ B.gates init m (by omega)]
              rw [binStep_old _ (by rw [bin_wires_len]; simp [hinitLen]; omega)]
              exact ihm (by omega)
          exact hkeep k le_rfl
        have hclamp (idx : ℕ) : bw.getD (clamp k idx) false = bw.getD idx false := by
          simp only [clamp]
          split
          · rfl
          · rw [h10f]
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by rw [show bw.length = 11 + k from hblen]; omega)]
            rfl
        intro i hi
        by_cases hlt : i < 11 + k
        · rw [binStep_old _ (by rw [show bw.length = 11 + k from hblen]; exact hlt)]
          have hltw : wire i < w.length := by rw [hlen]; exact wire_lt hlt
          exact (hold (wire i) hltw).trans (hw i hlt)
        · have heq : i = 11 + k := by omega
          subst i
          rw [show (11 + k) = bw.length from hblen.symm, binStep_new, hblen]
          rw [hnew, hw _ (hreads j).1, hw _ (hreads j).2]
          change ((bw.getD (clamp k B.gates[k].left) false ^^ (aPin j).2) &&
            (bw.getD (clamp k B.gates[k].right) false ^^ (bPin j).2)) = _
          rw [hclamp, hclamp, ← hop j]
    obtain ⟨hlen, hblen, hw⟩ := hrun n le_rfl
    have hbw_eq : (B.gates.take n).foldl binStep init = B.wires init := by
      rw [List.take_of_length_le le_rfl]; rfl
    change (run (gs ++ [last]) x).getD (pin outPin (12 + 3 * n)) false =
      ((B.wires init).getD B.output false != p)
    rw [run_append]
    change (step (run gs x) last).getD (pin outPin (12 + 3 * n)) false = _
    rw [← hlen, step_pin (w := run gs x) (p := outPin) (by rw [hlen]; exact wire_lt hout)]
    rw [hw outPin.1 hout, hbw_eq]
    have houtVal : (B.wires init).getD outPin.1 false = (B.wires init).getD B.output false := by
      simp only [outPin]
      split
      · rfl
      · have h10f : (B.wires init).getD 10 false = false := by
          have h0 : init.getD 10 false = false := by
            simp only [init, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by simp)]; simp
          have hkeep : ∀ m ≤ n, ((B.gates.take m).foldl binStep init).getD 10 false = false := by
            intro m hm
            induction m with
            | zero => simpa using h0
            | succ m ihm =>
              rw [bin_wires_take_succ B.gates init m (by omega)]
              rw [binStep_old _ (by rw [bin_wires_len]; simp [hinitLen]; omega)]
              exact ihm (by omega)
          rw [← hbw_eq]; exact hkeep n le_rfl
        rw [h10f]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by rw [← hbw_eq, hblen]; omega)]
        rfl
    rw [houtVal]

end SignedCompile2940


namespace CaseB2940

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutFormula PetersenCutIndependent
open PetersenFirstGroup PetersenCutTrace PetersenScratch

def target10 (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

abbrev valid10 (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 4)

def row10 (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def depBefore : Fin 9 → ℕ := ![528, 4, 2, 4, 513, 128, 2, 4, 8]
def depAfter  : Fin 9 → ℕ := ![529, 6, 6, 12, 529, 160, 66, 132, 264]

lemma checkedDepB : ∀ i : Fin 9,
    let p := row10 (depBefore i); let q := row10 (depAfter i)
    valid10 p ∧ valid10 q ∧ (∀ j : Fin 10, j ≠ i.castSucc → p j = q j) ∧
    target10 p ≠ target10 q := by decide +kernel

def cofNo0  : Fin 10 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def cofNo1  : Fin 10 → ℕ := ![513, 2, 4, 8, 528, 32, 64, 128, 256, 513]
def cofYes0 : Fin 10 → ℕ := ![6, 12, 66, 6, 6, 6, 6, 6, 6, 6]
def cofYes1 : Fin 10 → ℕ := ![515, 6, 6, 12, 529, 38, 66, 132, 262, 515]

lemma checkedCofB : ∀ (i : Fin 10) (b : Bool),
    let p := row10 (if b then cofNo1 i else cofNo0 i)
    let q := row10 (if b then cofYes1 i else cofYes0 i)
    valid10 p ∧ valid10 q ∧ p i = b ∧ q i = b ∧ target10 p ≠ target10 q := by decide +kernel

def pairsB : List (Fin 10 × Fin 10) :=
  [(1,2),(1,6),(2,3),(2,7),(3,8),(5,7),(5,8),(6,8)]

def contextsB (e : Fin 10 × Fin 10) : Nat × Nat :=
  match e.1.val, e.2.val with
  | 1, 2 => (0, 72)
  | 1, 6 => (0, 260)
  | 2, 3 => (0, 258)
  | 2, 7 => (0, 34)
  | 3, 8 => (0, 36)
  | 5, 7 => (0, 260)
  | 5, 8 => (0, 136)
  | _, _ => (0, 10)

lemma checkedContextsB : ∀ e ∈ pairsB, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (row10 (contextsB e).1) a b
    let xo := pairInput e.1 e.2 (row10 (contextsB e).2) a b
    valid10 xa ∧ target10 xa = (a && b) ∧ valid10 xo ∧ target10 xo = (a || b) := by
  decide +kernel

theorem boundaryConflictB {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool, valid10 x → vl gs x out.val = target10 x)
    (e : Fin 10 × Fin 10) (he : e ∈ pairsB) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 10, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]; exact same.symm
  have factor (base : Fin 10 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor (row10 (contextsB e).1)
  obtain ⟨fo, ho⟩ := factor (row10 (contextsB e).2)
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h := checkedContextsB e he a b
    exact (ha a b).trans ((computes _ h.1).trans h.2.1)
  · intro a b
    have h := checkedContextsB e he a b
    exact (ho a b).trans ((computes _ h.2.2.1).trans h.2.2.2)

abbrev cubeB (i j k : Fin 10) (a b c : ℕ) : Prop :=
  let hi m := Function.update (row10 m) k true
  (∀ v, v ≠ i → v ≠ j → row10 a v = row10 b v ∧ row10 b v = row10 c v) ∧
  valid10 (row10 a) ∧ valid10 (row10 b) ∧ valid10 (hi a) ∧ valid10 (hi b) ∧ valid10 (hi c) ∧
  target10 (row10 a) ≠ target10 (row10 b) ∧ target10 (hi a) ≠ target10 (hi c) ∧ target10 (hi b) ≠ target10 (hi c)

def cubesBList : List (Fin 10 × Fin 10 × Fin 10 × ℕ × ℕ × ℕ) := [
  (0, 1, 6, 530, 529, 528),
  (0, 2, 4, 641, 645, 640),
  (0, 3, 4, 517, 525, 516),
  (0, 5, 7, 560, 529, 528),
  (0, 6, 1, 592, 529, 528),
  (0, 7, 5, 656, 529, 528),
  (0, 8, 4, 577, 833, 576),
  (1, 3, 6, 536, 530, 528),
  (1, 3, 8, 521, 515, 513),
  (1, 4, 0, 532, 534, 516),
  (1, 5, 6, 160, 130, 128),
  (1, 5, 8, 36, 6, 4),
  (1, 7, 2, 160, 34, 32),
  (1, 7, 6, 160, 34, 32),
  (1, 8, 5, 260, 6, 4),
  (1, 8, 6, 260, 6, 4),
  (2, 4, 3, 529, 517, 513),
  (2, 4, 7, 529, 517, 513),
  (2, 5, 7, 34, 6, 2),
  (2, 5, 8, 34, 6, 2),
  (2, 6, 1, 72, 12, 8),
  (2, 6, 8, 192, 132, 128),
  (2, 8, 3, 258, 6, 2),
  (2, 8, 5, 258, 6, 2),
  (2, 8, 7, 320, 68, 64),
  (3, 4, 2, 529, 521, 513),
  (3, 4, 8, 529, 521, 513),
  (3, 5, 2, 545, 521, 513),
  (3, 5, 7, 560, 536, 528),
  (3, 5, 8, 36, 12, 4),
  (3, 6, 1, 592, 536, 528),
  (3, 6, 8, 66, 10, 2),
  (3, 7, 2, 160, 40, 32),
  (3, 7, 5, 656, 536, 528),
  (4, 5, 0, 656, 688, 640),
  (4, 6, 0, 784, 848, 768),
  (4, 7, 0, 532, 660, 516),
  (4, 8, 3, 769, 529, 513),
  (4, 8, 6, 769, 529, 513),
  (5, 6, 1, 192, 160, 128),
  (5, 6, 8, 66, 34, 2),
  (6, 7, 2, 384, 320, 256),
  (6, 7, 5, 130, 66, 2),
  (7, 8, 2, 320, 192, 64),
  (7, 8, 5, 260, 132, 4)
]

lemma checkedCubesB : ∀ q ∈ cubesBList, cubeB q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 := by
  decide +kernel

def CutB (label : Fin 10 → Fin 5) (t : Fin 5) : Prop :=
  ∃ code : (Fin 10 → Bool) → Bool,
    (∀ x y, (∀ i, label i ≤ t → x i = y i) → code x = code y) ∧
    (∀ x y, valid10 x → valid10 y → (∀ i, label i ≠ t → x i = y i) →
      code x = code y → target10 x = target10 y)

lemma cubeBoundB (label : Fin 10 → Fin 5) (cut : ∀ t, CutB label t)
    (i j k : Fin 10) (a b c : ℕ) (hw : cubeB i j k a b c) :
    label i = label j → label k ≤ label i := by
  intro hh
  by_contra hle
  have hlt : label i < label k := lt_of_not_ge hle
  obtain ⟨code, low, high⟩ := cut (label i)
  obtain ⟨same, va, vb, vha, vhb, vhc, nab, nac, nbc⟩ := hw
  let hi (m : ℕ) := Function.update (row10 m) k true
  have aux (m : ℕ) : code (hi m) = code (row10 m) := by
    apply low
    intro u hu
    have hne : u ≠ k := by rintro rfl; exact (not_le_of_gt hlt) hu
    exact Function.update_of_ne hne _ _
  have off {u} (h : label u ≠ label i) : u ≠ i ∧ u ≠ j :=
    ⟨fun he => h (he ▸ rfl), fun he => h (he ▸ hh.symm)⟩
  have hab : code (row10 a) ≠ code (row10 b) := fun e =>
    nab (high _ _ va vb (fun u hu => (same u (off hu).1 (off hu).2).1) e)
  have lift {m n : ℕ} (h : ∀ u, label u ≠ label i → row10 m u = row10 n u) :
      ∀ u, label u ≠ label i → hi m u = hi n u := by
    intro u hu
    by_cases eq : u = k
    · subst u; simp [hi]
    · simpa [hi, Function.update_of_ne eq] using h u hu
  have hac : code (row10 a) ≠ code (row10 c) := fun e =>
    nac (high _ _ vha vhc (lift (fun u hu => ((same u (off hu).1 (off hu).2).1).trans
      (same u (off hu).1 (off hu).2).2)) ((aux a).trans (e.trans (aux c).symm)))
  have hbc : code (row10 b) ≠ code (row10 c) := fun e =>
    nbc (high _ _ vhb vhc (lift (fun u hu => (same u (off hu).1 (off hu).2).2))
      ((aux b).trans (e.trans (aux c).symm)))
  cases ha : code (row10 a) <;> cases hb : code (row10 b) <;> cases hc : code (row10 c) <;> simp_all

def chkB_leaf (x1 : Nat) (x2 : Nat) (x8 : Nat) (x5 : Nat) (x6 : Nat) (x7 : Nat) (x3 : Nat) (x0 : Nat) (x4 : Nat) : Bool :=
  (x0 == 4 && x3 == 4 && x4 == 4) || (x0 == 4 && x1 == 4 && x4 == 4) || (x0 == 4 && x4 == 4 && x5 == 4)

def chkB_s8 (x1 : Nat) (x2 : Nat) (x8 : Nat) (x5 : Nat) (x6 : Nat) (x7 : Nat) (x3 : Nat) (x0 : Nat) : Bool :=
  (let x4 := 0; (!((!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x3 == x4) || decide (x2 ≤ x3)) && (!(x3 == x4) || decide (x8 ≤ x3)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x6) || decide (x0 ≤ x4)) && (!(x4 == x7) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4))) || chkB_leaf x1 x2 x8 x5 x6 x7 x3 x0 x4)) &&
  (let x4 := 1; (!((!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x3 == x4) || decide (x2 ≤ x3)) && (!(x3 == x4) || decide (x8 ≤ x3)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x6) || decide (x0 ≤ x4)) && (!(x4 == x7) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4))) || chkB_leaf x1 x2 x8 x5 x6 x7 x3 x0 x4)) &&
  (let x4 := 2; (!((!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x3 == x4) || decide (x2 ≤ x3)) && (!(x3 == x4) || decide (x8 ≤ x3)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x6) || decide (x0 ≤ x4)) && (!(x4 == x7) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4))) || chkB_leaf x1 x2 x8 x5 x6 x7 x3 x0 x4)) &&
  (let x4 := 3; (!((!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x3 == x4) || decide (x2 ≤ x3)) && (!(x3 == x4) || decide (x8 ≤ x3)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x6) || decide (x0 ≤ x4)) && (!(x4 == x7) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4))) || chkB_leaf x1 x2 x8 x5 x6 x7 x3 x0 x4)) &&
  (let x4 := 4; (!((!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x3 == x4) || decide (x2 ≤ x3)) && (!(x3 == x4) || decide (x8 ≤ x3)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x6) || decide (x0 ≤ x4)) && (!(x4 == x7) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4))) || chkB_leaf x1 x2 x8 x5 x6 x7 x3 x0 x4))

def chkB_s7 (x1 : Nat) (x2 : Nat) (x8 : Nat) (x5 : Nat) (x6 : Nat) (x7 : Nat) (x3 : Nat) : Bool :=
  (let x0 := 0; (!((!(x0 == x1) || decide (x6 ≤ x0)) && (!(x0 == x5) || decide (x7 ≤ x0)) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0))) || chkB_s8 x1 x2 x8 x5 x6 x7 x3 x0)) &&
  (let x0 := 1; (!((!(x0 == x1) || decide (x6 ≤ x0)) && (!(x0 == x5) || decide (x7 ≤ x0)) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0))) || chkB_s8 x1 x2 x8 x5 x6 x7 x3 x0)) &&
  (let x0 := 2; (!((!(x0 == x1) || decide (x6 ≤ x0)) && (!(x0 == x5) || decide (x7 ≤ x0)) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0))) || chkB_s8 x1 x2 x8 x5 x6 x7 x3 x0)) &&
  (let x0 := 3; (!((!(x0 == x1) || decide (x6 ≤ x0)) && (!(x0 == x5) || decide (x7 ≤ x0)) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0))) || chkB_s8 x1 x2 x8 x5 x6 x7 x3 x0)) &&
  (let x0 := 4; (!((!(x0 == x1) || decide (x6 ≤ x0)) && (!(x0 == x5) || decide (x7 ≤ x0)) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0))) || chkB_s8 x1 x2 x8 x5 x6 x7 x3 x0))

def chkB_s6 (x1 : Nat) (x2 : Nat) (x8 : Nat) (x5 : Nat) (x6 : Nat) (x7 : Nat) : Bool :=
  (let x3 := 0; (!((x2 != x3) && (x3 != x8) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x5) || decide (x8 ≤ x3)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3))) || chkB_s7 x1 x2 x8 x5 x6 x7 x3)) &&
  (let x3 := 1; (!((x2 != x3) && (x3 != x8) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x5) || decide (x8 ≤ x3)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3))) || chkB_s7 x1 x2 x8 x5 x6 x7 x3)) &&
  (let x3 := 2; (!((x2 != x3) && (x3 != x8) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x5) || decide (x8 ≤ x3)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3))) || chkB_s7 x1 x2 x8 x5 x6 x7 x3)) &&
  (let x3 := 3; (!((x2 != x3) && (x3 != x8) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x5) || decide (x8 ≤ x3)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3))) || chkB_s7 x1 x2 x8 x5 x6 x7 x3)) &&
  (let x3 := 4; (!((x2 != x3) && (x3 != x8) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x5) || decide (x8 ≤ x3)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3))) || chkB_s7 x1 x2 x8 x5 x6 x7 x3))

def chkB_s5 (x1 : Nat) (x2 : Nat) (x8 : Nat) (x5 : Nat) (x6 : Nat) : Bool :=
  (let x7 := 0; (!((x2 != x7) && (x5 != x7) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7))) || chkB_s6 x1 x2 x8 x5 x6 x7)) &&
  (let x7 := 1; (!((x2 != x7) && (x5 != x7) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7))) || chkB_s6 x1 x2 x8 x5 x6 x7)) &&
  (let x7 := 2; (!((x2 != x7) && (x5 != x7) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7))) || chkB_s6 x1 x2 x8 x5 x6 x7)) &&
  (let x7 := 3; (!((x2 != x7) && (x5 != x7) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7))) || chkB_s6 x1 x2 x8 x5 x6 x7)) &&
  (let x7 := 4; (!((x2 != x7) && (x5 != x7) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7))) || chkB_s6 x1 x2 x8 x5 x6 x7))

def chkB_s4 (x1 : Nat) (x2 : Nat) (x8 : Nat) (x5 : Nat) : Bool :=
  (let x6 := 0; (!((x1 != x6) && (x6 != x8) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x2 == x6) || decide (x8 ≤ x2)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkB_s5 x1 x2 x8 x5 x6)) &&
  (let x6 := 1; (!((x1 != x6) && (x6 != x8) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x2 == x6) || decide (x8 ≤ x2)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkB_s5 x1 x2 x8 x5 x6)) &&
  (let x6 := 2; (!((x1 != x6) && (x6 != x8) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x2 == x6) || decide (x8 ≤ x2)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkB_s5 x1 x2 x8 x5 x6)) &&
  (let x6 := 3; (!((x1 != x6) && (x6 != x8) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x2 == x6) || decide (x8 ≤ x2)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkB_s5 x1 x2 x8 x5 x6)) &&
  (let x6 := 4; (!((x1 != x6) && (x6 != x8) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x2 == x6) || decide (x8 ≤ x2)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkB_s5 x1 x2 x8 x5 x6))

def chkB_s3 (x1 : Nat) (x2 : Nat) (x8 : Nat) : Bool :=
  (let x5 := 0; (!((x5 != x8) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2))) || chkB_s4 x1 x2 x8 x5)) &&
  (let x5 := 1; (!((x5 != x8) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2))) || chkB_s4 x1 x2 x8 x5)) &&
  (let x5 := 2; (!((x5 != x8) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2))) || chkB_s4 x1 x2 x8 x5)) &&
  (let x5 := 3; (!((x5 != x8) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2))) || chkB_s4 x1 x2 x8 x5)) &&
  (let x5 := 4; (!((x5 != x8) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2))) || chkB_s4 x1 x2 x8 x5))

def chkB_s2 (x1 : Nat) (x2 : Nat) : Bool :=
  (let x8 := 0; chkB_s3 x1 x2 x8) &&
  (let x8 := 1; chkB_s3 x1 x2 x8) &&
  (let x8 := 2; chkB_s3 x1 x2 x8) &&
  (let x8 := 3; chkB_s3 x1 x2 x8) &&
  (let x8 := 4; chkB_s3 x1 x2 x8)

def chkB_s1 (x1 : Nat) : Bool :=
  (let x2 := 0; (!((x1 != x2)) || chkB_s2 x1 x2)) &&
  (let x2 := 1; (!((x1 != x2)) || chkB_s2 x1 x2)) &&
  (let x2 := 2; (!((x1 != x2)) || chkB_s2 x1 x2)) &&
  (let x2 := 3; (!((x1 != x2)) || chkB_s2 x1 x2)) &&
  (let x2 := 4; (!((x1 != x2)) || chkB_s2 x1 x2))

def chkB_s0  : Bool :=
  (let x1 := 0; chkB_s1 x1) &&
  (let x1 := 1; chkB_s1 x1) &&
  (let x1 := 2; chkB_s1 x1) &&
  (let x1 := 3; chkB_s1 x1) &&
  (let x1 := 4; chkB_s1 x1)


set_option maxHeartbeats 4000000 in
theorem chkB_ok : chkB_s0 = true := by decide +kernel

lemma chkB_sound (f : Fin 9 → Fin 5)
    (hc0 : f 1 ≠ f 2)
    (hc1 : f 1 ≠ f 6)
    (hc2 : f 2 ≠ f 3)
    (hc3 : f 2 ≠ f 7)
    (hc4 : f 3 ≠ f 8)
    (hc5 : f 5 ≠ f 7)
    (hc6 : f 5 ≠ f 8)
    (hc7 : f 6 ≠ f 8)
    (hq0 : f 0 = f 1 → f 6 ≤ f 0)
    (hq1 : f 0 = f 2 → f 4 ≤ f 0)
    (hq2 : f 0 = f 3 → f 4 ≤ f 0)
    (hq3 : f 0 = f 5 → f 7 ≤ f 0)
    (hq4 : f 0 = f 6 → f 1 ≤ f 0)
    (hq5 : f 0 = f 7 → f 5 ≤ f 0)
    (hq6 : f 0 = f 8 → f 4 ≤ f 0)
    (hq7 : f 1 = f 3 → f 6 ≤ f 1)
    (hq8 : f 1 = f 3 → f 8 ≤ f 1)
    (hq9 : f 1 = f 4 → f 0 ≤ f 1)
    (hq10 : f 1 = f 5 → f 6 ≤ f 1)
    (hq11 : f 1 = f 5 → f 8 ≤ f 1)
    (hq12 : f 1 = f 7 → f 2 ≤ f 1)
    (hq13 : f 1 = f 7 → f 6 ≤ f 1)
    (hq14 : f 1 = f 8 → f 5 ≤ f 1)
    (hq15 : f 1 = f 8 → f 6 ≤ f 1)
    (hq16 : f 2 = f 4 → f 3 ≤ f 2)
    (hq17 : f 2 = f 4 → f 7 ≤ f 2)
    (hq18 : f 2 = f 5 → f 7 ≤ f 2)
    (hq19 : f 2 = f 5 → f 8 ≤ f 2)
    (hq20 : f 2 = f 6 → f 1 ≤ f 2)
    (hq21 : f 2 = f 6 → f 8 ≤ f 2)
    (hq22 : f 2 = f 8 → f 3 ≤ f 2)
    (hq23 : f 2 = f 8 → f 5 ≤ f 2)
    (hq24 : f 2 = f 8 → f 7 ≤ f 2)
    (hq25 : f 3 = f 4 → f 2 ≤ f 3)
    (hq26 : f 3 = f 4 → f 8 ≤ f 3)
    (hq27 : f 3 = f 5 → f 2 ≤ f 3)
    (hq28 : f 3 = f 5 → f 7 ≤ f 3)
    (hq29 : f 3 = f 5 → f 8 ≤ f 3)
    (hq30 : f 3 = f 6 → f 1 ≤ f 3)
    (hq31 : f 3 = f 6 → f 8 ≤ f 3)
    (hq32 : f 3 = f 7 → f 2 ≤ f 3)
    (hq33 : f 3 = f 7 → f 5 ≤ f 3)
    (hq34 : f 4 = f 5 → f 0 ≤ f 4)
    (hq35 : f 4 = f 6 → f 0 ≤ f 4)
    (hq36 : f 4 = f 7 → f 0 ≤ f 4)
    (hq37 : f 4 = f 8 → f 3 ≤ f 4)
    (hq38 : f 4 = f 8 → f 6 ≤ f 4)
    (hq39 : f 5 = f 6 → f 1 ≤ f 5)
    (hq40 : f 5 = f 6 → f 8 ≤ f 5)
    (hq41 : f 6 = f 7 → f 2 ≤ f 6)
    (hq42 : f 6 = f 7 → f 5 ≤ f 6)
    (hq43 : f 7 = f 8 → f 2 ≤ f 7)
    (hq44 : f 7 = f 8 → f 5 ≤ f 7)
    (hok : chkB_s0 = true) : (f 0 = 4 ∧ f 3 = 4 ∧ f 4 = 4) ∨ (f 0 = 4 ∧ f 1 = 4 ∧ f 4 = 4) ∨ (f 0 = 4 ∧ f 4 = 4 ∧ f 5 = 4) := by
  have h0 : chkB_s1 (f 1).val = true := by
    have hval := (f 1).isLt
    have hstep : chkB_s1 (f 1).val = true := by
      unfold chkB_s0 at hok
      match hfv : (f 1).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.2
      | 4, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.2
    exact hstep
  have h1 : chkB_s2 (f 1).val (f 2).val = true := by
    have hval := (f 2).isLt
    have hstep : (!(((f 1).val != (f 2).val)) || chkB_s2 (f 1).val (f 2).val) = true := by
      unfold chkB_s1 at h0
      match hfv : (f 2).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.2
    have hguard : (((f 1).val != (f 2).val)) = true := by
      exact (conf_guard hc0)
    rw [hguard] at hstep; simpa using hstep
  have h2 : chkB_s3 (f 1).val (f 2).val (f 8).val = true := by
    have hval := (f 8).isLt
    have hstep : chkB_s3 (f 1).val (f 2).val (f 8).val = true := by
      unfold chkB_s2 at h1
      match hfv : (f 8).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.2
    exact hstep
  have h3 : chkB_s4 (f 1).val (f 2).val (f 8).val (f 5).val = true := by
    have hval := (f 5).isLt
    have hstep : (!(((f 5).val != (f 8).val) && (!((f 1).val == (f 5).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 5).val ≤ (f 1).val)) && (!((f 2).val == (f 5).val) || decide ((f 8).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 5).val ≤ (f 2).val))) || chkB_s4 (f 1).val (f 2).val (f 8).val (f 5).val) = true := by
      unfold chkB_s3 at h2
      match hfv : (f 5).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.2
    have hguard : (((f 5).val != (f 8).val) && (!((f 1).val == (f 5).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 5).val ≤ (f 1).val)) && (!((f 2).val == (f 5).val) || decide ((f 8).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 5).val ≤ (f 2).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨(conf_guard hc6), (cube_guard hq11)⟩, (cube_guard hq14)⟩, (cube_guard hq19)⟩, (cube_guard hq23)⟩
    rw [hguard] at hstep; simpa using hstep
  have h4 : chkB_s5 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val = true := by
    have hval := (f 6).isLt
    have hstep : (!(((f 1).val != (f 6).val) && ((f 6).val != (f 8).val) && (!((f 1).val == (f 5).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 6).val) || decide ((f 1).val ≤ (f 2).val)) && (!((f 2).val == (f 6).val) || decide ((f 8).val ≤ (f 2).val)) && (!((f 5).val == (f 6).val) || decide ((f 1).val ≤ (f 5).val)) && (!((f 5).val == (f 6).val) || decide ((f 8).val ≤ (f 5).val))) || chkB_s5 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val) = true := by
      unfold chkB_s4 at h3
      match hfv : (f 6).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.2
    have hguard : (((f 1).val != (f 6).val) && ((f 6).val != (f 8).val) && (!((f 1).val == (f 5).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 6).val) || decide ((f 1).val ≤ (f 2).val)) && (!((f 2).val == (f 6).val) || decide ((f 8).val ≤ (f 2).val)) && (!((f 5).val == (f 6).val) || decide ((f 1).val ≤ (f 5).val)) && (!((f 5).val == (f 6).val) || decide ((f 8).val ≤ (f 5).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨(conf_guard hc1), (conf_guard hc7)⟩, (cube_guard hq10)⟩, (cube_guard hq15)⟩, (cube_guard hq20)⟩, (cube_guard hq21)⟩, (cube_guard hq39)⟩, (cube_guard hq40)⟩
    rw [hguard] at hstep; simpa using hstep
  have h5 : chkB_s6 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val = true := by
    have hval := (f 7).isLt
    have hstep : (!(((f 2).val != (f 7).val) && ((f 5).val != (f 7).val) && (!((f 1).val == (f 7).val) || decide ((f 2).val ≤ (f 1).val)) && (!((f 1).val == (f 7).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 5).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 6).val == (f 7).val) || decide ((f 2).val ≤ (f 6).val)) && (!((f 6).val == (f 7).val) || decide ((f 5).val ≤ (f 6).val)) && (!((f 7).val == (f 8).val) || decide ((f 2).val ≤ (f 7).val)) && (!((f 7).val == (f 8).val) || decide ((f 5).val ≤ (f 7).val))) || chkB_s6 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val) = true := by
      unfold chkB_s5 at h4
      match hfv : (f 7).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.2
    have hguard : (((f 2).val != (f 7).val) && ((f 5).val != (f 7).val) && (!((f 1).val == (f 7).val) || decide ((f 2).val ≤ (f 1).val)) && (!((f 1).val == (f 7).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 5).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 6).val == (f 7).val) || decide ((f 2).val ≤ (f 6).val)) && (!((f 6).val == (f 7).val) || decide ((f 5).val ≤ (f 6).val)) && (!((f 7).val == (f 8).val) || decide ((f 2).val ≤ (f 7).val)) && (!((f 7).val == (f 8).val) || decide ((f 5).val ≤ (f 7).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨(conf_guard hc3), (conf_guard hc5)⟩, (cube_guard hq12)⟩, (cube_guard hq13)⟩, (cube_guard hq18)⟩, (cube_guard hq24)⟩, (cube_guard hq41)⟩, (cube_guard hq42)⟩, (cube_guard hq43)⟩, (cube_guard hq44)⟩
    rw [hguard] at hstep; simpa using hstep
  have h6 : chkB_s7 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val (f 3).val = true := by
    have hval := (f 3).isLt
    have hstep : (!(((f 2).val != (f 3).val) && ((f 3).val != (f 8).val) && (!((f 1).val == (f 3).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 3).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 2).val == (f 8).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 5).val) || decide ((f 7).val ≤ (f 3).val)) && (!((f 3).val == (f 5).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 1).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 5).val ≤ (f 3).val))) || chkB_s7 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val (f 3).val) = true := by
      unfold chkB_s6 at h5
      match hfv : (f 3).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.2
    have hguard : (((f 2).val != (f 3).val) && ((f 3).val != (f 8).val) && (!((f 1).val == (f 3).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 3).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 2).val == (f 8).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 5).val) || decide ((f 7).val ≤ (f 3).val)) && (!((f 3).val == (f 5).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 1).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 5).val ≤ (f 3).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(conf_guard hc2), (conf_guard hc4)⟩, (cube_guard hq7)⟩, (cube_guard hq8)⟩, (cube_guard hq22)⟩, (cube_guard hq27)⟩, (cube_guard hq28)⟩, (cube_guard hq29)⟩, (cube_guard hq30)⟩, (cube_guard hq31)⟩, (cube_guard hq32)⟩, (cube_guard hq33)⟩
    rw [hguard] at hstep; simpa using hstep
  have h7 : chkB_s8 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val (f 3).val (f 0).val = true := by
    have hval := (f 0).isLt
    have hstep : (!((!((f 0).val == (f 1).val) || decide ((f 6).val ≤ (f 0).val)) && (!((f 0).val == (f 5).val) || decide ((f 7).val ≤ (f 0).val)) && (!((f 0).val == (f 6).val) || decide ((f 1).val ≤ (f 0).val)) && (!((f 0).val == (f 7).val) || decide ((f 5).val ≤ (f 0).val))) || chkB_s8 (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val (f 3).val (f 0).val) = true := by
      unfold chkB_s7 at h6
      match hfv : (f 0).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.2
    have hguard : ((!((f 0).val == (f 1).val) || decide ((f 6).val ≤ (f 0).val)) && (!((f 0).val == (f 5).val) || decide ((f 7).val ≤ (f 0).val)) && (!((f 0).val == (f 6).val) || decide ((f 1).val ≤ (f 0).val)) && (!((f 0).val == (f 7).val) || decide ((f 5).val ≤ (f 0).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨(cube_guard hq0), (cube_guard hq3)⟩, (cube_guard hq4)⟩, (cube_guard hq5)⟩
    rw [hguard] at hstep; simpa using hstep
  have h8 : chkB_leaf (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val (f 3).val (f 0).val (f 4).val = true := by
    have hval := (f 4).isLt
    have hstep : (!((!((f 0).val == (f 2).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 3).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 1).val == (f 4).val) || decide ((f 0).val ≤ (f 1).val)) && (!((f 2).val == (f 4).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 2).val == (f 4).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 3).val == (f 4).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 4).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 4).val == (f 5).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 6).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 3).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 6).val ≤ (f 4).val))) || chkB_leaf (f 1).val (f 2).val (f 8).val (f 5).val (f 6).val (f 7).val (f 3).val (f 0).val (f 4).val) = true := by
      unfold chkB_s8 at h7
      match hfv : (f 4).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.2
    have hguard : ((!((f 0).val == (f 2).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 3).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 1).val == (f 4).val) || decide ((f 0).val ≤ (f 1).val)) && (!((f 2).val == (f 4).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 2).val == (f 4).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 3).val == (f 4).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 4).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 4).val == (f 5).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 6).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 3).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 6).val ≤ (f 4).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(cube_guard hq1), (cube_guard hq2)⟩, (cube_guard hq6)⟩, (cube_guard hq9)⟩, (cube_guard hq16)⟩, (cube_guard hq17)⟩, (cube_guard hq25)⟩, (cube_guard hq26)⟩, (cube_guard hq34)⟩, (cube_guard hq35)⟩, (cube_guard hq36)⟩, (cube_guard hq37)⟩, (cube_guard hq38)⟩
    rw [hguard] at hstep; simpa using hstep
  unfold chkB_leaf at h8
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h8
  rcases h8 with (⟨⟨a, b⟩, c⟩ | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩
  · exact Or.inl ⟨Fin.ext a, Fin.ext b, Fin.ext c⟩
  · exact Or.inr (Or.inl ⟨Fin.ext a, Fin.ext b, Fin.ext c⟩)
  · exact Or.inr (Or.inr ⟨Fin.ext a, Fin.ext b, Fin.ext c⟩)

-- 3-leaf tree factoring for any DMFormula where u, v, w each occur ≤ 1 time!
inductive Top3 | uv | uw | vw

def tripleInput {n : ℕ} (u v w : Fin n) (base : Fin n → Bool) (a b c : Bool) (i : Fin n) : Bool :=
  if i = u then a else if i = v then b else if i = w then c else base i

lemma eval_indep_of_occ_zero {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ i, occurrences i p ≠ 0 → x i = y i) : p.eval x = p.eval y := by
  induction p with
  | lit i pos =>
    have hx : x i = y i := h i (by simp [occurrences])
    simp [DMFormula.eval, hx]
  | and l r ihl ihr =>
    simp only [DMFormula.eval]
    rw [ihl (fun i hi => h i (by simp [occurrences]; omega)),
        ihr (fun i hi => h i (by simp [occurrences]; omega))]
  | or l r ihl ihr =>
    simp only [DMFormula.eval]
    rw [ihl (fun i hi => h i (by simp [occurrences]; omega)),
        ihr (fun i hi => h i (by simp [occurrences]; omega))]

def factorsTop3 {n : ℕ} (u v w : Fin n) (p : DMFormula n) (t : Top3) : Prop :=
  ∀ base : Fin n → Bool,
    match t with
    | .uv => ∃ (G H : Bool → Bool → Bool), ∀ a b c, p.eval (tripleInput u v w base a b c) = H (G a b) c
    | .uw => ∃ (G H : Bool → Bool → Bool), ∀ a b c, p.eval (tripleInput u v w base a b c) = H (G a c) b
    | .vw => ∃ (G H : Bool → Bool → Bool), ∀ a b c, p.eval (tripleInput u v w base a b c) = H (G b c) a

lemma factorsTop3_comp {n : ℕ} {u v w : Fin n} {p : DMFormula n} {t : Top3}
    (ht : factorsTop3 u v w p t) (f : (Fin n → Bool) → Bool → Bool) :
    ∀ base : Fin n → Bool,
      match t with
      | .uv => ∃ (G H : Bool → Bool → Bool), ∀ a b c, f base (p.eval (tripleInput u v w base a b c)) = H (G a b) c
      | .uw => ∃ (G H : Bool → Bool → Bool), ∀ a b c, f base (p.eval (tripleInput u v w base a b c)) = H (G a c) b
      | .vw => ∃ (G H : Bool → Bool → Bool), ∀ a b c, f base (p.eval (tripleInput u v w base a b c)) = H (G b c) a := by
  intro base
  have hb := ht base
  cases t with
  | uv => obtain ⟨G, H, h⟩ := hb; exact ⟨G, fun g c => f base (H g c), fun a b c => by simp [h]⟩
  | uw => obtain ⟨G, H, h⟩ := hb; exact ⟨G, fun g b => f base (H g b), fun a b c => by simp [h]⟩
  | vw => obtain ⟨G, H, h⟩ := hb; exact ⟨G, fun g a => f base (H g a), fun a b c => by simp [h]⟩

lemma dmFormula_factor3 {n : ℕ} (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (p : DMFormula n) (hu : occurrences u p ≤ 1) (hv : occurrences v p ≤ 1) (hw : occurrences w p ≤ 1) :
    ∃ t : Top3, factorsTop3 u v w p t := by
  have const_of_zero : ∀ (q : DMFormula n), occurrences u q = 0 → occurrences v q = 0 → occurrences w q = 0 →
      ∀ base a b c, q.eval (tripleInput u v w base a b c) = q.eval base := by
    intro q hu0 hv0 hw0 base a b c
    apply eval_indep_of_occ_zero
    intro i hi
    have hiu : i ≠ u := fun e => hi (e ▸ hu0)
    have hiv : i ≠ v := fun e => hi (e ▸ hv0)
    have hiw : i ≠ w := fun e => hi (e ▸ hw0)
    simp [tripleInput, hiu, hiv, hiw]
  have dep1 : ∀ (q : DMFormula n) (s : Fin n),
      (s = u → occurrences v q = 0 ∧ occurrences w q = 0) →
      (s = v → occurrences u q = 0 ∧ occurrences w q = 0) →
      (s = w → occurrences u q = 0 ∧ occurrences v q = 0) →
      s = u ∨ s = v ∨ s = w →
      ∀ base : Fin n → Bool, ∃ F : Bool → Bool, ∀ a b c,
        q.eval (tripleInput u v w base a b c) = F (if s = u then a else if s = v then b else c) := by
    intro q s h1 h2 h3 hs base
    rcases hs with hsu | hsv | hsw
    · subst s
      obtain ⟨hv0, hw0⟩ := h1 rfl
      refine ⟨fun a => q.eval (tripleInput u v w base a false false), fun a b c => ?_⟩
      simp only [↓reduceIte]
      apply eval_indep_of_occ_zero; intro i hi
      have hiv : i ≠ v := fun e => hi (e ▸ hv0)
      have hiw : i ≠ w := fun e => hi (e ▸ hw0)
      by_cases hiu : i = u <;> simp [tripleInput, hiu, hiv, hiw, huv, huv.symm, huw, huw.symm, hvw, hvw.symm]
    · subst s
      obtain ⟨hu0, hw0⟩ := h2 rfl
      refine ⟨fun b => q.eval (tripleInput u v w base false b false), fun a b c => ?_⟩
      simp only [huv.symm, ↓reduceIte]
      apply eval_indep_of_occ_zero; intro i hi
      have hiu : i ≠ u := fun e => hi (e ▸ hu0)
      have hiw : i ≠ w := fun e => hi (e ▸ hw0)
      by_cases hiv : i = v <;> simp [tripleInput, hiu, hiv, hiw, huv, huv.symm, huw, huw.symm, hvw, hvw.symm]
    · subst s
      obtain ⟨hu0, hv0⟩ := h3 rfl
      refine ⟨fun c => q.eval (tripleInput u v w base false false c), fun a b c => ?_⟩
      simp only [huw.symm, hvw.symm, ↓reduceIte]
      apply eval_indep_of_occ_zero; intro i hi
      have hiu : i ≠ u := fun e => hi (e ▸ hu0)
      have hiv : i ≠ v := fun e => hi (e ▸ hv0)
      by_cases hiw : i = w <;> simp [tripleInput, hiu, hiv, hiw, huv, huv.symm, huw, huw.symm, hvw, hvw.symm]
  have dep2 : ∀ (q : DMFormula n) (z : Fin n),
      occurrences z q = 0 →
      (z = w → ∀ base, ∃ G : Bool → Bool → Bool, ∀ a b c, q.eval (tripleInput u v w base a b c) = G a b) ∧
      (z = v → ∀ base, ∃ G : Bool → Bool → Bool, ∀ a b c, q.eval (tripleInput u v w base a b c) = G a c) ∧
      (z = u → ∀ base, ∃ G : Bool → Bool → Bool, ∀ a b c, q.eval (tripleInput u v w base a b c) = G b c) := by
    intro q z hz
    refine ⟨?_, ?_, ?_⟩
    · intro hzw base; subst z
      refine ⟨fun a b => q.eval (tripleInput u v w base a b false), fun a b c => ?_⟩
      apply eval_indep_of_occ_zero; intro i hi
      have hiw : i ≠ w := fun e => hi (e ▸ hz)
      by_cases hiu : i = u <;> by_cases hiv : i = v <;> simp [tripleInput, hiu, hiv, hiw, huv, huv.symm, huw, huw.symm, hvw, hvw.symm]
    · intro hzv base; subst z
      refine ⟨fun a c => q.eval (tripleInput u v w base a false c), fun a b c => ?_⟩
      apply eval_indep_of_occ_zero; intro i hi
      have hiv : i ≠ v := fun e => hi (e ▸ hz)
      by_cases hiu : i = u <;> by_cases hiw : i = w <;> simp [tripleInput, hiu, hiv, hiw, huv, huv.symm, huw, huw.symm, hvw, hvw.symm]
    · intro hzu base; subst z
      refine ⟨fun b c => q.eval (tripleInput u v w base false b c), fun a b c => ?_⟩
      apply eval_indep_of_occ_zero; intro i hi
      have hiu : i ≠ u := fun e => hi (e ▸ hz)
      by_cases hiv : i = v <;> by_cases hiw : i = w <;> simp [tripleInput, hiu, hiv, hiw, huv, huv.symm, huw, huw.symm, hvw, hvw.symm]
  have combine : ∀ (op : Bool → Bool → Bool) (l r : DMFormula n),
      occurrences u l + occurrences u r ≤ 1 →
      occurrences v l + occurrences v r ≤ 1 →
      occurrences w l + occurrences w r ≤ 1 →
      (∃ t, factorsTop3 u v w l t) → (∃ t, factorsTop3 u v w r t) →
      ∃ t : Top3, ∀ base,
        match t with
        | .uv => ∃ (G H : Bool → Bool → Bool), ∀ a b c, op (l.eval (tripleInput u v w base a b c)) (r.eval (tripleInput u v w base a b c)) = H (G a b) c
        | .uw => ∃ (G H : Bool → Bool → Bool), ∀ a b c, op (l.eval (tripleInput u v w base a b c)) (r.eval (tripleInput u v w base a b c)) = H (G a c) b
        | .vw => ∃ (G H : Bool → Bool → Bool), ∀ a b c, op (l.eval (tripleInput u v w base a b c)) (r.eval (tripleInput u v w base a b c)) = H (G b c) a := by
    intro op l r hu' hv' hw' ihl ihr
    by_cases hr0 : occurrences u r = 0 ∧ occurrences v r = 0 ∧ occurrences w r = 0
    · obtain ⟨t, ht⟩ := ihl
      refine ⟨t, ?_⟩
      have hcomp := factorsTop3_comp ht (fun base x => op x (r.eval base))
      intro base
      have hcr := const_of_zero r hr0.1 hr0.2.1 hr0.2.2 base
      cases t <;> simpa only [hcr] using hcomp base
    · by_cases hl0 : occurrences u l = 0 ∧ occurrences v l = 0 ∧ occurrences w l = 0
      · obtain ⟨t, ht⟩ := ihr
        refine ⟨t, ?_⟩
        have hcomp := factorsTop3_comp ht (fun base x => op (l.eval base) x)
        intro base
        have hcl := const_of_zero l hl0.1 hl0.2.1 hl0.2.2 base
        cases t <;> simpa only [hcl] using hcomp base
      · -- Both l and r contain ≥ 1 of u, v, w; total ≤ 3, so one has 1 and the other has ≤ 2!
        by_cases hwr : occurrences w r = 1
        · have hwl : occurrences w l = 0 := by omega
          by_cases h1 : occurrences u r = 0 ∧ occurrences v r = 0
          · refine ⟨.uv, fun base => ?_⟩
            obtain ⟨G, hG⟩ := (dep2 l w hwl).1 rfl base
            obtain ⟨F, hF⟩ := dep1 r w (fun h => (huw.symm h).elim) (fun h => (hvw.symm h).elim) (fun _ => h1) (Or.inr (Or.inr rfl)) base
            refine ⟨G, fun g c => op g (F c), fun a b c => ?_⟩
            rw [hG a b c, hF a b c]; simp [huw.symm, hvw.symm]
          · -- r has w AND one of u,v, so l has only the other of u,v!
            by_cases hur : occurrences u r = 1
            · have hul : occurrences u l = 0 := by omega
              have hvr : occurrences v r = 0 := by omega
              refine ⟨.uw, fun base => ?_⟩
              obtain ⟨G, hG⟩ := (dep2 r v hvr).2.1 rfl base
              obtain ⟨F, hF⟩ := dep1 l v (fun h => (huv.symm h).elim) (fun _ => ⟨hul, hwl⟩) (fun h => (hvw h).elim) (Or.inr (Or.inl rfl)) base
              refine ⟨G, fun g b => op (F b) g, fun a b c => ?_⟩
              rw [hG a b c, hF a b c]; simp [huv.symm]
            · have hvr : occurrences v r = 1 := by omega
              have hvl : occurrences v l = 0 := by omega
              have hur0 : occurrences u r = 0 := by omega
              refine ⟨.vw, fun base => ?_⟩
              obtain ⟨G, hG⟩ := (dep2 r u hur0).2.2 rfl base
              obtain ⟨F, hF⟩ := dep1 l u (fun _ => ⟨hvl, hwl⟩) (fun h => (huv h).elim) (fun h => (huw h).elim) (Or.inl rfl) base
              refine ⟨G, fun g a => op (F a) g, fun a b c => ?_⟩
              rw [hG a b c, hF a b c]; simp
        · have hwr0 : occurrences w r = 0 := by omega
          by_cases h1 : occurrences u l = 0 ∧ occurrences v l = 0
          · refine ⟨.uv, fun base => ?_⟩
            obtain ⟨G, hG⟩ := (dep2 r w hwr0).1 rfl base
            obtain ⟨F, hF⟩ := dep1 l w (fun h => (huw.symm h).elim) (fun h => (hvw.symm h).elim) (fun _ => h1) (Or.inr (Or.inr rfl)) base
            refine ⟨G, fun g c => op (F c) g, fun a b c => ?_⟩
            rw [hG a b c, hF a b c]; simp [huw.symm, hvw.symm]
          · by_cases hul : occurrences u l = 1
            · have hur : occurrences u r = 0 := by omega
              have hvl : occurrences v l = 0 := by omega
              refine ⟨.uw, fun base => ?_⟩
              obtain ⟨G, hG⟩ := (dep2 l v hvl).2.1 rfl base
              obtain ⟨F, hF⟩ := dep1 r v (fun h => (huv.symm h).elim) (fun _ => ⟨hur, hwr0⟩) (fun h => (hvw h).elim) (Or.inr (Or.inl rfl)) base
              refine ⟨G, fun g b => op g (F b), fun a b c => ?_⟩
              rw [hG a b c, hF a b c]; simp [huv.symm]
            · have hvl : occurrences v l = 1 := by omega
              have hvr : occurrences v r = 0 := by omega
              have hul0 : occurrences u l = 0 := by omega
              refine ⟨.vw, fun base => ?_⟩
              obtain ⟨G, hG⟩ := (dep2 l u hul0).2.2 rfl base
              obtain ⟨F, hF⟩ := dep1 r u (fun _ => ⟨hvr, hwr0⟩) (fun h => (huv h).elim) (fun h => (huw h).elim) (Or.inl rfl) base
              refine ⟨G, fun g a => op g (F a), fun a b c => ?_⟩
              rw [hG a b c, hF a b c]; simp
  induction p with
  | lit k pos =>
    refine ⟨.uv, fun base => ?_⟩
    by_cases hkw : k = w
    · subst k
      refine ⟨fun _ _ => false, fun _ c => if pos then c else !c, fun a b c => ?_⟩
      simp [DMFormula.eval, tripleInput, huw.symm, hvw.symm]
    · refine ⟨fun a b => if pos then tripleInput u v w base a b false k else !(tripleInput u v w base a b false k),
        fun g _ => g, fun a b c => ?_⟩
      by_cases hku : k = u <;> by_cases hkv : k = v <;>
        simp [DMFormula.eval, tripleInput, hku, hkv, hkw]
  | and l r ihl ihr =>
    simp only [occurrences] at hu hv hw
    obtain ⟨t, ht⟩ := combine (· && ·) l r hu hv hw (ihl (by omega) (by omega) (by omega)) (ihr (by omega) (by omega) (by omega))
    exact ⟨t, fun base => by cases t <;> exact ht base⟩
  | or l r ihl ihr =>
    simp only [occurrences] at hu hv hw
    obtain ⟨t, ht⟩ := combine (· || ·) l r hu hv hw (ihl (by omega) (by omega) (by omega)) (ihr (by omega) (by omega) (by omega))
    exact ⟨t, fun base => by cases t <;> exact ht base⟩

def hasFactor3 (u v w : Fin 10) (t : Top3) (baseMask : ℕ) : Bool :=
  (List.range 16).any fun gbits =>
    (List.range 16).any fun hbits =>
      [false, true].all fun a =>
        [false, true].all fun b =>
          [false, true].all fun c =>
            let x := tripleInput u v w (row10 baseMask) a b c
            !(x 9 == (x 0 || x 4)) ||
            let (p, q, r) := match t with
              | .uv => (a, b, c)
              | .uw => (a, c, b)
              | .vw => (b, c, a)
            let g := gbits.testBit ((if p then 2 else 0) + (if q then 1 else 0))
            let h := hbits.testBit ((if g then 2 else 0) + (if r then 1 else 0))
            h == target10 x

lemma noFactor3_check :
    hasFactor3 0 3 4 .uv 516 = false ∧ hasFactor3 0 3 4 .uw 512 = false ∧ hasFactor3 0 3 4 .vw 512 = false ∧
    hasFactor3 0 1 4 .uv 512 = false ∧ hasFactor3 0 1 4 .uw 512 = false ∧ hasFactor3 0 1 4 .vw 516 = false ∧
    hasFactor3 0 4 5 .uv 512 = false ∧ hasFactor3 0 4 5 .uw 512 = false ∧ hasFactor3 0 4 5 .vw 640 = false := by
  decide +kernel

def encode2 (f : Bool → Bool → Bool) : ℕ :=
  (if f false false then 1 else 0) + (if f false true then 2 else 0) +
  (if f true false then 4 else 0) + (if f true true then 8 else 0)

lemma encode2_lt (f : Bool → Bool → Bool) : encode2 f < 16 := by
  unfold encode2; cases f false false <;> cases f false true <;> cases f true false <;> cases f true true <;> decide

lemma encode2_testBit (f : Bool → Bool → Bool) (a b : Bool) :
    (encode2 f).testBit ((if a then 2 else 0) + (if b then 1 else 0)) = f a b := by
  unfold encode2
  cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;>
    cases a <;> cases b <;> simp [h00, h01, h10, h11] <;> decide

lemma factor3_implies_hasFactor3 {u v w : Fin 10} {p : DMFormula 10} {t : Top3}
    (hfac : factorsTop3 u v w p t)
    (hcomp : ∀ x : Fin 10 → Bool, valid10 x → p.eval x = target10 x)
    (baseMask : ℕ) : hasFactor3 u v w t baseMask = true := by
  unfold hasFactor3
  rw [List.any_eq_true]
  have hb := hfac (row10 baseMask)
  cases t with
  | uv =>
    obtain ⟨G, H, hGH⟩ := hb
    refine ⟨encode2 G, List.mem_range.mpr (encode2_lt G), ?_⟩
    rw [List.any_eq_true]
    refine ⟨encode2 H, List.mem_range.mpr (encode2_lt H), ?_⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    have check : ∀ a b c : Bool,
        let x := tripleInput u v w (row10 baseMask) a b c
        (!(x 9 == (x 0 || x 4)) ||
          ((encode2 H).testBit ((if (encode2 G).testBit ((if a then 2 else 0) + (if b then 1 else 0)) then 2 else 0) +
            (if c then 1 else 0)) == target10 x)) = true := by
      intro a b c
      dsimp only
      by_cases hv : valid10 (tripleInput u v w (row10 baseMask) a b c)
      · rw [encode2_testBit, encode2_testBit, ← hGH a b c, hcomp _ hv]; simp
      · unfold valid10 at hv; simp [hv]
    exact ⟨⟨⟨check false false false, check false false true⟩, ⟨check false true false, check false true true⟩⟩,
           ⟨⟨check true false false, check true false true⟩, ⟨check true true false, check true true true⟩⟩⟩
  | uw =>
    obtain ⟨G, H, hGH⟩ := hb
    refine ⟨encode2 G, List.mem_range.mpr (encode2_lt G), ?_⟩
    rw [List.any_eq_true]
    refine ⟨encode2 H, List.mem_range.mpr (encode2_lt H), ?_⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    have check : ∀ a b c : Bool,
        let x := tripleInput u v w (row10 baseMask) a b c
        (!(x 9 == (x 0 || x 4)) ||
          ((encode2 H).testBit ((if (encode2 G).testBit ((if a then 2 else 0) + (if c then 1 else 0)) then 2 else 0) +
            (if b then 1 else 0)) == target10 x)) = true := by
      intro a b c
      dsimp only
      by_cases hv : valid10 (tripleInput u v w (row10 baseMask) a b c)
      · rw [encode2_testBit, encode2_testBit, ← hGH a b c, hcomp _ hv]; simp
      · unfold valid10 at hv; simp [hv]
    exact ⟨⟨⟨check false false false, check false false true⟩, ⟨check false true false, check false true true⟩⟩,
           ⟨⟨check true false false, check true false true⟩, ⟨check true true false, check true true true⟩⟩⟩
  | vw =>
    obtain ⟨G, H, hGH⟩ := hb
    refine ⟨encode2 G, List.mem_range.mpr (encode2_lt G), ?_⟩
    rw [List.any_eq_true]
    refine ⟨encode2 H, List.mem_range.mpr (encode2_lt H), ?_⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    have check : ∀ a b c : Bool,
        let x := tripleInput u v w (row10 baseMask) a b c
        (!(x 9 == (x 0 || x 4)) ||
          ((encode2 H).testBit ((if (encode2 G).testBit ((if b then 2 else 0) + (if c then 1 else 0)) then 2 else 0) +
            (if a then 1 else 0)) == target10 x)) = true := by
      intro a b c
      dsimp only
      by_cases hv : valid10 (tripleInput u v w (row10 baseMask) a b c)
      · rw [encode2_testBit, encode2_testBit, ← hGH a b c, hcomp _ hv]; simp
      · unfold valid10 at hv; simp [hv]
    exact ⟨⟨⟨check false false false, check false false true⟩, ⟨check false true false, check false true true⟩⟩,
           ⟨⟨check true false false, check true false true⟩, ⟨check true true false, check true true true⟩⟩⟩

lemma dep_of_pair {n : ℕ} {H : (Fin n → Bool) → Bool} {i : Fin n}
    (p q : Fin n → Bool) (ha : ∀ j, j ≠ i → p j = q j) (hf : H p ≠ H q) : Dep H i := by
  have ne : p i ≠ q i := fun hp => hf (congrArg H (funext fun j => if h : j = i then h ▸ hp else ha j h))
  have hi : (!p i) = q i := by cases hp : p i <;> cases hq : q i <;> simp_all
  have up : Function.update p i (!p i) = q := funext fun j => by
    by_cases h : j = i
    · simpa only [h, Function.update_self] using hi
    · simpa only [Function.update_of_ne h] using ha j h
  exact ⟨p, by simpa only [up] using hf.symm⟩

theorem caseB_impossible (D : Circuit) (fan : FanInTwo D) (budget : nonNotCount D.gates ≤ 13)
    (agree : ∀ x : Fin 10 → Bool, valid10 x → circuitFun 10 D x = target10 x)
    (hdep9 : Dep (circuitFun 10 D) 9) : False := by
  classical
  have dep : ∀ i : Fin 10, Dep (circuitFun 10 D) i := by
    intro i
    by_cases hlt : i.val < 9
    · let v : Fin 9 := ⟨i.val, hlt⟩
      have hi : i = v.castSucc := Fin.ext rfl
      obtain ⟨vp, vq, hsame, hne⟩ := checkedDepB v
      rw [hi]
      exact dep_of_pair (row10 (depBefore v)) (row10 (depAfter v)) hsame
        (by rw [agree _ vp, agree _ vq]; exact hne)
    · have h9 : i = 9 := Fin.ext (by have := i.isLt; omega)
      rw [h9]; exact hdep9
  have still : ∀ (i : Fin 10) (b : Bool), ∃ x y : Fin 10 → Bool,
      circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b) := by
    intro i b
    obtain ⟨vp, vq, hpi, hqi, hne⟩ := checkedCofB i b
    let p := row10 (if b then cofNo1 i else cofNo0 i)
    let q := row10 (if b then cofYes1 i else cofYes0 i)
    refine ⟨p, q, ?_⟩
    have ep : Function.update p i b = p := hpi ▸ Function.update_eq_self _ _
    have eq : Function.update q i b = q := hqi ▸ Function.update_eq_self _ _
    rw [ep, eq, agree _ vp, agree _ vq]
    exact hne
  have nc := dep_nc (dep 0)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have valid : o < 10 + gs.length := by
    by_contra! h
    obtain ⟨x, y, different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10 + gs.length) := ⟨o, valid⟩
  have live := least_read_edge_live least nc dep still valid
  have distinct := predecessors_nodup least nc
  have branches := forksOfBudget (n := 10) (K := 4) least.hcl out live (by omega)
  obtain ⟨label, locations, isLast, codes⟩ := normalizedCutsK (n := 10) (K := 4) least.hcl out live branches
  have computes (x : Fin 10 → Bool) (hx : valid10 x) :
      vl gs x out.val = target10 x := (least.hev x).trans (agree x hx)
  have cutB : ∀ t : Fin 5, CutB label t := fun t => by
    obtain ⟨c, low, high⟩ := codes t
    refine ⟨c, low, fun x y vx vy rest same => ?_⟩
    exact (computes x vx).symm.trans ((high x y rest same).trans (computes y vy))
  have hcf (i j : Fin 9) (hm : (i.castSucc, j.castSucc) ∈ pairsB) : label i.castSucc ≠ label j.castSucc := fun same =>
    boundaryConflictB least.hcl out live distinct computes (i.castSucc, j.castSucc) hm ((locations _ _).mp same)
  have hcb := checkedCubesB
  have hbound (i j k : Fin 9) (a b c : ℕ) (hw : cubeB i.castSucc j.castSucc k.castSucc a b c) :
      label i.castSucc = label j.castSucc → label k.castSucc ≤ label i.castSucc :=
    cubeBoundB label cutB i.castSucc j.castSucc k.castSucc a b c hw
  have htriple := chkB_sound (fun v : Fin 9 => label v.castSucc)
    (hcf 1 2 (by decide))
    (hcf 1 6 (by decide))
    (hcf 2 3 (by decide))
    (hcf 2 7 (by decide))
    (hcf 3 8 (by decide))
    (hcf 5 7 (by decide))
    (hcf 5 8 (by decide))
    (hcf 6 8 (by decide))
    (hbound 0 1 6 530 529 528 (hcb (0, 1, 6, 530, 529, 528) (by decide)))
    (hbound 0 2 4 641 645 640 (hcb (0, 2, 4, 641, 645, 640) (by decide)))
    (hbound 0 3 4 517 525 516 (hcb (0, 3, 4, 517, 525, 516) (by decide)))
    (hbound 0 5 7 560 529 528 (hcb (0, 5, 7, 560, 529, 528) (by decide)))
    (hbound 0 6 1 592 529 528 (hcb (0, 6, 1, 592, 529, 528) (by decide)))
    (hbound 0 7 5 656 529 528 (hcb (0, 7, 5, 656, 529, 528) (by decide)))
    (hbound 0 8 4 577 833 576 (hcb (0, 8, 4, 577, 833, 576) (by decide)))
    (hbound 1 3 6 536 530 528 (hcb (1, 3, 6, 536, 530, 528) (by decide)))
    (hbound 1 3 8 521 515 513 (hcb (1, 3, 8, 521, 515, 513) (by decide)))
    (hbound 1 4 0 532 534 516 (hcb (1, 4, 0, 532, 534, 516) (by decide)))
    (hbound 1 5 6 160 130 128 (hcb (1, 5, 6, 160, 130, 128) (by decide)))
    (hbound 1 5 8 36 6 4 (hcb (1, 5, 8, 36, 6, 4) (by decide)))
    (hbound 1 7 2 160 34 32 (hcb (1, 7, 2, 160, 34, 32) (by decide)))
    (hbound 1 7 6 160 34 32 (hcb (1, 7, 6, 160, 34, 32) (by decide)))
    (hbound 1 8 5 260 6 4 (hcb (1, 8, 5, 260, 6, 4) (by decide)))
    (hbound 1 8 6 260 6 4 (hcb (1, 8, 6, 260, 6, 4) (by decide)))
    (hbound 2 4 3 529 517 513 (hcb (2, 4, 3, 529, 517, 513) (by decide)))
    (hbound 2 4 7 529 517 513 (hcb (2, 4, 7, 529, 517, 513) (by decide)))
    (hbound 2 5 7 34 6 2 (hcb (2, 5, 7, 34, 6, 2) (by decide)))
    (hbound 2 5 8 34 6 2 (hcb (2, 5, 8, 34, 6, 2) (by decide)))
    (hbound 2 6 1 72 12 8 (hcb (2, 6, 1, 72, 12, 8) (by decide)))
    (hbound 2 6 8 192 132 128 (hcb (2, 6, 8, 192, 132, 128) (by decide)))
    (hbound 2 8 3 258 6 2 (hcb (2, 8, 3, 258, 6, 2) (by decide)))
    (hbound 2 8 5 258 6 2 (hcb (2, 8, 5, 258, 6, 2) (by decide)))
    (hbound 2 8 7 320 68 64 (hcb (2, 8, 7, 320, 68, 64) (by decide)))
    (hbound 3 4 2 529 521 513 (hcb (3, 4, 2, 529, 521, 513) (by decide)))
    (hbound 3 4 8 529 521 513 (hcb (3, 4, 8, 529, 521, 513) (by decide)))
    (hbound 3 5 2 545 521 513 (hcb (3, 5, 2, 545, 521, 513) (by decide)))
    (hbound 3 5 7 560 536 528 (hcb (3, 5, 7, 560, 536, 528) (by decide)))
    (hbound 3 5 8 36 12 4 (hcb (3, 5, 8, 36, 12, 4) (by decide)))
    (hbound 3 6 1 592 536 528 (hcb (3, 6, 1, 592, 536, 528) (by decide)))
    (hbound 3 6 8 66 10 2 (hcb (3, 6, 8, 66, 10, 2) (by decide)))
    (hbound 3 7 2 160 40 32 (hcb (3, 7, 2, 160, 40, 32) (by decide)))
    (hbound 3 7 5 656 536 528 (hcb (3, 7, 5, 656, 536, 528) (by decide)))
    (hbound 4 5 0 656 688 640 (hcb (4, 5, 0, 656, 688, 640) (by decide)))
    (hbound 4 6 0 784 848 768 (hcb (4, 6, 0, 784, 848, 768) (by decide)))
    (hbound 4 7 0 532 660 516 (hcb (4, 7, 0, 532, 660, 516) (by decide)))
    (hbound 4 8 3 769 529 513 (hcb (4, 8, 3, 769, 529, 513) (by decide)))
    (hbound 4 8 6 769 529 513 (hcb (4, 8, 6, 769, 529, 513) (by decide)))
    (hbound 5 6 1 192 160 128 (hcb (5, 6, 1, 192, 160, 128) (by decide)))
    (hbound 5 6 8 66 34 2 (hcb (5, 6, 8, 66, 34, 2) (by decide)))
    (hbound 6 7 2 384 320 256 (hcb (6, 7, 2, 384, 320, 256) (by decide)))
    (hbound 6 7 5 130 66 2 (hcb (6, 7, 5, 130, 66, 2) (by decide)))
    (hbound 7 8 2 320 192 64 (hcb (7, 8, 2, 320, 192, 64) (by decide)))
    (hbound 7 8 5 260 132 4 (hcb (7, 8, 5, 260, 132, 4) (by decide)))
    chkB_ok
  have killTriple (u v w : Fin 10) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (m_uv m_uw m_vw : ℕ)
      (hnuv : hasFactor3 u v w .uv m_uv = false)
      (hnuw : hasFactor3 u v w .uw m_uw = false)
      (hnvw : hasFactor3 u v w .vw m_vw = false)
      (hu : label u = Fin.last 4) (hv : label v = Fin.last 4) (hw : label w = Fin.last 4) : False := by
    have b_u : firstInputBoundary least.hcl out live u = out := (isLast u).mp hu
    have b_v : firstInputBoundary least.hcl out live v = out := (isLast v).mp hv
    have b_w : firstInputBoundary least.hcl out live w = out := (isLast w).mp hw
    have ou := firstInputBoundary_occurrences_le_one least.hcl out live distinct u u
    have ov := firstInputBoundary_occurrences_le_one least.hcl out live distinct u v
    have ow := firstInputBoundary_occurrences_le_one least.hcl out live distinct u w
    rw [b_u] at ou; rw [b_v] at ov; rw [b_w] at ow
    obtain ⟨t, ht⟩ := dmFormula_factor3 u v w huv huw hvw (wireFormula u gs out.val) ou ov ow
    have hcomp : ∀ x : Fin 10 → Bool, valid10 x → (wireFormula u gs out.val).eval x = target10 x := fun x hx =>
      (wireFormula_eval u least.hcl x out.val out.isLt).trans (computes x hx)
    cases t with
    | uv => exact Bool.noConfusion ((factor3_implies_hasFactor3 ht hcomp m_uv).symm.trans hnuv)
    | uw => exact Bool.noConfusion ((factor3_implies_hasFactor3 ht hcomp m_uw).symm.trans hnuw)
    | vw => exact Bool.noConfusion ((factor3_implies_hasFactor3 ht hcomp m_vw).symm.trans hnvw)
  have hnf := noFactor3_check
  rcases htriple with ⟨h0, h3, h4⟩ | ⟨h0, h1, h4⟩ | ⟨h0, h4, h5⟩
  · exact killTriple 0 3 4 (by decide) (by decide) (by decide) 516 512 512 hnf.1 hnf.2.1 hnf.2.2.1 h0 h3 h4
  · exact killTriple 0 1 4 (by decide) (by decide) (by decide) 512 512 516 hnf.2.2.2.1 hnf.2.2.2.2.1 hnf.2.2.2.2.2.1 h0 h1 h4
  · exact killTriple 0 4 5 (by decide) (by decide) (by decide) 512 512 640 hnf.2.2.2.2.2.2.1 hnf.2.2.2.2.2.2.2.1 hnf.2.2.2.2.2.2.2.2 h0 h4 h5

end CaseB2940


namespace XTree2940



-- Y-assignment encoded as y : Fin 32 (bits 0..4 = y1, y2, y4, y5, y8)
-- X-assignment as x : Fin 4 → Bool (0 -> v0, 1 -> v3, 2 -> v6, 3 -> v7)

def yBit (y : Fin 32) (j : Nat) : Bool := y.val.testBit j

def isIndepY (y : Fin 32) : Bool :=
  !((yBit y 0 && yBit y 1) || (yBit y 3 && yBit y 4))

def AvY (v : Fin 4) (y : Fin 32) : Bool :=
  match v with
  | ⟨0, _⟩ => yBit y 0 || yBit y 2 || yBit y 3
  | ⟨1, _⟩ => yBit y 1 || yBit y 2 || yBit y 4
  | ⟨2, _⟩ => yBit y 0 || yBit y 4
  | ⟨3, _⟩ => yBit y 1 || yBit y 3

def targetXY (x : Fin 4 → Bool) (y : Fin 32) : Bool :=
  !isIndepY y ||
  (x 0 && AvY 0 y) || (x 1 && AvY 1 y) || (x 2 && AvY 2 y) || (x 3 && AvY 3 y)

-- Witness y values in Fin 32:
-- For each pair (u, v) in Fin 4 (u ≠ v), there exists y with isIndepY y = true, AvY u y = true, AvY v y = true!
-- And there exists y with isIndepY y = true, AvY u y = false, AvY v y = true!
def yBoth (u v : Fin 4) : Fin 32 :=
  match u.val, v.val with
  | 0, 1 | 1, 0 => ⟨4, by decide⟩   -- y4=1
  | 0, 2 | 2, 0 => ⟨1, by decide⟩   -- y1=1
  | 0, 3 | 3, 0 => ⟨8, by decide⟩   -- y5=1
  | 1, 2 | 2, 1 => ⟨16, by decide⟩  -- y8=1
  | 1, 3 | 3, 1 => ⟨2, by decide⟩   -- y2=1
  | _, _        => ⟨9, by decide⟩   -- y1=1, y5=1 (indep! A6=1, A7=1)

lemma yBoth_spec : ∀ u v : Fin 4, u ≠ v →
    isIndepY (yBoth u v) = true ∧ AvY u (yBoth u v) = true ∧ AvY v (yBoth u v) = true := by
  decide

def yOnlyNot (u v : Fin 4) : Fin 32 :=
  -- isIndepY = true, AvY u = false, AvY v = true
  match u.val, v.val with
  | 0, 1 => ⟨2, by decide⟩   -- y2=1: A0=0, A3=1
  | 0, 2 => ⟨16, by decide⟩  -- y8=1: A0=0, A6=1
  | 0, 3 => ⟨2, by decide⟩   -- y2=1: A0=0, A7=1
  | 1, 0 => ⟨1, by decide⟩   -- y1=1: A3=0, A0=1
  | 1, 2 => ⟨1, by decide⟩   -- y1=1: A3=0, A6=1
  | 1, 3 => ⟨8, by decide⟩   -- y5=1: A3=0, A7=1
  | 2, 0 => ⟨4, by decide⟩   -- y4=1: A6=0, A0=1
  | 2, 1 => ⟨4, by decide⟩   -- y4=1: A6=0, A3=1
  | 2, 3 => ⟨2, by decide⟩   -- y2=1: A6=0, A7=1
  | 3, 0 => ⟨1, by decide⟩   -- y1=1: A7=0, A0=1
  | 3, 1 => ⟨4, by decide⟩   -- y4=1: A7=0, A3=1
  | _, _ => ⟨1, by decide⟩   -- y1=1: A7=0, A6=1

lemma yOnlyNot_spec : ∀ u v : Fin 4, u ≠ v →
    isIndepY (yOnlyNot u v) = true ∧ AvY u (yOnlyNot u v) = false ∧ AvY v (yOnlyNot u v) = true := by
  decide

-- Normalized De Morgan XTree (every node stores the Nat mask of its pure-y side wire, bit y = wire value at y!)
inductive XTree where
  | leaf (v : Fin 4) (neg : Bool)
  | andY (t : XTree) (mask : Nat)
  | orY  (t : XTree) (mask : Nat)
  | andX (l r : XTree)
  | orX  (l r : XTree)

namespace XTree

def eval (x : Fin 4 → Bool) (y : Fin 32) : XTree → Bool
  | leaf v neg => x v ^^ neg
  | andY t m   => eval x y t && m.testBit y.val
  | orY t m    => eval x y t || m.testBit y.val
  | andX l r   => eval x y l && eval x y r
  | orX l r    => eval x y l || eval x y r

def leaves : XTree → List (Fin 4)
  | leaf v _ => [v]
  | andY t _ => leaves t
  | orY t _  => leaves t
  | andX l r => leaves l ++ leaves r
  | orX l r  => leaves l ++ leaves r

def orXCount : XTree → Nat
  | leaf _ _ => 0
  | andY t _ => orXCount t
  | orY t _  => orXCount t
  | andX l r => orXCount l + orXCount r
  | orX l r  => 1 + orXCount l + orXCount r

def andYCount : XTree → Nat
  | leaf _ _ => 0
  | andY t _ => 1 + andYCount t
  | orY t _  => andYCount t
  | andX l r => andYCount l + andYCount r
  | orX l r  => andYCount l + andYCount r

def orYCount : XTree → Nat
  | leaf _ _ => 0
  | andY t _ => orYCount t
  | orY t _  => 1 + orYCount t
  | andX l r => orYCount l + orYCount r
  | orX l r  => orYCount l + orYCount r

def gateCount : XTree → Nat
  | leaf _ _ => 0
  | andY t _ => 1 + gateCount t
  | orY t _  => 1 + gateCount t
  | andX l r => 1 + gateCount l + gateCount r
  | orX l r  => 1 + gateCount l + gateCount r

def noAndX : XTree → Prop
  | leaf _ _ => True
  | andY t _ => noAndX t
  | orY t _  => noAndX t
  | andX _ _ => False
  | orX l r  => noAndX l ∧ noAndX r

def allPos : XTree → Prop
  | leaf _ neg => neg = false
  | andY t _   => allPos t
  | orY t _    => allPos t
  | andX l r   => allPos l ∧ allPos r
  | orX l r    => allPos l ∧ allPos r

lemma gateCount_of_noAndX {t : XTree} (h : noAndX t) :
    t.gateCount = t.orXCount + t.andYCount + t.orYCount := by
  induction t with
  | leaf _ _ => rfl
  | andY t _ ih => simp [gateCount, orXCount, andYCount, orYCount, ih h]; omega
  | orY t _ ih => simp [gateCount, orXCount, andYCount, orYCount, ih h]; omega
  | andX _ _ => exact h.elim
  | orX l r ihl ihr =>
    simp [gateCount, orXCount, andYCount, orYCount, ihl h.1, ihr h.2]; omega

lemma orXCount_eq_leaves {t : XTree} (h : noAndX t) :
    t.orXCount + 1 = t.leaves.length := by
  induction t with
  | leaf _ _ => rfl
  | andY t _ ih => exact ih h
  | orY t _ ih => exact ih h
  | andX _ _ => exact h.elim
  | orX l r ihl ihr =>
    simp [orXCount, leaves, List.length_append]
    have := ihl h.1; have := ihr h.2; omega

lemma eval_indep {t : XTree} {x1 x2 : Fin 4 → Bool} {y : Fin 32}
    (h : ∀ v ∈ t.leaves, x1 v = x2 v) : t.eval x1 y = t.eval x2 y := by
  induction t with
  | leaf v neg => simp [eval, h v (by simp [leaves])]
  | andY t m ih => simp [eval, ih h]
  | orY t m ih => simp [eval, ih h]
  | andX l r ihl ihr =>
    simp [eval, ihl (fun v hv => h v (by simp [leaves, hv])),
                ihr (fun v hv => h v (by simp [leaves, hv]))]
  | orX l r ihl ihr =>
    simp [eval, ihl (fun v hv => h v (by simp [leaves, hv])),
                ihr (fun v hv => h v (by simp [leaves, hv]))]

-- Monotonicity of a tree in a leaf v that occurs at most once!
lemma eval_mono_absent {t : XTree} {x : Fin 4 → Bool} {y : Fin 32} {v : Fin 4}
    (hv : v ∉ t.leaves) (b : Bool) :
    t.eval (Function.update x v b) y = t.eval x y :=
  eval_indep fun u hu => Function.update_of_ne (fun h => by subst h; exact hv hu) _ _

lemma leaves_ne_nil (t : XTree) : t.leaves ≠ [] := by
  induction t with
  | leaf _ _ => simp [leaves]
  | andY _ _ ih => exact ih
  | orY _ _ ih => exact ih
  | andX _ _ ihl _ => simp [leaves, ihl]
  | orX _ _ ihl _ => simp [leaves, ihl]

-- Even simpler: prove directly by induction on t that if t.leaves.Nodup and for EVERY v ∈ t.leaves,
-- t is NOT antitone in v? Better: define `hasNeg v t : Prop` and prove `hasNeg v t → ∀ x y, eval (update x v true) y = true → eval (update x v false) y = true`!
def hasNeg (v : Fin 4) : XTree → Prop
  | leaf u neg => u = v ∧ neg = true
  | andY t _   => hasNeg v t
  | orY t _    => hasNeg v t
  | andX l r   => hasNeg v l ∨ hasNeg v r
  | orX l r    => hasNeg v l ∨ hasNeg v r

lemma hasNeg_mem {v : Fin 4} {t : XTree} (h : hasNeg v t) : v ∈ t.leaves := by
  induction t with
  | leaf u neg => obtain ⟨rfl, _⟩ := h; simp [leaves]
  | andY t _ ih => exact ih h
  | orY t _ ih => exact ih h
  | andX l r ihl ihr =>
    simp only [leaves, List.mem_append]
    rcases h with h | h; exact Or.inl (ihl h); exact Or.inr (ihr h)
  | orX l r ihl ihr =>
    simp only [leaves, List.mem_append]
    rcases h with h | h; exact Or.inl (ihl h); exact Or.inr (ihr h)

lemma eval_antitone_of_hasNeg {v : Fin 4} {t : XTree} (hnd : t.leaves.Nodup) (hn : hasNeg v t)
    (x : Fin 4 → Bool) (y : Fin 32) :
    t.eval (Function.update x v true) y = true → t.eval (Function.update x v false) y = true := by
  induction t with
  | leaf u neg =>
    obtain ⟨rfl, rfl⟩ := hn
    simp [eval]
  | andY t m ih =>
    simp only [eval, Bool.and_eq_true]
    rintro ⟨ht, hm⟩; exact ⟨ih hnd hn ht, hm⟩
  | orY t m ih =>
    simp only [eval, Bool.or_eq_true]
    rintro (ht | hm); exact Or.inl (ih hnd hn ht); exact Or.inr hm
  | andX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    simp only [eval, Bool.and_eq_true]
    rcases hn with hl | hr
    · have hnr : v ∉ r.leaves := fun hr' => hdisj v (hasNeg_mem hl) v hr' rfl
      rintro ⟨h1, h2⟩
      refine ⟨ihl hndl hl h1, ?_⟩
      rw [eval_mono_absent hnr true] at h2
      rw [eval_mono_absent hnr false]; exact h2
    · have hnl : v ∉ l.leaves := fun hl' => hdisj v hl' v (hasNeg_mem hr) rfl
      rintro ⟨h1, h2⟩
      refine ⟨?_, ihr hndr hr h2⟩
      rw [eval_mono_absent hnl true] at h1
      rw [eval_mono_absent hnl false]; exact h1
  | orX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    simp only [eval, Bool.or_eq_true]
    rcases hn with hl | hr
    · have hnr : v ∉ r.leaves := fun hr' => hdisj v (hasNeg_mem hl) v hr' rfl
      rintro (h1 | h2)
      · exact Or.inl (ihl hndl hl h1)
      · rw [eval_mono_absent hnr true] at h2
        rw [eval_mono_absent hnr false]; exact Or.inr h2
    · have hnl : v ∉ l.leaves := fun hl' => hdisj v hl' v (hasNeg_mem hr) rfl
      rintro (h1 | h2)
      · rw [eval_mono_absent hnl true] at h1
        rw [eval_mono_absent hnl false]; exact Or.inl h1
      · exact Or.inr (ihr hndr hr h2)

lemma allPos_of_not_hasNeg {t : XTree} (h : ∀ v, ¬ hasNeg v t) : allPos t := by
  induction t with
  | leaf u neg =>
    cases neg
    · rfl
    · exact (h u ⟨rfl, rfl⟩).elim
  | andY t _ ih => exact ih h
  | orY t _ ih => exact ih h
  | andX l r ihl ihr => exact ⟨ihl fun v hv => h v (Or.inl hv), ihr fun v hv => h v (Or.inr hv)⟩
  | orX l r ihl ihr => exact ⟨ihl fun v hv => h v (Or.inl hv), ihr fun v hv => h v (Or.inr hv)⟩

lemma eval_mono_allPos {t : XTree} (hp : allPos t) {x1 x2 : Fin 4 → Bool} {y : Fin 32}
    (hle : ∀ v, x1 v = true → x2 v = true) :
    t.eval x1 y = true → t.eval x2 y = true := by
  induction t with
  | leaf u neg =>
    subst hp; simp only [eval, Bool.xor_false]; exact hle u
  | andY t m ih =>
    simp only [eval, Bool.and_eq_true]; rintro ⟨h1, h2⟩; exact ⟨ih hp h1, h2⟩
  | orY t m ih =>
    simp only [eval, Bool.or_eq_true]; rintro (h1 | h2); exact Or.inl (ih hp h1); exact Or.inr h2
  | andX l r ihl ihr =>
    simp only [eval, Bool.and_eq_true]; rintro ⟨h1, h2⟩; exact ⟨ihl hp.1 h1, ihr hp.2 h2⟩
  | orX l r ihl ihr =>
    simp only [eval, Bool.or_eq_true]; rintro (h1 | h2); exact Or.inl (ihl hp.1 h1); exact Or.inr (ihr hp.2 h2)

-- Key lemma: if allPos t and t.leaves.Nodup and t has an andX node,
-- then for SOME distinct u, v ∈ t.leaves, at EVERY y and EVERY x with x u = false ∧ x v = false:
--   eval (update x u true) y = true ∧ eval (update x v true) y = true → eval x y = true!
-- (Because in a monotone tree, at an andX(l, r) node with u ∈ l, v ∈ r,
--  changing ONLY u cannot raise r, and changing ONLY v cannot raise l;
--  so if setting u=1 makes eval=1 (so r(0)=1) AND setting v=1 makes eval=1 (so l(0)=1),
--  then at (0,0) BOTH l(0)=1 and r(0)=1, so andX(l,r)(0,0)=1, hence eval(0,0)=1!!)
lemma andX_forces_zero {t : XTree} (hp : allPos t) (hnd : t.leaves.Nodup) (hax : ¬ noAndX t) :
    ∃ u ∈ t.leaves, ∃ v ∈ t.leaves, u ≠ v ∧
      ∀ (x : Fin 4 → Bool) (y : Fin 32), x u = false → x v = false →
        t.eval (Function.update x u true) y = true →
        t.eval (Function.update x v true) y = true →
        t.eval x y = true := by
  induction t with
  | leaf _ _ => exact (hax trivial).elim
  | andY t m ih =>
    obtain ⟨u, hu, v, hv, hne, hprop⟩ := ih hp hnd hax
    refine ⟨u, hu, v, hv, hne, fun x y hxu hxv h1 h2 => ?_⟩
    simp only [eval, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨hprop x y hxu hxv h1.1 h2.1, h1.2⟩
  | orY t m ih =>
    obtain ⟨u, hu, v, hv, hne, hprop⟩ := ih hp hnd hax
    refine ⟨u, hu, v, hv, hne, fun x y hxu hxv h1 h2 => ?_⟩
    simp only [eval, Bool.or_eq_true] at h1 h2 ⊢
    rcases h1 with h1 | hm
    · rcases h2 with h2 | hm
      · exact Or.inl (hprop x y hxu hxv h1 h2)
      · exact Or.inr hm
    · exact Or.inr hm
  | orX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    by_cases hl : noAndX l
    · have hr : ¬ noAndX r := fun hr => hax ⟨hl, hr⟩
      obtain ⟨u, hu, v, hv, hne, hprop⟩ := ihr hp.2 hndr hr
      refine ⟨u, by simp [leaves, hu], v, by simp [leaves, hv], hne, fun x y hxu hxv h1 h2 => ?_⟩
      have hnu : u ∉ l.leaves := fun h => hdisj u h u hu rfl
      have hnv : v ∉ l.leaves := fun h => hdisj v h v hv rfl
      simp only [eval, Bool.or_eq_true] at h1 h2 ⊢
      rw [eval_mono_absent hnu true] at h1
      rw [eval_mono_absent hnv true] at h2
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (hprop x y hxu hxv h1 h2)
    · obtain ⟨u, hu, v, hv, hne, hprop⟩ := ihl hp.1 hndl hl
      refine ⟨u, by simp [leaves, hu], v, by simp [leaves, hv], hne, fun x y hxu hxv h1 h2 => ?_⟩
      have hnu : u ∉ r.leaves := fun h => hdisj u hu u h rfl
      have hnv : v ∉ r.leaves := fun h => hdisj v hv v h rfl
      simp only [eval, Bool.or_eq_true] at h1 h2 ⊢
      rw [eval_mono_absent hnu true] at h1
      rw [eval_mono_absent hnv true] at h2
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact Or.inl (hprop x y hxu hxv h1 h2)
        · exact Or.inr h2
      · exact Or.inr h1
  | andX l r _ _ =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil l.leaves (leaves_ne_nil l)
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil r.leaves (leaves_ne_nil r)
    have huv : u ≠ v := fun h => hdisj u hu v hv h
    have hnu : u ∉ r.leaves := fun h => hdisj u hu u h rfl
    have hnv : v ∉ l.leaves := fun h => hdisj v h v hv rfl
    refine ⟨u, by simp [leaves, hu], v, by simp [leaves, hv], huv, fun x y hxu hxv h1 h2 => ?_⟩
    simp only [eval, Bool.and_eq_true] at h1 h2 ⊢
    rw [eval_mono_absent hnu true] at h1
    rw [eval_mono_absent hnv true] at h2
    exact ⟨h2.1, h1.2⟩

-- Linear form of a noAndX, allPos tree!
def constPart (y : Fin 32) : XTree → Bool
  | leaf _ _ => false
  | andY t m => constPart y t && m.testBit y.val
  | orY t m  => constPart y t || m.testBit y.val
  | andX _ _ => false
  | orX l r  => constPart y l || constPart y r

def coeff (v : Fin 4) (y : Fin 32) : XTree → Bool
  | leaf u _ => decide (u = v)
  | andY t m => coeff v y t && m.testBit y.val
  | orY t _  => coeff v y t
  | andX _ _ => false
  | orX l r  => coeff v y l || coeff v y r

lemma eval_linear {t : XTree} (hp : allPos t) (hn : noAndX t) (x : Fin 4 → Bool) (y : Fin 32) :
    t.eval x y = (t.constPart y ||
      ((x 0 && t.coeff 0 y) || (x 1 && t.coeff 1 y) || (x 2 && t.coeff 2 y) || (x 3 && t.coeff 3 y))) := by
  induction t with
  | leaf u neg =>
    subst hp
    fin_cases u <;> simp [eval, constPart, coeff]
  | andY t m ih =>
    simp only [eval, constPart, coeff, ih hp hn]
    cases (m.testBit y.val) <;> simp
  | orY t m ih =>
    simp only [eval, constPart, coeff, ih hp hn]
    cases (m.testBit y.val) <;> simp [Bool.or_left_comm, Bool.or_comm, Bool.or_assoc]
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    simp only [eval, constPart, coeff, ihl hp.1 hn.1, ihr hp.2 hn.2, Bool.and_or_distrib_left]
    ac_rfl

-- List of AND-Y masks on the path from leaf v to root (when leaves.Nodup and noAndX):
def pathAndMasks (v : Fin 4) : XTree → List Nat
  | leaf _ _ => []
  | andY t m => if v ∈ t.leaves then m :: pathAndMasks v t else []
  | orY t _  => pathAndMasks v t
  | andX _ _ => []
  | orX l r  => if v ∈ l.leaves then pathAndMasks v l else pathAndMasks v r

lemma coeff_eq_all_pathAndMasks {t : XTree} (hn : noAndX t) (hnd : t.leaves.Nodup)
    {v : Fin 4} (hv : v ∈ t.leaves) (y : Fin 32) :
    t.coeff v y = (t.pathAndMasks v).all (fun m => m.testBit y.val) := by
  induction t with
  | leaf u _ =>
    have hvu : v = u := List.mem_singleton.mp hv
    subst hvu; simp [coeff, pathAndMasks]
  | andY t m ih =>
    have hv' : v ∈ t.leaves := hv
    simp only [coeff, pathAndMasks, hv', ↓reduceIte, List.all_cons, ih hn hnd hv', Bool.and_comm]
  | orY t _ ih => exact ih hn hnd hv
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    have coeff_absent : ∀ (s : XTree), noAndX s → v ∉ s.leaves → s.coeff v y = false := by
      intro s hs hns
      induction s with
      | leaf u _ => simp [coeff]; rintro rfl; exact hns (by simp [leaves])
      | andY s _ ihs => simp [coeff, ihs hs hns]
      | orY s _ ihs => exact ihs hs hns
      | andX _ _ => exact hs.elim
      | orX a b iha ihb =>
        simp [leaves] at hns
        simp [coeff, iha hs.1 hns.1, ihb hs.2 hns.2]
    simp only [leaves, List.mem_append] at hv
    rcases hv with hl | hr
    · have hnr : v ∉ r.leaves := fun h => hdisj v hl v h rfl
      simp [coeff, pathAndMasks, hl, ihl hn.1 hndl hl, coeff_absent r hn.2 hnr]
    · have hnl : v ∉ l.leaves := fun h => hdisj v h v hr rfl
      simp [coeff, pathAndMasks, hnl, ihr hn.2 hndr hr, coeff_absent l hn.1 hnl]

-- Private AND-Y count (andY nodes strictly below any orX ancestor of leaf v):
def privAndY (v : Fin 4) : XTree → Nat
  | leaf _ _ => 0
  | andY t _ => if t.leaves.length = 1 ∧ v ∈ t.leaves then 1 + privAndY v t else privAndY v t
  | orY t _  => privAndY v t
  | andX _ _ => 0
  | orX l r  => privAndY v l + privAndY v r

lemma sum_privAndY_le_andYCount {t : XTree} (hn : noAndX t) (hnd : t.leaves.Nodup) :
    t.privAndY 0 + t.privAndY 1 + t.privAndY 2 + t.privAndY 3 ≤ t.andYCount := by
  induction t with
  | leaf _ _ => simp [privAndY, andYCount]
  | andY t m ih =>
    have hih := ih hn hnd
    simp only [privAndY, andYCount]
    by_cases h1 : t.leaves.length = 1
    · obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h1
      have hm : ∀ v : Fin 4, v ∈ t.leaves ↔ v = u := by intro v; simp [hu]
      fin_cases u <;> simp [h1, hm] <;> omega
    · simp [h1]; omega
  | orY t _ ih => exact ih hn hnd
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    have hl := ihl hn.1 hndl
    have hr := ihr hn.2 hndr
    simp only [privAndY, andYCount]; omega

def allMasks : XTree → List Nat
  | leaf _ _ => []
  | andY t m => m :: allMasks t
  | orY t m  => m :: allMasks t
  | andX l r => allMasks l ++ allMasks r
  | orX l r  => allMasks l ++ allMasks r

lemma pathAndMasks_sub_allMasks {t : XTree} (v : Fin 4) {m : Nat} (hm : m ∈ t.pathAndMasks v) :
    m ∈ t.allMasks := by
  induction t with
  | leaf _ _ => simp [pathAndMasks] at hm
  | andY t m' ih =>
    simp only [pathAndMasks] at hm
    split at hm
    · simp only [List.mem_cons] at hm; rcases hm with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    · simp at hm
  | orY t _ ih => exact List.mem_cons_of_mem _ (ih hm)
  | andX _ _ => simp [pathAndMasks] at hm
  | orX l r ihl ihr =>
    simp only [pathAndMasks] at hm
    split at hm
    · exact List.mem_append_left _ (ihl hm)
    · exact List.mem_append_right _ (ihr hm)

lemma coeff_absent {t : XTree} (hn : noAndX t) {v : Fin 4} (hnv : v ∉ t.leaves) (y : Fin 32) :
    t.coeff v y = false := by
  induction t with
  | leaf u _ => simp [coeff]; rintro rfl; exact hnv (by simp [leaves])
  | andY t _ ih => simp [coeff, ih hn hnv]
  | orY t _ ih => exact ih hn hnv
  | andX _ _ => exact hn.elim
  | orX a b iha ihb =>
    simp [leaves] at hnv
    simp [coeff, iha hn.1 hnv.1, ihb hn.2 hnv.2]

lemma pathAndMasks_empty_of_len1_priv0 {t : XTree} (hn : noAndX t) {v : Fin 4}
    (hv : v ∈ t.leaves) (hlen1 : t.leaves.length = 1) (h0 : t.privAndY v = 0) :
    t.pathAndMasks v = [] := by
  induction t with
  | leaf _ _ => rfl
  | andY t _ ih =>
    have h1' : t.leaves.length = 1 := hlen1
    have hv' : v ∈ t.leaves := hv
    simp [privAndY, h1', hv'] at h0
  | orY t _ ih => exact ih hn hv hlen1 h0
  | andX _ _ => exact hn.elim
  | orX a b _ _ =>
    have ha := List.length_pos_of_ne_nil (leaves_ne_nil a)
    have hb := List.length_pos_of_ne_nil (leaves_ne_nil b)
    simp [leaves] at hlen1; omega

-- If privAndY v t = 0 and v ∈ t.leaves and t.leaves.length ≥ 2 (so v meets a sibling w!),
-- then pathAndMasks v t is a sublist of pathAndMasks w t (for some sibling w ≠ v in t.leaves)!
lemma no_privAndY_sibling {t : XTree} (hn : noAndX t) (hnd : t.leaves.Nodup)
    {v : Fin 4} (hv : v ∈ t.leaves) (h2 : 2 ≤ t.leaves.length) (h0 : t.privAndY v = 0) :
    ∃ w ∈ t.leaves, w ≠ v ∧ ∀ m ∈ t.pathAndMasks v, m ∈ t.pathAndMasks w := by
  induction t with
  | leaf _ _ => simp [leaves] at h2
  | andY t m ih =>
    have h2' : 2 ≤ t.leaves.length := h2
    have hne1 : t.leaves.length ≠ 1 := by omega
    have h0' : t.privAndY v = 0 := by simpa [privAndY, hne1] using h0
    have hv' : v ∈ t.leaves := hv
    obtain ⟨w, hw, hne, hsub⟩ := ih hn hnd hv' h2' h0'
    refine ⟨w, hw, hne, fun m' hm' => ?_⟩
    simp only [pathAndMasks, hv', hw, ↓reduceIte, List.mem_cons] at hm' ⊢
    rcases hm' with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (hsub m' h')
  | orY t _ ih => exact ih hn hnd hv h2 h0
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    simp only [privAndY] at h0
    simp only [leaves, List.mem_append] at hv
    rcases hv with hl | hr
    · have hnr : v ∉ r.leaves := fun h => hdisj v hl v h rfl
      by_cases hl2 : 2 ≤ l.leaves.length
      · obtain ⟨w, hw, hne, hsub⟩ := ihl hn.1 hndl hl hl2 (by omega)
        refine ⟨w, by simp [leaves, hw], hne, fun m' hm' => ?_⟩
        simp only [pathAndMasks, hl, hw, ↓reduceIte] at hm' ⊢
        exact hsub m' hm'
      · have hlen1 : l.leaves.length = 1 := by have := List.length_pos_of_mem hl; omega
        have hempty := pathAndMasks_empty_of_len1_priv0 hn.1 hl hlen1 (by omega)
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil r.leaves (leaves_ne_nil r)
        refine ⟨w, by simp [leaves, hw], fun h => hnr (h ▸ hw), fun m' hm' => ?_⟩
        simp [pathAndMasks, hl, hempty] at hm'
    · have hnl : v ∉ l.leaves := fun h => hdisj v h v hr rfl
      by_cases hr2 : 2 ≤ r.leaves.length
      · obtain ⟨w, hw, hne, hsub⟩ := ihr hn.2 hndr hr hr2 (by omega)
        have hwnl : w ∉ l.leaves := fun h => hdisj w h w hw rfl
        refine ⟨w, by simp [leaves, hw], hne, fun m' hm' => ?_⟩
        simp only [pathAndMasks, hnl, hwnl, ↓reduceIte] at hm' ⊢
        exact hsub m' hm'
      · have hlen1 : r.leaves.length = 1 := by have := List.length_pos_of_mem hr; omega
        have hempty := pathAndMasks_empty_of_len1_priv0 hn.2 hr hlen1 (by omega)
        obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil l.leaves (leaves_ne_nil l)
        refine ⟨w, by simp [leaves, hw], fun h => hnl (h ▸ hw), fun m' hm' => ?_⟩
        simp [pathAndMasks, hnl, hempty] at hm'

-- If orYCount t = 0, then constPart y t = false!
lemma constPart_eq_false_of_orYCount_zero {t : XTree} (hn : noAndX t) (h0 : t.orYCount = 0)
    (y : Fin 32) : t.constPart y = false := by
  induction t with
  | leaf _ _ => rfl
  | andY t _ ih => simp [constPart, ih hn h0]
  | orY _ _ => simp [orYCount] at h0
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    simp [orYCount] at h0
    simp [constPart, ihl hn.1 h0.1, ihr hn.2 h0.2]

-- When t has NO non-private andY nodes (i.e. every andY node has t'.leaves.length = 1)
-- AND t.orYCount = 1, then constPart y = s.testBit y.val && (guard), where guard is either true or pathAndMasks v!
def allAndYPriv : XTree → Prop
  | leaf _ _ => True
  | andY t _ => t.leaves.length = 1 ∧ allAndYPriv t
  | orY t _  => allAndYPriv t
  | andX _ _ => False
  | orX l r  => allAndYPriv l ∧ allAndYPriv r

lemma allAndYPriv_of_sum_eq {t : XTree} (hn : noAndX t) (hnd : t.leaves.Nodup)
    (heq : t.privAndY 0 + t.privAndY 1 + t.privAndY 2 + t.privAndY 3 = t.andYCount) :
    allAndYPriv t := by
  induction t with
  | leaf _ _ => trivial
  | andY t m ih =>
    have hle := sum_privAndY_le_andYCount (t := t) hn hnd
    simp only [privAndY, andYCount] at heq
    by_cases h1 : t.leaves.length = 1
    · obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h1
      have hm : ∀ v : Fin 4, v ∈ t.leaves ↔ v = u := by intro v; simp [hu]
      have heq' : t.privAndY 0 + t.privAndY 1 + t.privAndY 2 + t.privAndY 3 = t.andYCount := by
        fin_cases u <;> simp [h1, hm] at heq <;> omega
      exact ⟨h1, ih hn hnd heq'⟩
    · simp only [h1, false_and, ↓reduceIte] at heq
      omega
  | orY t _ ih => exact ih hn hnd heq
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    have hl := sum_privAndY_le_andYCount hn.1 hndl
    have hr := sum_privAndY_le_andYCount hn.2 hndr
    simp only [privAndY, andYCount] at heq
    exact ⟨ihl hn.1 hndl (by omega), ihr hn.2 hndr (by omega)⟩

lemma single_orY_mask {t : XTree} (hn : noAndX t) (hnd : t.leaves.Nodup)
    (hpriv : allAndYPriv t) (ho1 : t.orYCount = 1) :
    ∃ s ∈ t.allMasks,
      (∀ y : Fin 32, t.constPart y = true → s.testBit y.val = true) ∧
      ((∀ y : Fin 32, t.constPart y = false → s.testBit y.val = false) ∨
       (∃ v ∈ t.leaves,
          (∃ m' ∈ t.pathAndMasks v, ∀ y : Fin 32, t.constPart y = true → m'.testBit y.val = true) ∧
          (∀ y : Fin 32, t.constPart y = false → t.coeff v y = true → s.testBit y.val = false))) := by
  induction t with
  | leaf _ _ => simp [orYCount] at ho1
  | andY t m ih =>
    obtain ⟨h1, hpriv'⟩ := hpriv
    obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp h1
    have hum : u ∈ t.leaves := by simp [hu]
    obtain ⟨s, hs, htrue, hfalse⟩ := ih hn hnd hpriv' ho1
    refine ⟨s, List.mem_cons_of_mem _ hs, ?_, Or.inr ⟨u, hum, ?_, ?_⟩⟩
    · intro y hy
      simp only [constPart, Bool.and_eq_true] at hy
      exact htrue y hy.1
    · refine ⟨m, by simp [pathAndMasks, hum], fun y hy => ?_⟩
      simp only [constPart, Bool.and_eq_true] at hy
      exact hy.2
    · intro y hy hc
      simp only [constPart, coeff, Bool.and_eq_true] at hy hc
      have hty : t.constPart y = false := by
        cases h : t.constPart y
        · rfl
        · simp [h, hc.2] at hy
      rcases hfalse with hf | ⟨v, hv, _, hf⟩
      · exact hf y hty
      · have hvu : v = u := by simpa [hu] using hv
        subst hvu
        exact hf y hty hc.1
  | orY t m ih =>
    have ho0 : t.orYCount = 0 := by simp [orYCount] at ho1; omega
    refine ⟨m, List.mem_cons_self, ?_, Or.inl ?_⟩
    · intro y hy
      rw [constPart, constPart_eq_false_of_orYCount_zero (t := t) hn ho0 y, Bool.false_or] at hy
      exact hy
    · intro y hy
      rw [constPart, constPart_eq_false_of_orYCount_zero (t := t) hn ho0 y, Bool.false_or] at hy
      exact hy
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    simp only [orYCount] at ho1
    have hcase : (l.orYCount = 1 ∧ r.orYCount = 0) ∨ (l.orYCount = 0 ∧ r.orYCount = 1) := by omega
    rcases hcase with ⟨hl1, hr0⟩ | ⟨hl0, hr1⟩
    · obtain ⟨s, hs, htrue, hfalse⟩ := ihl hn.1 hndl hpriv.1 hl1
      refine ⟨s, List.mem_append_left _ hs, ?_, ?_⟩
      · intro y hy
        rw [constPart, constPart_eq_false_of_orYCount_zero hn.2 hr0 y, Bool.or_false] at hy
        exact htrue y hy
      · rcases hfalse with hf | ⟨v, hv, ⟨m', hm', hmt⟩, hf⟩
        · exact Or.inl fun y hy => hf y (by
            rw [constPart, constPart_eq_false_of_orYCount_zero hn.2 hr0 y, Bool.or_false] at hy; exact hy)
        · refine Or.inr ⟨v, by simp [leaves, hv], ⟨m', by simp [pathAndMasks, hv, hm'], fun y hy => ?_⟩, fun y hy hc => ?_⟩
          · rw [constPart, constPart_eq_false_of_orYCount_zero hn.2 hr0 y, Bool.or_false] at hy
            exact hmt y hy
          · rw [constPart, constPart_eq_false_of_orYCount_zero hn.2 hr0 y, Bool.or_false] at hy
            have hnr : v ∉ r.leaves := fun h => hdisj v hv v h rfl
            rw [coeff, coeff_absent hn.2 hnr y, Bool.or_false] at hc
            exact hf y hy hc
    · obtain ⟨s, hs, htrue, hfalse⟩ := ihr hn.2 hndr hpriv.2 hr1
      refine ⟨s, List.mem_append_right _ hs, ?_, ?_⟩
      · intro y hy
        rw [constPart, constPart_eq_false_of_orYCount_zero hn.1 hl0 y, Bool.false_or] at hy
        exact htrue y hy
      · rcases hfalse with hf | ⟨v, hv, ⟨m', hm', hmt⟩, hf⟩
        · exact Or.inl fun y hy => hf y (by
            rw [constPart, constPart_eq_false_of_orYCount_zero hn.1 hl0 y, Bool.false_or] at hy; exact hy)
        · have hnl : v ∉ l.leaves := fun h => hdisj v h v hv rfl
          refine Or.inr ⟨v, by simp [leaves, hv], ⟨m', by simp [pathAndMasks, hnl, hm'], fun y hy => ?_⟩, fun y hy hc => ?_⟩
          · rw [constPart, constPart_eq_false_of_orYCount_zero hn.1 hl0 y, Bool.false_or] at hy
            exact hmt y hy
          · rw [constPart, constPart_eq_false_of_orYCount_zero hn.1 hl0 y, Bool.false_or] at hy
            rw [coeff, coeff_absent hn.1 hnl y, Bool.false_or] at hc
            exact hf y hy hc

lemma pathAndMasks_len_eq_privAndY {t : XTree} (hn : noAndX t) (hnd : t.leaves.Nodup)
    (hpriv : allAndYPriv t) {v : Fin 4} (hv : v ∈ t.leaves) :
    (t.pathAndMasks v).length = t.privAndY v := by
  induction t with
  | leaf _ _ => rfl
  | andY t m ih =>
    obtain ⟨h1, hpriv'⟩ := hpriv
    have hv' : v ∈ t.leaves := hv
    have := ih hn hnd hpriv' hv'
    simp [pathAndMasks, privAndY, h1, hv']; omega
  | orY t _ ih => exact ih hn hnd hpriv hv
  | andX _ _ => exact hn.elim
  | orX l r ihl ihr =>
    have hdisj := (List.nodup_append.mp hnd).2.2
    have hndl := (List.nodup_append.mp hnd).1
    have hndr := (List.nodup_append.mp hnd).2.1
    have priv_absent : ∀ (s : XTree), noAndX s → v ∉ s.leaves → s.privAndY v = 0 := by
      intro s hs hns
      induction s with
      | leaf _ _ => rfl
      | andY s _ ihs =>
        have hns' : v ∉ s.leaves := hns
        simp [privAndY, hns', ihs hs hns']
      | orY s _ ihs => exact ihs hs hns
      | andX _ _ => exact hs.elim
      | orX a b iha ihb =>
        simp [leaves] at hns
        simp [privAndY, iha hs.1 hns.1, ihb hs.2 hns.2]
    simp only [leaves, List.mem_append] at hv
    rcases hv with hl | hr
    · have hnr : v ∉ r.leaves := fun h => hdisj v hl v h rfl
      simp [pathAndMasks, privAndY, hl, ihl hn.1 hndl hpriv.1 hl, priv_absent r hn.2 hnr]
    · have hnl : v ∉ l.leaves := fun h => hdisj v h v hr rfl
      simp [pathAndMasks, privAndY, hnl, ihr hn.2 hndr hpriv.2 hr, priv_absent l hn.1 hnl]

-- MAIN XTREE SUMMARY THEOREM:
theorem xtree_summary {t : XTree} (hnd : t.leaves.Nodup) (hcov : ∀ v : Fin 4, v ∈ t.leaves)
    (heval : ∀ x y, t.eval x y = targetXY x y) :
    8 ≤ t.gateCount ∧
    (∀ v : Fin 4, ∀ y : Fin 32, isIndepY y = true →
      (t.pathAndMasks v).all (fun m => m.testBit y.val) = AvY v y) ∧
    (t.gateCount = 8 →
      ∃ (m : Fin 4 → Nat) (s : Nat),
        (∀ v : Fin 4, m v ∈ t.allMasks ∧
          ∀ y : Fin 32, isIndepY y = true → (m v).testBit y.val = AvY v y) ∧
        s ∈ t.allMasks ∧
        (∀ y : Fin 32, isIndepY y = false → s.testBit y.val = true) ∧
        ((∀ y : Fin 32, isIndepY y = true → s.testBit y.val = false) ∨
         ∃ v : Fin 4,
           (∀ y : Fin 32, isIndepY y = false → (m v).testBit y.val = true) ∧
           (∀ y : Fin 32, isIndepY y = true → AvY v y = true → s.testBit y.val = false))) := by
  have hlen4 : t.leaves.length = 4 := by
    have hsub1 : t.leaves ⊆ List.finRange 4 := fun v _ => List.mem_finRange v
    have hsub2 : List.finRange 4 ⊆ t.leaves := fun v _ => hcov v
    have h1 := List.Subperm.length_le (List.subperm_of_subset hnd hsub1)
    have h2 := List.Subperm.length_le (List.subperm_of_subset (List.nodup_finRange 4) hsub2)
    simp at h1 h2; omega
  -- 1. All leaves positive!
  have targetXY_unit : ∀ (v : Fin 4) (y : Fin 32),
      isIndepY y = true → AvY v y = true →
      targetXY (Function.update (fun _ => false) v true) y = true := by
    intro v y h1 h2
    fin_cases v <;> simp [targetXY, h1] <;> exact (by simpa using h2)
  have targetXY_zero : ∀ (y : Fin 32), isIndepY y = true →
      targetXY (fun _ => false) y = false := fun y h1 => by simp [targetXY, h1]
  have hallPos : allPos t := by
    apply allPos_of_not_hasNeg
    intro v hnv
    let w : Fin 4 := if v = 0 then 1 else 0
    have hwv : v ≠ w := by fin_cases v <;> decide
    have hy := yBoth_spec v w hwv
    have hanti := eval_antitone_of_hasNeg hnd hnv (fun _ => false) (yBoth v w)
    rw [heval, heval] at hanti
    have h1 := targetXY_unit v (yBoth v w) hy.1 hy.2.1
    have h0 : targetXY (Function.update (fun _ => false) v false) (yBoth v w) = false := by
      have heq : Function.update (fun _ : Fin 4 => false) v false = fun _ => false := by
        funext u; by_cases h : u = v <;> simp [h]
      rw [heq]; exact targetXY_zero _ hy.1
    exact Bool.noConfusion ((hanti h1).symm.trans h0)
  -- 2. No andX nodes!
  have hnoAndX : noAndX t := by
    by_contra hax
    obtain ⟨u, _, v, _, huv, hforce⟩ := andX_forces_zero hallPos hnd hax
    have hy := yBoth_spec u v huv
    have hres := hforce (fun _ => false) (yBoth u v) rfl rfl
    rw [heval, heval, heval] at hres
    have hu1 := targetXY_unit u (yBoth u v) hy.1 hy.2.1
    have hv1 := targetXY_unit v (yBoth u v) hy.1 hy.2.2
    have h00 := targetXY_zero (yBoth u v) hy.1
    exact Bool.noConfusion ((hres hu1 hv1).symm.trans h00)
  -- 3. Linear form: constPart = !isIndepY, coeff v = AvY v on indep!
  have hconst : ∀ y : Fin 32, t.constPart y = !isIndepY y := by
    intro y
    have h := heval (fun _ => false) y
    rw [eval_linear hallPos hnoAndX] at h
    simpa [targetXY] using h
  have hcoeff : ∀ v : Fin 4, ∀ y : Fin 32, isIndepY y = true → t.coeff v y = AvY v y := by
    intro v y hy
    have h := heval (Function.update (fun _ => false) v true) y
    rw [eval_linear hallPos hnoAndX, hconst y, hy] at h
    fin_cases v <;> simpa [targetXY, hy] using h
  have hpath : ∀ v : Fin 4, ∀ y : Fin 32, isIndepY y = true →
      (t.pathAndMasks v).all (fun m => m.testBit y.val) = AvY v y := by
    intro v y hy
    rw [← coeff_eq_all_pathAndMasks hnoAndX hnd (hcov v) y]
    exact hcoeff v y hy
  -- 4. privAndY v ≥ 1 for all v : Fin 4!
  have hpriv1 : ∀ v : Fin 4, 1 ≤ t.privAndY v := by
    intro v
    by_contra hlt
    have h0 : t.privAndY v = 0 := by omega
    obtain ⟨w, hw, hne, hsub⟩ := no_privAndY_sibling hnoAndX hnd (hcov v) (by omega) h0
    have hy := yOnlyNot_spec v w hne.symm
    have hcv := hpath v (yOnlyNot v w) hy.1
    have hcw := hpath w (yOnlyNot v w) hy.1
    rw [hy.2.1] at hcv
    rw [hy.2.2] at hcw
    have hall : (t.pathAndMasks v).all (fun m => m.testBit (yOnlyNot v w).val) = true := by
      rw [List.all_eq_true]
      intro m hm
      exact (List.all_eq_true.mp hcw) m (hsub m hm)
    exact Bool.noConfusion (hall.symm.trans hcv)
  -- 5. orXCount = 3, andYCount ≥ 4, orYCount ≥ 1, gateCount ≥ 8!
  have horX : t.orXCount = 3 := by
    have := orXCount_eq_leaves hnoAndX; omega
  have handY : 4 ≤ t.andYCount := by
    have hsum := sum_privAndY_le_andYCount hnoAndX hnd
    have h0 := hpriv1 0; have h1 := hpriv1 1; have h2 := hpriv1 2; have h3 := hpriv1 3
    omega
  have horY : 1 ≤ t.orYCount := by
    by_contra hlt
    have h0 : t.orYCount = 0 := by omega
    have hc := constPart_eq_false_of_orYCount_zero hnoAndX h0 ⟨3, by decide⟩
    rw [hconst ⟨3, by decide⟩] at hc
    exact Bool.noConfusion hc
  have hgc := gateCount_of_noAndX hnoAndX
  refine ⟨by omega, hpath, ?_⟩
  intro hgc8
  have handY4 : t.andYCount = 4 := by omega
  have horY1 : t.orYCount = 1 := by omega
  have hsumEq : t.privAndY 0 + t.privAndY 1 + t.privAndY 2 + t.privAndY 3 = t.andYCount := by
    have hsum := sum_privAndY_le_andYCount hnoAndX hnd
    have h0 := hpriv1 0; have h1 := hpriv1 1; have h2 := hpriv1 2; have h3 := hpriv1 3
    omega
  have hp1each : ∀ v : Fin 4, t.privAndY v = 1 := by
    have hsum4 : t.privAndY 0 + t.privAndY 1 + t.privAndY 2 + t.privAndY 3 = 4 := hsumEq.trans handY4
    have h0 := hpriv1 0; have h1 := hpriv1 1; have h2 := hpriv1 2; have h3 := hpriv1 3
    intro v
    fin_cases v
    · change t.privAndY 0 = 1; omega
    · change t.privAndY 1 = 1; omega
    · change t.privAndY 2 = 1; omega
    · change t.privAndY 3 = 1; omega
  have hap := allAndYPriv_of_sum_eq hnoAndX hnd hsumEq
  have hlen1 : ∀ v : Fin 4, (t.pathAndMasks v).length = 1 := fun v => by
    rw [pathAndMasks_len_eq_privAndY hnoAndX hnd hap (hcov v), hp1each v]
  let m : Fin 4 → Nat := fun v => (t.pathAndMasks v).head (by intro h; have := hlen1 v; simp [h] at this)
  have hm_eq : ∀ v : Fin 4, t.pathAndMasks v = [m v] := fun v => by
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hlen1 v)
    simp [m, ha]
  obtain ⟨s, hs, htr, hfl⟩ := single_orY_mask hnoAndX hnd hap horY1
  refine ⟨m, s, ?_, hs, fun y hy => htr y (by rw [hconst y, hy]; rfl), ?_⟩
  · intro v
    refine ⟨pathAndMasks_sub_allMasks v (by simp [hm_eq v]), fun y hy => ?_⟩
    have := hpath v y hy
    simpa [hm_eq v] using this
  · rcases hfl with hf | ⟨v, _, ⟨m', hm', hmt⟩, hf⟩
    · exact Or.inl fun y hy => hf y (by rw [hconst y, hy]; rfl)
    · have hm'eq : m' = m v := by simpa [hm_eq v] using hm'
      subst hm'eq
      exact Or.inr ⟨v,
        fun y hy => hmt y (by rw [hconst y, hy]; rfl),
        fun y hy hav => hf y (by rw [hconst y, hy]; rfl) (by rw [hcoeff v y hy, hav])⟩

end XTree

end XTree2940


namespace PureY2940



def all32 : Nat := 0xffffffff
def maskIndep : Nat := 0x00777777
def maskNonIndep : Nat := 0xff888888
def maskA0 : Nat := 0x00727772
def maskA3 : Nat := 0x00777474
def maskA6 : Nat := 0x00772222
def maskA7 : Nat := 0x00447744

def inY : Fin 5 → Nat
  | ⟨0, _⟩ => 0xaaaaaaaa
  | ⟨1, _⟩ => 0xcccccccc
  | ⟨2, _⟩ => 0xf0f0f0f0
  | ⟨3, _⟩ => 0xff00ff00
  | ⟨4, _⟩ => 0xffff0000

def not32 (w : Nat) : Nat := w ^^^ all32

def inList : List Nat := [0, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def canon (w : Nat) : Nat :=
  if w.testBit 0 then not32 (w &&& all32) else w &&& all32

def gateOuts (a b : Nat) : List Nat :=
  [canon (a &&& b), canon (a ||| b), canon (a &&& not32 b), canon (not32 a &&& b)]

def stepAll (pool : List Nat) : List Nat :=
  pool.flatMap fun a => pool.flatMap fun b => gateOuts a b

def dedup : List Nat → List Nat
  | [] => []
  | x :: xs => let r := dedup xs; if x ∈ r then r else x :: r

def L1List : List Nat :=
  dedup ((stepAll inList).filter fun w => !(inList.contains w))

def isSup (w Av : Nat) : Bool :=
  (((Av &&& not32 w) == 0) && ((w &&& maskIndep) != maskIndep)) ||
  (((Av &&& w) == 0) && ((not32 w &&& maskIndep) != maskIndep))

def isW6e4 (w : Nat) : Bool :=
  (((maskA6 &&& not32 w) == 0) && !w.testBit 4) ||
  (((maskA6 &&& w) == 0) && w.testBit 4)

def isW7e4 (w : Nat) : Bool :=
  (((maskA7 &&& not32 w) == 0) && !w.testBit 4) ||
  (((maskA7 &&& w) == 0) && w.testBit 4)

def isW67e4 (w : Nat) : Bool :=
  ((((maskA6 ||| maskA7) &&& not32 w) == 0) && !w.testBit 4) ||
  ((((maskA6 ||| maskA7) &&& w) == 0) && w.testBit 4)

def isS1 (w : Nat) : Bool :=
  let ok (u : Nat) : Bool :=
    ((u &&& maskNonIndep) == maskNonIndep) &&
    (((u &&& maskA0) == 0) || ((u &&& maskA3) == 0) ||
     ((u &&& maskA6) == 0) || ((u &&& maskA7) == 0))
  ok w || ok (not32 w)

def wA6 : Nat := 0xffffaaaa
def wA7 : Nat := 0xffccffcc

theorem masks_check :
    (List.range 32).all (fun y =>
      let y1 := y.testBit 0; let y2 := y.testBit 1; let y4 := y.testBit 2
      let y5 := y.testBit 3; let y8 := y.testBit 4
      let ind := !((y1 && y2) || (y5 && y8))
      (maskIndep.testBit y == ind) &&
      (maskNonIndep.testBit y == !ind) &&
      (maskA0.testBit y == (ind && (y1 || y4 || y5))) &&
      (maskA3.testBit y == (ind && (y2 || y4 || y8))) &&
      (maskA6.testBit y == (ind && (y1 || y8))) &&
      (maskA7.testBit y == (ind && (y2 || y5))) &&
      ((inY 0).testBit y == y1) && ((inY 1).testBit y == y2) &&
      ((inY 2).testBit y == y4) && ((inY 3).testBit y == y5) &&
      ((inY 4).testBit y == y8)) = true := by decide +kernel

theorem no_L0 :
    inList.all (fun w =>
      !isSup w maskA0 && !isSup w maskA3 && !isSup w maskA6 && !isSup w maskA7 && !isS1 w) = true := by
  decide +kernel

theorem no_L1_A0_A3_S1 :
    L1List.all (fun w => !isSup w maskA0 && !isSup w maskA3 && !isS1 w) = true := by
  decide +kernel

theorem uniq_L1_A6_A7 :
    L1List.all (fun w =>
      (!isW6e4 w || w == wA6) && (!isW7e4 w || w == wA7)) = true := by
  decide +kernel

theorem no_step_from_A6_A7 :
    (stepAll (inList ++ [wA6, wA7])).all (fun w =>
      !isSup w maskA0 && !isSup w maskA3 && !isS1 w) = true := by
  decide +kernel

theorem step_from_A6_only_A7 :
    (stepAll (inList ++ [wA6])).all (fun w =>
      !isSup w maskA0 && !isSup w maskA3 && (!isW7e4 w || w == wA7)) = true := by
  decide +kernel

theorem step_from_A7_only_A6 :
    (stepAll (inList ++ [wA7])).all (fun w =>
      !isSup w maskA0 && !isSup w maskA3 && (!isW6e4 w || w == wA6)) = true := by
  decide +kernel

def check1c : Bool :=
  (L1List.filter fun g0 => g0 != wA6 && g0 != wA7).all fun g0 =>
    let p1 := inList ++ [g0]
    let c1 := dedup ((stepAll p1).filter fun w => isSup w maskA0 || isSup w maskA3 || isW67e4 w)
    c1.all fun g1 =>
      let p2 := p1 ++ [g1]
      let h0 := isSup g1 maskA0
      let h3 := isSup g1 maskA3
      let h6 := isW67e4 g1
      let c2 := dedup ((stepAll p2).filter fun w =>
        (!h0 && isSup w maskA0) || (!h3 && isSup w maskA3) || (!h6 && isW67e4 w))
      c2.all fun g2 =>
        let p3 := p2 ++ [g2]
        let h0' := h0 || isSup g2 maskA0
        let h3' := h3 || isSup g2 maskA3
        let h6' := h6 || isW67e4 g2
        (stepAll p3).all fun g3 =>
          !((!h0' && isSup g3 maskA0) || (!h3' && isSup g3 maskA3) || (!h6' && isW67e4 g3))

set_option maxHeartbeats 4000000 in
theorem subcase1c_ok : check1c = true := by decide +kernel

-- Helper bit arithmetic for Nat masks on 32 bits:
def PureStep (pool : List Nat) (w : Nat) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, w ∈ gateOuts a b

lemma mem_stepAll {pool : List Nat} {a b w : Nat}
    (ha : a ∈ pool) (hb : b ∈ pool) (hw : w ∈ gateOuts a b) : w ∈ stepAll pool := by
  unfold stepAll
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, hw⟩⟩

lemma stepAll_mono {p q : List Nat} (hsub : ∀ x ∈ p, x ∈ q) {w : Nat}
    (hw : w ∈ stepAll p) : w ∈ stepAll q := by
  unfold stepAll at hw ⊢
  obtain ⟨a, ha, hrest⟩ := List.mem_flatMap.mp hw
  obtain ⟨b, hb, hmem⟩ := List.mem_flatMap.mp hrest
  exact List.mem_flatMap.mpr ⟨a, hsub a ha, List.mem_flatMap.mpr ⟨b, hsub b hb, hmem⟩⟩

lemma mem_dedup {l : List Nat} {x : Nat} : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp only [dedup]
    split
    · rename_i h
      simp only [List.mem_cons]
      constructor
      · intro hx; exact Or.inr (ih.mp hx)
      · rintro (rfl | hx); exact h; exact ih.mpr hx
    · simp only [List.mem_cons, ih]

lemma mem_L1List {w : Nat} (hstep : PureStep inList w) (hnot : w ∉ inList) :
    w ∈ L1List := by
  obtain ⟨a, ha, b, hb, hw⟩ := hstep
  unfold L1List
  rw [mem_dedup, List.mem_filter]
  exact ⟨mem_stepAll ha hb hw, by simpa using hnot⟩

-- Bit helpers for distinctness:
lemma land_eq_zero_testBit {a b i : Nat} (h : (a &&& b) == 0) (ha : a.testBit i = true) :
    b.testBit i = false := by
  have hz : a &&& b = 0 := beq_iff_eq.mp h
  have ht := congrArg (fun n => n.testBit i) hz
  rw [Nat.testBit_and, ha, Bool.true_and, Nat.zero_testBit] at ht
  exact ht

lemma not32_testBit {w i : Nat} (hi : i < 32) : (not32 w).testBit i = !(w.testBit i) := by
  unfold not32 all32
  rw [Nat.testBit_xor]
  have ha : (0xffffffff : Nat).testBit i = true := by
    have : ∀ j : Fin 32, (0xffffffff : Nat).testBit j.val = true := by decide
    exact this ⟨i, hi⟩
  rw [ha, Bool.xor_true]

def isW0e2 (w : Nat) : Bool :=
  (((maskA0 &&& not32 w) == 0) && !w.testBit 2) ||
  (((maskA0 &&& w) == 0) && w.testBit 2)

def isW3e1 (w : Nat) : Bool :=
  (((maskA3 &&& not32 w) == 0) && !w.testBit 1) ||
  (((maskA3 &&& w) == 0) && w.testBit 1)

lemma isSup_of_isW0e2 {w : Nat} (h : isW0e2 w = true) : isSup w maskA0 = true := by
  unfold isW0e2 at h; unfold isSup
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne] at h ⊢
  rcases h with ⟨h0, hb⟩ | ⟨h0, hb⟩
  · refine Or.inl ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 2) heq
    rw [Nat.testBit_and, hb, Bool.false_and] at ht
    exact Bool.noConfusion ht
  · refine Or.inr ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 2) heq
    rw [Nat.testBit_and, not32_testBit (by omega), hb] at ht
    exact Bool.noConfusion ht

lemma isSup_of_isW3e1 {w : Nat} (h : isW3e1 w = true) : isSup w maskA3 = true := by
  unfold isW3e1 at h; unfold isSup
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne] at h ⊢
  rcases h with ⟨h0, hb⟩ | ⟨h0, hb⟩
  · refine Or.inl ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 1) heq
    rw [Nat.testBit_and, hb, Bool.false_and] at ht
    exact Bool.noConfusion ht
  · refine Or.inr ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 1) heq
    rw [Nat.testBit_and, not32_testBit (by omega), hb] at ht
    exact Bool.noConfusion ht

lemma isSup_of_isW6e4 {w : Nat} (h : isW6e4 w = true) : isSup w maskA6 = true := by
  unfold isW6e4 at h; unfold isSup
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne] at h ⊢
  rcases h with ⟨h0, hb⟩ | ⟨h0, hb⟩
  · refine Or.inl ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 4) heq
    rw [Nat.testBit_and, hb, Bool.false_and] at ht
    exact Bool.noConfusion ht
  · refine Or.inr ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 4) heq
    rw [Nat.testBit_and, not32_testBit (by omega), hb] at ht
    exact Bool.noConfusion ht

lemma isSup_of_isW7e4 {w : Nat} (h : isW7e4 w = true) : isSup w maskA7 = true := by
  unfold isW7e4 at h; unfold isSup
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne] at h ⊢
  rcases h with ⟨h0, hb⟩ | ⟨h0, hb⟩
  · refine Or.inl ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 4) heq
    rw [Nat.testBit_and, hb, Bool.false_and] at ht
    exact Bool.noConfusion ht
  · refine Or.inr ⟨h0, fun heq => ?_⟩
    have ht := congrArg (fun n => n.testBit 4) heq
    rw [Nat.testBit_and, not32_testBit (by omega), hb] at ht
    exact Bool.noConfusion ht

lemma w0_ne_w3 {w : Nat} (h0 : isW0e2 w = true) (h3 : isW3e1 w = true) : False := by
  unfold isW0e2 at h0; unfold isW3e1 at h3
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h0 h3
  rcases h0 with ⟨ha0, hb2⟩ | ⟨ha0, hb2⟩ <;> rcases h3 with ⟨ha3, hb1⟩ | ⟨ha3, hb1⟩
  · have := land_eq_zero_testBit ha3 (i := 2) (by decide)
    rw [not32_testBit (by omega), hb2] at this; exact Bool.noConfusion this
  · have t1 := land_eq_zero_testBit ha0 (i := 4) (by decide)
    have t2 := land_eq_zero_testBit ha3 (i := 4) (by decide)
    rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
  · have t1 := land_eq_zero_testBit ha0 (i := 4) (by decide)
    have t2 := land_eq_zero_testBit ha3 (i := 4) (by decide)
    rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
  · have := land_eq_zero_testBit ha3 (i := 2) (by decide)
    rw [hb2] at this; exact Bool.noConfusion this

lemma w0_ne_w6 {w : Nat} (h0 : isW0e2 w = true) (h6 : isW6e4 w = true) : False := by
  unfold isW0e2 at h0; unfold isW6e4 at h6
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h0 h6
  rcases h0 with ⟨ha0, _⟩ | ⟨ha0, _⟩ <;> rcases h6 with ⟨ha6, hb4⟩ | ⟨ha6, hb4⟩
  · have := land_eq_zero_testBit ha0 (i := 4) (by decide)
    rw [not32_testBit (by omega), hb4] at this; exact Bool.noConfusion this
  · have t1 := land_eq_zero_testBit ha0 (i := 1) (by decide)
    have t2 := land_eq_zero_testBit ha6 (i := 1) (by decide)
    rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
  · have t1 := land_eq_zero_testBit ha0 (i := 1) (by decide)
    have t2 := land_eq_zero_testBit ha6 (i := 1) (by decide)
    rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
  · have := land_eq_zero_testBit ha0 (i := 4) (by decide)
    rw [hb4] at this; exact Bool.noConfusion this

lemma w0_ne_w7 {w : Nat} (h0 : isW0e2 w = true) (h7 : isW7e4 w = true) : False := by
  unfold isW0e2 at h0; unfold isW7e4 at h7
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h0 h7
  rcases h0 with ⟨ha0, _⟩ | ⟨ha0, _⟩ <;> rcases h7 with ⟨ha7, hb4⟩ | ⟨ha7, hb4⟩
  · have := land_eq_zero_testBit ha0 (i := 4) (by decide)
    rw [not32_testBit (by omega), hb4] at this; exact Bool.noConfusion this
  · have t1 := land_eq_zero_testBit ha0 (i := 8) (by decide)
    have t2 := land_eq_zero_testBit ha7 (i := 8) (by decide)
    rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
  · have t1 := land_eq_zero_testBit ha0 (i := 8) (by decide)
    have t2 := land_eq_zero_testBit ha7 (i := 8) (by decide)
    rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
  · have := land_eq_zero_testBit ha0 (i := 4) (by decide)
    rw [hb4] at this; exact Bool.noConfusion this

lemma w3_ne_w6 {w : Nat} (h3 : isW3e1 w = true) (h6 : isW6e4 w = true) : False := by
  unfold isW3e1 at h3; unfold isW6e4 at h6
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h3 h6
  rcases h3 with ⟨ha3, _⟩ | ⟨ha3, _⟩ <;> rcases h6 with ⟨ha6, hb4⟩ | ⟨ha6, hb4⟩
  · have := land_eq_zero_testBit ha3 (i := 4) (by decide)
    rw [not32_testBit (by omega), hb4] at this; exact Bool.noConfusion this
  · have t1 := land_eq_zero_testBit ha3 (i := 16) (by decide)
    have t2 := land_eq_zero_testBit ha6 (i := 16) (by decide)
    rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
  · have t1 := land_eq_zero_testBit ha3 (i := 16) (by decide)
    have t2 := land_eq_zero_testBit ha6 (i := 16) (by decide)
    rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
  · have := land_eq_zero_testBit ha3 (i := 4) (by decide)
    rw [hb4] at this; exact Bool.noConfusion this

lemma w3_ne_w7 {w : Nat} (h3 : isW3e1 w = true) (h7 : isW7e4 w = true) : False := by
  unfold isW3e1 at h3; unfold isW7e4 at h7
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h3 h7
  rcases h3 with ⟨ha3, _⟩ | ⟨ha3, _⟩ <;> rcases h7 with ⟨ha7, hb4⟩ | ⟨ha7, hb4⟩
  · have := land_eq_zero_testBit ha3 (i := 4) (by decide)
    rw [not32_testBit (by omega), hb4] at this; exact Bool.noConfusion this
  · have t1 := land_eq_zero_testBit ha3 (i := 2) (by decide)
    have t2 := land_eq_zero_testBit ha7 (i := 2) (by decide)
    rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
  · have t1 := land_eq_zero_testBit ha3 (i := 2) (by decide)
    have t2 := land_eq_zero_testBit ha7 (i := 2) (by decide)
    rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
  · have := land_eq_zero_testBit ha3 (i := 4) (by decide)
    rw [hb4] at this; exact Bool.noConfusion this

lemma land_lor_eq_zero {a b c : Nat} (ha : a &&& c = 0) (hb : b &&& c = 0) :
    (a ||| b) &&& c = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 := congrArg (fun n => n.testBit i) ha
  have h2 := congrArg (fun n => n.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 h2 ⊢
  cases hc : c.testBit i
  · simp
  · simp [hc] at h1 h2 ⊢; simp [h1, h2]

lemma land_lor_eq_zero_left {a b c : Nat} (hab : (a ||| b) &&& c = 0) : a &&& c = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun n => n.testBit i) hab
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h ⊢
  cases hc : c.testBit i
  · simp
  · simp [hc] at h ⊢; exact h.1

lemma w67_of_both {w : Nat} (h6 : isW6e4 w = true) (h7 : isW7e4 w = true) : isW67e4 w = true := by
  unfold isW6e4 at h6; unfold isW7e4 at h7; unfold isW67e4
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h6 h7 ⊢
  rcases h6 with ⟨ha6, hb4⟩ | ⟨ha6, hb4⟩ <;> rcases h7 with ⟨ha7, hb4'⟩ | ⟨ha7, hb4'⟩
  · exact Or.inl ⟨land_lor_eq_zero ha6 ha7, hb4⟩
  · exact Bool.noConfusion (hb4.symm.trans hb4')
  · exact Bool.noConfusion (hb4.symm.trans hb4')
  · exact Or.inr ⟨land_lor_eq_zero ha6 ha7, hb4⟩

-- Clean a PureStep list to remove elements already in inList or earlier in the list:
def ValidPureSeq (gs : List Nat) : Prop :=
  ∀ (k : Nat) (hk : k < gs.length), PureStep (inList ++ gs.take k) gs[k]

lemma clean_pure_seq (gs : List Nat) (hv : ValidPureSeq gs) :
    ∃ hs : List Nat, hs.length ≤ gs.length ∧ hs.Nodup ∧ (∀ x ∈ hs, x ∉ inList) ∧
      ValidPureSeq hs ∧ (∀ x ∈ gs, x ∈ inList ++ hs) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], le_rfl, List.nodup_nil, by simp, fun _ hk => by simp at hk, by simp⟩
  | append_singleton gs a ih =>
    have hv_pre : ValidPureSeq gs := fun k hk => by
      have h := hv k (by simp; omega)
      simpa [List.take_append_of_le_length (le_of_lt hk), List.getElem_append_left hk] using h
    obtain ⟨hs, hlen, hnd, hni, hvh, hcov⟩ := ih hv_pre
    have ha_step : PureStep (inList ++ hs) a := by
      have h := hv gs.length (by simp)
      simp only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] at h
      obtain ⟨u, hu, v, hv', hout⟩ := h
      have lift (x : Nat) (hx : x ∈ inList ++ gs) : x ∈ inList ++ hs := by
        rcases List.mem_append.mp hx with hi | hg
        · exact List.mem_append_left _ hi
        · exact hcov x hg
      exact ⟨u, lift u hu, v, lift v hv', hout⟩
    by_cases hmem : a ∈ inList ++ hs
    · refine ⟨hs, by simp; omega, hnd, hni, hvh, fun x hx => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hg | rfl
      · exact hcov x hg
      · exact hmem
    · refine ⟨hs ++ [a], by simp; omega, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hnd, List.nodup_singleton a, fun x hx y hy => by
          rw [List.mem_singleton.mp hy]; rintro rfl; exact hmem (List.mem_append_right _ hx)⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with h | rfl
        · exact hni x h
        · exact fun hi => hmem (List.mem_append_left _ hi)
      · intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hlt : k < hs.length
        · simpa [List.take_append_of_le_length (le_of_lt hlt), List.getElem_append_left hlt] using hvh k hlt
        · have heq : k = hs.length := by omega
          subst heq
          simpa [List.take_append_of_le_length le_rfl] using ha_step
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        rcases hx with hg | rfl
        · rcases List.mem_append.mp (hcov x hg) with hi | hh
          · exact Or.inl hi
          · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr rfl)

-- Main Theorem 1: No ValidPureSeq of length <= 4 produces w0, w3, w6, w7!
theorem pureY_le4_impossible (gs : List Nat) (hv : ValidPureSeq gs) (hlen : gs.length ≤ 4)
    (w0 w3 w6 w7 : Nat)
    (hm0 : w0 ∈ inList ++ gs) (hm3 : w3 ∈ inList ++ gs)
    (hm6 : w6 ∈ inList ++ gs) (hm7 : w7 ∈ inList ++ gs)
    (hw0 : isW0e2 w0 = true) (hw3 : isW3e1 w3 = true)
    (hw6 : isW6e4 w6 = true) (hw7 : isW7e4 w7 = true) : False := by
  obtain ⟨hs, hsh, hnd, hni, hvh, hcov⟩ := clean_pure_seq gs hv
  have lift (x : Nat) (hx : x ∈ inList ++ gs) : x ∈ inList ++ hs := by
    rcases List.mem_append.mp hx with hi | hg
    · exact List.mem_append_left _ hi
    · exact hcov x hg
  have not_in_inList_of_sup0 {x} (hx : isSup x maskA0 = true) : x ∉ inList := fun hi => by
    have h := (List.all_eq_true.mp no_L0) x hi
    simp [hx] at h
  have not_in_inList_of_sup3 {x} (hx : isSup x maskA3 = true) : x ∉ inList := fun hi => by
    have h := (List.all_eq_true.mp no_L0) x hi
    simp [hx] at h
  have not_in_inList_of_sup6 {x} (hx : isSup x maskA6 = true) : x ∉ inList := fun hi => by
    have h := (List.all_eq_true.mp no_L0) x hi
    simp [hx] at h
  have not_in_inList_of_sup7 {x} (hx : isSup x maskA7 = true) : x ∉ inList := fun hi => by
    have h := (List.all_eq_true.mp no_L0) x hi
    simp [hx] at h
  have h0s : w0 ∈ hs := (List.mem_append.mp (lift w0 hm0)).resolve_left (not_in_inList_of_sup0 (isSup_of_isW0e2 hw0))
  have h3s : w3 ∈ hs := (List.mem_append.mp (lift w3 hm3)).resolve_left (not_in_inList_of_sup3 (isSup_of_isW3e1 hw3))
  have h6s : w6 ∈ hs := (List.mem_append.mp (lift w6 hm6)).resolve_left (not_in_inList_of_sup6 (isSup_of_isW6e4 hw6))
  have h7s : w7 ∈ hs := (List.mem_append.mp (lift w7 hm7)).resolve_left (not_in_inList_of_sup7 (isSup_of_isW7e4 hw7))
  have h03 : w0 ≠ w3 := fun e => w0_ne_w3 hw0 (e ▸ hw3)
  have h06 : w0 ≠ w6 := fun e => w0_ne_w6 hw0 (e ▸ hw6)
  have h07 : w0 ≠ w7 := fun e => w0_ne_w7 hw0 (e ▸ hw7)
  have h36 : w3 ≠ w6 := fun e => w3_ne_w6 hw3 (e ▸ hw6)
  have h37 : w3 ≠ w7 := fun e => w3_ne_w7 hw3 (e ▸ hw7)
  -- hs has length <= 4 and contains 3 distinct elements w0, w3, w6 -> length is 3 or 4!
  match hs with
  | [] => simp at h0s
  | [g0] => simp at h0s h3s; exact h03 (h0s.trans h3s.symm)
  | [g0, g1] =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0s h3s h6s
    rcases h0s with rfl | rfl <;> rcases h3s with h | h <;> rcases h6s with h' | h' <;>
      first | exact h03 h.symm | exact h06 h'.symm | exact h36 (h.trans h'.symm)
  | [g0, g1, g2] =>
    have hg0L1 : g0 ∈ L1List := mem_L1List (by simpa using hvh 0 (by simp)) (hni g0 (by simp))
    have hg0_not0 : g0 ≠ w0 := fun e => by
      have h := (List.all_eq_true.mp no_L1_A0_A3_S1) g0 hg0L1
      simp [e, isSup_of_isW0e2 hw0] at h
    have hg0_not3 : g0 ≠ w3 := fun e => by
      have h := (List.all_eq_true.mp no_L1_A0_A3_S1) g0 hg0L1
      simp [e, isSup_of_isW3e1 hw3] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0s h3s h6s h7s
    have h60 : w6 = g0 := by
      rcases h0s with h | rfl | rfl
      · exact (hg0_not0 h.symm).elim
      · rcases h3s with h | h | rfl
        · exact (hg0_not3 h.symm).elim
        · exact (h03 h.symm).elim
        · rcases h6s with rfl | h | h; rfl; exact (h06 h.symm).elim; exact (h36 h.symm).elim
      · rcases h3s with h | rfl | h
        · exact (hg0_not3 h.symm).elim
        · rcases h6s with rfl | h | h; rfl; exact (h36 h.symm).elim; exact (h06 h.symm).elim
        · exact (h03 h.symm).elim
    have h70 : w7 = g0 := by
      rcases h0s with h | rfl | rfl
      · exact (hg0_not0 h.symm).elim
      · rcases h3s with h | h | rfl
        · exact (hg0_not3 h.symm).elim
        · exact (h03 h.symm).elim
        · rcases h7s with rfl | h | h; rfl; exact (h07 h.symm).elim; exact (h37 h.symm).elim
      · rcases h3s with h | rfl | h
        · exact (hg0_not3 h.symm).elim
        · rcases h7s with rfl | h | h; rfl; exact (h37 h.symm).elim; exact (h07 h.symm).elim
        · exact (h03 h.symm).elim
    have hu := (List.all_eq_true.mp uniq_L1_A6_A7) g0 hg0L1
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
    have he1 : g0 = wA6 := hu.1.resolve_left (by simp [← h60, hw6])
    have he2 : g0 = wA7 := hu.2.resolve_left (by simp [← h70, hw7])
    exact absurd (he1.symm.trans he2) (by decide)
  | [g0, g1, g2, g3] =>
    have hg0L1 : g0 ∈ L1List := mem_L1List (by simpa using hvh 0 (by simp)) (hni g0 (by simp))
    have hg0_not0 : g0 ≠ w0 := fun e => by
      have h := (List.all_eq_true.mp no_L1_A0_A3_S1) g0 hg0L1
      simp [e, isSup_of_isW0e2 hw0] at h
    have hg0_not3 : g0 ≠ w3 := fun e => by
      have h := (List.all_eq_true.mp no_L1_A0_A3_S1) g0 hg0L1
      simp [e, isSup_of_isW3e1 hw3] at h
    have hg1_step : g1 ∈ stepAll (inList ++ [g0]) := by
      obtain ⟨a, ha, b, hb, hm⟩ := hvh 1 (by simp)
      exact mem_stepAll ha hb hm
    have hg2_step : g2 ∈ stepAll (inList ++ [g0, g1]) := by
      obtain ⟨a, ha, b, hb, hm⟩ := hvh 2 (by simp)
      exact mem_stepAll ha hb hm
    have hg3_step : g3 ∈ stepAll (inList ++ [g0, g1, g2]) := by
      obtain ⟨a, ha, b, hb, hm⟩ := hvh 3 (by simp)
      exact mem_stepAll ha hb hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0s h3s h6s h7s
    by_cases hA6 : g0 = wA6
    · subst hA6
      have hs1 := (List.all_eq_true.mp step_from_A6_only_A7) g1 hg1_step
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hs1
      have hg1_not0 : g1 ≠ w0 := fun e => by rw [e] at hs1; simp [isSup_of_isW0e2 hw0] at hs1
      have hg1_not3 : g1 ≠ w3 := fun e => by rw [e] at hs1; simp [isSup_of_isW3e1 hw3] at hs1
      have h7_eq : w7 = g1 := by
        have hg0_not7 : wA6 ≠ w7 := fun e => by
          have hu := (List.all_eq_true.mp uniq_L1_A6_A7) wA6 hg0L1
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
          have hw7' : isW7e4 wA6 = true := by rw [e]; exact hw7
          have := hu.2.resolve_left (by simp [hw7'])
          exact absurd this (by decide)
        rcases h0s with h | h | rfl | rfl
        · exact (hg0_not0 h.symm).elim
        · exact (hg1_not0 h.symm).elim
        · rcases h3s with h | h | h | rfl
          · exact (hg0_not3 h.symm).elim
          · exact (hg1_not3 h.symm).elim
          · exact (h03 h.symm).elim
          · rcases h7s with h | rfl | h | h
            · exact (hg0_not7 h.symm).elim
            · rfl
            · exact (h07 h.symm).elim
            · exact (h37 h.symm).elim
        · rcases h3s with h | h | rfl | h
          · exact (hg0_not3 h.symm).elim
          · exact (hg1_not3 h.symm).elim
          · rcases h7s with h | rfl | h | h
            · exact (hg0_not7 h.symm).elim
            · rfl
            · exact (h37 h.symm).elim
            · exact (h07 h.symm).elim
          · exact (h03 h.symm).elim
      have hg1_A7 : g1 = wA7 := hs1.2.resolve_left (by simp [← h7_eq, hw7])
      subst hg1_A7
      have hs2 := (List.all_eq_true.mp no_step_from_A6_A7) g2 hg2_step
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs2
      rcases h0s with h | h | rfl | h
      · exact (hg0_not0 h.symm).elim
      · exact (hg1_not0 h.symm).elim
      · exact Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hs2.1.1)
      · rcases h3s with h' | h' | rfl | h'
        · exact (hg0_not3 h'.symm).elim
        · exact (hg1_not3 h'.symm).elim
        · exact Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hs2.1.2)
        · exact h03 (h.trans h'.symm)
    · by_cases hA7 : g0 = wA7
      · subst hA7
        have hs1 := (List.all_eq_true.mp step_from_A7_only_A6) g1 hg1_step
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hs1
        have hg1_not0 : g1 ≠ w0 := fun e => by rw [e] at hs1; simp [isSup_of_isW0e2 hw0] at hs1
        have hg1_not3 : g1 ≠ w3 := fun e => by rw [e] at hs1; simp [isSup_of_isW3e1 hw3] at hs1
        have h6_eq : w6 = g1 := by
          have hg0_not6 : wA7 ≠ w6 := fun e => by
            have hu := (List.all_eq_true.mp uniq_L1_A6_A7) wA7 hg0L1
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
            have hw6' : isW6e4 wA7 = true := by rw [e]; exact hw6
            have := hu.1.resolve_left (by simp [hw6'])
            exact absurd this (by decide)
          rcases h0s with h | h | rfl | rfl
          · exact (hg0_not0 h.symm).elim
          · exact (hg1_not0 h.symm).elim
          · rcases h3s with h | h | h | rfl
            · exact (hg0_not3 h.symm).elim
            · exact (hg1_not3 h.symm).elim
            · exact (h03 h.symm).elim
            · rcases h6s with h | rfl | h | h
              · exact (hg0_not6 h.symm).elim
              · rfl
              · exact (h06 h.symm).elim
              · exact (h36 h.symm).elim
          · rcases h3s with h | h | rfl | h
            · exact (hg0_not3 h.symm).elim
            · exact (hg1_not3 h.symm).elim
            · rcases h6s with h | rfl | h | h
              · exact (hg0_not6 h.symm).elim
              · rfl
              · exact (h36 h.symm).elim
              · exact (h06 h.symm).elim
            · exact (h03 h.symm).elim
        have hg1_A6 : g1 = wA6 := hs1.2.resolve_left (by simp [← h6_eq, hw6])
        subst hg1_A6
        have hg2_step' : g2 ∈ stepAll (inList ++ [wA6, wA7]) :=
          stepAll_mono (fun x hx => by
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
            rcases hx with h | rfl | rfl
            · exact Or.inl h
            · exact Or.inr (Or.inr rfl)
            · exact Or.inr (Or.inl rfl)) hg2_step
        have hs2 := (List.all_eq_true.mp no_step_from_A6_A7) g2 hg2_step'
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs2
        rcases h0s with h | h | rfl | h
        · exact (hg0_not0 h.symm).elim
        · exact (hg1_not0 h.symm).elim
        · exact Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hs2.1.1)
        · rcases h3s with h' | h' | rfl | h'
          · exact (hg0_not3 h'.symm).elim
          · exact (hg1_not3 h'.symm).elim
          · exact Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hs2.1.2)
          · exact h03 (h.trans h'.symm)
      · -- Subcase 1c: g0 ∈ L1List \ {wA6, wA7}!
        have hu := (List.all_eq_true.mp uniq_L1_A6_A7) g0 hg0L1
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
        have hg0_not6 : g0 ≠ w6 := fun e => hA6 (hu.1.resolve_left (by rw [e, hw6]; decide))
        have hg0_not7 : g0 ≠ w7 := fun e => hA7 (hu.2.resolve_left (by rw [e, hw7]; decide))
        have h0' : w0 = g1 ∨ w0 = g2 ∨ w0 = g3 := by rcases h0s with h | h | h | h; exact (hg0_not0 h.symm).elim; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
        have h3' : w3 = g1 ∨ w3 = g2 ∨ w3 = g3 := by rcases h3s with h | h | h | h; exact (hg0_not3 h.symm).elim; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
        have h6' : w6 = g1 ∨ w6 = g2 ∨ w6 = g3 := by rcases h6s with h | h | h | h; exact (hg0_not6 h.symm).elim; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
        have h7' : w7 = g1 ∨ w7 = g2 ∨ w7 = g3 := by rcases h7s with h | h | h | h; exact (hg0_not7 h.symm).elim; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
        have h67_eq : w6 = w7 := by
          rcases h0' with rfl | rfl | rfl <;> rcases h3' with h3e | h3e | h3e <;>
          rcases h6' with h6e | h6e | h6e <;> rcases h7' with h7e | h7e | h7e <;>
            first | exact h6e.trans h7e.symm | exact (h03 h3e.symm).elim | exact (h06 h6e.symm).elim |
                    exact (h07 h7e.symm).elim | exact (h36 (h3e.trans h6e.symm)).elim |
                    exact (h37 (h3e.trans h7e.symm)).elim
        have hw67 : isW67e4 w6 = true := w67_of_both hw6 (h67_eq ▸ hw7)
        -- Now invoke subcase1c_ok!
        have hfilt : g0 ∈ L1List.filter (fun x => x != wA6 && x != wA7) := by
          rw [List.mem_filter]; exact ⟨hg0L1, by simp [hA6, hA7]⟩
        have hc1c := (List.all_eq_true.mp subcase1c_ok) g0 hfilt
        dsimp only at hc1c
        -- Check each of the 6 permutations of {w0, w3, w6} = {g1, g2, g3}!
        have hperm : ∀ (x y z : Nat), x ∈ [w0, w3, w6] → y ∈ [w0, w3, w6] → z ∈ [w0, w3, w6] →
            True := fun _ _ _ _ _ _ => trivial
        have h1_good : isSup g1 maskA0 = true ∨ isSup g1 maskA3 = true ∨ isW67e4 g1 = true := by
          rcases h0' with rfl | rfl | rfl
          · exact Or.inl (isSup_of_isW0e2 hw0)
          · rcases h3' with rfl | h3e | rfl
            · exact Or.inr (Or.inl (isSup_of_isW3e1 hw3))
            · exact (h03 h3e.symm).elim
            · rcases h6' with rfl | h6e | h6e
              · exact Or.inr (Or.inr hw67)
              · exact (h06 h6e.symm).elim
              · exact (h36 h6e.symm).elim
          · rcases h3' with rfl | rfl | h3e
            · exact Or.inr (Or.inl (isSup_of_isW3e1 hw3))
            · rcases h6' with rfl | h6e | h6e
              · exact Or.inr (Or.inr hw67)
              · exact (h36 h6e.symm).elim
              · exact (h06 h6e.symm).elim
            · exact (h03 h3e.symm).elim
        have hg1_c1 : g1 ∈ dedup ((stepAll (inList ++ [g0])).filter fun w => isSup w maskA0 || isSup w maskA3 || isW67e4 w) := by
          rw [mem_dedup, List.mem_filter]
          exact ⟨hg1_step, by rcases h1_good with h | h | h <;> simp [h]⟩
        have hc2 := (List.all_eq_true.mp hc1c) g1 hg1_c1
        -- Check that g2 hits a remaining target and g3 hits the last target!
        -- Notice: since w0, w3, w6 are pairwise distinct and cannot satisfy two of {isW0e2, isW3e1, isW6e4},
        -- Wait: could w0 satisfy isW67e4? NO! w0_ne_w6! Could w0 satisfy isSup maskA3?
        -- WAIT: check if w0 could satisfy isSup maskA3 (e.g. w0 = 0 on 00000 and e_2 -> A3(e_2)=1 so NO!)!
        have hnot_w0_A3 : isSup w0 maskA3 = false := by
          cases h : isSup w0 maskA3; rfl
          exfalso; unfold isSup at h; unfold isW0e2 at hw0
          simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h hw0
          rcases hw0 with ⟨ha0, hb2⟩ | ⟨ha0, hb2⟩ <;> rcases h with ⟨ha3, _⟩ | ⟨ha3, _⟩
          · have := land_eq_zero_testBit ha3 (i := 2) (by decide)
            rw [not32_testBit (by omega), hb2] at this; exact Bool.noConfusion this
          · have t1 := land_eq_zero_testBit ha0 (i := 4) (by decide)
            have t2 := land_eq_zero_testBit ha3 (i := 4) (by decide)
            rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
          · have t1 := land_eq_zero_testBit ha0 (i := 4) (by decide)
            have t2 := land_eq_zero_testBit ha3 (i := 4) (by decide)
            rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
          · have := land_eq_zero_testBit ha3 (i := 2) (by decide)
            rw [hb2] at this; exact Bool.noConfusion this
        have hnot_w3_A0 : isSup w3 maskA0 = false := by
          cases h : isSup w3 maskA0; rfl
          exfalso; unfold isSup at h; unfold isW3e1 at hw3
          simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h hw3
          rcases hw3 with ⟨ha3, hb1⟩ | ⟨ha3, hb1⟩ <;> rcases h with ⟨ha0, _⟩ | ⟨ha0, _⟩
          · have := land_eq_zero_testBit ha0 (i := 1) (by decide)
            rw [not32_testBit (by omega), hb1] at this; exact Bool.noConfusion this
          · have t1 := land_eq_zero_testBit ha0 (i := 4) (by decide)
            have t2 := land_eq_zero_testBit ha3 (i := 4) (by decide)
            rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
          · have t1 := land_eq_zero_testBit ha0 (i := 4) (by decide)
            have t2 := land_eq_zero_testBit ha3 (i := 4) (by decide)
            rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
          · have := land_eq_zero_testBit ha0 (i := 1) (by decide)
            rw [hb1] at this; exact Bool.noConfusion this
        have hnot_w0_67 : isW67e4 w0 = false := by
          cases h : isW67e4 w0; rfl
          exfalso
          have h6 : isW6e4 w0 = true := by
            unfold isW67e4 at h; unfold isW6e4
            simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h ⊢
            rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact Or.inl ⟨land_lor_eq_zero_left ha, hb⟩
            · exact Or.inr ⟨land_lor_eq_zero_left ha, hb⟩
          exact w0_ne_w6 hw0 h6
        have hnot_w3_67 : isW67e4 w3 = false := by
          cases h : isW67e4 w3; rfl
          exfalso
          have h6 : isW6e4 w3 = true := by
            unfold isW67e4 at h; unfold isW6e4
            simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h ⊢
            rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact Or.inl ⟨land_lor_eq_zero_left ha, hb⟩
            · exact Or.inr ⟨land_lor_eq_zero_left ha, hb⟩
          exact w3_ne_w6 hw3 h6
        have hnot_w6_A0 : isSup w6 maskA0 = false := by
          cases h : isSup w6 maskA0; rfl
          exfalso; unfold isSup at h; unfold isW6e4 at hw6
          simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h hw6
          rcases hw6 with ⟨ha6, hb4⟩ | ⟨ha6, hb4⟩ <;> rcases h with ⟨ha0, _⟩ | ⟨ha0, _⟩
          · have := land_eq_zero_testBit ha0 (i := 4) (by decide)
            rw [not32_testBit (by omega), hb4] at this; exact Bool.noConfusion this
          · have t1 := land_eq_zero_testBit ha0 (i := 1) (by decide)
            have t2 := land_eq_zero_testBit ha6 (i := 1) (by decide)
            rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
          · have t1 := land_eq_zero_testBit ha0 (i := 1) (by decide)
            have t2 := land_eq_zero_testBit ha6 (i := 1) (by decide)
            rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
          · have := land_eq_zero_testBit ha0 (i := 4) (by decide)
            rw [hb4] at this; exact Bool.noConfusion this
        have hnot_w6_A3 : isSup w6 maskA3 = false := by
          cases h : isSup w6 maskA3; rfl
          exfalso; unfold isSup at h; unfold isW6e4 at hw6
          simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h hw6
          rcases hw6 with ⟨ha6, hb4⟩ | ⟨ha6, hb4⟩ <;> rcases h with ⟨ha3, _⟩ | ⟨ha3, _⟩
          · have := land_eq_zero_testBit ha3 (i := 4) (by decide)
            rw [not32_testBit (by omega), hb4] at this; exact Bool.noConfusion this
          · have t1 := land_eq_zero_testBit ha3 (i := 16) (by decide)
            have t2 := land_eq_zero_testBit ha6 (i := 16) (by decide)
            rw [not32_testBit (by omega), t1] at t2; exact Bool.noConfusion t2
          · have t1 := land_eq_zero_testBit ha3 (i := 16) (by decide)
            have t2 := land_eq_zero_testBit ha6 (i := 16) (by decide)
            rw [not32_testBit (by omega), t2] at t1; exact Bool.noConfusion t1
          · have := land_eq_zero_testBit ha3 (i := 4) (by decide)
            rw [hb4] at this; exact Bool.noConfusion this
        have step1c_finish (h2m : g2 ∈ dedup ((stepAll (inList ++ [g0] ++ [g1])).filter fun w =>
              (!isSup g1 maskA0 && isSup w maskA0) || (!isSup g1 maskA3 && isSup w maskA3) || (!isW67e4 g1 && isW67e4 w)))
            (h3ok : ((! (isSup g1 maskA0 || isSup g2 maskA0) && isSup g3 maskA0) ||
                     (! (isSup g1 maskA3 || isSup g2 maskA3) && isSup g3 maskA3) ||
                     (! (isW67e4 g1 || isW67e4 g2) && isW67e4 g3)) = true) : False := by
          have hc3 := (List.all_eq_true.mp hc2) g2 h2m
          have hbad := (List.all_eq_true.mp hc3) g3 (by simpa [List.append_assoc] using hg3_step)
          rw [h3ok] at hbad; exact Bool.noConfusion hbad
        have hg2_step' : g2 ∈ stepAll (inList ++ [g0] ++ [g1]) := by
          simpa [List.append_assoc] using hg2_step
        rcases h0' with rfl | rfl | rfl <;> rcases h3' with h3e | h3e | h3e <;> rcases h6' with h6e | h6e | h6e
        all_goals
          first
          | exact (h03 h3e.symm).elim
          | exact (h06 h6e.symm).elim
          | exact (h36 (h3e.trans h6e.symm)).elim
          | (subst h3e; subst h6e; apply step1c_finish
             · rw [mem_dedup, List.mem_filter]
               exact ⟨hg2_step', by simp [isSup_of_isW0e2 hw0, isSup_of_isW3e1 hw3, hw67,
                 hnot_w0_A3, hnot_w3_A0, hnot_w0_67, hnot_w3_67, hnot_w6_A0, hnot_w6_A3]⟩
             · simp [isSup_of_isW0e2 hw0, isSup_of_isW3e1 hw3, hw67,
                 hnot_w0_A3, hnot_w3_A0, hnot_w0_67, hnot_w3_67, hnot_w6_A0, hnot_w6_A3])
  | _ :: _ :: _ :: _ :: _ :: _ => simp at hsh; omega

-- Main Theorem 2: No ValidPureSeq of length == 5 produces distinct w0, w3, w6, w7, s1!
theorem pureY_eq5_impossible (gs : List Nat) (hv : ValidPureSeq gs) (hlen : gs.length = 5)
    (w0 w3 w6 w7 s1 : Nat)
    (hm0 : w0 ∈ inList ++ gs) (hm3 : w3 ∈ inList ++ gs)
    (hm6 : w6 ∈ inList ++ gs) (hm7 : w7 ∈ inList ++ gs) (hms : s1 ∈ inList ++ gs)
    (hw0 : isW0e2 w0 = true) (hw3 : isW3e1 w3 = true)
    (hw6 : isW6e4 w6 = true) (hw7 : isW7e4 w7 = true) (hws : isS1 s1 = true)
    (h67 : w6 ≠ w7) (h0s : w0 ≠ s1) (h3s : w3 ≠ s1) (h6s : w6 ≠ s1) (h7s : w7 ≠ s1) : False := by
  obtain ⟨hs, hsh, hnd, hni, hvh, hcov⟩ := clean_pure_seq gs hv
  have lift (x : Nat) (hx : x ∈ inList ++ gs) : x ∈ inList ++ hs := by
    rcases List.mem_append.mp hx with hi | hg
    · exact List.mem_append_left _ hi
    · exact hcov x hg
  have hnot_in {x} (hx : isSup x maskA0 = true ∨ isSup x maskA3 = true ∨ isSup x maskA6 = true ∨ isSup x maskA7 = true ∨ isS1 x = true) :
      x ∉ inList := fun hi => by
    have h := (List.all_eq_true.mp no_L0) x hi
    rcases hx with h' | h' | h' | h' | h' <;> simp [h'] at h
  have h0m : w0 ∈ hs := (List.mem_append.mp (lift w0 hm0)).resolve_left (hnot_in (Or.inl (isSup_of_isW0e2 hw0)))
  have h3m : w3 ∈ hs := (List.mem_append.mp (lift w3 hm3)).resolve_left (hnot_in (Or.inr (Or.inl (isSup_of_isW3e1 hw3))))
  have h6m : w6 ∈ hs := (List.mem_append.mp (lift w6 hm6)).resolve_left (hnot_in (Or.inr (Or.inr (Or.inl (isSup_of_isW6e4 hw6)))))
  have h7m : w7 ∈ hs := (List.mem_append.mp (lift w7 hm7)).resolve_left (hnot_in (Or.inr (Or.inr (Or.inr (Or.inl (isSup_of_isW7e4 hw7))))))
  have hsm : s1 ∈ hs := (List.mem_append.mp (lift s1 hms)).resolve_left (hnot_in (Or.inr (Or.inr (Or.inr (Or.inr hws)))))
  have h03 : w0 ≠ w3 := fun e => w0_ne_w3 hw0 (e ▸ hw3)
  have h06 : w0 ≠ w6 := fun e => w0_ne_w6 hw0 (e ▸ hw6)
  have h07 : w0 ≠ w7 := fun e => w0_ne_w7 hw0 (e ▸ hw7)
  have h36 : w3 ≠ w6 := fun e => w3_ne_w6 hw3 (e ▸ hw6)
  have h37 : w3 ≠ w7 := fun e => w3_ne_w7 hw3 (e ▸ hw7)
  -- Since w0, w3, w6, w7, s1 are 5 distinct elements of hs and hs.length <= 5, hs.length = 5!
  have h5 : 5 ≤ hs.length := by
    have hsub : [w0, w3, w6, w7, s1] ⊆ hs := by
      intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hnd5 : ([w0, w3, w6, w7, s1] : List Nat).Nodup := by
      simp [h03, h06, h07, h0s, h36, h37, h3s, h67, h6s, h7s]
    exact List.Subperm.length_le (List.subperm_of_subset hnd5 hsub)
  have hslen : hs.length = 5 := by omega
  match hs with
  | [g0, g1, g2, g3, g4] =>
    have hmem5 : ∀ x ∈ [g0, g1, g2, g3, g4], x = w0 ∨ x = w3 ∨ x = w6 ∨ x = w7 ∨ x = s1 := by
      -- Since [w0, w3, w6, w7, s1] ⊆ [g0,g1,g2,g3,g4] both length 5 and Nodup, every element is in [w0,w3,w6,w7,s1]!
      have hnd5 : ([w0, w3, w6, w7, s1] : List Nat).Nodup := by
        simp [h03, h06, h07, h0s, h36, h37, h3s, h67, h6s, h7s]
      have hsub : [w0, w3, w6, w7, s1] ⊆ [g0, g1, g2, g3, g4] := by
        intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hperm : [w0, w3, w6, w7, s1].Perm [g0, g1, g2, g3, g4] :=
        (List.subperm_of_subset hnd5 hsub).perm_of_length_le (by simp)
      intro x hx
      have := hperm.mem_iff.mpr hx
      simpa using this
    have hg0L1 : g0 ∈ L1List := mem_L1List (by simpa using hvh 0 (by simp)) (hni g0 (by simp))
    have hg1_step : g1 ∈ stepAll (inList ++ [g0]) := by
      obtain ⟨a, ha, b, hb, hm⟩ := hvh 1 (by simp); exact mem_stepAll ha hb hm
    have hg2_step : g2 ∈ stepAll (inList ++ [g0, g1]) := by
      obtain ⟨a, ha, b, hb, hm⟩ := hvh 2 (by simp); exact mem_stepAll ha hb hm
    have hL1_bad := (List.all_eq_true.mp no_L1_A0_A3_S1) g0 hg0L1
    have hL1_uniq := (List.all_eq_true.mp uniq_L1_A6_A7) g0 hg0L1
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hL1_bad hL1_uniq
    -- g0 must be w6 (= wA6) or w7 (= wA7)!
    have hg0_67 : g0 = w6 ∨ g0 = w7 := by
      rcases hmem5 g0 (by simp) with rfl | rfl | rfl | rfl | rfl
      · exact (Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hL1_bad.1.1))
      · exact (Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hL1_bad.1.2))
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (Bool.noConfusion (hws.symm.trans hL1_bad.2))
    have hg0_ne_g1 : g0 ≠ g1 := (List.nodup_cons.mp hnd).1 |> fun h e => h (by simp [e])
    have hg0_ne_g2 : g0 ≠ g2 := (List.nodup_cons.mp hnd).1 |> fun h e => h (by simp [e])
    have hg1_ne_g2 : g1 ≠ g2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 |> fun h e => h (by simp [e])
    rcases hg0_67 with hg0w6 | hg0w7
    · have hg0A6 : g0 = wA6 := hL1_uniq.1.resolve_left (by simp [hg0w6, hw6])
      have hs1 := (List.all_eq_true.mp step_from_A6_only_A7) g1 (hg0A6 ▸ hg1_step)
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hs1
      have hg1_step' : g1 ∈ stepAll (inList ++ [wA6, wA7]) :=
        stepAll_mono (fun x hx => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          rcases hx with h | rfl
          · exact Or.inl h
          · exact Or.inr (Or.inl rfl)) (hg0A6 ▸ hg1_step)
      have hs1' := (List.all_eq_true.mp no_step_from_A6_A7) g1 hg1_step'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs1'
      have hg1w7 : g1 = w7 := by
        rcases hmem5 g1 (by simp) with rfl | rfl | rfl | rfl | rfl
        · exact Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hs1'.1.1)
        · exact Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hs1'.1.2)
        · exact (hg0_ne_g1 hg0w6).elim
        · rfl
        · exact Bool.noConfusion (hws.symm.trans hs1'.2)
      have hg1A7 : g1 = wA7 := hs1.2.resolve_left (by simp [hg1w7, hw7])
      have hs2 := (List.all_eq_true.mp no_step_from_A6_A7) g2 (hg0A6 ▸ hg1A7 ▸ hg2_step)
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs2
      rcases hmem5 g2 (by simp) with rfl | rfl | rfl | rfl | rfl
      · exact Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hs2.1.1)
      · exact Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hs2.1.2)
      · exact (hg0_ne_g2 hg0w6).elim
      · exact (hg1_ne_g2 hg1w7).elim
      · exact Bool.noConfusion (hws.symm.trans hs2.2)
    · have hg0A7 : g0 = wA7 := hL1_uniq.2.resolve_left (by simp [hg0w7, hw7])
      have hs1 := (List.all_eq_true.mp step_from_A7_only_A6) g1 (hg0A7 ▸ hg1_step)
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hs1
      have hg1_step' : g1 ∈ stepAll (inList ++ [wA6, wA7]) :=
        stepAll_mono (fun x hx => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          rcases hx with h | rfl
          · exact Or.inl h
          · exact Or.inr (Or.inr rfl)) (hg0A7 ▸ hg1_step)
      have hs1' := (List.all_eq_true.mp no_step_from_A6_A7) g1 hg1_step'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs1'
      have hg1w6 : g1 = w6 := by
        rcases hmem5 g1 (by simp) with rfl | rfl | rfl | rfl | rfl
        · exact Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hs1'.1.1)
        · exact Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hs1'.1.2)
        · rfl
        · exact (hg0_ne_g1 hg0w7).elim
        · exact Bool.noConfusion (hws.symm.trans hs1'.2)
      have hg1A6 : g1 = wA6 := hs1.2.resolve_left (by simp [hg1w6, hw6])
      have hg2_step' : g2 ∈ stepAll (inList ++ [wA6, wA7]) :=
        stepAll_mono (fun x hx => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
          rcases hx with h | rfl | rfl
          · exact Or.inl h
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)) (hg0A7 ▸ hg1A6 ▸ hg2_step)
      have hs2 := (List.all_eq_true.mp no_step_from_A6_A7) g2 hg2_step'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs2
      rcases hmem5 g2 (by simp) with rfl | rfl | rfl | rfl | rfl
      · exact Bool.noConfusion ((isSup_of_isW0e2 hw0).symm.trans hs2.1.1)
      · exact Bool.noConfusion ((isSup_of_isW3e1 hw3).symm.trans hs2.1.2)
      · exact (hg1_ne_g2 hg1w6).elim
      · exact (hg0_ne_g2 hg0w7).elim
      · exact Bool.noConfusion (hws.symm.trans hs2.2)


end PureY2940


namespace CaseA2940

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutFormula PetersenCutIndependent
open PetersenFirstGroup PetersenCutTrace PetersenScratch
open XTree2940 PureY2940

def target9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def row9 (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

def pairsA : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def contextsA (e : Fin 9 × Fin 9) : Nat × Nat :=
  match e.1.val, e.2.val with
  | 0, 1 => (0, 20)
  | 1, 2 => (0, 9)
  | 2, 3 => (0, 18)
  | 3, 4 => (0, 5)
  | 4, 0 => (0, 10)
  | 0, 5 => (0, 130)
  | 1, 6 => (0, 257)
  | 2, 7 => (0, 34)
  | 3, 8 => (0, 36)
  | 5, 7 => (0, 5)
  | 6, 8 => (0, 10)
  | _, _ => (0, 9)

lemma checkedContextsA : ∀ e ∈ pairsA, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (row9 (contextsA e).1) a b
    let xo := pairInput e.1 e.2 (row9 (contextsA e).2) a b
    target9 xa = (a && b) ∧ target9 xo = (a || b) := by
  decide +kernel

theorem boundaryConflictA {gs : List Gate} (clean : CleanL 9 gs)
    (out : Fin (9 + gs.length))
    (live : ∀ w : Fin (9 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 9 → Bool, vl gs x out.val = target9 x)
    (e : Fin 9 × Fin 9) (he : e ∈ pairsA) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 9, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]; exact same.symm
  have factor (base : Fin 9 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor (row9 (contextsA e).1)
  obtain ⟨fo, ho⟩ := factor (row9 (contextsA e).2)
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h := checkedContextsA e he a b
    exact (ha a b).trans ((computes _).trans h.1)
  · intro a b
    have h := checkedContextsA e he a b
    exact (ho a b).trans ((computes _).trans h.2)

abbrev cubeA (i j k : Fin 9) (a b c : ℕ) : Prop :=
  let hi m := Function.update (row9 m) k true
  (∀ v, v ≠ i → v ≠ j → row9 a v = row9 b v ∧ row9 b v = row9 c v) ∧
  target9 (row9 a) ≠ target9 (row9 b) ∧ target9 (hi a) ≠ target9 (hi c) ∧ target9 (hi b) ≠ target9 (hi c)

def cubesAList : List (Fin 9 × Fin 9 × Fin 9 × ℕ × ℕ × ℕ) := [
  (0, 2, 4, 132, 129, 128),
  (0, 2, 5, 12, 9, 8),
  (0, 2, 7, 20, 17, 16),
  (0, 3, 4, 10, 3, 2),
  (0, 3, 5, 12, 5, 4),
  (0, 3, 8, 10, 3, 2),
  (0, 6, 1, 80, 17, 16),
  (0, 6, 4, 320, 257, 256),
  (0, 7, 4, 132, 5, 4),
  (0, 7, 5, 130, 3, 2),
  (0, 8, 3, 258, 3, 2),
  (0, 8, 4, 320, 65, 64),
  (0, 8, 6, 272, 17, 16),
  (1, 3, 4, 72, 66, 64),
  (1, 3, 6, 24, 18, 16),
  (1, 3, 8, 9, 3, 1),
  (1, 4, 0, 20, 6, 4),
  (1, 4, 6, 24, 10, 8),
  (1, 5, 6, 160, 130, 128),
  (1, 5, 7, 96, 66, 64),
  (1, 5, 8, 36, 6, 4),
  (1, 7, 2, 129, 3, 1),
  (1, 7, 6, 160, 34, 32),
  (1, 8, 3, 257, 3, 1),
  (1, 8, 5, 260, 6, 4),
  (1, 8, 6, 257, 3, 1),
  (2, 4, 0, 144, 132, 128),
  (2, 4, 3, 17, 5, 1),
  (2, 4, 7, 17, 5, 1),
  (2, 5, 3, 33, 5, 1),
  (2, 5, 7, 33, 5, 1),
  (2, 5, 8, 34, 6, 2),
  (2, 6, 1, 72, 12, 8),
  (2, 6, 7, 320, 260, 256),
  (2, 8, 3, 258, 6, 2),
  (2, 8, 5, 258, 6, 2),
  (2, 8, 7, 320, 68, 64),
  (3, 5, 2, 33, 9, 1),
  (3, 5, 7, 48, 24, 16),
  (3, 5, 8, 33, 9, 1),
  (3, 6, 1, 80, 24, 16),
  (3, 6, 4, 66, 10, 2),
  (3, 6, 8, 66, 10, 2),
  (3, 7, 2, 144, 24, 16),
  (3, 7, 4, 160, 40, 32),
  (3, 7, 5, 144, 24, 16),
  (4, 5, 0, 40, 24, 8),
  (4, 5, 7, 40, 24, 8),
  (4, 6, 1, 72, 24, 8),
  (4, 6, 3, 66, 18, 2),
  (4, 6, 8, 65, 17, 1),
  (4, 7, 2, 129, 17, 1),
  (4, 7, 3, 160, 48, 32),
  (4, 7, 5, 136, 24, 8),
  (4, 8, 0, 320, 80, 64),
  (4, 8, 3, 257, 17, 1),
  (4, 8, 6, 257, 17, 1),
  (5, 6, 1, 192, 160, 128),
  (5, 6, 7, 66, 34, 2),
  (5, 6, 8, 65, 33, 1),
  (6, 7, 2, 384, 320, 256),
  (6, 7, 5, 130, 66, 2),
  (6, 7, 8, 132, 68, 4),
  (7, 8, 2, 320, 192, 64),
  (7, 8, 5, 260, 132, 4),
  (7, 8, 6, 260, 132, 4)
]

lemma checkedCubesA : ∀ q ∈ cubesAList, cubeA q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 := by
  decide +kernel

def CutA (label : Fin 9 → Fin 6) (t : Fin 6) : Prop :=
  ∃ code : (Fin 9 → Bool) → Bool,
    (∀ x y, (∀ i, label i ≤ t → x i = y i) → code x = code y) ∧
    (∀ x y, (∀ i, label i ≠ t → x i = y i) → code x = code y → target9 x = target9 y)

lemma cubeBoundA (label : Fin 9 → Fin 6) (cut : ∀ t, CutA label t)
    (i j k : Fin 9) (a b c : ℕ) (hw : cubeA i j k a b c) :
    label i = label j → label k ≤ label i := by
  intro hh
  by_contra hle
  have hlt : label i < label k := lt_of_not_ge hle
  obtain ⟨code, low, high⟩ := cut (label i)
  obtain ⟨same, nab, nac, nbc⟩ := hw
  let hi (m : ℕ) := Function.update (row9 m) k true
  have aux (m : ℕ) : code (hi m) = code (row9 m) := by
    apply low
    intro u hu
    have hne : u ≠ k := by rintro rfl; exact (not_le_of_gt hlt) hu
    exact Function.update_of_ne hne _ _
  have off {u} (h : label u ≠ label i) : u ≠ i ∧ u ≠ j :=
    ⟨fun he => h (he ▸ rfl), fun he => h (he ▸ hh.symm)⟩
  have hab : code (row9 a) ≠ code (row9 b) := fun e =>
    nab (high _ _ (fun u hu => (same u (off hu).1 (off hu).2).1) e)
  have lift {m n : ℕ} (h : ∀ u, label u ≠ label i → row9 m u = row9 n u) :
      ∀ u, label u ≠ label i → hi m u = hi n u := by
    intro u hu
    by_cases eq : u = k
    · subst u; simp [hi]
    · simpa [hi, Function.update_of_ne eq] using h u hu
  have hac : code (row9 a) ≠ code (row9 c) := fun e =>
    nac (high _ _ (lift (fun u hu => ((same u (off hu).1 (off hu).2).1).trans
      (same u (off hu).1 (off hu).2).2)) ((aux a).trans (e.trans (aux c).symm)))
  have hbc : code (row9 b) ≠ code (row9 c) := fun e =>
    nbc (high _ _ (lift (fun u hu => (same u (off hu).1 (off hu).2).2))
      ((aux b).trans (e.trans (aux c).symm)))
  cases ha : code (row9 a) <;> cases hb : code (row9 b) <;> cases hc : code (row9 c) <;> simp_all

def chkA_leaf (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x5 : Nat) (x8 : Nat) (x4 : Nat) (x6 : Nat) (x7 : Nat) : Bool :=
  (x0 == 5 && x3 == 5 && x6 == 5 && x7 == 5) || (x1 == 5 && x4 == 5 && x7 == 5 && x8 == 5) || (x2 == 5 && x4 == 5 && x5 == 5 && x6 == 5)

def chkA_s8 (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x5 : Nat) (x8 : Nat) (x4 : Nat) (x6 : Nat) : Bool :=
  (let x7 := 0; (!((x2 != x7) && (x5 != x7) && (!(x0 == x2) || decide (x7 ≤ x0)) && (!(x0 == x7) || decide (x4 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0)) && (!(x1 == x5) || decide (x7 ≤ x1)) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x6) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x4 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3)) && (!(x4 == x5) || decide (x7 ≤ x4)) && (!(x4 == x7) || decide (x2 ≤ x4)) && (!(x4 == x7) || decide (x3 ≤ x4)) && (!(x4 == x7) || decide (x5 ≤ x4)) && (!(x5 == x6) || decide (x7 ≤ x5)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x6 == x7) || decide (x8 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7)) && (!(x7 == x8) || decide (x6 ≤ x7))) || chkA_leaf x0 x1 x2 x3 x5 x8 x4 x6 x7)) &&
  (let x7 := 1; (!((x2 != x7) && (x5 != x7) && (!(x0 == x2) || decide (x7 ≤ x0)) && (!(x0 == x7) || decide (x4 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0)) && (!(x1 == x5) || decide (x7 ≤ x1)) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x6) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x4 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3)) && (!(x4 == x5) || decide (x7 ≤ x4)) && (!(x4 == x7) || decide (x2 ≤ x4)) && (!(x4 == x7) || decide (x3 ≤ x4)) && (!(x4 == x7) || decide (x5 ≤ x4)) && (!(x5 == x6) || decide (x7 ≤ x5)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x6 == x7) || decide (x8 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7)) && (!(x7 == x8) || decide (x6 ≤ x7))) || chkA_leaf x0 x1 x2 x3 x5 x8 x4 x6 x7)) &&
  (let x7 := 2; (!((x2 != x7) && (x5 != x7) && (!(x0 == x2) || decide (x7 ≤ x0)) && (!(x0 == x7) || decide (x4 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0)) && (!(x1 == x5) || decide (x7 ≤ x1)) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x6) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x4 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3)) && (!(x4 == x5) || decide (x7 ≤ x4)) && (!(x4 == x7) || decide (x2 ≤ x4)) && (!(x4 == x7) || decide (x3 ≤ x4)) && (!(x4 == x7) || decide (x5 ≤ x4)) && (!(x5 == x6) || decide (x7 ≤ x5)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x6 == x7) || decide (x8 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7)) && (!(x7 == x8) || decide (x6 ≤ x7))) || chkA_leaf x0 x1 x2 x3 x5 x8 x4 x6 x7)) &&
  (let x7 := 3; (!((x2 != x7) && (x5 != x7) && (!(x0 == x2) || decide (x7 ≤ x0)) && (!(x0 == x7) || decide (x4 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0)) && (!(x1 == x5) || decide (x7 ≤ x1)) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x6) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x4 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3)) && (!(x4 == x5) || decide (x7 ≤ x4)) && (!(x4 == x7) || decide (x2 ≤ x4)) && (!(x4 == x7) || decide (x3 ≤ x4)) && (!(x4 == x7) || decide (x5 ≤ x4)) && (!(x5 == x6) || decide (x7 ≤ x5)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x6 == x7) || decide (x8 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7)) && (!(x7 == x8) || decide (x6 ≤ x7))) || chkA_leaf x0 x1 x2 x3 x5 x8 x4 x6 x7)) &&
  (let x7 := 4; (!((x2 != x7) && (x5 != x7) && (!(x0 == x2) || decide (x7 ≤ x0)) && (!(x0 == x7) || decide (x4 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0)) && (!(x1 == x5) || decide (x7 ≤ x1)) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x6) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x4 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3)) && (!(x4 == x5) || decide (x7 ≤ x4)) && (!(x4 == x7) || decide (x2 ≤ x4)) && (!(x4 == x7) || decide (x3 ≤ x4)) && (!(x4 == x7) || decide (x5 ≤ x4)) && (!(x5 == x6) || decide (x7 ≤ x5)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x6 == x7) || decide (x8 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7)) && (!(x7 == x8) || decide (x6 ≤ x7))) || chkA_leaf x0 x1 x2 x3 x5 x8 x4 x6 x7)) &&
  (let x7 := 5; (!((x2 != x7) && (x5 != x7) && (!(x0 == x2) || decide (x7 ≤ x0)) && (!(x0 == x7) || decide (x4 ≤ x0)) && (!(x0 == x7) || decide (x5 ≤ x0)) && (!(x1 == x5) || decide (x7 ≤ x1)) && (!(x1 == x7) || decide (x2 ≤ x1)) && (!(x1 == x7) || decide (x6 ≤ x1)) && (!(x2 == x4) || decide (x7 ≤ x2)) && (!(x2 == x5) || decide (x7 ≤ x2)) && (!(x2 == x6) || decide (x7 ≤ x2)) && (!(x2 == x8) || decide (x7 ≤ x2)) && (!(x3 == x5) || decide (x7 ≤ x3)) && (!(x3 == x7) || decide (x2 ≤ x3)) && (!(x3 == x7) || decide (x4 ≤ x3)) && (!(x3 == x7) || decide (x5 ≤ x3)) && (!(x4 == x5) || decide (x7 ≤ x4)) && (!(x4 == x7) || decide (x2 ≤ x4)) && (!(x4 == x7) || decide (x3 ≤ x4)) && (!(x4 == x7) || decide (x5 ≤ x4)) && (!(x5 == x6) || decide (x7 ≤ x5)) && (!(x6 == x7) || decide (x2 ≤ x6)) && (!(x6 == x7) || decide (x5 ≤ x6)) && (!(x6 == x7) || decide (x8 ≤ x6)) && (!(x7 == x8) || decide (x2 ≤ x7)) && (!(x7 == x8) || decide (x5 ≤ x7)) && (!(x7 == x8) || decide (x6 ≤ x7))) || chkA_leaf x0 x1 x2 x3 x5 x8 x4 x6 x7))

def chkA_s7 (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x5 : Nat) (x8 : Nat) (x4 : Nat) : Bool :=
  (let x6 := 0; (!((x1 != x6) && (x6 != x8) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x6) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x6 ≤ x0)) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x4) || decide (x6 ≤ x1)) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x4 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x4 == x6) || decide (x1 ≤ x4)) && (!(x4 == x6) || decide (x3 ≤ x4)) && (!(x4 == x6) || decide (x8 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkA_s8 x0 x1 x2 x3 x5 x8 x4 x6)) &&
  (let x6 := 1; (!((x1 != x6) && (x6 != x8) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x6) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x6 ≤ x0)) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x4) || decide (x6 ≤ x1)) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x4 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x4 == x6) || decide (x1 ≤ x4)) && (!(x4 == x6) || decide (x3 ≤ x4)) && (!(x4 == x6) || decide (x8 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkA_s8 x0 x1 x2 x3 x5 x8 x4 x6)) &&
  (let x6 := 2; (!((x1 != x6) && (x6 != x8) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x6) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x6 ≤ x0)) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x4) || decide (x6 ≤ x1)) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x4 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x4 == x6) || decide (x1 ≤ x4)) && (!(x4 == x6) || decide (x3 ≤ x4)) && (!(x4 == x6) || decide (x8 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkA_s8 x0 x1 x2 x3 x5 x8 x4 x6)) &&
  (let x6 := 3; (!((x1 != x6) && (x6 != x8) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x6) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x6 ≤ x0)) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x4) || decide (x6 ≤ x1)) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x4 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x4 == x6) || decide (x1 ≤ x4)) && (!(x4 == x6) || decide (x3 ≤ x4)) && (!(x4 == x6) || decide (x8 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkA_s8 x0 x1 x2 x3 x5 x8 x4 x6)) &&
  (let x6 := 4; (!((x1 != x6) && (x6 != x8) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x6) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x6 ≤ x0)) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x4) || decide (x6 ≤ x1)) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x4 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x4 == x6) || decide (x1 ≤ x4)) && (!(x4 == x6) || decide (x3 ≤ x4)) && (!(x4 == x6) || decide (x8 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkA_s8 x0 x1 x2 x3 x5 x8 x4 x6)) &&
  (let x6 := 5; (!((x1 != x6) && (x6 != x8) && (!(x0 == x6) || decide (x1 ≤ x0)) && (!(x0 == x6) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x6 ≤ x0)) && (!(x1 == x3) || decide (x6 ≤ x1)) && (!(x1 == x4) || decide (x6 ≤ x1)) && (!(x1 == x5) || decide (x6 ≤ x1)) && (!(x1 == x8) || decide (x6 ≤ x1)) && (!(x2 == x6) || decide (x1 ≤ x2)) && (!(x3 == x6) || decide (x1 ≤ x3)) && (!(x3 == x6) || decide (x4 ≤ x3)) && (!(x3 == x6) || decide (x8 ≤ x3)) && (!(x4 == x6) || decide (x1 ≤ x4)) && (!(x4 == x6) || decide (x3 ≤ x4)) && (!(x4 == x6) || decide (x8 ≤ x4)) && (!(x4 == x8) || decide (x6 ≤ x4)) && (!(x5 == x6) || decide (x1 ≤ x5)) && (!(x5 == x6) || decide (x8 ≤ x5))) || chkA_s8 x0 x1 x2 x3 x5 x8 x4 x6))

def chkA_s6 (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x5 : Nat) (x8 : Nat) : Bool :=
  (let x4 := 0; (!((x3 != x4) && (x4 != x0) && (!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x3) || decide (x4 ≤ x1)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x0 ≤ x2)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4))) || chkA_s7 x0 x1 x2 x3 x5 x8 x4)) &&
  (let x4 := 1; (!((x3 != x4) && (x4 != x0) && (!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x3) || decide (x4 ≤ x1)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x0 ≤ x2)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4))) || chkA_s7 x0 x1 x2 x3 x5 x8 x4)) &&
  (let x4 := 2; (!((x3 != x4) && (x4 != x0) && (!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x3) || decide (x4 ≤ x1)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x0 ≤ x2)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4))) || chkA_s7 x0 x1 x2 x3 x5 x8 x4)) &&
  (let x4 := 3; (!((x3 != x4) && (x4 != x0) && (!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x3) || decide (x4 ≤ x1)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x0 ≤ x2)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4))) || chkA_s7 x0 x1 x2 x3 x5 x8 x4)) &&
  (let x4 := 4; (!((x3 != x4) && (x4 != x0) && (!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x3) || decide (x4 ≤ x1)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x0 ≤ x2)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4))) || chkA_s7 x0 x1 x2 x3 x5 x8 x4)) &&
  (let x4 := 5; (!((x3 != x4) && (x4 != x0) && (!(x0 == x2) || decide (x4 ≤ x0)) && (!(x0 == x3) || decide (x4 ≤ x0)) && (!(x0 == x8) || decide (x4 ≤ x0)) && (!(x1 == x3) || decide (x4 ≤ x1)) && (!(x1 == x4) || decide (x0 ≤ x1)) && (!(x2 == x4) || decide (x0 ≤ x2)) && (!(x2 == x4) || decide (x3 ≤ x2)) && (!(x4 == x5) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x0 ≤ x4)) && (!(x4 == x8) || decide (x3 ≤ x4))) || chkA_s7 x0 x1 x2 x3 x5 x8 x4))

def chkA_s5 (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x5 : Nat) : Bool :=
  (let x8 := 0; (!((x3 != x8) && (x8 != x5) && (!(x0 == x3) || decide (x8 ≤ x0)) && (!(x0 == x8) || decide (x3 ≤ x0)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x3 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2)) && (!(x3 == x5) || decide (x8 ≤ x3))) || chkA_s6 x0 x1 x2 x3 x5 x8)) &&
  (let x8 := 1; (!((x3 != x8) && (x8 != x5) && (!(x0 == x3) || decide (x8 ≤ x0)) && (!(x0 == x8) || decide (x3 ≤ x0)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x3 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2)) && (!(x3 == x5) || decide (x8 ≤ x3))) || chkA_s6 x0 x1 x2 x3 x5 x8)) &&
  (let x8 := 2; (!((x3 != x8) && (x8 != x5) && (!(x0 == x3) || decide (x8 ≤ x0)) && (!(x0 == x8) || decide (x3 ≤ x0)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x3 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2)) && (!(x3 == x5) || decide (x8 ≤ x3))) || chkA_s6 x0 x1 x2 x3 x5 x8)) &&
  (let x8 := 3; (!((x3 != x8) && (x8 != x5) && (!(x0 == x3) || decide (x8 ≤ x0)) && (!(x0 == x8) || decide (x3 ≤ x0)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x3 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2)) && (!(x3 == x5) || decide (x8 ≤ x3))) || chkA_s6 x0 x1 x2 x3 x5 x8)) &&
  (let x8 := 4; (!((x3 != x8) && (x8 != x5) && (!(x0 == x3) || decide (x8 ≤ x0)) && (!(x0 == x8) || decide (x3 ≤ x0)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x3 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2)) && (!(x3 == x5) || decide (x8 ≤ x3))) || chkA_s6 x0 x1 x2 x3 x5 x8)) &&
  (let x8 := 5; (!((x3 != x8) && (x8 != x5) && (!(x0 == x3) || decide (x8 ≤ x0)) && (!(x0 == x8) || decide (x3 ≤ x0)) && (!(x1 == x3) || decide (x8 ≤ x1)) && (!(x1 == x5) || decide (x8 ≤ x1)) && (!(x1 == x8) || decide (x3 ≤ x1)) && (!(x1 == x8) || decide (x5 ≤ x1)) && (!(x2 == x5) || decide (x8 ≤ x2)) && (!(x2 == x8) || decide (x3 ≤ x2)) && (!(x2 == x8) || decide (x5 ≤ x2)) && (!(x3 == x5) || decide (x8 ≤ x3))) || chkA_s6 x0 x1 x2 x3 x5 x8))

def chkA_s4 (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) : Bool :=
  (let x5 := 0; (!((x0 != x5) && (!(x0 == x2) || decide (x5 ≤ x0)) && (!(x0 == x3) || decide (x5 ≤ x0)) && (!(x2 == x5) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3))) || chkA_s5 x0 x1 x2 x3 x5)) &&
  (let x5 := 1; (!((x0 != x5) && (!(x0 == x2) || decide (x5 ≤ x0)) && (!(x0 == x3) || decide (x5 ≤ x0)) && (!(x2 == x5) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3))) || chkA_s5 x0 x1 x2 x3 x5)) &&
  (let x5 := 2; (!((x0 != x5) && (!(x0 == x2) || decide (x5 ≤ x0)) && (!(x0 == x3) || decide (x5 ≤ x0)) && (!(x2 == x5) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3))) || chkA_s5 x0 x1 x2 x3 x5)) &&
  (let x5 := 3; (!((x0 != x5) && (!(x0 == x2) || decide (x5 ≤ x0)) && (!(x0 == x3) || decide (x5 ≤ x0)) && (!(x2 == x5) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3))) || chkA_s5 x0 x1 x2 x3 x5)) &&
  (let x5 := 4; (!((x0 != x5) && (!(x0 == x2) || decide (x5 ≤ x0)) && (!(x0 == x3) || decide (x5 ≤ x0)) && (!(x2 == x5) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3))) || chkA_s5 x0 x1 x2 x3 x5)) &&
  (let x5 := 5; (!((x0 != x5) && (!(x0 == x2) || decide (x5 ≤ x0)) && (!(x0 == x3) || decide (x5 ≤ x0)) && (!(x2 == x5) || decide (x3 ≤ x2)) && (!(x3 == x5) || decide (x2 ≤ x3))) || chkA_s5 x0 x1 x2 x3 x5))

def chkA_s3 (x0 : Nat) (x1 : Nat) (x2 : Nat) : Bool :=
  (let x3 := 0; (!((x2 != x3)) || chkA_s4 x0 x1 x2 x3)) &&
  (let x3 := 1; (!((x2 != x3)) || chkA_s4 x0 x1 x2 x3)) &&
  (let x3 := 2; (!((x2 != x3)) || chkA_s4 x0 x1 x2 x3)) &&
  (let x3 := 3; (!((x2 != x3)) || chkA_s4 x0 x1 x2 x3)) &&
  (let x3 := 4; (!((x2 != x3)) || chkA_s4 x0 x1 x2 x3)) &&
  (let x3 := 5; (!((x2 != x3)) || chkA_s4 x0 x1 x2 x3))

def chkA_s2 (x0 : Nat) (x1 : Nat) : Bool :=
  (let x2 := 0; (!((x1 != x2)) || chkA_s3 x0 x1 x2)) &&
  (let x2 := 1; (!((x1 != x2)) || chkA_s3 x0 x1 x2)) &&
  (let x2 := 2; (!((x1 != x2)) || chkA_s3 x0 x1 x2)) &&
  (let x2 := 3; (!((x1 != x2)) || chkA_s3 x0 x1 x2)) &&
  (let x2 := 4; (!((x1 != x2)) || chkA_s3 x0 x1 x2)) &&
  (let x2 := 5; (!((x1 != x2)) || chkA_s3 x0 x1 x2))

def chkA_s1 (x0 : Nat) : Bool :=
  (let x1 := 0; (!((x0 != x1)) || chkA_s2 x0 x1)) &&
  (let x1 := 1; (!((x0 != x1)) || chkA_s2 x0 x1)) &&
  (let x1 := 2; (!((x0 != x1)) || chkA_s2 x0 x1)) &&
  (let x1 := 3; (!((x0 != x1)) || chkA_s2 x0 x1)) &&
  (let x1 := 4; (!((x0 != x1)) || chkA_s2 x0 x1)) &&
  (let x1 := 5; (!((x0 != x1)) || chkA_s2 x0 x1))

def chkA_s0  : Bool :=
  (let x0 := 0; chkA_s1 x0) &&
  (let x0 := 1; chkA_s1 x0) &&
  (let x0 := 2; chkA_s1 x0) &&
  (let x0 := 3; chkA_s1 x0) &&
  (let x0 := 4; chkA_s1 x0) &&
  (let x0 := 5; chkA_s1 x0)


set_option maxHeartbeats 8000000 in
theorem chkA_ok : chkA_s0 = true := by decide +kernel

lemma chkA_sound (f : Fin 9 → Fin 6)
    (hc0 : f 0 ≠ f 1)
    (hc1 : f 1 ≠ f 2)
    (hc2 : f 2 ≠ f 3)
    (hc3 : f 3 ≠ f 4)
    (hc4 : f 4 ≠ f 0)
    (hc5 : f 0 ≠ f 5)
    (hc6 : f 1 ≠ f 6)
    (hc7 : f 2 ≠ f 7)
    (hc8 : f 3 ≠ f 8)
    (hc9 : f 5 ≠ f 7)
    (hc10 : f 6 ≠ f 8)
    (hc11 : f 8 ≠ f 5)
    (hq0 : f 0 = f 2 → f 4 ≤ f 0)
    (hq1 : f 0 = f 2 → f 5 ≤ f 0)
    (hq2 : f 0 = f 2 → f 7 ≤ f 0)
    (hq3 : f 0 = f 3 → f 4 ≤ f 0)
    (hq4 : f 0 = f 3 → f 5 ≤ f 0)
    (hq5 : f 0 = f 3 → f 8 ≤ f 0)
    (hq6 : f 0 = f 6 → f 1 ≤ f 0)
    (hq7 : f 0 = f 6 → f 4 ≤ f 0)
    (hq8 : f 0 = f 7 → f 4 ≤ f 0)
    (hq9 : f 0 = f 7 → f 5 ≤ f 0)
    (hq10 : f 0 = f 8 → f 3 ≤ f 0)
    (hq11 : f 0 = f 8 → f 4 ≤ f 0)
    (hq12 : f 0 = f 8 → f 6 ≤ f 0)
    (hq13 : f 1 = f 3 → f 4 ≤ f 1)
    (hq14 : f 1 = f 3 → f 6 ≤ f 1)
    (hq15 : f 1 = f 3 → f 8 ≤ f 1)
    (hq16 : f 1 = f 4 → f 0 ≤ f 1)
    (hq17 : f 1 = f 4 → f 6 ≤ f 1)
    (hq18 : f 1 = f 5 → f 6 ≤ f 1)
    (hq19 : f 1 = f 5 → f 7 ≤ f 1)
    (hq20 : f 1 = f 5 → f 8 ≤ f 1)
    (hq21 : f 1 = f 7 → f 2 ≤ f 1)
    (hq22 : f 1 = f 7 → f 6 ≤ f 1)
    (hq23 : f 1 = f 8 → f 3 ≤ f 1)
    (hq24 : f 1 = f 8 → f 5 ≤ f 1)
    (hq25 : f 1 = f 8 → f 6 ≤ f 1)
    (hq26 : f 2 = f 4 → f 0 ≤ f 2)
    (hq27 : f 2 = f 4 → f 3 ≤ f 2)
    (hq28 : f 2 = f 4 → f 7 ≤ f 2)
    (hq29 : f 2 = f 5 → f 3 ≤ f 2)
    (hq30 : f 2 = f 5 → f 7 ≤ f 2)
    (hq31 : f 2 = f 5 → f 8 ≤ f 2)
    (hq32 : f 2 = f 6 → f 1 ≤ f 2)
    (hq33 : f 2 = f 6 → f 7 ≤ f 2)
    (hq34 : f 2 = f 8 → f 3 ≤ f 2)
    (hq35 : f 2 = f 8 → f 5 ≤ f 2)
    (hq36 : f 2 = f 8 → f 7 ≤ f 2)
    (hq37 : f 3 = f 5 → f 2 ≤ f 3)
    (hq38 : f 3 = f 5 → f 7 ≤ f 3)
    (hq39 : f 3 = f 5 → f 8 ≤ f 3)
    (hq40 : f 3 = f 6 → f 1 ≤ f 3)
    (hq41 : f 3 = f 6 → f 4 ≤ f 3)
    (hq42 : f 3 = f 6 → f 8 ≤ f 3)
    (hq43 : f 3 = f 7 → f 2 ≤ f 3)
    (hq44 : f 3 = f 7 → f 4 ≤ f 3)
    (hq45 : f 3 = f 7 → f 5 ≤ f 3)
    (hq46 : f 4 = f 5 → f 0 ≤ f 4)
    (hq47 : f 4 = f 5 → f 7 ≤ f 4)
    (hq48 : f 4 = f 6 → f 1 ≤ f 4)
    (hq49 : f 4 = f 6 → f 3 ≤ f 4)
    (hq50 : f 4 = f 6 → f 8 ≤ f 4)
    (hq51 : f 4 = f 7 → f 2 ≤ f 4)
    (hq52 : f 4 = f 7 → f 3 ≤ f 4)
    (hq53 : f 4 = f 7 → f 5 ≤ f 4)
    (hq54 : f 4 = f 8 → f 0 ≤ f 4)
    (hq55 : f 4 = f 8 → f 3 ≤ f 4)
    (hq56 : f 4 = f 8 → f 6 ≤ f 4)
    (hq57 : f 5 = f 6 → f 1 ≤ f 5)
    (hq58 : f 5 = f 6 → f 7 ≤ f 5)
    (hq59 : f 5 = f 6 → f 8 ≤ f 5)
    (hq60 : f 6 = f 7 → f 2 ≤ f 6)
    (hq61 : f 6 = f 7 → f 5 ≤ f 6)
    (hq62 : f 6 = f 7 → f 8 ≤ f 6)
    (hq63 : f 7 = f 8 → f 2 ≤ f 7)
    (hq64 : f 7 = f 8 → f 5 ≤ f 7)
    (hq65 : f 7 = f 8 → f 6 ≤ f 7)
    (hok : chkA_s0 = true) : (f 0 = 5 ∧ f 3 = 5 ∧ f 6 = 5 ∧ f 7 = 5) ∨ (f 1 = 5 ∧ f 4 = 5 ∧ f 7 = 5 ∧ f 8 = 5) ∨ (f 2 = 5 ∧ f 4 = 5 ∧ f 5 = 5 ∧ f 6 = 5) := by
  have h0 : chkA_s1 (f 0).val = true := by
    have hval := (f 0).isLt
    have hstep : chkA_s1 (f 0).val = true := by
      unfold chkA_s0 at hok
      match hfv : (f 0).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.1.2
      | 5, _ => simp only [Bool.and_eq_true] at hok; simpa only [hfv] using hok.2
    exact hstep
  have h1 : chkA_s2 (f 0).val (f 1).val = true := by
    have hval := (f 1).isLt
    have hstep : (!(((f 0).val != (f 1).val)) || chkA_s2 (f 0).val (f 1).val) = true := by
      unfold chkA_s1 at h0
      match hfv : (f 1).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h0; simpa only [hfv] using h0.2
    have hguard : (((f 0).val != (f 1).val)) = true := by
      exact (conf_guard hc0)
    rw [hguard] at hstep; simpa using hstep
  have h2 : chkA_s3 (f 0).val (f 1).val (f 2).val = true := by
    have hval := (f 2).isLt
    have hstep : (!(((f 1).val != (f 2).val)) || chkA_s3 (f 0).val (f 1).val (f 2).val) = true := by
      unfold chkA_s2 at h1
      match hfv : (f 2).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h1; simpa only [hfv] using h1.2
    have hguard : (((f 1).val != (f 2).val)) = true := by
      exact (conf_guard hc1)
    rw [hguard] at hstep; simpa using hstep
  have h3 : chkA_s4 (f 0).val (f 1).val (f 2).val (f 3).val = true := by
    have hval := (f 3).isLt
    have hstep : (!(((f 2).val != (f 3).val)) || chkA_s4 (f 0).val (f 1).val (f 2).val (f 3).val) = true := by
      unfold chkA_s3 at h2
      match hfv : (f 3).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h2; simpa only [hfv] using h2.2
    have hguard : (((f 2).val != (f 3).val)) = true := by
      exact (conf_guard hc2)
    rw [hguard] at hstep; simpa using hstep
  have h4 : chkA_s5 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val = true := by
    have hval := (f 5).isLt
    have hstep : (!(((f 0).val != (f 5).val) && (!((f 0).val == (f 2).val) || decide ((f 5).val ≤ (f 0).val)) && (!((f 0).val == (f 3).val) || decide ((f 5).val ≤ (f 0).val)) && (!((f 2).val == (f 5).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 2).val ≤ (f 3).val))) || chkA_s5 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val) = true := by
      unfold chkA_s4 at h3
      match hfv : (f 5).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h3; simpa only [hfv] using h3.2
    have hguard : (((f 0).val != (f 5).val) && (!((f 0).val == (f 2).val) || decide ((f 5).val ≤ (f 0).val)) && (!((f 0).val == (f 3).val) || decide ((f 5).val ≤ (f 0).val)) && (!((f 2).val == (f 5).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 2).val ≤ (f 3).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨(conf_guard hc5), (cube_guard hq1)⟩, (cube_guard hq4)⟩, (cube_guard hq29)⟩, (cube_guard hq37)⟩
    rw [hguard] at hstep; simpa using hstep
  have h5 : chkA_s6 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val = true := by
    have hval := (f 8).isLt
    have hstep : (!(((f 3).val != (f 8).val) && ((f 8).val != (f 5).val) && (!((f 0).val == (f 3).val) || decide ((f 8).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 3).val ≤ (f 0).val)) && (!((f 1).val == (f 3).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 1).val == (f 5).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 3).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 5).val ≤ (f 1).val)) && (!((f 2).val == (f 5).val) || decide ((f 8).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 5).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 8).val ≤ (f 3).val))) || chkA_s6 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val) = true := by
      unfold chkA_s5 at h4
      match hfv : (f 8).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h4; simpa only [hfv] using h4.2
    have hguard : (((f 3).val != (f 8).val) && ((f 8).val != (f 5).val) && (!((f 0).val == (f 3).val) || decide ((f 8).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 3).val ≤ (f 0).val)) && (!((f 1).val == (f 3).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 1).val == (f 5).val) || decide ((f 8).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 3).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 5).val ≤ (f 1).val)) && (!((f 2).val == (f 5).val) || decide ((f 8).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 5).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 8).val ≤ (f 3).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(conf_guard hc8), (conf_guard hc11)⟩, (cube_guard hq5)⟩, (cube_guard hq10)⟩, (cube_guard hq15)⟩, (cube_guard hq20)⟩, (cube_guard hq23)⟩, (cube_guard hq24)⟩, (cube_guard hq31)⟩, (cube_guard hq34)⟩, (cube_guard hq35)⟩, (cube_guard hq39)⟩
    rw [hguard] at hstep; simpa using hstep
  have h6 : chkA_s7 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val (f 4).val = true := by
    have hval := (f 4).isLt
    have hstep : (!(((f 3).val != (f 4).val) && ((f 4).val != (f 0).val) && (!((f 0).val == (f 2).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 3).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 1).val == (f 3).val) || decide ((f 4).val ≤ (f 1).val)) && (!((f 1).val == (f 4).val) || decide ((f 0).val ≤ (f 1).val)) && (!((f 2).val == (f 4).val) || decide ((f 0).val ≤ (f 2).val)) && (!((f 2).val == (f 4).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 4).val == (f 5).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 3).val ≤ (f 4).val))) || chkA_s7 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val (f 4).val) = true := by
      unfold chkA_s6 at h5
      match hfv : (f 4).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h5; simpa only [hfv] using h5.2
    have hguard : (((f 3).val != (f 4).val) && ((f 4).val != (f 0).val) && (!((f 0).val == (f 2).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 3).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 1).val == (f 3).val) || decide ((f 4).val ≤ (f 1).val)) && (!((f 1).val == (f 4).val) || decide ((f 0).val ≤ (f 1).val)) && (!((f 2).val == (f 4).val) || decide ((f 0).val ≤ (f 2).val)) && (!((f 2).val == (f 4).val) || decide ((f 3).val ≤ (f 2).val)) && (!((f 4).val == (f 5).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 0).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 3).val ≤ (f 4).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(conf_guard hc3), (conf_guard hc4)⟩, (cube_guard hq0)⟩, (cube_guard hq3)⟩, (cube_guard hq11)⟩, (cube_guard hq13)⟩, (cube_guard hq16)⟩, (cube_guard hq26)⟩, (cube_guard hq27)⟩, (cube_guard hq46)⟩, (cube_guard hq54)⟩, (cube_guard hq55)⟩
    rw [hguard] at hstep; simpa using hstep
  have h7 : chkA_s8 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val (f 4).val (f 6).val = true := by
    have hval := (f 6).isLt
    have hstep : (!(((f 1).val != (f 6).val) && ((f 6).val != (f 8).val) && (!((f 0).val == (f 6).val) || decide ((f 1).val ≤ (f 0).val)) && (!((f 0).val == (f 6).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 6).val ≤ (f 0).val)) && (!((f 1).val == (f 3).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 4).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 5).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 6).val) || decide ((f 1).val ≤ (f 2).val)) && (!((f 3).val == (f 6).val) || decide ((f 1).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 4).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 4).val == (f 6).val) || decide ((f 1).val ≤ (f 4).val)) && (!((f 4).val == (f 6).val) || decide ((f 3).val ≤ (f 4).val)) && (!((f 4).val == (f 6).val) || decide ((f 8).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 6).val ≤ (f 4).val)) && (!((f 5).val == (f 6).val) || decide ((f 1).val ≤ (f 5).val)) && (!((f 5).val == (f 6).val) || decide ((f 8).val ≤ (f 5).val))) || chkA_s8 (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val (f 4).val (f 6).val) = true := by
      unfold chkA_s7 at h6
      match hfv : (f 6).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h6; simpa only [hfv] using h6.2
    have hguard : (((f 1).val != (f 6).val) && ((f 6).val != (f 8).val) && (!((f 0).val == (f 6).val) || decide ((f 1).val ≤ (f 0).val)) && (!((f 0).val == (f 6).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 8).val) || decide ((f 6).val ≤ (f 0).val)) && (!((f 1).val == (f 3).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 4).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 5).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 1).val == (f 8).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 6).val) || decide ((f 1).val ≤ (f 2).val)) && (!((f 3).val == (f 6).val) || decide ((f 1).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 4).val ≤ (f 3).val)) && (!((f 3).val == (f 6).val) || decide ((f 8).val ≤ (f 3).val)) && (!((f 4).val == (f 6).val) || decide ((f 1).val ≤ (f 4).val)) && (!((f 4).val == (f 6).val) || decide ((f 3).val ≤ (f 4).val)) && (!((f 4).val == (f 6).val) || decide ((f 8).val ≤ (f 4).val)) && (!((f 4).val == (f 8).val) || decide ((f 6).val ≤ (f 4).val)) && (!((f 5).val == (f 6).val) || decide ((f 1).val ≤ (f 5).val)) && (!((f 5).val == (f 6).val) || decide ((f 8).val ≤ (f 5).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(conf_guard hc6), (conf_guard hc10)⟩, (cube_guard hq6)⟩, (cube_guard hq7)⟩, (cube_guard hq12)⟩, (cube_guard hq14)⟩, (cube_guard hq17)⟩, (cube_guard hq18)⟩, (cube_guard hq25)⟩, (cube_guard hq32)⟩, (cube_guard hq40)⟩, (cube_guard hq41)⟩, (cube_guard hq42)⟩, (cube_guard hq48)⟩, (cube_guard hq49)⟩, (cube_guard hq50)⟩, (cube_guard hq56)⟩, (cube_guard hq57)⟩, (cube_guard hq59)⟩
    rw [hguard] at hstep; simpa using hstep
  have h8 : chkA_leaf (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val (f 4).val (f 6).val (f 7).val = true := by
    have hval := (f 7).isLt
    have hstep : (!(((f 2).val != (f 7).val) && ((f 5).val != (f 7).val) && (!((f 0).val == (f 2).val) || decide ((f 7).val ≤ (f 0).val)) && (!((f 0).val == (f 7).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 7).val) || decide ((f 5).val ≤ (f 0).val)) && (!((f 1).val == (f 5).val) || decide ((f 7).val ≤ (f 1).val)) && (!((f 1).val == (f 7).val) || decide ((f 2).val ≤ (f 1).val)) && (!((f 1).val == (f 7).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 4).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 5).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 6).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 7).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 4).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 5).val ≤ (f 3).val)) && (!((f 4).val == (f 5).val) || decide ((f 7).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 2).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 3).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 5).val ≤ (f 4).val)) && (!((f 5).val == (f 6).val) || decide ((f 7).val ≤ (f 5).val)) && (!((f 6).val == (f 7).val) || decide ((f 2).val ≤ (f 6).val)) && (!((f 6).val == (f 7).val) || decide ((f 5).val ≤ (f 6).val)) && (!((f 6).val == (f 7).val) || decide ((f 8).val ≤ (f 6).val)) && (!((f 7).val == (f 8).val) || decide ((f 2).val ≤ (f 7).val)) && (!((f 7).val == (f 8).val) || decide ((f 5).val ≤ (f 7).val)) && (!((f 7).val == (f 8).val) || decide ((f 6).val ≤ (f 7).val))) || chkA_leaf (f 0).val (f 1).val (f 2).val (f 3).val (f 5).val (f 8).val (f 4).val (f 6).val (f 7).val) = true := by
      unfold chkA_s8 at h7
      match hfv : (f 7).val, hval with
      | 0, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.1.1.1
      | 1, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.1.1.2
      | 2, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.1.2
      | 3, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.1.2
      | 4, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.1.2
      | 5, _ => simp only [Bool.and_eq_true] at h7; simpa only [hfv] using h7.2
    have hguard : (((f 2).val != (f 7).val) && ((f 5).val != (f 7).val) && (!((f 0).val == (f 2).val) || decide ((f 7).val ≤ (f 0).val)) && (!((f 0).val == (f 7).val) || decide ((f 4).val ≤ (f 0).val)) && (!((f 0).val == (f 7).val) || decide ((f 5).val ≤ (f 0).val)) && (!((f 1).val == (f 5).val) || decide ((f 7).val ≤ (f 1).val)) && (!((f 1).val == (f 7).val) || decide ((f 2).val ≤ (f 1).val)) && (!((f 1).val == (f 7).val) || decide ((f 6).val ≤ (f 1).val)) && (!((f 2).val == (f 4).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 5).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 6).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 2).val == (f 8).val) || decide ((f 7).val ≤ (f 2).val)) && (!((f 3).val == (f 5).val) || decide ((f 7).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 2).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 4).val ≤ (f 3).val)) && (!((f 3).val == (f 7).val) || decide ((f 5).val ≤ (f 3).val)) && (!((f 4).val == (f 5).val) || decide ((f 7).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 2).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 3).val ≤ (f 4).val)) && (!((f 4).val == (f 7).val) || decide ((f 5).val ≤ (f 4).val)) && (!((f 5).val == (f 6).val) || decide ((f 7).val ≤ (f 5).val)) && (!((f 6).val == (f 7).val) || decide ((f 2).val ≤ (f 6).val)) && (!((f 6).val == (f 7).val) || decide ((f 5).val ≤ (f 6).val)) && (!((f 6).val == (f 7).val) || decide ((f 8).val ≤ (f 6).val)) && (!((f 7).val == (f 8).val) || decide ((f 2).val ≤ (f 7).val)) && (!((f 7).val == (f 8).val) || decide ((f 5).val ≤ (f 7).val)) && (!((f 7).val == (f 8).val) || decide ((f 6).val ≤ (f 7).val))) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨(conf_guard hc7), (conf_guard hc9)⟩, (cube_guard hq2)⟩, (cube_guard hq8)⟩, (cube_guard hq9)⟩, (cube_guard hq19)⟩, (cube_guard hq21)⟩, (cube_guard hq22)⟩, (cube_guard hq28)⟩, (cube_guard hq30)⟩, (cube_guard hq33)⟩, (cube_guard hq36)⟩, (cube_guard hq38)⟩, (cube_guard hq43)⟩, (cube_guard hq44)⟩, (cube_guard hq45)⟩, (cube_guard hq47)⟩, (cube_guard hq51)⟩, (cube_guard hq52)⟩, (cube_guard hq53)⟩, (cube_guard hq58)⟩, (cube_guard hq60)⟩, (cube_guard hq61)⟩, (cube_guard hq62)⟩, (cube_guard hq63)⟩, (cube_guard hq64)⟩, (cube_guard hq65)⟩
    rw [hguard] at hstep; simpa using hstep
  unfold chkA_leaf at h8
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h8
  rcases h8 with (⟨⟨⟨a, b⟩, c⟩, d⟩ | ⟨⟨⟨a, b⟩, c⟩, d⟩) | ⟨⟨⟨a, b⟩, c⟩, d⟩
  · exact Or.inl ⟨Fin.ext a, Fin.ext b, Fin.ext c, Fin.ext d⟩
  · exact Or.inr (Or.inl ⟨Fin.ext a, Fin.ext b, Fin.ext c, Fin.ext d⟩)
  · exact Or.inr (Or.inr ⟨Fin.ext a, Fin.ext b, Fin.ext c, Fin.ext d⟩)

-- Bit-mask construction and bitwise helpers for PureY extraction:
def maskRec (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => maskRec f k ||| (if f k then 1 <<< k else 0)

lemma testBit_one_ne_zero {n : ℕ} (hn : n ≠ 0) : (1 : ℕ).testBit n = false := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ m => exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega)))

lemma maskRec_testBit (f : Nat → Bool) (k i : Nat) :
    (maskRec f k).testBit i = (decide (i < k) && f i) := by
  induction k with
  | zero => simp [maskRec]
  | succ k ih =>
    rw [maskRec, Nat.testBit_or, ih]
    by_cases h : i = k
    · subst h
      cases hf : f i <;> simp [Nat.testBit_shiftLeft]
    · by_cases hlt : i < k
      · cases hf : f k <;> simp [hlt, show i < k + 1 by omega, Nat.testBit_shiftLeft]
      · have hlt' : ¬ i < k + 1 := by omega
        have hgt : i - k ≠ 0 := by omega
        cases hf : f k <;> simp [hlt, hlt', Nat.testBit_shiftLeft, testBit_one_ne_zero hgt]

lemma maskRec_and_all32 (f : Nat → Bool) : maskRec f 32 &&& all32 = maskRec f 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskRec_testBit]
  by_cases hi : i < 32
  · have ha : all32.testBit i = true := by
      have : ∀ k : Fin 32, all32.testBit k.val = true := by decide
      exact this ⟨i, hi⟩
    simp [hi, ha]
  · simp [hi]

lemma not32_maskRec (f : Nat → Bool) : not32 (maskRec f 32) = maskRec (fun i => !f i) 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · rw [not32_testBit hi, maskRec_testBit, maskRec_testBit]; simp [hi]
  · rw [not32, Nat.testBit_xor, maskRec_testBit, maskRec_testBit]
    have ha : all32.testBit i = false := Nat.testBit_lt_two_pow (by unfold all32; exact lt_of_lt_of_le (by decide : 0xffffffff < 2 ^ 32) (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, ha]

lemma not32_not32_maskRec (f : Nat → Bool) : not32 (not32 (maskRec f 32)) = maskRec f 32 := by
  rw [not32_maskRec, not32_maskRec]
  apply Nat.eq_of_testBit_eq; intro i; simp [maskRec_testBit]

lemma canon_maskRec_not (f : Nat → Bool) : canon (not32 (maskRec f 32)) = canon (maskRec f 32) := by
  unfold canon
  rw [not32_testBit (by omega), maskRec_and_all32, not32_maskRec, maskRec_and_all32, ← not32_maskRec]
  cases hf : (maskRec f 32).testBit 0
  · simp [not32_not32_maskRec]
  · simp

lemma canon_maskRec_eq (f : Nat → Bool) :
    maskRec f 32 = canon (maskRec f 32) ∨ maskRec f 32 = not32 (canon (maskRec f 32)) := by
  unfold canon
  rw [maskRec_and_all32]
  cases hf : (maskRec f 32).testBit 0
  · exact Or.inl (by simp)
  · exact Or.inr (by simp [not32_not32_maskRec])

lemma maskRec_and (f g : Nat → Bool) :
    maskRec (fun i => f i && g i) 32 = maskRec f 32 &&& maskRec g 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, maskRec_testBit, maskRec_testBit, maskRec_testBit]
  by_cases hi : i < 32 <;> simp [hi]

lemma maskRec_or (f g : Nat → Bool) :
    maskRec (fun i => f i || g i) 32 = maskRec f 32 ||| maskRec g 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, maskRec_testBit, maskRec_testBit, maskRec_testBit]
  by_cases hi : i < 32 <;> simp [hi]

lemma not32_land (f g : Nat → Bool) :
    not32 (maskRec f 32) &&& not32 (maskRec g 32) = not32 (maskRec f 32 ||| maskRec g 32) := by
  rw [not32_maskRec, not32_maskRec, ← maskRec_and, ← maskRec_or, not32_maskRec]
  apply Nat.eq_of_testBit_eq; intro i; simp [maskRec_testBit]

lemma not32_lor (f g : Nat → Bool) :
    not32 (maskRec f 32) ||| not32 (maskRec g 32) = not32 (maskRec f 32 &&& maskRec g 32) := by
  rw [not32_maskRec, not32_maskRec, ← maskRec_or, ← maskRec_and, not32_maskRec]
  apply Nat.eq_of_testBit_eq; intro i; simp [maskRec_testBit]

lemma lor_not32_right (f g : Nat → Bool) :
    maskRec f 32 ||| not32 (maskRec g 32) = not32 (not32 (maskRec f 32) &&& maskRec g 32) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 32
  · rw [Nat.testBit_or, not32_testBit hi, not32_testBit hi, Nat.testBit_and, not32_testBit hi]
    cases (maskRec f 32).testBit i <;> cases (maskRec g 32).testBit i <;> rfl
  · rw [not32_maskRec, not32_maskRec, ← maskRec_or, ← maskRec_and, not32_maskRec, maskRec_testBit, maskRec_testBit]
    simp [hi]

lemma lor_not32_left (f g : Nat → Bool) :
    not32 (maskRec f 32) ||| maskRec g 32 = not32 (maskRec f 32 &&& not32 (maskRec g 32)) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 32
  · rw [Nat.testBit_or, not32_testBit hi, not32_testBit hi, Nat.testBit_and, not32_testBit hi]
    cases (maskRec f 32).testBit i <;> cases (maskRec g 32).testBit i <;> rfl
  · rw [not32_maskRec, not32_maskRec, ← maskRec_or, ← maskRec_and, not32_maskRec, maskRec_testBit, maskRec_testBit]
    simp [hi]

lemma gate_step_in_gateOuts (f g : Nat → Bool) (isAnd : Bool) :
    let ca := canon (maskRec f 32)
    let cb := canon (maskRec g 32)
    let out := if isAnd then canon (maskRec f 32 &&& maskRec g 32) else canon (maskRec f 32 ||| maskRec g 32)
    out ∈ gateOuts ca cb := by
  intro ca cb out
  have hca_eq : ∃ fa : Nat → Bool, ca = maskRec fa 32 := by
    unfold ca canon; rw [maskRec_and_all32]
    cases (maskRec f 32).testBit 0
    · exact ⟨f, by simp⟩
    · exact ⟨fun i => !f i, by simp [not32_maskRec]⟩
  have hcb_eq : ∃ fb : Nat → Bool, cb = maskRec fb 32 := by
    unfold cb canon; rw [maskRec_and_all32]
    cases (maskRec g 32).testBit 0
    · exact ⟨g, by simp⟩
    · exact ⟨fun i => !g i, by simp [not32_maskRec]⟩
  obtain ⟨fa, hfa⟩ := hca_eq
  obtain ⟨fb, hfb⟩ := hcb_eq
  have hmem4 (x a b c d : Nat) (h : x = a ∨ x = b ∨ x = c ∨ x = d) : x ∈ [a, b, c, d] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact h
  rcases canon_maskRec_eq f with hf | hf <;> rcases canon_maskRec_eq g with hg | hg <;> cases isAnd
  · apply hmem4; right; left; simp only [out, Bool.false_eq_true, ↓reduceIte]; rw [hf, hg]
  · apply hmem4; left; simp only [out, ↓reduceIte]; rw [hf, hg]
  · apply hmem4; right; right; right
    simp only [out, Bool.false_eq_true, ↓reduceIte]
    change canon (maskRec f 32 ||| maskRec g 32) = canon (not32 ca &&& cb)
    rw [hf, hg]; change canon (ca ||| not32 cb) = canon (not32 ca &&& cb)
    rw [hfa, hfb, lor_not32_right]
    rw [show not32 (maskRec fa 32) &&& maskRec fb 32 = maskRec (fun i => !fa i && fb i) 32 by rw [not32_maskRec, ← maskRec_and]]
    rw [canon_maskRec_not]
  · apply hmem4; right; right; left; simp only [out, ↓reduceIte]; rw [hf, hg]
  · apply hmem4; right; right; left
    simp only [out, Bool.false_eq_true, ↓reduceIte]
    change canon (maskRec f 32 ||| maskRec g 32) = canon (ca &&& not32 cb)
    rw [hf, hg]; change canon (not32 ca ||| cb) = canon (ca &&& not32 cb)
    rw [hfa, hfb, lor_not32_left]
    rw [show maskRec fa 32 &&& not32 (maskRec fb 32) = maskRec (fun i => fa i && !fb i) 32 by rw [not32_maskRec, ← maskRec_and]]
    rw [canon_maskRec_not]
  · apply hmem4; right; right; right; simp only [out, ↓reduceIte]; rw [hf, hg]
  · apply hmem4; left
    simp only [out, Bool.false_eq_true, ↓reduceIte]
    change canon (maskRec f 32 ||| maskRec g 32) = canon (ca &&& cb)
    rw [hf, hg]; change canon (not32 ca ||| not32 cb) = canon (ca &&& cb)
    rw [hfa, hfb, not32_lor, ← maskRec_and, canon_maskRec_not, maskRec_and]
  · apply hmem4; right; left
    simp only [out, ↓reduceIte]
    change canon (maskRec f 32 &&& maskRec g 32) = canon (ca ||| cb)
    rw [hf, hg]; change canon (not32 ca &&& not32 cb) = canon (ca ||| cb)
    rw [hfa, hfb, not32_land, ← maskRec_or, canon_maskRec_not, maskRec_or]

-- Permutations and X/Y coordinate mapping
def xIdx : Fin 4 → Fin 9 := ![0, 3, 6, 7]
def yIdx : Fin 5 → Fin 9 := ![1, 2, 4, 5, 8]

def baseCombine (x : Fin 4 → Bool) (y : Fin 32) : Fin 9 → Bool
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => y.val.testBit 0
  | ⟨2, _⟩ => y.val.testBit 1
  | ⟨3, _⟩ => x 1
  | ⟨4, _⟩ => y.val.testBit 2
  | ⟨5, _⟩ => y.val.testBit 3
  | ⟨6, _⟩ => x 2
  | ⟨7, _⟩ => x 3
  | ⟨8, _⟩ => y.val.testBit 4

lemma target9_baseCombine (x : Fin 4 → Bool) (y : Fin 32) :
    target9 (baseCombine x y) = targetXY x y := by
  have h : ∀ a0 a1 a2 a3 b0 b1 b2 b3 b4 : Bool,
      ((a0 && b0) || (b0 && b1) || (b1 && a1) || (a1 && b2) || (b2 && a0) ||
       (a0 && b3) || (b0 && a2) || (b1 && a3) || (a1 && b4) || (b3 && a3) ||
       (a2 && b4) || (b4 && b3)) =
      (((b0 && b1) || (b3 && b4)) ||
       (a0 && (b0 || b2 || b3)) || (a1 && (b1 || b2 || b4)) ||
       (a2 && (b0 || b4)) || (a3 && (b1 || b3))) := by decide
  have := h (x 0) (x 1) (x 2) (x 3) (y.val.testBit 0) (y.val.testBit 1) (y.val.testBit 2) (y.val.testBit 3) (y.val.testBit 4)
  simpa only [target9, targetXY, baseCombine, isIndepY, AvY, yBit, Bool.not_not] using this

def combineXY (σinv : Fin 9 → Fin 9) (x : Fin 4 → Bool) (y : Fin 32) (i : Fin 9) : Bool :=
  baseCombine x y (σinv i)

def σ0 : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
def σ0inv : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]

def σ1 : Fin 9 → Fin 9 := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
def σ1inv : Fin 9 → Fin 9 := ![1, 0, 5, 8, 6, 2, 4, 7, 3]

def σ2 : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
def σ2inv : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]

lemma perm_specs :
    (∀ i, σ0inv (σ0 i) = i) ∧ (∀ i, σ0 (σ0inv i) = i) ∧ (∀ m : Fin 512, target9 (fun i => m.val.testBit (σ0inv i).val) = target9 (row9 m.val)) ∧
    (∀ i, σ1inv (σ1 i) = i) ∧ (∀ i, σ1 (σ1inv i) = i) ∧ (∀ m : Fin 512, target9 (fun i => m.val.testBit (σ1inv i).val) = target9 (row9 m.val)) ∧
    (∀ i, σ2inv (σ2 i) = i) ∧ (∀ i, σ2 (σ2inv i) = i) ∧ (∀ m : Fin 512, target9 (fun i => m.val.testBit (σ2inv i).val) = target9 (row9 m.val)) := by
  decide +kernel

lemma target9_perm (σinv : Fin 9 → Fin 9)
    (h : ∀ m : Fin 512, target9 (fun i => m.val.testBit (σinv i).val) = target9 (row9 m.val))
    (f : Fin 9 → Bool) : target9 (fun i => f (σinv i)) = target9 f := by
  let m : ℕ := (List.finRange 9).foldl (fun acc j => if f j then acc ||| (1 <<< j.val) else acc) 0
  have hm_lt : m < 512 := by
    have step : ∀ (l : List (Fin 9)) (acc : ℕ), acc < 512 →
        (l.foldl (fun a j => if f j then a ||| (1 <<< j.val) else a) acc) < 512 := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons j l ih =>
        intro acc hacc
        apply ih
        by_cases hf : f j
        · simp only [hf, ↓reduceIte]
          have hbit : (1 <<< j.val) < 2 ^ 9 := by fin_cases j <;> decide
          exact Nat.or_lt_two_pow (n := 9) hacc hbit
        · simp [hf, hacc]
    exact step (List.finRange 9) 0 (by decide)
  have hm_bit : ∀ k : Fin 9, m.testBit k.val = f k := by
    have aux : ∀ (l : List (Fin 9)) (acc : ℕ) (k : Fin 9),
        (l.foldl (fun a j => if f j then a ||| (1 <<< j.val) else a) acc).testBit k.val =
          (acc.testBit k.val || (decide (k ∈ l) && f k)) := by
      intro l
      induction l with
      | nil => intro acc k; simp
      | cons j l ih =>
        intro acc k
        simp only [List.foldl_cons, ih, List.mem_cons]
        by_cases hkj : k = j
        · subst hkj
          by_cases hf : f k <;> simp [hf, Nat.testBit_or, Nat.testBit_shiftLeft]
        · have hne : k.val ≠ j.val := fun e => hkj (Fin.ext e)
          by_cases hlt : j.val ≤ k.val
          · have hsub : k.val - j.val ≠ 0 := by omega
            by_cases hf : f j <;> simp [hf, hkj, hlt, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_one_ne_zero hsub]
          · by_cases hf : f j <;> simp [hf, hkj, hlt, Nat.testBit_or, Nat.testBit_shiftLeft]
    intro k
    simpa [m, List.mem_finRange] using aux (List.finRange 9) 0 k
  have h1 : (fun i => f (σinv i)) = (fun i => (⟨m, hm_lt⟩ : Fin 512).val.testBit (σinv i).val) :=
    funext fun i => (hm_bit (σinv i)).symm
  have h2 : f = row9 (⟨m, hm_lt⟩ : Fin 512).val :=
    funext fun i => (hm_bit i).symm
  rw [h1, h ⟨m, hm_lt⟩, ← h2]

-- Bridge from XTree2940 mask properties to PureY2940 predicates:
lemma maskIndep_bit (y : Fin 32) : maskIndep.testBit y.val = isIndepY y := by
  have h := (List.all_eq_true.mp masks_check) y.val (List.mem_range.mpr y.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1

lemma maskNonIndep_bit (y : Fin 32) : maskNonIndep.testBit y.val = !isIndepY y := by
  have h := (List.all_eq_true.mp masks_check) y.val (List.mem_range.mpr y.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.2

def maskA : Fin 4 → Nat
  | 0 => maskA0
  | 1 => maskA3
  | 2 => maskA6
  | 3 => maskA7

lemma maskA_bit (v : Fin 4) (y : Fin 32) :
    (maskA v).testBit y.val = (isIndepY y && AvY v y) := by
  have h := (List.all_eq_true.mp masks_check) y.val (List.mem_range.mpr y.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  fin_cases v
  · exact h.1.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.2

lemma inY_bit (j : Fin 5) (y : Fin 32) : (inY j).testBit y.val = y.val.testBit j.val := by
  have h := (List.all_eq_true.mp masks_check) y.val (List.mem_range.mpr y.isLt)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  fin_cases j
  · exact h.1.1.1.1.2
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

lemma inY_mem_inList (j : Fin 5) : inY j ∈ inList := by
  fin_cases j <;> decide

lemma canon_inY (j : Fin 5) : canon (inY j) = inY j := by
  fin_cases j <;> decide

lemma maskA_lt32 (v : Fin 4) (i : ℕ) (hi : 32 ≤ i) :
    (maskA v).testBit i = false := by
  fin_cases v <;>
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by omega) hi))

lemma maskNonIndep_lt32 (i : ℕ) (hi : 32 ≤ i) : maskNonIndep.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : maskNonIndep < 2 ^ 32) (Nat.pow_le_pow_right (by omega) hi))

lemma mask_sup_zero (f : Nat → Bool) (v : Fin 4)
    (h : ∀ y : Fin 32, isIndepY y = true → AvY v y = true → (maskRec f 32).testBit y.val = true) :
    maskA v &&& not32 (maskRec f 32) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < 32
  · rw [not32_testBit hi, maskA_bit v ⟨i, hi⟩]
    cases hind : isIndepY ⟨i, hi⟩
    · simp
    · cases hav : AvY v ⟨i, hi⟩
      · simp
      · simp [h ⟨i, hi⟩ hind hav]
  · rw [maskA_lt32 v i (by omega)]; simp

lemma isW0e2_of_mask (f : Nat → Bool)
    (hsup : ∀ y : Fin 32, isIndepY y = true → AvY 0 y = true → (maskRec f 32).testBit y.val = true)
    (h2 : (maskRec f 32).testBit 2 = false) : isW0e2 (canon (maskRec f 32)) = true := by
  have hz : maskA0 &&& not32 (maskRec f 32) = 0 := mask_sup_zero f 0 hsup
  unfold canon; rw [maskRec_and_all32]
  cases hb0 : (maskRec f 32).testBit 0
  · unfold isW0e2; simp [hz, h2]
  · unfold isW0e2
    have hnb : (not32 (maskRec f 32)).testBit 2 = true := by rw [not32_testBit (by omega), h2]; rfl
    simp [hz, hnb]

lemma isW3e1_of_mask (f : Nat → Bool)
    (hsup : ∀ y : Fin 32, isIndepY y = true → AvY 1 y = true → (maskRec f 32).testBit y.val = true)
    (h1 : (maskRec f 32).testBit 1 = false) : isW3e1 (canon (maskRec f 32)) = true := by
  have hz : maskA3 &&& not32 (maskRec f 32) = 0 := mask_sup_zero f 1 hsup
  unfold canon; rw [maskRec_and_all32]
  cases hb0 : (maskRec f 32).testBit 0
  · unfold isW3e1; simp [hz, h1]
  · unfold isW3e1
    have hnb : (not32 (maskRec f 32)).testBit 1 = true := by rw [not32_testBit (by omega), h1]; rfl
    simp [hz, hnb]

lemma isW6e4_of_mask (f : Nat → Bool)
    (hsup : ∀ y : Fin 32, isIndepY y = true → AvY 2 y = true → (maskRec f 32).testBit y.val = true)
    (h4 : (maskRec f 32).testBit 4 = false) : isW6e4 (canon (maskRec f 32)) = true := by
  have hz : maskA6 &&& not32 (maskRec f 32) = 0 := mask_sup_zero f 2 hsup
  unfold canon; rw [maskRec_and_all32]
  cases hb0 : (maskRec f 32).testBit 0
  · unfold isW6e4; simp [hz, h4]
  · unfold isW6e4
    have hnb : (not32 (maskRec f 32)).testBit 4 = true := by rw [not32_testBit (by omega), h4]; rfl
    simp [hz, hnb]

lemma isW7e4_of_mask (f : Nat → Bool)
    (hsup : ∀ y : Fin 32, isIndepY y = true → AvY 3 y = true → (maskRec f 32).testBit y.val = true)
    (h4 : (maskRec f 32).testBit 4 = false) : isW7e4 (canon (maskRec f 32)) = true := by
  have hz : maskA7 &&& not32 (maskRec f 32) = 0 := mask_sup_zero f 3 hsup
  unfold canon; rw [maskRec_and_all32]
  cases hb0 : (maskRec f 32).testBit 0
  · unfold isW7e4; simp [hz, h4]
  · unfold isW7e4
    have hnb : (not32 (maskRec f 32)).testBit 4 = true := by rw [not32_testBit (by omega), h4]; rfl
    simp [hz, hnb]

lemma isS1_of_mask (f : Nat → Bool)
    (htr : ∀ y : Fin 32, isIndepY y = false → (maskRec f 32).testBit y.val = true)
    (hfl : ∃ v : Fin 4, ∀ y : Fin 32, isIndepY y = true → AvY v y = true → (maskRec f 32).testBit y.val = false) :
    isS1 (canon (maskRec f 32)) = true := by
  have hni : maskRec f 32 &&& maskNonIndep = maskNonIndep := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 32
    · rw [maskNonIndep_bit ⟨i, hi⟩]
      cases hind : isIndepY ⟨i, hi⟩
      · simp [htr ⟨i, hi⟩ hind]
      · simp
    · rw [maskNonIndep_lt32 i (by omega)]; simp
  obtain ⟨v, hv⟩ := hfl
  have hzero : maskRec f 32 &&& maskA v = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 32
    · rw [maskA_bit v ⟨i, hi⟩]
      cases hind : isIndepY ⟨i, hi⟩
      · simp
      · cases hav : AvY v ⟨i, hi⟩
        · simp
        · simp [hv ⟨i, hi⟩ hind hav]
    · rw [maskA_lt32 v i (by omega)]; simp
  have hdisj : ((maskRec f 32 &&& maskA0 == 0) || (maskRec f 32 &&& maskA3 == 0) ||
      (maskRec f 32 &&& maskA6 == 0) || (maskRec f 32 &&& maskA7 == 0)) = true := by
    fin_cases v <;> simp [maskA] at hzero <;> simp [hzero]
  unfold canon; rw [maskRec_and_all32]
  cases hb0 : (maskRec f 32).testBit 0
  · unfold isS1; simp [hni, hdisj]
  · unfold isS1; simp [not32_not32_maskRec, hni, hdisj]

-- Top-level XTree builder (avoids local `let rec` overhead in proof)
noncomputable def buildXTree (gs : List Gate) (σinv : Fin 9 → Fin 9)
    (hasX : Fin (9 + gs.length) → Bool)
    (pureMask : Fin (9 + gs.length) → Bool → Nat)
    (w : ℕ) (neg : Bool) : XTree :=
  if hw9 : w < 9 then
    match (σinv ⟨w, hw9⟩).val with
    | 0 => .leaf 0 neg
    | 3 => .leaf 1 neg
    | 6 => .leaf 2 neg
    | 7 => .leaf 3 neg
    | _ => .leaf 0 neg
  else if hwg : w < 9 + gs.length then
    let g := gs[w - 9]'(by omega)
    match g.op, g.inputs with
    | .not, [a] => if ha : a < w then buildXTree gs σinv hasX pureMask a (!neg) else .leaf 0 neg
    | .and, [a, b] =>
      if hab : a < w ∧ b < w then
        let xa := hasX ⟨a, by omega⟩
        let xb := hasX ⟨b, by omega⟩
        if xa && xb then
          if !neg then .andX (buildXTree gs σinv hasX pureMask a neg) (buildXTree gs σinv hasX pureMask b neg)
          else .orX (buildXTree gs σinv hasX pureMask a neg) (buildXTree gs σinv hasX pureMask b neg)
        else if xa then
          if !neg then .andY (buildXTree gs σinv hasX pureMask a neg) (pureMask ⟨b, by omega⟩ neg)
          else .orY (buildXTree gs σinv hasX pureMask a neg) (pureMask ⟨b, by omega⟩ neg)
        else if xb then
          if !neg then .andY (buildXTree gs σinv hasX pureMask b neg) (pureMask ⟨a, by omega⟩ neg)
          else .orY (buildXTree gs σinv hasX pureMask b neg) (pureMask ⟨a, by omega⟩ neg)
        else .leaf 0 neg
      else .leaf 0 neg
    | .or, [a, b] =>
      if hab : a < w ∧ b < w then
        let xa := hasX ⟨a, by omega⟩
        let xb := hasX ⟨b, by omega⟩
        if xa && xb then
          if neg then .andX (buildXTree gs σinv hasX pureMask a neg) (buildXTree gs σinv hasX pureMask b neg)
          else .orX (buildXTree gs σinv hasX pureMask a neg) (buildXTree gs σinv hasX pureMask b neg)
        else if xa then
          if neg then .andY (buildXTree gs σinv hasX pureMask a neg) (pureMask ⟨b, by omega⟩ neg)
          else .orY (buildXTree gs σinv hasX pureMask a neg) (pureMask ⟨b, by omega⟩ neg)
        else if xb then
          if neg then .andY (buildXTree gs σinv hasX pureMask b neg) (pureMask ⟨a, by omega⟩ neg)
          else .orY (buildXTree gs σinv hasX pureMask b neg) (pureMask ⟨a, by omega⟩ neg)
        else .leaf 0 neg
      else .leaf 0 neg
    | _, _ => .leaf 0 neg
  else .leaf 0 neg
termination_by w

def ywFn : Fin 4 → Fin 32
  | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨1, by decide⟩ | 3 => ⟨2, by decide⟩

lemma ywFn_spec : ∀ u : Fin 4, isIndepY (ywFn u) = true ∧ AvY u (ywFn u) = true := by decide

def yuvFn : Fin 4 → Fin 4 → Fin 32
  | 0, 0 => ⟨1, by decide⟩ | 0, 1 => ⟨4, by decide⟩ | 0, 2 => ⟨1, by decide⟩ | 0, 3 => ⟨8, by decide⟩
  | 1, 0 => ⟨4, by decide⟩ | 1, 1 => ⟨2, by decide⟩ | 1, 2 => ⟨16, by decide⟩ | 1, 3 => ⟨2, by decide⟩
  | 2, 0 => ⟨1, by decide⟩ | 2, 1 => ⟨16, by decide⟩ | 2, 2 => ⟨1, by decide⟩ | 2, 3 => ⟨18, by decide⟩
  | 3, 0 => ⟨8, by decide⟩ | 3, 1 => ⟨2, by decide⟩ | 3, 2 => ⟨18, by decide⟩ | 3, 3 => ⟨2, by decide⟩

lemma yuvFn_spec : ∀ u v : Fin 4, isIndepY (yuvFn u v) = true ∧ AvY u (yuvFn u v) = true ∧ AvY v (yuvFn u v) = true := by decide

-- Core Case A contradiction once we have a Petersen-9 automorphism σ putting X = σ((0, 3, 6, 7)) at out!
set_option maxHeartbeats 2500000 in
theorem caseA_with_perm {gs : List Gate} (clean : CleanL 9 gs)
    (out : Fin (9 + gs.length))
    (live : ∀ w : Fin (9 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (budget : nonNotCount gs ≤ 13)
    (computes : ∀ x : Fin 9 → Bool, vl gs x out.val = target9 x)
    (σ σinv : Fin 9 → Fin 9)
    (hinv1 : ∀ i, σinv (σ i) = i) (hinv2 : ∀ i, σ (σinv i) = i)
    (haut : ∀ f : Fin 9 → Bool, target9 (fun i => f (σinv i)) = target9 f)
    (hXout : ∀ v : Fin 4, firstInputBoundary clean out live (σ (xIdx v)) = out) : False := by
  classical
  let hasX (w : Fin (9 + gs.length)) : Bool :=
    decide (∃ v : Fin 4, Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) w)
  have hasX_step {a b : Fin (9 + gs.length)} (ha : hasX a = true) (hab : readEdge gs a b) : hasX b = true := by
    simp only [hasX, decide_eq_true_eq] at ha ⊢
    obtain ⟨v, hv⟩ := ha
    exact ⟨v, hv.tail hab⟩
  have hX : ∀ v : Fin 4, FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs (σ (xIdx v))) = out := hXout
  have hasX_no_branch {w : Fin (9 + gs.length)} (hw : hasX w = true) (hne : w ≠ out) :
      ¬ FirstBranchRoute.Branches (readEdge gs) w := by
    intro hbr
    simp only [hasX, decide_eq_true_eq] at hw
    obtain ⟨v, hv⟩ := hw
    have hlt : w < out := lt_of_le_of_ne (wire_le_output clean out live w) hne
    have hterm : FirstBranchRoute.Terminal (readEdge gs) out w := Or.inr hbr
    have hfol : Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) (inputWire gs (σ (xIdx v))) w := by
      have hrb := FirstBranchRoute.read_before (readEdge gs) out (read_order clean) live hv
      rw [hX v] at hrb
      exact (hrb (le_of_lt hlt)).1
    have huniq := FirstBranchRoute.boundary_unique (readEdge gs) out (read_order clean) hterm
      (FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs (σ (xIdx v))))
      hfol (FirstBranchRoute.first_path (readEdge gs) out (read_order clean) live (inputWire gs (σ (xIdx v))))
    rw [hX v] at huniq
    exact hne huniq
  have hasX_unique_reader {a b c : Fin (9 + gs.length)} (ha : hasX a = true) (hne : a ≠ out)
      (hab : readEdge gs a b) (hac : readEdge gs a c) : b = c := by
    by_contra hbc
    exact hasX_no_branch ha hne ⟨b, c, hab, hac, hbc⟩
  have hasX_ancestors_disjoint {w a b : Fin (9 + gs.length)} (hab : a ≠ b)
      (haw : readEdge gs a w) (hbw : readEdge gs b w)
      {u : Fin (9 + gs.length)} (hu : hasX u = true)
      (hua : Relation.ReflTransGen (readEdge gs) u a)
      (hub : Relation.ReflTransGen (readEdge gs) u b) : False := by
    have ha_lt : a < w := read_order clean haw
    have hb_lt : b < w := read_order clean hbw
    have hw_le : w ≤ out := wire_le_output clean out live w
    have hfol : ∀ {x y : Fin (9 + gs.length)}, hasX x = true → y < w →
        Relation.ReflTransGen (readEdge gs) x y →
        Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) x y := by
      intro x y hx hyw hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail z z' hxz hzz' ih =>
        have hz_lt : z < z' := read_order clean hzz'
        have hz_ne : z ≠ out := ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hz_lt (le_of_lt hyw)) hw_le)
        have hzx : hasX z = true := by
          clear ih hzz' hz_lt hz_ne hyw
          induction hxz with
          | refl => exact hx
          | tail _ hstep ih' => exact hasX_step ih' hstep
        have hnot : ¬ FirstBranchRoute.Terminal (readEdge gs) out z := fun ht =>
          ht.elim hz_ne (hasX_no_branch hzx hz_ne)
        exact (ih (lt_trans hz_lt hyw)).tail ⟨hzz', hnot⟩
    have hfa := hfol hu ha_lt hua
    have hfb := hfol hu hb_lt hub
    have hlin : ∀ {x y z : Fin (9 + gs.length)},
        Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) x y →
        Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) x z →
        Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) y z ∨
        Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) z y := by
      intro x y z hxy
      induction hxy using Relation.ReflTransGen.head_induction_on with
      | refl => intro hxz; exact Or.inl hxz
      | @head x1 x2 h12 h2y ih =>
        intro hxz
        cases hxz using Relation.ReflTransGen.head_induction_on with
        | refl => exact Or.inr (Relation.ReflTransGen.head h12 h2y)
        | head h13 h3z =>
          have h23 : x2 = _ := FirstBranchRoute.follow_unique (readEdge gs) out h12 h13
          subst h23
          exact ih h3z
    have no_path : ∀ {p q : Fin (9 + gs.length)}, p ≠ q → hasX p = true →
        readEdge gs p w → q < w →
        ¬ Relation.ReflTransGen (FirstBranchRoute.Follow (readEdge gs) out) p q := by
      intro p q hpq hp hpw hqw hpath
      cases hpath using Relation.ReflTransGen.head_induction_on with
      | refl => exact hpq rfl
      | head hpp' hp'q =>
        have hp_ne : p ≠ out := ne_of_lt (lt_of_lt_of_le (read_order clean hpw) hw_le)
        have heq : _ = w := hasX_unique_reader hp hp_ne hpp'.1 hpw
        subst heq
        have hle := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) (FirstBranchRoute.follows_is_read_path (readEdge gs) out hp'q)
        exact not_lt_of_ge hle hqw
    have hax : hasX a = true := by
      clear hfa hfb hab haw hbw ha_lt hb_lt hub
      induction hua with | refl => exact hu | tail _ hs ih => exact hasX_step ih hs
    have hbx : hasX b = true := by
      clear hfa hfb hab haw hbw ha_lt hb_lt hua hax
      induction hub with | refl => exact hu | tail _ hs ih => exact hasX_step ih hs
    rcases hlin hfa hfb with h | h
    · exact no_path hab hax haw hb_lt h
    · exact no_path hab.symm hbx hbw ha_lt h
  -- PureY masks!
  let pureFn (w : Fin (9 + gs.length)) (neg : Bool) (y : Nat) : Bool :=
    if hy : y < 32 then vl gs (combineXY σinv (fun _ => false) ⟨y, hy⟩) w.val ^^ neg else false
  let pureMask (w : Fin (9 + gs.length)) (neg : Bool) : Nat := maskRec (pureFn w neg) 32
  have pureMask_bit (w : Fin (9 + gs.length)) (neg : Bool) (y : Fin 32) :
      (pureMask w neg).testBit y.val = (vl gs (combineXY σinv (fun _ => false) y) w.val ^^ neg) := by
    simp [pureMask, maskRec_testBit, pureFn, y.isLt]
  have pureMask_eval {w : Fin (9 + gs.length)} (hnx : hasX w = false) (neg : Bool)
      (x : Fin 4 → Bool) (y : Fin 32) :
      (pureMask w neg).testBit y.val = (vl gs (combineXY σinv x y) w.val ^^ neg) := by
    rw [pureMask_bit]
    congr 1
    apply agree_on_input_ancestors clean
    intro i hpath
    have hni : ∀ v : Fin 4, i ≠ σ (xIdx v) := by
      intro v heq
      subst heq
      have ht : hasX w = true := by simp only [hasX, decide_eq_true_eq]; exact ⟨v, hpath⟩
      rw [ht] at hnx; exact Bool.noConfusion hnx
    have hinv_not : σinv i ≠ 0 ∧ σinv i ≠ 3 ∧ σinv i ≠ 6 ∧ σinv i ≠ 7 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact hni 0 (by rw [← hinv2 i, h]; rfl)
      · intro h; exact hni 1 (by rw [← hinv2 i, h]; rfl)
      · intro h; exact hni 2 (by rw [← hinv2 i, h]; rfl)
      · intro h; exact hni 3 (by rw [← hinv2 i, h]; rfl)
    simp only [combineXY]
    generalize hk : σinv i = k at hinv_not ⊢
    fin_cases k <;> simp_all [baseCombine]
  -- Gate decoding helper for CleanL 9 gs:
  have clean_gate_cases : ∀ (w : Fin (9 + gs.length)) (hw9 : 9 ≤ w.val),
      let g := gs[w.val - 9]'(by have := w.isLt; omega)
      (∃ a : Fin (9 + gs.length), a.val < w.val ∧ g.op = .not ∧ g.inputs = [a.val] ∧ readEdge gs a w) ∨
      (∃ a b : Fin (9 + gs.length), a.val < w.val ∧ b.val < w.val ∧ a ≠ b ∧
        (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a.val, b.val] ∧ readEdge gs a w ∧ readEdge gs b w) := by
    intro w hw9
    have hp : w.val - 9 < gs.length := by have := w.isLt; omega
    have hcg := clean (w.val - 9) gs[w.val - 9] (by rw [List.getElem?_eq_getElem hp])
    have hidx : 9 + (w.val - 9) = w.val := by omega
    rw [hidx] at hcg
    rcases hcg with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
    · left
      let a : Fin (9 + gs.length) := ⟨j, by omega⟩
      refine ⟨a, hj, hop, hin, w.val - 9, gs[w.val - 9], List.getElem?_eq_getElem hp, by omega, by simp [hin, a]⟩
    · right
      let a : Fin (9 + gs.length) := ⟨j, by omega⟩
      let b : Fin (9 + gs.length) := ⟨k, by omega⟩
      have hnd := distinct w
      have hpred : (predecessors clean w).map Fin.val = gs[w.val - 9].inputs :=
        predecessors_val_gate clean w (List.getElem?_eq_getElem hp) (by omega)
      have hab : a ≠ b := by
        intro heq
        have hjk : j = k := congrArg Fin.val heq
        subst hjk
        rw [hin] at hpred
        have hnd2 : ([j, j] : List ℕ).Nodup := by
          rw [← hpred]; exact hnd.map Fin.val_injective
        simp at hnd2
      refine ⟨a, b, hj, hk, hab, hop, hin,
        ⟨w.val - 9, gs[w.val - 9], List.getElem?_eq_getElem hp, by omega, by simp [hin, a]⟩,
        ⟨w.val - 9, gs[w.val - 9], List.getElem?_eq_getElem hp, by omega, by simp [hin, b]⟩⟩
  -- Set of hasX non-NOT gate ancestors of w:
  let ancNonNot (w : Fin (9 + gs.length)) : Finset (Fin gs.length) :=
    Finset.univ.filter fun p =>
      let u : Fin (9 + gs.length) := ⟨9 + p.val, by omega⟩
      hasX u = true ∧ !isNotGate gs[p.val].op ∧ Relation.ReflTransGen (readEdge gs) u w
  -- Main strong induction on w proving all 5 invariants of buildXTree!
  have build_spec : ∀ (w : ℕ) (hw : w < 9 + gs.length) (hx : hasX ⟨w, hw⟩ = true) (neg : Bool),
      let t := buildXTree gs σinv hasX pureMask w neg
      (∀ x y, t.eval x y = (vl gs (combineXY σinv x y) w ^^ neg)) ∧
      t.leaves.Nodup ∧
      (∀ v : Fin 4, v ∈ t.leaves ↔ Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) ⟨w, hw⟩) ∧
      t.gateCount ≤ (ancNonNot ⟨w, hw⟩).card ∧
      (∀ m ∈ t.allMasks, ∃ u : Fin (9 + gs.length), hasX u = false ∧ (m = pureMask u false ∨ m = pureMask u true)) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hx neg
      by_cases hw9 : w < 9
      · -- Input wire: must be σ (xIdx v) for a unique v : Fin 4!
        have hx' : ∃ v : Fin 4, Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) ⟨w, hw⟩ := by
          simpa only [hasX, decide_eq_true_eq] using hx
        obtain ⟨v0, hv0⟩ := hx'
        have hpath_eq : ∀ (v : Fin 4),
            Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) ⟨w, hw⟩ ↔
              inputWire gs (σ (xIdx v)) = ⟨w, hw⟩ := by
          intro v
          constructor
          · intro hp
            cases hp with
            | refl => rfl
            | tail _ hbc =>
              obtain ⟨p, g, _, hcw, _⟩ := hbc
              dsimp at hcw; omega
          · intro heq; rw [heq]
        have hv0eq : ⟨w, hw9⟩ = σ (xIdx v0) := by
          have := (hpath_eq v0).mp hv0
          exact Fin.ext (congrArg Fin.val this).symm
        have hinv_eq : σinv ⟨w, hw9⟩ = xIdx v0 := by rw [hv0eq, hinv1]
        have hbuild : buildXTree gs σinv hasX pureMask w neg = .leaf v0 neg := by
          rw [buildXTree]; simp only [hw9, ↓reduceDIte, hinv_eq]
          fin_cases v0 <;> rfl
        rw [hbuild]
        refine ⟨?_, List.nodup_singleton v0, ?_, Nat.zero_le _, by simp [XTree.allMasks]⟩
        · intro x y
          rw [vl_input gs (combineXY σinv x y) w hw9]
          simp only [XTree.eval, combineXY, hinv_eq]
          fin_cases v0 <;> rfl
        · intro v
          simp only [XTree.leaves, List.mem_singleton, hpath_eq]
          constructor
          · rintro rfl; exact Fin.ext (congrArg Fin.val hv0eq).symm
          · intro heq
            have h1 : σ (xIdx v) = σ (xIdx v0) := Fin.ext ((congrArg Fin.val heq).trans (congrArg Fin.val hv0eq))
            have h2 : xIdx v = xIdx v0 := by
              have := congrArg σinv h1; rwa [hinv1, hinv1] at this
            fin_cases v <;> fin_cases v0 <;> first | rfl | exact absurd h2 (by decide)
      · -- Gate wire: w ≥ 9
        have h9le : 9 ≤ w := by omega
        let wFin : Fin (9 + gs.length) := ⟨w, hw⟩
        have hvl_gate : ∀ x, vl gs x w =
            gs[w - 9].op.eval (gs[w - 9].inputs.map fun i => vl gs x i) := fun x => by
          have h := vl_gate gs clean x (w - 9) gs[w - 9] (List.getElem?_eq_getElem (by omega))
          simpa [show 9 + (w - 9) = w by omega] using h
        have hanc_sub : ∀ {a : Fin (9 + gs.length)}, readEdge gs a wFin → ancNonNot a ⊆ ancNonNot wFin := by
          intro a haw p hp
          simp only [ancNonNot, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact ⟨hp.1, hp.2.1, hp.2.2.tail haw⟩
        have hreach_pred : ∀ (v : Fin 4) (S : Fin (9 + gs.length) → Prop),
            (∀ u, readEdge gs u wFin → S u) →
            Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) wFin →
            ∃ u, S u ∧ Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) u := by
          intro v S hS hp
          rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hiu, huw⟩
          · have h1 := congrArg Fin.val heq
            have h2 : (inputWire gs (σ (xIdx v))).val < 9 := (σ (xIdx v)).isLt
            dsimp [wFin] at h1; omega
          · exact ⟨u, hS u huw, hiu⟩
        rcases clean_gate_cases wFin h9le with ⟨a, haw_lt, hop, hin, haw⟩ | ⟨a, b, haw_lt, hbw_lt, hab, hop, hin, haw, hbw⟩
        · -- NOT gate with single input a!
          dsimp only [wFin] at hop hin haw_lt
          have hax : hasX a = true := by
            simp only [hasX, decide_eq_true_eq] at hx ⊢
            obtain ⟨v, hv⟩ := hx
            obtain ⟨u, hu, hvu⟩ := hreach_pred v (fun u => u = a) (fun u huw => by
              obtain ⟨p, g, hpg, hpw, hmem⟩ := huw
              have hp_eq : p = w - 9 := by dsimp [wFin] at hpw; omega
              subst hp_eq
              have hg_eq : g = gs[w - 9] := Option.some.inj (by rw [← hpg, List.getElem?_eq_getElem (by omega)])
              subst hg_eq; rw [hin] at hmem; simp at hmem; exact Fin.ext hmem) hv
            subst hu; exact ⟨v, hvu⟩
          have hbuild : buildXTree gs σinv hasX pureMask w neg = buildXTree gs σinv hasX pureMask a.val (!neg) := by
            rw [buildXTree]; simp only [hw9, hw, ↓reduceDIte, hop, hin, haw_lt]
          rw [hbuild]
          obtain ⟨heval, hnd, hlv, hgc, hms⟩ := ih a.val haw_lt a.isLt hax (!neg)
          refine ⟨?_, hnd, ?_, hgc.trans (Finset.card_le_card (hanc_sub haw)), hms⟩
          · intro x y
            rw [heval x y, hvl_gate, hop, hin]
            simp only [List.map_cons, List.map_nil, GateOp.eval]
            cases vl gs (combineXY σinv x y) a.val <;> cases neg <;> rfl
          · intro v
            rw [hlv v]
            constructor
            · intro hp; exact hp.tail haw
            · intro hp
              obtain ⟨u, hu, hvu⟩ := hreach_pred v (fun u => u = a) (fun u huw => by
                obtain ⟨p, g, hpg, hpw, hmem⟩ := huw
                have hp_eq : p = w - 9 := by dsimp [wFin] at hpw; omega
                subst hp_eq
                have hg_eq : g = gs[w - 9] := Option.some.inj (by rw [← hpg, List.getElem?_eq_getElem (by omega)])
                subst hg_eq; rw [hin] at hmem; simp at hmem; exact Fin.ext hmem) hp
              subst hu; exact hvu
        · -- Binary AND/OR gate with inputs [a, b], a ≠ b!
          dsimp only [wFin] at hop hin haw_lt hbw_lt
          have hpred_ab : ∀ u, readEdge gs u wFin → u = a ∨ u = b := by
            intro u huw
            obtain ⟨p, g, hpg, hpw, hmem⟩ := huw
            have hp_eq : p = w - 9 := by dsimp [wFin] at hpw; omega
            subst hp_eq
            have hg_eq : g = gs[w - 9] := Option.some.inj (by rw [← hpg, List.getElem?_eq_getElem (by omega)])
            subst hg_eq; rw [hin] at hmem; simp at hmem
            rcases hmem with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Fin.ext h)
          let pFin : Fin gs.length := ⟨w - 9, by omega⟩
          have hp_in : pFin ∈ ancNonNot wFin := by
            simp only [ancNonNot, Finset.mem_filter, Finset.mem_univ, true_and]
            have hw_eq : (⟨9 + pFin.val, by omega⟩ : Fin (9 + gs.length)) = wFin := Fin.ext (by dsimp [pFin, wFin]; omega)
            rw [hw_eq]
            refine ⟨hx, ?_, Relation.ReflTransGen.refl⟩
            change (!isNotGate gs[w - 9].op) = true
            rcases hop with h | h <;> simp [h, isNotGate]
          have hp_not_anc : ∀ (c : Fin (9 + gs.length)), c.val < w → pFin ∉ ancNonNot c := by
            intro c hcw hmem
            simp only [ancNonNot, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            have hle : (9 + pFin.val) ≤ c.val := FirstBranchRoute.path_forward (readEdge gs) (read_order clean) hmem.2.2
            dsimp [pFin] at hle
            omega
          have hax_or_hbx : hasX a = true ∨ hasX b = true := by
            simp only [hasX, decide_eq_true_eq] at hx ⊢
            obtain ⟨v, hv⟩ := hx
            obtain ⟨u, hu, hvu⟩ := hreach_pred v (fun u => u = a ∨ u = b) hpred_ab hv
            rcases hu with rfl | rfl
            · exact Or.inl ⟨v, hvu⟩
            · exact Or.inr ⟨v, hvu⟩
          have hbuild_bin (isAnd : Bool) (hgate_op : gs[w - 9].op = if isAnd then .and else .or) :
              let t := buildXTree gs σinv hasX pureMask w neg
              (∀ x y, t.eval x y = (vl gs (combineXY σinv x y) w ^^ neg)) ∧
              t.leaves.Nodup ∧
              (∀ v : Fin 4, v ∈ t.leaves ↔ Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) wFin) ∧
              t.gateCount ≤ (ancNonNot wFin).card ∧
              (∀ m ∈ t.allMasks, ∃ u : Fin (9 + gs.length), hasX u = false ∧ (m = pureMask u false ∨ m = pureMask u true)) := by
            have hreach_iff (v : Fin 4) :
                Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) wFin ↔
                  Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) a ∨
                  Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) b := by
              constructor
              · intro hp
                obtain ⟨u, hu, hvu⟩ := hreach_pred v (fun u => u = a ∨ u = b) hpred_ab hp
                rcases hu with rfl | rfl
                · exact Or.inl hvu
                · exact Or.inr hvu
              · rintro (h | h)
                · exact h.tail haw
                · exact h.tail hbw
            have hgate_eval : ∀ (x : Fin 9 → Bool), (vl gs x w ^^ neg) =
                if (isAnd != neg) then (vl gs x a.val ^^ neg) && (vl gs x b.val ^^ neg)
                else (vl gs x a.val ^^ neg) || (vl gs x b.val ^^ neg) := by
              intro x
              rw [hvl_gate x, hgate_op, hin]
              cases isAnd <;> cases neg <;> simp [GateOp.eval] <;>
                cases vl gs x a.val <;> cases vl gs x b.val <;> rfl
            cases hxa : hasX a <;> cases hxb : hasX b
            · exfalso; rcases hax_or_hbx with h | h <;> simp_all
            · -- only b has X, a is pureY!
              obtain ⟨heval, hnd, hlv, hgc, hms⟩ := ih b.val hbw_lt b.isLt hxb neg
              rw [Fin.eta] at hgc
              have hnot_a : ∀ v : Fin 4, ¬ Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) a := by
                intro v hv
                have : hasX a = true := by simp only [hasX, decide_eq_true_eq]; exact ⟨v, hv⟩
                rw [this] at hxa; exact Bool.noConfusion hxa
              have hcard_le : 1 + (ancNonNot b).card ≤ (ancNonNot wFin).card := by
                have hsub : insert pFin (ancNonNot b) ⊆ ancNonNot wFin :=
                  Finset.insert_subset_iff.mpr ⟨hp_in, hanc_sub hbw⟩
                have hci := Finset.card_insert_of_notMem (hp_not_anc b hbw_lt)
                have hle := Finset.card_le_card hsub
                omega
              have hmask_a : pureMask a neg = pureMask a false ∨ pureMask a neg = pureMask a true := by
                cases neg <;> simp
              cases isAnd <;> cases neg
              all_goals
                dsimp only
                rw [buildXTree]
                simp only [hw9, hw, ↓reduceDIte, hgate_op, hin, haw_lt, hbw_lt, and_self, hxa, hxb,
                  Bool.false_eq_true, Bool.false_and, Bool.not_true, Bool.not_false, ↓reduceIte, Fin.eta]
                refine ⟨fun x y => ?_, hnd, fun v => ?_, ?_, ?_⟩
                · simp only [XTree.eval, heval x y, pureMask_eval hxa _ x y, hgate_eval]
                  cases vl gs (combineXY σinv x y) a.val <;> cases vl gs (combineXY σinv x y) b.val <;> rfl
                · simp only [XTree.leaves, hlv v, hreach_iff v, hnot_a v, false_or]
                · simp only [XTree.gateCount]; omega
                · intro m hm
                  simp only [XTree.allMasks, List.mem_cons] at hm
                  rcases hm with rfl | hm'
                  · exact ⟨a, hxa, hmask_a⟩
                  · exact hms m hm'
            · -- only a has X, b is pureY!
              obtain ⟨heval, hnd, hlv, hgc, hms⟩ := ih a.val haw_lt a.isLt hxa neg
              rw [Fin.eta] at hgc
              have hnot_b : ∀ v : Fin 4, ¬ Relation.ReflTransGen (readEdge gs) (inputWire gs (σ (xIdx v))) b := by
                intro v hv
                have : hasX b = true := by simp only [hasX, decide_eq_true_eq]; exact ⟨v, hv⟩
                rw [this] at hxb; exact Bool.noConfusion hxb
              have hcard_le : 1 + (ancNonNot a).card ≤ (ancNonNot wFin).card := by
                have hsub : insert pFin (ancNonNot a) ⊆ ancNonNot wFin :=
                  Finset.insert_subset_iff.mpr ⟨hp_in, hanc_sub haw⟩
                have hci := Finset.card_insert_of_notMem (hp_not_anc a haw_lt)
                have hle := Finset.card_le_card hsub
                omega
              have hmask_b : pureMask b neg = pureMask b false ∨ pureMask b neg = pureMask b true := by
                cases neg <;> simp
              cases isAnd <;> cases neg
              all_goals
                dsimp only
                rw [buildXTree]
                simp only [hw9, hw, ↓reduceDIte, hgate_op, hin, haw_lt, hbw_lt, and_self, hxa, hxb,
                  Bool.false_eq_true, Bool.true_and, Bool.not_true, Bool.not_false, ↓reduceIte, Fin.eta]
                refine ⟨fun x y => ?_, hnd, fun v => ?_, ?_, ?_⟩
                · simp only [XTree.eval, heval x y, pureMask_eval hxb _ x y, hgate_eval]
                  cases vl gs (combineXY σinv x y) a.val <;> cases vl gs (combineXY σinv x y) b.val <;> rfl
                · simp only [XTree.leaves, hlv v, hreach_iff v, hnot_b v, or_false]
                · simp only [XTree.gateCount]; omega
                · intro m hm
                  simp only [XTree.allMasks, List.mem_cons] at hm
                  rcases hm with rfl | hm'
                  · exact ⟨b, hxb, hmask_b⟩
                  · exact hms m hm'
            · -- BOTH a and b have X!
              obtain ⟨heva, hnda, hlva, hgca, hmsa⟩ := ih a.val haw_lt a.isLt hxa neg
              obtain ⟨hevb, hndb, hlvb, hgcb, hmsb⟩ := ih b.val hbw_lt b.isLt hxb neg
              rw [Fin.eta] at hgca hgcb
              have hlv_disj : ∀ v ∈ (buildXTree gs σinv hasX pureMask a.val neg).leaves,
                  v ∉ (buildXTree gs σinv hasX pureMask b.val neg).leaves := by
                intro v hva hvb
                have pa := (hlva v).mp hva
                have pb := (hlvb v).mp hvb
                have hvin : hasX (inputWire gs (σ (xIdx v))) = true := by
                  simp only [hasX, decide_eq_true_eq]; exact ⟨v, Relation.ReflTransGen.refl⟩
                exact hasX_ancestors_disjoint hab haw hbw hvin pa pb
              have hnd_ab : ((buildXTree gs σinv hasX pureMask a.val neg).leaves ++
                  (buildXTree gs σinv hasX pureMask b.val neg).leaves).Nodup :=
                List.nodup_append.mpr ⟨hnda, hndb, fun u hu v hv e => hlv_disj u hu (e ▸ hv)⟩
              have hanc_disj : Disjoint (ancNonNot a) (ancNonNot b) := by
                rw [Finset.disjoint_left]
                intro p hpa hpb
                simp only [ancNonNot, Finset.mem_filter, Finset.mem_univ, true_and] at hpa hpb
                exact hasX_ancestors_disjoint hab haw hbw hpa.1 hpa.2.2 hpb.2.2
              have hcard_le : 1 + (ancNonNot a).card + (ancNonNot b).card ≤ (ancNonNot wFin).card := by
                have hsub : insert pFin (ancNonNot a ∪ ancNonNot b) ⊆ ancNonNot wFin :=
                  Finset.insert_subset_iff.mpr ⟨hp_in, Finset.union_subset (hanc_sub haw) (hanc_sub hbw)⟩
                have hp_not : pFin ∉ ancNonNot a ∪ ancNonNot b := by
                  rw [Finset.mem_union, not_or]
                  exact ⟨hp_not_anc a haw_lt, hp_not_anc b hbw_lt⟩
                have hci := Finset.card_insert_of_notMem hp_not
                have hcu := Finset.card_union_of_disjoint hanc_disj
                have hle := Finset.card_le_card hsub
                omega
              cases isAnd <;> cases neg
              all_goals
                dsimp only
                rw [buildXTree]
                simp only [hw9, hw, ↓reduceDIte, hgate_op, hin, haw_lt, hbw_lt, and_self, hxa, hxb,
                  Bool.false_eq_true, Bool.true_and, Bool.not_true, Bool.not_false, ↓reduceIte, Fin.eta]
                refine ⟨fun x y => ?_, hnd_ab, fun v => ?_, ?_, ?_⟩
                · simp only [XTree.eval, heva x y, hevb x y, hgate_eval]
                  cases vl gs (combineXY σinv x y) a.val <;> cases vl gs (combineXY σinv x y) b.val <;> rfl
                · simp only [XTree.leaves, List.mem_append, hlva v, hlvb v, hreach_iff v]
                · simp only [XTree.gateCount]; omega
                · intro m hm
                  simp only [XTree.allMasks, List.mem_append] at hm
                  rcases hm with h | h
                  · exact hmsa m h
                  · exact hmsb m h
          rcases hop with hand | hor
          · exact hbuild_bin true hand
          · exact hbuild_bin false hor
  -- Apply build_spec to out!
  have houtX : hasX out = true := by
    simp only [hasX, decide_eq_true_eq]
    refine ⟨0, ?_⟩
    have fp := FirstBranchRoute.first_path (readEdge gs) out (read_order clean) live (inputWire gs (σ (xIdx 0)))
    rw [hX 0] at fp
    exact FirstBranchRoute.follows_is_read_path (readEdge gs) out fp
  obtain ⟨heval_out, hnd_out, hlv_out, hgc_out, hms_out⟩ := build_spec out.val out.isLt houtX false
  let t : XTree := buildXTree gs σinv hasX pureMask out.val false
  have ht_cov : ∀ v : Fin 4, v ∈ t.leaves := fun v => by
    rw [hlv_out v]
    have fp := FirstBranchRoute.first_path (readEdge gs) out (read_order clean) live (inputWire gs (σ (xIdx v)))
    rw [hX v] at fp
    exact FirstBranchRoute.follows_is_read_path (readEdge gs) out fp
  have ht_eval : ∀ x y, t.eval x y = targetXY x y := fun x y => by
    have h1 := heval_out x y
    simp only [Bool.xor_false] at h1
    rw [h1, computes]
    change target9 (fun i => baseCombine x y (σinv i)) = targetXY x y
    rw [haut, target9_baseCombine]
  -- Extract PureY sequence from all pure-Y non-NOT gates in gs!
  let isPureNonNot (p : Fin gs.length) : Bool :=
    !hasX ⟨9 + p.val, by omega⟩ && !isNotGate gs[p.val].op
  let pureGates : List (Fin gs.length) := (List.finRange gs.length).filter isPureNonNot
  let pureYSeq : List Nat := pureGates.map fun p => canon (pureMask ⟨9 + p.val, by omega⟩ false)
  -- Budget accounting: ancNonNot out and pureGates are disjoint subsets of nonNot gates!
  have hdisj_count : t.gateCount + pureYSeq.length ≤ nonNotCount gs := by
    let nonNotSet : Finset (Fin gs.length) := Finset.univ.filter fun p => !isNotGate gs[p.val].op
    let pureSet : Finset (Fin gs.length) := Finset.univ.filter fun p => isPureNonNot p = true
    have hnn_card : nonNotSet.card = nonNotCount gs := by
      unfold nonNotCount
      rw [List.countP_eq_length_filter]
      have h1 : nonNotSet.card = ((List.finRange gs.length).filter fun p => !isNotGate gs[p.val].op).length := by
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange gs.length).filter _)]
        congr 1; ext p; simp [nonNotSet]
      rw [h1]
      have hmap : gs = (List.finRange gs.length).map (fun p => gs[p.val]) := by
        apply List.ext_getElem (by simp)
        intro i h1 h2; simp
      conv_rhs => rw [hmap, List.filter_map, List.length_map]
      rfl
    have hpure_len : pureYSeq.length = pureSet.card := by
      simp only [pureYSeq, List.length_map, pureGates]
      rw [← List.toFinset_card_of_nodup ((List.nodup_finRange gs.length).filter _)]
      congr 1; ext p; simp [pureSet]
    have hsub : ancNonNot out ∪ pureSet ⊆ nonNotSet := by
      intro p hp
      simp only [Finset.mem_union, ancNonNot, pureSet, nonNotSet, isPureNonNot,
        Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
      rcases hp with h | h
      · exact h.2.1
      · exact h.2
    have hdj : Disjoint (ancNonNot out) pureSet := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [ancNonNot, pureSet, isPureNonNot, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, Bool.not_eq_true'] at h1 h2
      rw [h1.1] at h2; exact Bool.noConfusion h2.1
    have hcu := Finset.card_union_of_disjoint hdj
    have hle := Finset.card_le_card hsub
    have hgc_t : t.gateCount ≤ (ancNonNot out).card := hgc_out
    omega
  -- Prove every pureY wire u < 9 + limit has canon (pureMask u false) in inList ++ pureGates(< limit)!
  have pure_before : ∀ (limit : ℕ) (hlim : limit ≤ gs.length) (u : Fin (9 + gs.length)),
      u.val < 9 + limit → hasX u = false →
      canon (pureMask u false) ∈ inList ++
        ((List.finRange gs.length).filter fun p => p.val < limit && isPureNonNot p).map
          (fun p => canon (pureMask ⟨9 + p.val, by omega⟩ false)) := by
    intro limit hlim u
    induction hu_val : u.val using Nat.strongRecOn generalizing u with
    | ind k ih =>
      intro hult hnx
      subst hu_val
      by_cases hu9 : u.val < 9
      · -- PureY input wire: must be σ (yIdx j) for some j : Fin 5!
        have hnotx : σinv ⟨u.val, hu9⟩ ≠ 0 ∧ σinv ⟨u.val, hu9⟩ ≠ 3 ∧ σinv ⟨u.val, hu9⟩ ≠ 6 ∧ σinv ⟨u.val, hu9⟩ ≠ 7 := by
          have hni : ∀ v : Fin 4, (⟨u.val, hu9⟩ : Fin 9) ≠ σ (xIdx v) := by
            intro v heq
            have hu_eq : u = inputWire gs (σ (xIdx v)) := Fin.ext (show u.val = (σ (xIdx v)).val from congrArg Fin.val heq)
            have ht : hasX u = true := by
              simp only [hasX, decide_eq_true_eq]; exact ⟨v, hu_eq ▸ Relation.ReflTransGen.refl⟩
            rw [ht] at hnx; exact Bool.noConfusion hnx
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h; exact hni 0 (by rw [← hinv2 ⟨u.val, hu9⟩, h]; rfl)
          · intro h; exact hni 1 (by rw [← hinv2 ⟨u.val, hu9⟩, h]; rfl)
          · intro h; exact hni 2 (by rw [← hinv2 ⟨u.val, hu9⟩, h]; rfl)
          · intro h; exact hni 3 (by rw [← hinv2 ⟨u.val, hu9⟩, h]; rfl)
        have hmem_in : ∃ j : Fin 5, pureMask u false = inY j := by
          have hexj : ∃ j : Fin 5, σinv ⟨u.val, hu9⟩ = yIdx j := by
            generalize hk : σinv ⟨u.val, hu9⟩ = kv at hnotx
            fin_cases kv
            · exact (hnotx.1 rfl).elim
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
            · exact (hnotx.2.1 rfl).elim
            · exact ⟨2, rfl⟩
            · exact ⟨3, rfl⟩
            · exact (hnotx.2.2.1 rfl).elim
            · exact (hnotx.2.2.2 rfl).elim
            · exact ⟨4, rfl⟩
          obtain ⟨j, hj⟩ := hexj
          refine ⟨j, ?_⟩
          apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 32
          · rw [pureMask_bit u false ⟨i, hi⟩, vl_input gs _ u.val hu9, inY_bit j ⟨i, hi⟩]
            simp only [Bool.xor_false, combineXY, hj]
            fin_cases j <;> rfl
          · rw [show (pureMask u false).testBit i = false by simp [pureMask, maskRec_testBit, hi]]
            have hlt32 : inY j < 2 ^ 32 := by fin_cases j <;> decide
            have : (inY j).testBit i = false :=
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt32 (Nat.pow_le_pow_right (by omega) (by omega)))
            exact this.symm
        obtain ⟨j, hj⟩ := hmem_in
        rw [hj, canon_inY j]
        exact List.mem_append_left _ (inY_mem_inList j)
      · have h9le : 9 ≤ u.val := by omega
        rcases clean_gate_cases u h9le with ⟨a, hau_lt, hop, hin, hau⟩ | ⟨a, b, hau_lt, hbu_lt, _, hop, hin, hau, hbu⟩
        · -- PureY NOT gate: canon (pureMask u false) = canon (pureMask a false)!
          have hna : hasX a = false := by
            cases h : hasX a; rfl
            have := hasX_step h hau; rw [this] at hnx; exact Bool.noConfusion hnx
          have heq : pureMask u false = not32 (pureMask a false) := by
            apply Nat.eq_of_testBit_eq; intro i
            by_cases hi : i < 32
            · rw [not32_testBit hi, pureMask_bit u false ⟨i, hi⟩, pureMask_bit a false ⟨i, hi⟩]
              have hvg := vl_gate gs clean (combineXY σinv (fun _ => false) ⟨i, hi⟩) (u.val - 9) gs[u.val - 9] (List.getElem?_eq_getElem (by omega))
              rw [show 9 + (u.val - 9) = u.val by omega, hop, hin] at hvg
              simp [hvg, GateOp.eval]
            · rw [show (pureMask u false).testBit i = false by simp [pureMask, maskRec_testBit, hi]]
              rw [not32_maskRec, maskRec_testBit]; simp [hi]
          rw [heq, canon_maskRec_not]
          exact ih a.val hau_lt a rfl (by omega) hna
        · -- PureY non-NOT gate: u itself is in pureGates(< limit)!
          let pFin : Fin gs.length := ⟨u.val - 9, by omega⟩
          have hp_mem : pFin ∈ (List.finRange gs.length).filter (fun p => p.val < limit && isPureNonNot p) := by
            rw [List.mem_filter]
            refine ⟨List.mem_finRange pFin, ?_⟩
            simp only [Bool.and_eq_true, decide_eq_true_eq, isPureNonNot, Bool.not_eq_true']
            have hu_eq : (⟨9 + pFin.val, by omega⟩ : Fin (9 + gs.length)) = u := Fin.ext (by dsimp [pFin]; omega)
            rw [hu_eq]
            refine ⟨by dsimp [pFin]; omega, hnx, ?_⟩
            change isNotGate gs[u.val - 9].op = false
            rcases hop with h | h <;> simp [h, isNotGate]
          apply List.mem_append_right
          rw [List.mem_map]
          refine ⟨pFin, hp_mem, ?_⟩
          congr 1; congr 1; apply Fin.ext; dsimp [pFin]; omega
  -- Prove pureYSeq is a ValidPureSeq!
  have hvalid_seq : ValidPureSeq pureYSeq := by
    intro k hk
    have hk' : k < pureGates.length := by simpa [pureYSeq] using hk
    let p := pureGates[k]'hk'
    have hp_mem : p ∈ pureGates := List.getElem_mem hk'
    have hp_cond : isPureNonNot p = true := (List.mem_filter.mp hp_mem).2
    simp only [isPureNonNot, Bool.and_eq_true, Bool.not_eq_true'] at hp_cond
    let u : Fin (9 + gs.length) := ⟨9 + p.val, by omega⟩
    have hnx : hasX u = false := hp_cond.1
    have hnotnot : isNotGate gs[p.val].op = false := hp_cond.2
    -- Every q ∈ pureGates with q.val < p.val appears in pureGates.take k!
    have hsub_take : ∀ q : Fin gs.length,
        q ∈ (List.finRange gs.length).filter (fun q => q.val < p.val && isPureNonNot q) →
        q ∈ pureGates.take k := by
      intro q hq
      rw [List.mem_filter] at hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      have hqm : q ∈ pureGates := List.mem_filter.mpr ⟨List.mem_finRange q, hq.2.2⟩
      obtain ⟨idx, hidx, hqeq⟩ := List.mem_iff_getElem.mp hqm
      have hmono : ∀ i j (hi : i < pureGates.length) (hj : j < pureGates.length),
          i < j → (pureGates[i]'hi).val < (pureGates[j]'hj).val := by
        have hsort : pureGates.Pairwise (fun a b => a.val < b.val) := by
          apply List.Pairwise.filter
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          simp [hij]
        rw [List.pairwise_iff_getElem] at hsort
        exact hsort
      have hidx_lt : idx < k := by
        by_contra hge
        have hle : k ≤ idx := by omega
        rcases lt_or_eq_of_le hle with hlt | rfl
        · have := hmono k idx hk' hidx hlt
          rw [hqeq] at this; omega
        · have hqp : p = q := hqeq
          rw [hqp] at hq; exact (lt_irrefl _) hq.2.1
      rw [List.mem_iff_getElem]
      exact ⟨idx, by simp; omega, by rw [List.getElem_take]; exact hqeq⟩
    rcases clean_gate_cases u (by dsimp [u]; omega) with ⟨_, _, hop, _, _⟩ | ⟨a, b, hau_lt, hbu_lt, _, hop, hin, hau, hbu⟩
    · have hop' : gs[p.val].op = .not := by convert hop; dsimp [u]; omega
      rw [hop'] at hnotnot; simp [isNotGate] at hnotnot
    · have hna : hasX a = false := by
        cases h : hasX a; rfl
        have := hasX_step h hau; rw [this] at hnx; exact Bool.noConfusion hnx
      have hnb : hasX b = false := by
        cases h : hasX b; rfl
        have := hasX_step h hbu; rw [this] at hnx; exact Bool.noConfusion hnx
      have lift_mem (c : Fin (9 + gs.length)) (hlt : c.val < 9 + p.val) (hnc : hasX c = false) :
          canon (pureMask c false) ∈ inList ++ pureYSeq.take k := by
        have hm := pure_before p.val (le_of_lt p.isLt) c hlt hnc
        rcases List.mem_append.mp hm with h1 | h2
        · exact List.mem_append_left _ h1
        · apply List.mem_append_right
          rw [List.mem_map] at h2
          obtain ⟨q, hq, hqeq⟩ := h2
          rw [← hqeq, show pureYSeq.take k = (pureGates.take k).map _ from (List.map_take ..).symm]
          exact List.mem_map.mpr ⟨q, hsub_take q hq, rfl⟩
      have ha_mem := lift_mem a hau_lt hna
      have hb_mem := lift_mem b hbu_lt hnb
      refine ⟨canon (pureMask a false), ha_mem, canon (pureMask b false), hb_mem, ?_⟩
      have hout_eq : pureYSeq[k]'hk = canon (pureMask u false) := by
        simp [pureYSeq, p, u]
      rw [hout_eq]
      rcases hop with hand | hor
      · have hmask : pureMask u false = pureMask a false &&& pureMask b false := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and]
          by_cases hi : i < 32
          · rw [pureMask_bit u false ⟨i, hi⟩, pureMask_bit a false ⟨i, hi⟩, pureMask_bit b false ⟨i, hi⟩]
            have hvg := vl_gate gs clean (combineXY σinv (fun _ => false) ⟨i, hi⟩) p.val gs[p.val] (List.getElem?_eq_getElem p.isLt)
            have hand' : gs[p.val].op = .and := by simpa [u] using hand
            have hin' : gs[p.val].inputs = [a.val, b.val] := by simpa [u] using hin
            rw [hand', hin'] at hvg
            simpa [u, GateOp.eval] using congrArg id hvg
          · simp [pureMask, maskRec_testBit, hi]
        rw [hmask]
        exact gate_step_in_gateOuts (pureFn a false) (pureFn b false) true
      · have hmask : pureMask u false = pureMask a false ||| pureMask b false := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_or]
          by_cases hi : i < 32
          · rw [pureMask_bit u false ⟨i, hi⟩, pureMask_bit a false ⟨i, hi⟩, pureMask_bit b false ⟨i, hi⟩]
            have hvg := vl_gate gs clean (combineXY σinv (fun _ => false) ⟨i, hi⟩) p.val gs[p.val] (List.getElem?_eq_getElem p.isLt)
            have hor' : gs[p.val].op = .or := by simpa [u] using hor
            have hin' : gs[p.val].inputs = [a.val, b.val] := by simpa [u] using hin
            rw [hor', hin'] at hvg
            simpa [u, GateOp.eval] using congrArg id hvg
          · simp [pureMask, maskRec_testBit, hi]
        rw [hmask]
        exact gate_step_in_gateOuts (pureFn a false) (pureFn b false) false
  -- Every mask in t.allMasks has canon m ∈ inList ++ pureYSeq AND is maskRec f 32 for some f!
  have allMasks_in_seq : ∀ m ∈ t.allMasks,
      canon m ∈ inList ++ pureYSeq ∧ ∃ f : Nat → Bool, m = maskRec f 32 := by
    intro m hm
    obtain ⟨u, hnx, hu | hu⟩ := hms_out m hm
    · refine ⟨?_, pureFn u false, hu⟩
      rw [hu]
      have h := pure_before gs.length le_rfl u u.isLt hnx
      have hfilt : ((List.finRange gs.length).filter fun p => p.val < gs.length && isPureNonNot p) = pureGates := by
        congr 1; funext p; simp [p.isLt]
      rw [hfilt] at h; exact h
    · refine ⟨?_, pureFn u true, hu⟩
      have hnot : pureMask u true = not32 (pureMask u false) := by
        rw [not32_maskRec]; apply Nat.eq_of_testBit_eq; intro i
        by_cases hi : i < 32
        · simp [pureMask, maskRec_testBit, pureFn, hi]
        · simp [pureMask, maskRec_testBit, hi]
      rw [hu, hnot, canon_maskRec_not]
      have h := pure_before gs.length le_rfl u u.isLt hnx
      have hfilt : ((List.finRange gs.length).filter fun p => p.val < gs.length && isPureNonNot p) = pureGates := by
        congr 1; funext p; simp [p.isLt]
      rw [hfilt] at h; exact h
  -- NOW APPLY XTREE SUMMARY AND PUREY IMPOSSIBILITY!
  obtain ⟨hgc8, hpath, hgc8_eq⟩ := XTree.xtree_summary hnd_out ht_cov ht_eval
  have hgc8' : 8 ≤ t.gateCount := hgc8
  have hpure_le5 : pureYSeq.length ≤ 5 := by omega
  by_cases hle4 : pureYSeq.length ≤ 4
  · -- Extract m0, m3, m6, m7 from pathAndMasks!
    have pick (v : Fin 4) (y0 : Fin 32) (hy0 : isIndepY y0 = true) (hfalse : AvY v y0 = false) :
        ∃ m ∈ t.allMasks, (∀ y : Fin 32, isIndepY y = true → AvY v y = true → m.testBit y.val = true) ∧
          m.testBit y0.val = false := by
      have hall0 := hpath v y0 hy0
      rw [hfalse] at hall0
      have hnot : ¬ (t.pathAndMasks v).all (fun m => m.testBit y0.val) = true := by rw [hall0]; decide
      rw [List.all_eq_true] at hnot
      push Not at hnot
      obtain ⟨m, hm, hmf⟩ := hnot
      refine ⟨m, XTree.pathAndMasks_sub_allMasks v hm, ?_, by cases h : m.testBit y0.val <;> simp_all⟩
      intro y hy hav
      have hpy := hpath v y hy
      rw [hav] at hpy
      exact (List.all_eq_true.mp hpy) m hm
    obtain ⟨m0, hm0, h0s, h0f⟩ := pick 0 ⟨2, by decide⟩ (by decide) (by decide)
    obtain ⟨m3, hm3, h3s, h3f⟩ := pick 1 ⟨1, by decide⟩ (by decide) (by decide)
    obtain ⟨m6, hm6, h6s, h6f⟩ := pick 2 ⟨4, by decide⟩ (by decide) (by decide)
    obtain ⟨m7, hm7, h7s, h7f⟩ := pick 3 ⟨4, by decide⟩ (by decide) (by decide)
    obtain ⟨hc0, f0, hf0⟩ := allMasks_in_seq m0 hm0
    obtain ⟨hc3, f3, hf3⟩ := allMasks_in_seq m3 hm3
    obtain ⟨hc6, f6, hf6⟩ := allMasks_in_seq m6 hm6
    obtain ⟨hc7, f7, hf7⟩ := allMasks_in_seq m7 hm7
    subst hf0 hf3 hf6 hf7
    exact pureY_le4_impossible pureYSeq hvalid_seq hle4
      (canon (maskRec f0 32)) (canon (maskRec f3 32)) (canon (maskRec f6 32)) (canon (maskRec f7 32))
      hc0 hc3 hc6 hc7
      (isW0e2_of_mask f0 h0s h0f) (isW3e1_of_mask f3 h3s h3f)
      (isW6e4_of_mask f6 h6s h6f) (isW7e4_of_mask f7 h7s h7f)
  · -- pureYSeq.length = 5 and t.gateCount = 8!
    have hlen5 : pureYSeq.length = 5 := by omega
    have hgc_eq8 : t.gateCount = 8 := by omega
    obtain ⟨m, s, hm_spec, hs_mem, hs_ni, hs_ind⟩ := hgc8_eq hgc_eq8
    have hm_rec : ∀ v : Fin 4, canon (m v) ∈ inList ++ pureYSeq ∧ ∃ f : Nat → Bool, m v = maskRec f 32 :=
      fun v => allMasks_in_seq (m v) (hm_spec v).1
    obtain ⟨hcs, fs, hfs⟩ := allMasks_in_seq s hs_mem
    obtain ⟨hc0, f0, hf0⟩ := hm_rec 0
    obtain ⟨hc3, f3, hf3⟩ := hm_rec 1
    obtain ⟨hc6, f6, hf6⟩ := hm_rec 2
    obtain ⟨hc7, f7, hf7⟩ := hm_rec 3
    have hm0_bit : ∀ y : Fin 32, isIndepY y = true → (maskRec f0 32).testBit y.val = AvY 0 y := by rw [← hf0]; exact (hm_spec 0).2
    have hm3_bit : ∀ y : Fin 32, isIndepY y = true → (maskRec f3 32).testBit y.val = AvY 1 y := by rw [← hf3]; exact (hm_spec 1).2
    have hm6_bit : ∀ y : Fin 32, isIndepY y = true → (maskRec f6 32).testBit y.val = AvY 2 y := by rw [← hf6]; exact (hm_spec 2).2
    have hm7_bit : ∀ y : Fin 32, isIndepY y = true → (maskRec f7 32).testBit y.val = AvY 3 y := by rw [← hf7]; exact (hm_spec 3).2
    have hm_bit0 : ∀ v : Fin 4, (m v).testBit 0 = false := fun v => by
      have h1 := (hm_spec v).2 ⟨0, by decide⟩ (by decide)
      have h2 : AvY v ⟨0, by decide⟩ = false := by fin_cases v <;> decide
      exact h1.trans h2
    have hm_canon_eq (v : Fin 4) (fv : Nat → Bool) (hfv : m v = maskRec fv 32) : canon (m v) = m v := by
      rw [hfv]; unfold canon; rw [maskRec_and_all32, ← hfv, hm_bit0 v]; rfl
    have h67 : canon (m 2) ≠ canon (m 3) := fun e => by
      rw [hm_canon_eq 2 f6 hf6, hm_canon_eq 3 f7 hf7] at e
      have h1 := congrArg (fun n => n.testBit 1) e
      rw [(hm_spec 2).2 ⟨1, by decide⟩ (by decide), (hm_spec 3).2 ⟨1, by decide⟩ (by decide)] at h1
      exact Bool.noConfusion h1
    have hws : isS1 (canon (maskRec fs 32)) = true := by
      apply isS1_of_mask fs (by rw [← hfs]; exact hs_ni)
      rcases hs_ind with hall | ⟨v, _, hv⟩
      · exact ⟨0, fun y hy _ => by rw [← hfs]; exact hall y hy⟩
      · exact ⟨v, fun y hy hav => by rw [← hfs]; exact hv y hy hav⟩
    have hne_s (u : Fin 4) (fu : Nat → Bool) (hfu : m u = maskRec fu 32) : canon (m u) ≠ canon s := by
      intro e
      rw [hm_canon_eq u fu hfu] at e
      rcases hs_ind with hall | ⟨v, hmv_ni, hvs⟩
      · have hs0 : s.testBit 0 = false := hall ⟨0, by decide⟩ (by decide)
        have hcs_eq : canon s = s := by rw [hfs]; unfold canon; rw [maskRec_and_all32, ← hfs, hs0]; rfl
        rw [hcs_eq] at e
        have hyw := ywFn_spec u
        have hb := congrArg (fun n => n.testBit (ywFn u).val) e
        rw [(hm_spec u).2 (ywFn u) hyw.1, hyw.2, hall (ywFn u) hyw.1] at hb
        exact Bool.noConfusion hb
      · -- Case s has s(y) = false on AvY v, m v = true on nonIndep!
        have hsc := canon_maskRec_eq fs
        rw [← hfs] at hsc
        rcases hsc with hpos | hneg
        · -- s = canon s = m u: pick y ∈ indep with AvY u y = true ∧ AvY v y = true!
          have hyuv := yuvFn_spec u v
          have hb := congrArg (fun n => n.testBit (yuvFn u v).val) (e.trans hpos.symm)
          rw [(hm_spec u).2 (yuvFn u v) hyuv.1, hyuv.2.1, hvs (yuvFn u v) hyuv.1 hyuv.2.2] at hb
          exact Bool.noConfusion hb
        · -- s = not32 (canon s) = not32 (m u)!
          have hsn : s = not32 (m u) := hneg.trans (congrArg not32 e.symm)
          by_cases huv : u = v
          · subst huv
            have hb := congrArg (fun n => n.testBit 3) hsn
            rw [not32_testBit (by omega), hs_ni ⟨3, by decide⟩ (by decide), hmv_ni ⟨3, by decide⟩ (by decide)] at hb
            exact Bool.noConfusion hb
          · have hy := XTree2940.yOnlyNot_spec u v huv
            have hb := congrArg (fun n => n.testBit (XTree2940.yOnlyNot u v).val) hsn
            rw [not32_testBit (XTree2940.yOnlyNot u v).isLt, (hm_spec u).2 _ hy.1, hy.2.1, hvs _ hy.1 hy.2.2] at hb
            exact Bool.noConfusion hb
    exact pureY_eq5_impossible pureYSeq hvalid_seq hlen5
      (canon (m 0)) (canon (m 1)) (canon (m 2)) (canon (m 3)) (canon s)
      hc0 hc3 hc6 hc7 hcs
      (by rw [hf0]; exact isW0e2_of_mask f0 (fun y hy hav => by rw [hm0_bit y hy, hav]) (by rw [hm0_bit ⟨2, by decide⟩ (by decide)]; decide))
      (by rw [hf3]; exact isW3e1_of_mask f3 (fun y hy hav => by rw [hm3_bit y hy, hav]) (by rw [hm3_bit ⟨1, by decide⟩ (by decide)]; decide))
      (by rw [hf6]; exact isW6e4_of_mask f6 (fun y hy hav => by rw [hm6_bit y hy, hav]) (by rw [hm6_bit ⟨4, by decide⟩ (by decide)]; decide))
      (by rw [hf7]; exact isW7e4_of_mask f7 (fun y hy hav => by rw [hm7_bit y hy, hav]) (by rw [hm7_bit ⟨4, by decide⟩ (by decide)]; decide))
      (by rw [hfs]; exact hws)
      h67 (hne_s 0 f0 hf0) (hne_s 1 f3 hf3) (hne_s 2 f6 hf6) (hne_s 3 f7 hf7)

def plug10 (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x

lemma plug10_list (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (plug10 x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ_last]; simp [plug10]; rfl

lemma plug10_castSucc (x : Fin 9 → Bool) (b : Bool) (k : Fin 9) : plug10 x b k.castSucc = x k := by
  simp [plug10]

lemma plug10_last (x : Fin 9 → Bool) (b : Bool) : plug10 x b 9 = b :=
  Fin.lastCases_last (motive := fun _ => Bool)

theorem caseA_impossible (D : Circuit) (fan : FanInTwo D) (budget : nonNotCount D.gates ≤ 13)
    (agree : ∀ x : Fin 10 → Bool, CaseB2940.valid10 x → circuitFun 10 D x = CaseB2940.target10 x)
    (hnodep9 : ¬ Dep (circuitFun 10 D) 9) : False := by
  classical
  -- Prepend a single NOT gate on input 0 to eliminate input 9 at 0 non-NOT cost!
  let a : Gate := ⟨.not, [0]⟩
  let D9 : Circuit := ⟨a :: D.gates, D.output⟩
  have fan9 : FanInTwo D9 := by
    intro g hg
    change g ∈ a :: D.gates at hg
    rcases List.mem_cons.mp hg with rfl | hmem
    · simp [a]
    · exact fan g hmem
  have budget9 : nonNotCount D9.gates ≤ 13 := by
    have : nonNotCount (a :: D.gates) = nonNotCount D.gates := by
      simp [nonNotCount, a, isNotGate]
    simpa [D9, this] using budget
  have hfun9 : ∀ x : Fin 9 → Bool, circuitFun 9 D9 x = target9 x := by
    intro x
    let p1 := plug10 x (!x 0)
    let p2 := plug10 x (x 0 || x 4)
    have h9_eq : circuitFun 10 D p1 = circuitFun 10 D p2 := by
      by_cases h : (!x 0) = (x 0 || x 4)
      · simp [p1, p2, h]
      · have hflip : p2 = Function.update p1 9 (!p1 9) := by
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change p2 9 = Function.update p1 9 (!p1 9) 9
            rw [Function.update_self]
            dsimp only [p1, p2]
            rw [plug10_last, plug10_last]
            cases hx0 : x 0 <;> cases hx4 : x 4 <;> simp_all
          · change p2 k.castSucc = Function.update p1 (Fin.last 9) (!p1 9) k.castSucc
            rw [Function.update_of_ne (Fin.castSucc_ne_last k)]
            simp [p1, p2, plug10_castSucc]
        rw [hflip]
        by_contra hne
        exact hnodep9 ⟨p1, Ne.symm hne⟩
    have hstep : Circuit.wires D9 (List.ofFn x) = Circuit.wires D (List.ofFn p1) := by
      change (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x ++ [!(List.ofFn x).getD 0 false])) = _
      have h0 : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD]
      rw [h0, ← plug10_list]; rfl
    have hv2 : CaseB2940.valid10 p2 := by
      have h0 : p2 0 = x 0 := plug10_castSucc x (x 0 || x 4) 0
      have h4 : p2 4 = x 4 := plug10_castSucc x (x 0 || x 4) 4
      have h9 : p2 9 = (x 0 || x 4) := plug10_last x (x 0 || x 4)
      simp only [CaseB2940.valid10, h0, h4, h9]
    have ht2 : CaseB2940.target10 p2 = target9 x := by
      have hc : ∀ k : Fin 9, p2 k.castSucc = x k := fun k => plug10_castSucc x (x 0 || x 4) k
      have h0 : p2 0 = x 0 := hc 0; have h1 : p2 1 = x 1 := hc 1; have h2 : p2 2 = x 2 := hc 2
      have h3 : p2 3 = x 3 := hc 3; have h4 : p2 4 = x 4 := hc 4; have h5 : p2 5 = x 5 := hc 5
      have h6 : p2 6 = x 6 := hc 6; have h7 : p2 7 = x 7 := hc 7; have h8 : p2 8 = x 8 := hc 8
      simp only [CaseB2940.target10, target9, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    change (Circuit.wires D9 (List.ofFn x)).getD D.output false = target9 x
    rw [hstep]
    exact h9_eq.trans ((agree p2 hv2).trans ht2)
  have htarget_eq : ∀ x : Fin 9 → Bool, target9 x = petersenF x := fun x => by
    simp [target9, petersenF, edgeFun, edges, Bool.or_assoc]
  have he : ∀ x : Fin 9 → Bool, circuitFun 9 D9 x = petersenF x := fun x => (hfun9 x).trans (htarget_eq x)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D9 fan9 he petersen_nonconstant
  have valid := least_petersen_output_valid least
  let out : Fin (9 + gs.length) := ⟨o, valid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant valid
  have distinct := predecessors_nodup least petersen_nonconstant
  have branches := forksOfBudget (n := 9) (K := 5) least.hcl out live (by omega)
  obtain ⟨label, locations, isLast, codes⟩ := normalizedCutsK (n := 9) (K := 5) least.hcl out live branches
  have computes (x : Fin 9 → Bool) : vl gs x out.val = target9 x :=
    (least.hev x).trans (htarget_eq x).symm
  have cutA : ∀ t : Fin 6, CutA label t := fun t => by
    obtain ⟨c, low, high⟩ := codes t
    refine ⟨c, low, fun x y rest same => ?_⟩
    exact (computes x).symm.trans ((high x y rest same).trans (computes y))
  have hcf (i j : Fin 9) (hm : (i, j) ∈ pairsA) : label i ≠ label j := fun same =>
    boundaryConflictA least.hcl out live distinct computes (i, j) hm ((locations _ _).mp same)
  have hca := checkedCubesA
  have hbound (i j k : Fin 9) (a b c : ℕ) (hw : cubeA i j k a b c) :
      label i = label j → label k ≤ label i := cubeBoundA label cutA i j k a b c hw
  have hquad := chkA_sound label
    (hcf 0 1 (by decide))
    (hcf 1 2 (by decide))
    (hcf 2 3 (by decide))
    (hcf 3 4 (by decide))
    (hcf 4 0 (by decide))
    (hcf 0 5 (by decide))
    (hcf 1 6 (by decide))
    (hcf 2 7 (by decide))
    (hcf 3 8 (by decide))
    (hcf 5 7 (by decide))
    (hcf 6 8 (by decide))
    (hcf 8 5 (by decide))
    (hbound 0 2 4 132 129 128 (hca (0, 2, 4, 132, 129, 128) (by decide)))
    (hbound 0 2 5 12 9 8 (hca (0, 2, 5, 12, 9, 8) (by decide)))
    (hbound 0 2 7 20 17 16 (hca (0, 2, 7, 20, 17, 16) (by decide)))
    (hbound 0 3 4 10 3 2 (hca (0, 3, 4, 10, 3, 2) (by decide)))
    (hbound 0 3 5 12 5 4 (hca (0, 3, 5, 12, 5, 4) (by decide)))
    (hbound 0 3 8 10 3 2 (hca (0, 3, 8, 10, 3, 2) (by decide)))
    (hbound 0 6 1 80 17 16 (hca (0, 6, 1, 80, 17, 16) (by decide)))
    (hbound 0 6 4 320 257 256 (hca (0, 6, 4, 320, 257, 256) (by decide)))
    (hbound 0 7 4 132 5 4 (hca (0, 7, 4, 132, 5, 4) (by decide)))
    (hbound 0 7 5 130 3 2 (hca (0, 7, 5, 130, 3, 2) (by decide)))
    (hbound 0 8 3 258 3 2 (hca (0, 8, 3, 258, 3, 2) (by decide)))
    (hbound 0 8 4 320 65 64 (hca (0, 8, 4, 320, 65, 64) (by decide)))
    (hbound 0 8 6 272 17 16 (hca (0, 8, 6, 272, 17, 16) (by decide)))
    (hbound 1 3 4 72 66 64 (hca (1, 3, 4, 72, 66, 64) (by decide)))
    (hbound 1 3 6 24 18 16 (hca (1, 3, 6, 24, 18, 16) (by decide)))
    (hbound 1 3 8 9 3 1 (hca (1, 3, 8, 9, 3, 1) (by decide)))
    (hbound 1 4 0 20 6 4 (hca (1, 4, 0, 20, 6, 4) (by decide)))
    (hbound 1 4 6 24 10 8 (hca (1, 4, 6, 24, 10, 8) (by decide)))
    (hbound 1 5 6 160 130 128 (hca (1, 5, 6, 160, 130, 128) (by decide)))
    (hbound 1 5 7 96 66 64 (hca (1, 5, 7, 96, 66, 64) (by decide)))
    (hbound 1 5 8 36 6 4 (hca (1, 5, 8, 36, 6, 4) (by decide)))
    (hbound 1 7 2 129 3 1 (hca (1, 7, 2, 129, 3, 1) (by decide)))
    (hbound 1 7 6 160 34 32 (hca (1, 7, 6, 160, 34, 32) (by decide)))
    (hbound 1 8 3 257 3 1 (hca (1, 8, 3, 257, 3, 1) (by decide)))
    (hbound 1 8 5 260 6 4 (hca (1, 8, 5, 260, 6, 4) (by decide)))
    (hbound 1 8 6 257 3 1 (hca (1, 8, 6, 257, 3, 1) (by decide)))
    (hbound 2 4 0 144 132 128 (hca (2, 4, 0, 144, 132, 128) (by decide)))
    (hbound 2 4 3 17 5 1 (hca (2, 4, 3, 17, 5, 1) (by decide)))
    (hbound 2 4 7 17 5 1 (hca (2, 4, 7, 17, 5, 1) (by decide)))
    (hbound 2 5 3 33 5 1 (hca (2, 5, 3, 33, 5, 1) (by decide)))
    (hbound 2 5 7 33 5 1 (hca (2, 5, 7, 33, 5, 1) (by decide)))
    (hbound 2 5 8 34 6 2 (hca (2, 5, 8, 34, 6, 2) (by decide)))
    (hbound 2 6 1 72 12 8 (hca (2, 6, 1, 72, 12, 8) (by decide)))
    (hbound 2 6 7 320 260 256 (hca (2, 6, 7, 320, 260, 256) (by decide)))
    (hbound 2 8 3 258 6 2 (hca (2, 8, 3, 258, 6, 2) (by decide)))
    (hbound 2 8 5 258 6 2 (hca (2, 8, 5, 258, 6, 2) (by decide)))
    (hbound 2 8 7 320 68 64 (hca (2, 8, 7, 320, 68, 64) (by decide)))
    (hbound 3 5 2 33 9 1 (hca (3, 5, 2, 33, 9, 1) (by decide)))
    (hbound 3 5 7 48 24 16 (hca (3, 5, 7, 48, 24, 16) (by decide)))
    (hbound 3 5 8 33 9 1 (hca (3, 5, 8, 33, 9, 1) (by decide)))
    (hbound 3 6 1 80 24 16 (hca (3, 6, 1, 80, 24, 16) (by decide)))
    (hbound 3 6 4 66 10 2 (hca (3, 6, 4, 66, 10, 2) (by decide)))
    (hbound 3 6 8 66 10 2 (hca (3, 6, 8, 66, 10, 2) (by decide)))
    (hbound 3 7 2 144 24 16 (hca (3, 7, 2, 144, 24, 16) (by decide)))
    (hbound 3 7 4 160 40 32 (hca (3, 7, 4, 160, 40, 32) (by decide)))
    (hbound 3 7 5 144 24 16 (hca (3, 7, 5, 144, 24, 16) (by decide)))
    (hbound 4 5 0 40 24 8 (hca (4, 5, 0, 40, 24, 8) (by decide)))
    (hbound 4 5 7 40 24 8 (hca (4, 5, 7, 40, 24, 8) (by decide)))
    (hbound 4 6 1 72 24 8 (hca (4, 6, 1, 72, 24, 8) (by decide)))
    (hbound 4 6 3 66 18 2 (hca (4, 6, 3, 66, 18, 2) (by decide)))
    (hbound 4 6 8 65 17 1 (hca (4, 6, 8, 65, 17, 1) (by decide)))
    (hbound 4 7 2 129 17 1 (hca (4, 7, 2, 129, 17, 1) (by decide)))
    (hbound 4 7 3 160 48 32 (hca (4, 7, 3, 160, 48, 32) (by decide)))
    (hbound 4 7 5 136 24 8 (hca (4, 7, 5, 136, 24, 8) (by decide)))
    (hbound 4 8 0 320 80 64 (hca (4, 8, 0, 320, 80, 64) (by decide)))
    (hbound 4 8 3 257 17 1 (hca (4, 8, 3, 257, 17, 1) (by decide)))
    (hbound 4 8 6 257 17 1 (hca (4, 8, 6, 257, 17, 1) (by decide)))
    (hbound 5 6 1 192 160 128 (hca (5, 6, 1, 192, 160, 128) (by decide)))
    (hbound 5 6 7 66 34 2 (hca (5, 6, 7, 66, 34, 2) (by decide)))
    (hbound 5 6 8 65 33 1 (hca (5, 6, 8, 65, 33, 1) (by decide)))
    (hbound 6 7 2 384 320 256 (hca (6, 7, 2, 384, 320, 256) (by decide)))
    (hbound 6 7 5 130 66 2 (hca (6, 7, 5, 130, 66, 2) (by decide)))
    (hbound 6 7 8 132 68 4 (hca (6, 7, 8, 132, 68, 4) (by decide)))
    (hbound 7 8 2 320 192 64 (hca (7, 8, 2, 320, 192, 64) (by decide)))
    (hbound 7 8 5 260 132 4 (hca (7, 8, 5, 260, 132, 4) (by decide)))
    (hbound 7 8 6 260 132 4 (hca (7, 8, 6, 260, 132, 4) (by decide)))
    chkA_ok
  have hps := perm_specs
  rcases hquad with ⟨h0, h3, h6, h7⟩ | ⟨h1, h4, h7, h8⟩ | ⟨h2, h4, h5, h6⟩
  · exact caseA_with_perm least.hcl out live distinct (bound.trans budget9) computes σ0 σ0inv
      hps.1 hps.2.1 (target9_perm σ0inv hps.2.2.1) (fun v => by
        fin_cases v
        · exact (isLast 0).mp h0
        · exact (isLast 3).mp h3
        · exact (isLast 6).mp h6
        · exact (isLast 7).mp h7)
  · exact caseA_with_perm least.hcl out live distinct (bound.trans budget9) computes σ1 σ1inv
      hps.2.2.2.1 hps.2.2.2.2.1 (target9_perm σ1inv hps.2.2.2.2.2.1) (fun v => by
        fin_cases v
        · exact (isLast 1).mp h1
        · exact (isLast 8).mp h8
        · exact (isLast 4).mp h4
        · exact (isLast 7).mp h7)
  · exact caseA_with_perm least.hcl out live distinct (bound.trans budget9) computes σ2 σ2inv
      hps.2.2.2.2.2.2.1 hps.2.2.2.2.2.2.2.1 (target9_perm σ2inv hps.2.2.2.2.2.2.2.2) (fun v => by
        fin_cases v
        · exact (isLast 2).mp h2
        · exact (isLast 5).mp h5
        · exact (isLast 6).mp h6
        · exact (isLast 4).mp h4)

end CaseA2940

theorem main : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro B p hsigned heval
  by_contra hlt
  have hle13 : B.size ≤ 13 := by omega
  obtain ⟨D, fan, hbudget, hcomp⟩ := SignedCompile2940.compile_binary B p hsigned
  have agree : ∀ x : Fin 10 → Bool, CaseB2940.valid10 x →
      PEqualNP.MetaComplexity.circuitFun 10 D x = CaseB2940.target10 x := by
    intro x hx
    rw [hcomp x]
    let x4 : Fin 9 → Bool := fun i => x i.castSucc
    have hlist : List.ofFn x ++ [false] = List.ofFn x4 ++ [x4 0 || x4 4, false] := by
      have hx9 : x (Fin.last 9) = (x4 0 || x4 4) := hx
      rw [List.ofFn_succ_last, hx9, List.append_assoc]; rfl
    rw [hlist]
    exact heval x4
  by_cases hdep9 : CircuitProof.Readers.Dep (PEqualNP.MetaComplexity.circuitFun 10 D) 9
  · exact CaseB2940.caseB_impossible D fan (hbudget ▸ hle13) agree hdep9
  · exact CaseA2940.caseA_impossible D fan (hbudget ▸ hle13) agree hdep9

end PEqualNP.Outside.L_meta_2940

theorem PEqualNP.Outside.L_meta_2940 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size :=
  PEqualNP.Outside.L_meta_2940.main

