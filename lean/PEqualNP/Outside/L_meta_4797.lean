import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4797_aux









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
    exact PEqualNP.Outside.L_meta_4797_aux.least_gate_inputs_nodup least nonnull _
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

namespace C6Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open Relation

def c6Edges : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 3), (1, 4), (2, 4), (3, 5), (2, 5)]

def c6Fun (x : Fin 6 → Bool) : Bool :=
  c6Edges.any fun e => x e.1 && x e.2

lemma c6_noLoops : ∀ e ∈ c6Edges, e.1 ≠ e.2 := by decide

def c6Graph : SimpleGraph (Fin 6) where
  Adj u v := (u, v) ∈ c6Edges ∨ (v, u) ∈ c6Edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => c6_noLoops (v, v) he rfl) (fun he => c6_noLoops (v, v) he rfl)⟩

instance c6AdjDec : DecidableRel c6Graph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ c6Edges ∨ (b, a) ∈ c6Edges))

lemma c6Fun_true (x : Fin 6 → Bool) :
    c6Fun x = true ↔ ∃ a b : Fin 6, ((a, b) ∈ c6Edges) ∧ x a = true ∧ x b = true := by
  unfold c6Fun
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, hval⟩
    rw [Bool.and_eq_true] at hval
    exact ⟨a, b, hmem, hval.1, hval.2⟩
  · rintro ⟨a, b, hmem, ha, hb⟩
    exact ⟨(a, b), hmem, by rw [Bool.and_eq_true]; exact ⟨ha, hb⟩⟩

lemma c6Fun_graph_edges (x : Fin 6 → Bool) :
    c6Fun x = true ↔ ∃ u v : Fin 6, c6Graph.Adj u v ∧ x u = true ∧ x v = true := by
  rw [c6Fun_true]
  constructor
  · rintro ⟨a, b, he, ha, hb⟩; exact ⟨a, b, Or.inl he, ha, hb⟩
  · rintro ⟨a, b, hadj, ha, hb⟩
    rcases hadj with he | he
    · exact ⟨a, b, he, ha, hb⟩
    · exact ⟨b, a, he, hb, ha⟩

lemma c6_marked_edges (S : Finset (Fin 6)) :
    c6Fun (setInput S) = true ↔ BranchGraph.containsEdge c6Graph S := by
  rw [c6Fun_graph_edges]
  constructor
  · rintro ⟨u, v, hadj, hu, hv⟩
    exact ⟨u, of_decide_eq_true hu, v, of_decide_eq_true hv, hadj⟩
  · rintro ⟨u, hu, v, hv, hadj⟩
    exact ⟨u, v, hadj, decide_eq_true hu, decide_eq_true hv⟩

lemma c6_alt_neighbors :
    ∀ i j : Fin 6, c6Graph.Adj i j →
      ∃ u v : Fin 6, c6Graph.Adj i u ∧ c6Graph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ c6Graph.Adj u v := by
  decide

lemma c6_dep_samples : ∀ v : Fin 6, ∃ w : Fin 6,
    c6Fun (Function.update (fun i => decide (i = w)) v (!(decide (v = w)))) ≠
      c6Fun (fun i => decide (i = w)) := by
  decide

lemma c6_depends (v : Fin 6) : Dep c6Fun v := by
  obtain ⟨w, hw⟩ := c6_dep_samples v
  exact ⟨fun i => decide (i = w), hw⟩

lemma c6_nonconstant : ∃ x y : Fin 6 → Bool, c6Fun x ≠ c6Fun y :=
  dep_nc (c6_depends 0)

lemma c6_cofactor_samples : ∀ (v : Fin 6) (b : Bool),
    c6Fun (Function.update (fun _ => false) v b) = false ∧
    c6Fun (Function.update (fun _ => true) v b) = true := by
  decide

lemma c6_restrict_nonconstant (v : Fin 6) (b : Bool) :
    ∃ x y, c6Fun (Function.update x v b) ≠ c6Fun (Function.update y v b) := by
  obtain ⟨no, yes⟩ := c6_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩

lemma c6_nonadj_pair_struct :
    ∀ u v : Fin 6, u ≠ v → ¬ c6Graph.Adj u v →
      (∃ a b w : Fin 6, a ≠ b ∧ a ≠ w ∧ b ≠ w ∧
        c6Graph.Adj u a ∧ ¬ c6Graph.Adj v a ∧
        c6Graph.Adj v b ∧ ¬ c6Graph.Adj u b ∧
        c6Graph.Adj u w ∧ c6Graph.Adj v w ∧
        ¬ c6Graph.Adj a w ∧ ¬ c6Graph.Adj b w ∧ ¬ c6Graph.Adj a b) ∨
      (∃ a1 a2 b1 b2 : Fin 6,
        a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
        c6Graph.Adj u a1 ∧ c6Graph.Adj u a2 ∧ ¬ c6Graph.Adj v a1 ∧ ¬ c6Graph.Adj v a2 ∧
        c6Graph.Adj v b1 ∧ c6Graph.Adj v b2 ∧ ¬ c6Graph.Adj u b1 ∧ ¬ c6Graph.Adj u b2 ∧
        ¬ c6Graph.Adj a1 b2 ∧ ¬ c6Graph.Adj b1 a2) := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide

lemma c6_cover_le2 :
    ∀ D : Finset (Fin 6), D.card ≤ 2 → ¬ BranchGraph.EdgelessAfter c6Graph D := by
  unfold BranchGraph.EdgelessAfter
  decide

lemma c6_cover_eq3 :
    ∀ D : Finset (Fin 6), D.card ≤ 3 → BranchGraph.EdgelessAfter c6Graph D →
      D = ({1, 2, 3} : Finset (Fin 6)) ∨ D = ({0, 4, 5} : Finset (Fin 6)) := by
  unfold BranchGraph.EdgelessAfter
  decide

lemma c6_cut_triangle {gs : List Gate} (clean : CleanL 6 gs)
    (out : Fin (6 + gs.length))
    (live : ∀ w : Fin (6 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (eval : ∀ x : Fin 6 → Bool, vl gs x out.val = c6Fun x)
    (r : Fin (6 + gs.length)) (hrlt : r < out)
    (term : FirstBranchRoute.Terminal (readEdge gs) out r)
    {u v a w : Fin 6}
    (hu : firstInputBoundary clean out live u = r)
    (hv : firstInputBoundary clean out live v = r)
    (hwr : r < firstInputBoundary clean out live w)
    (h1 : c6Graph.Adj u a) (h2 : ¬ c6Graph.Adj v a)
    (h3 : c6Graph.Adj v w) (h4 : ¬ c6Graph.Adj a w) : False := by
  have noBypass (k : Fin 6) (hk : firstInputBoundary clean out live k = r) :
      ¬ ReflTransGen (avoid (readEdge gs) r) (inputWire gs k) out := by
    intro bypass
    have hk' : FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs k) = r := hk
    have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
      (v := inputWire gs k) (w := out) (by rw [hk']; exact hrlt)
    apply forbid
    have weaker : ∀ x y, avoid (readEdge gs) r x y → FirstBranchRoute.Avoid (readEdge gs) r x y :=
      fun _ _ h => ⟨h.1, h.2.1⟩
    have conv := ReflTransGen.mono weaker _ _ bypass
    rw [hk']
    exact conv
  have cutAgree (x y : Fin 6 → Bool)
      (hdiff : ∀ i : Fin 6, x i ≠ y i → firstInputBoundary clean out live i = r)
      (hsame : vl gs x r.val = vl gs y r.val) : c6Fun x = c6Fun y := by
    rw [← eval x, ← eval y]
    exact circuit_cut_agreement clean r out x y hsame (fun i hi => noBypass i (hdiff i hi))
  have codeIndepW (x : Fin 6 → Bool) :
      vl gs (Function.update x w true) r.val = vl gs x r.val := by
    apply agree_on_input_ancestors clean
    intro i anc
    have hle : firstInputBoundary clean out live i ≤ r :=
      FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live anc term
    have hne : i ≠ w := by
      rintro rfl
      exact not_lt_of_ge hle hwr
    exact Function.update_of_ne hne true x
  let p0 : Fin 6 → Bool := fun i => decide (i = a)
  let pu : Fin 6 → Bool := fun i => decide (i = a ∨ i = u)
  let pv : Fin 6 → Bool := fun i => decide (i = a ∨ i = v)
  have c_p0 : c6Fun p0 = false := by
    cases h : c6Fun p0 with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, y, hadj, hx, hy⟩ := (c6Fun_graph_edges p0).mp h
      have hxa : x = a := of_decide_eq_true hx
      have hya : y = a := of_decide_eq_true hy
      subst hxa; subst hya
      exact c6Graph.loopless.irrefl _ hadj
  have c_pu : c6Fun pu = true :=
    (c6Fun_graph_edges pu).mpr ⟨u, a, h1, by simp [pu], by simp [pu]⟩
  have c_pv : c6Fun pv = false := by
    cases h : c6Fun pv with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, y, hadj, hx, hy⟩ := (c6Fun_graph_edges pv).mp h
      have hxv : x = a ∨ x = v := of_decide_eq_true hx
      have hyv : y = a ∨ y = v := of_decide_eq_true hy
      rcases hxv with rfl | rfl <;> rcases hyv with rfl | rfl
      · exact c6Graph.loopless.irrefl _ hadj
      · exact h2 hadj.symm
      · exact h2 hadj
      · exact c6Graph.loopless.irrefl _ hadj
  have c_p0w : c6Fun (Function.update p0 w true) = false := by
    cases h : c6Fun (Function.update p0 w true) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨x, y, hadj, hx, hy⟩ := (c6Fun_graph_edges _).mp h
      have hx' : x = w ∨ x = a := by
        by_cases hxw : x = w
        · exact Or.inl hxw
        · rw [Function.update_of_ne hxw] at hx; exact Or.inr (of_decide_eq_true hx)
      have hy' : y = w ∨ y = a := by
        by_cases hyw : y = w
        · exact Or.inl hyw
        · rw [Function.update_of_ne hyw] at hy; exact Or.inr (of_decide_eq_true hy)
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact c6Graph.loopless.irrefl _ hadj
      · exact h4 hadj.symm
      · exact h4 hadj
      · exact c6Graph.loopless.irrefl _ hadj
  have c_pvw : c6Fun (Function.update pv w true) = true :=
    (c6Fun_graph_edges _).mpr ⟨v, w, h3, by
      by_cases hvw : v = w
      · rw [hvw, Function.update_self]
      · rw [Function.update_of_ne hvw]; simp [pv],
      by rw [Function.update_self]⟩
  have hne0u : vl gs p0 r.val ≠ vl gs pu r.val := by
    intro heq
    have hc := cutAgree p0 pu (fun i hi => by
      have hiu : i = u := by
        by_contra hnu
        apply hi; simp [p0, pu, hnu]
      subst hiu; exact hu) heq
    rw [c_p0, c_pu] at hc; exact Bool.noConfusion hc
  have hneuv : vl gs pu r.val ≠ vl gs pv r.val := by
    intro heq
    have hc := cutAgree pu pv (fun i hi => by
      by_cases hiu : i = u
      · subst hiu; exact hu
      · by_cases hiv : i = v
        · subst hiv; exact hv
        · exact (hi (by simp [pu, pv, hiu, hiv])).elim) heq
    rw [c_pu, c_pv] at hc; exact Bool.noConfusion hc
  have hne0v : vl gs p0 r.val ≠ vl gs pv r.val := by
    intro heq
    have heqw : vl gs (Function.update p0 w true) r.val = vl gs (Function.update pv w true) r.val :=
      (codeIndepW p0).trans (heq.trans (codeIndepW pv).symm)
    have hc := cutAgree (Function.update p0 w true) (Function.update pv w true) (fun i hi => by
      have hiv : i = v := by
        by_contra hnv
        apply hi
        by_cases hiw : i = w
        · simp [hiw]
        · simp [Function.update_of_ne hiw, p0, pv, hnv]
      subst hiv; exact hv) heqw
    rw [c_p0w, c_pvw] at hc; exact Bool.noConfusion hc
  cases h0 : vl gs p0 r.val <;> cases h1' : vl gs pu r.val <;> cases h2' : vl gs pv r.val <;> simp_all

lemma c6_bucket_card_le_one {gs : List Gate} (clean : CleanL 6 gs)
    (out : Fin (6 + gs.length))
    (live : ∀ w : Fin (6 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (eval : ∀ x : Fin 6 → Bool, vl gs x out.val = c6Fun x)
    (hbr : (circuitBranchWires (n := 6) gs).card ≤ 3) :
    ∀ r ∈ circuitBranchWires (n := 6) gs,
      (BranchGroupsLean.bucket (firstInputBoundary clean out live) r).card ≤ 1 := by
  classical
  set label := firstInputBoundary clean out live
  set branches := circuitBranchWires (n := 6) gs
  have computes (x : Fin 6 → Bool) : vl gs x out.val = PetersenScratch.edgeValue c6Graph x := by
    rw [eval, Bool.eq_iff_iff, c6Fun_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 6)) : vl gs (setInput S) out.val = true ↔
      BranchGraph.containsEdge c6Graph S := by
    rw [eval]; exact c6_marked_edges S
  have independent (r) : BranchGraph.Independent c6Graph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent clean out live distinct c6Graph computes c6_alt_neighbors r
  have labels (v : Fin 6) : label v = out ∨ label v ∈ branches := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs v) with h | h
    · exact Or.inl h
    · exact Or.inr (in_circuit_branches.mpr h)
  have before (r) (hr : r ∈ branches) : r < out := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp hr
    exact lt_of_lt_of_le (read_order clean path) (wire_le_output clean out live a)
  intro r
  induction r using (measure (fun a : Fin (6 + gs.length) => a.val)).wf.induction with
  | h r ih =>
    intro hr
    have hbelow_sub : BranchGroupsLean.below label r ⊆
        (branches.filter fun q => q < r).biUnion (BranchGroupsLean.bucket label) := by
      intro x hx
      simp only [BranchGroupsLean.below, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hxr : label x ∈ branches := (labels x).resolve_left (fun h => by
        rw [h] at hx; exact not_lt_of_ge (le_of_lt (before r hr)) hx)
      exact Finset.mem_biUnion.mpr ⟨label x, Finset.mem_filter.mpr ⟨hxr, hx⟩,
        by simp [BranchGroupsLean.bucket]⟩
    have hflt_card : (branches.filter fun q => q < r).card ≤ 2 := by
      have hss : branches.filter (fun q => q < r) ⊂ branches := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
        have hmem : r ∈ branches.filter (fun q => q < r) := heq.symm ▸ hr
        exact lt_irrefl r (Finset.mem_filter.mp hmem).2
      have hlt := Finset.card_lt_card hss
      omega
    have hbelow_card : (BranchGroupsLean.below label r).card ≤ 2 := by
      calc (BranchGroupsLean.below label r).card
          ≤ ((branches.filter fun q => q < r).biUnion (BranchGroupsLean.bucket label)).card :=
            Finset.card_le_card hbelow_sub
        _ ≤ ∑ q ∈ branches.filter (fun q => q < r), (BranchGroupsLean.bucket label q).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ branches.filter (fun q => q < r), 1 := by
            apply Finset.sum_le_sum
            intro q hq
            obtain ⟨hqb, hql⟩ := Finset.mem_filter.mp hq
            exact ih q hql hqb
        _ = (branches.filter fun q => q < r).card := by simp
        _ ≤ 2 := hflt_card
    by_contra hgt
    have hge2 : 1 < (BranchGroupsLean.bucket label r).card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hge2
    have hlu : label u = r := (Finset.mem_filter.mp hu).2
    have hlv : label v = r := (Finset.mem_filter.mp hv).2
    have hna : ¬ c6Graph.Adj u v := independent r u hu v hv
    have htwins := circuit_branch_class_twins clean out live c6Graph marked r
      (le_of_lt (before r hr)) (Or.inr (in_circuit_branches.mp hr)) (independent r)
    change BranchGraph.TwinGroup c6Graph (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) at htwins
    have hgt_of_not_below : ∀ (z x : Fin 6), x ∈ BranchGroupsLean.bucket label r →
        c6Graph.Adj x z → z ∉ BranchGroupsLean.below label r → r < label z := by
      intro z x hx hxz hzn
      have hzne : label z ≠ r := fun h => independent r x hx z (by simp [BranchGroupsLean.bucket, h]) hxz
      have hnotlt : ¬ label z < r := fun h => hzn (by simp [BranchGroupsLean.below, h])
      exact lt_of_le_of_ne (not_lt.mp hnotlt) hzne.symm
    rcases c6_nonadj_pair_struct u v huv hna with
      ⟨a, b, w, hab, haw_ne, hbw_ne, hua, hva, hvb, hub, huw, hvw, haw, hbw, hab_na⟩ |
      ⟨a1, a2, b1, b2, h12, h13, h14, h23, h24, h34, hu1, hu2, hv1, hv2, hv3, hv4, hu3, hu4, ha1b2, hb1a2⟩
    · by_cases hnu : (BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) u).Nonempty
      · by_cases hnv : (BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) v).Nonempty
        · have hna_eq := htwins u hu v hv hnu hnv
          have ha_below : a ∈ BranchGroupsLean.below label r := by
            by_contra hna'
            have hmem : a ∈ BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) u := by
              simp [BranchGraph.neighborsAfter, hua, hna']
            rw [hna_eq] at hmem
            exact hva (Finset.mem_filter.mp hmem).2.1
          have hb_below : b ∈ BranchGroupsLean.below label r := by
            by_contra hnb'
            have hmem : b ∈ BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) v := by
              simp [BranchGraph.neighborsAfter, hvb, hnb']
            rw [← hna_eq] at hmem
            exact hub (Finset.mem_filter.mp hmem).2.1
          have hwnot : w ∉ BranchGroupsLean.below label r := by
            intro hw_below
            have h3 : ({a, b, w} : Finset (Fin 6)) ⊆ BranchGroupsLean.below label r := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl <;> assumption
            have hc3 : ({a, b, w} : Finset (Fin 6)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp [hbw_ne]
              · simp [hab, haw_ne]
            have := Finset.card_le_card h3
            omega
          exact c6_cut_triangle clean out live eval r (before r hr)
            (Or.inr (in_circuit_branches.mp hr)) hlu hlv (hgt_of_not_below w u hu huw hwnot) hua hva hvw haw
        · have hbv : b ∈ BranchGroupsLean.below label r := by
            by_contra hnb
            exact hnv ⟨b, by simp [BranchGraph.neighborsAfter, hvb, hnb]⟩
          have hwv : w ∈ BranchGroupsLean.below label r := by
            by_contra hnw
            exact hnv ⟨w, by simp [BranchGraph.neighborsAfter, hvw, hnw]⟩
          have hanot : a ∉ BranchGroupsLean.below label r := by
            intro ha_below
            have h3 : ({a, b, w} : Finset (Fin 6)) ⊆ BranchGroupsLean.below label r := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl <;> assumption
            have hc3 : ({a, b, w} : Finset (Fin 6)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp [hbw_ne]
              · simp [hab, haw_ne]
            have := Finset.card_le_card h3
            omega
          exact c6_cut_triangle clean out live eval r (before r hr)
            (Or.inr (in_circuit_branches.mp hr)) hlv hlu (hgt_of_not_below a u hu hua hanot) hvb hub hua (fun h => hab_na h.symm)
      · have hau : a ∈ BranchGroupsLean.below label r := by
          by_contra hna'
          exact hnu ⟨a, by simp [BranchGraph.neighborsAfter, hua, hna']⟩
        have hwu : w ∈ BranchGroupsLean.below label r := by
          by_contra hnw
          exact hnu ⟨w, by simp [BranchGraph.neighborsAfter, huw, hnw]⟩
        have hbnot : b ∉ BranchGroupsLean.below label r := by
          intro hb_below
          have h3 : ({a, b, w} : Finset (Fin 6)) ⊆ BranchGroupsLean.below label r := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have hc3 : ({a, b, w} : Finset (Fin 6)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [hbw_ne]
            · simp [hab, haw_ne]
          have := Finset.card_le_card h3
          omega
        exact c6_cut_triangle clean out live eval r (before r hr)
          (Or.inr (in_circuit_branches.mp hr)) hlu hlv (hgt_of_not_below b v hv hvb hbnot) hua hva hvb hab_na
    · by_cases hnu : (BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) u).Nonempty
      · by_cases hnv : (BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) v).Nonempty
        · have hna_eq := htwins u hu v hv hnu hnv
          have ha1 : a1 ∈ BranchGroupsLean.below label r := by
            by_contra h; have hm : a1 ∈ BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) u := by simp [BranchGraph.neighborsAfter, hu1, h]
            rw [hna_eq] at hm; exact hv1 (Finset.mem_filter.mp hm).2.1
          have ha2 : a2 ∈ BranchGroupsLean.below label r := by
            by_contra h; have hm : a2 ∈ BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) u := by simp [BranchGraph.neighborsAfter, hu2, h]
            rw [hna_eq] at hm; exact hv2 (Finset.mem_filter.mp hm).2.1
          have hb1 : b1 ∈ BranchGroupsLean.below label r := by
            by_contra h; have hm : b1 ∈ BranchGraph.neighborsAfter c6Graph (BranchGroupsLean.below label r) v := by simp [BranchGraph.neighborsAfter, hv3, h]
            rw [← hna_eq] at hm; exact hu3 (Finset.mem_filter.mp hm).2.1
          have h3 : ({a1, a2, b1} : Finset (Fin 6)) ⊆ BranchGroupsLean.below label r := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have hc3 : ({a1, a2, b1} : Finset (Fin 6)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [h23]
            · simp [h12, h13]
          have := Finset.card_le_card h3
          omega
        · have hb1 : b1 ∈ BranchGroupsLean.below label r := by
            by_contra h; exact hnv ⟨b1, by simp [BranchGraph.neighborsAfter, hv3, h]⟩
          have hb2 : b2 ∈ BranchGroupsLean.below label r := by
            by_contra h; exact hnv ⟨b2, by simp [BranchGraph.neighborsAfter, hv4, h]⟩
          have ha2not : a2 ∉ BranchGroupsLean.below label r := by
            intro ha2
            have h3 : ({a2, b1, b2} : Finset (Fin 6)) ⊆ BranchGroupsLean.below label r := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl <;> assumption
            have hc3 : ({a2, b1, b2} : Finset (Fin 6)).card = 3 := by
              rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
              · simp [h34]
              · simp [h23, h24]
            have := Finset.card_le_card h3
            omega
          exact c6_cut_triangle clean out live eval r (before r hr)
            (Or.inr (in_circuit_branches.mp hr)) hlv hlu (hgt_of_not_below a2 u hu hu2 ha2not) hv3 hu3 hu2 hb1a2
      · have ha1 : a1 ∈ BranchGroupsLean.below label r := by
          by_contra h; exact hnu ⟨a1, by simp [BranchGraph.neighborsAfter, hu1, h]⟩
        have ha2 : a2 ∈ BranchGroupsLean.below label r := by
          by_contra h; exact hnu ⟨a2, by simp [BranchGraph.neighborsAfter, hu2, h]⟩
        have hb2not : b2 ∉ BranchGroupsLean.below label r := by
          intro hb2
          have h3 : ({a1, a2, b2} : Finset (Fin 6)) ⊆ BranchGroupsLean.below label r := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have hc3 : ({a1, a2, b2} : Finset (Fin 6)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [h24]
            · simp [h12, h14]
          have := Finset.card_le_card h3
          omega
        exact c6_cut_triangle clean out live eval r (before r hr)
          (Or.inr (in_circuit_branches.mp hr)) hlu hlv (hgt_of_not_below b2 v hv hv4 hb2not) hu1 hv1 hv4 ha1b2

lemma c6_three_branches {gs : List Gate} (clean : CleanL 6 gs)
    (out : Fin (6 + gs.length))
    (live : ∀ w : Fin (6 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (eval : ∀ x : Fin 6 → Bool, vl gs x out.val = c6Fun x) :
    3 ≤ (circuitBranchWires (n := 6) gs).card := by
  classical
  by_contra hlt
  set label := firstInputBoundary clean out live
  set branches := circuitBranchWires (n := 6) gs
  change ¬ 3 ≤ branches.card at hlt
  have hle2 : branches.card ≤ 2 := by omega
  have hle1 := c6_bucket_card_le_one clean out live distinct eval (by change branches.card ≤ 3; omega)
  let D : Finset (Fin 6) := branches.biUnion (BranchGroupsLean.bucket label)
  have hDcard : D.card ≤ 2 := by
    calc D.card ≤ ∑ r ∈ branches, (BranchGroupsLean.bucket label r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ branches, 1 := Finset.sum_le_sum fun r hr => hle1 r hr
      _ = branches.card := by simp
      _ ≤ 2 := hle2
  have computes (x : Fin 6 → Bool) : vl gs x out.val = PetersenScratch.edgeValue c6Graph x := by
    rw [eval, Bool.eq_iff_iff, c6Fun_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have hind : BranchGraph.Independent c6Graph (BranchGroupsLean.bucket label out) :=
    firstInputGroup_independent clean out live distinct c6Graph computes c6_alt_neighbors out
  have hedge : BranchGraph.EdgelessAfter c6Graph D := by
    intro u v hu hv
    have hlu : label u = out := by
      rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs u) with h | h
      · exact h
      · exfalso; exact hu (Finset.mem_biUnion.mpr ⟨label u, in_circuit_branches.mpr h, by simp [BranchGroupsLean.bucket]⟩)
    have hlv : label v = out := by
      rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs v) with h | h
      · exact h
      · exfalso; exact hv (Finset.mem_biUnion.mpr ⟨label v, in_circuit_branches.mpr h, by simp [BranchGroupsLean.bucket]⟩)
    exact hind u (by simp [BranchGroupsLean.bucket, hlu]) v (by simp [BranchGroupsLean.bucket, hlv])
  exact c6_cover_le2 D hDcard hedge

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp <;> omega

lemma least_c6_output_valid {gs : List Gate} {out : Nat} (least : Least 6 c6Fun gs out) :
    out < 6 + gs.length := by
  by_contra! after
  obtain ⟨x, y, diff⟩ := least.ncv c6_nonconstant
  exact diff ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem c6_nonNot_ge_8 (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = c6Fun x) :
    8 ≤ nonNotCount C.gates := by
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C hfan he c6_nonconstant
  have valid := least_c6_output_valid least
  let outWire : Fin (6 + gs.length) := ⟨o, valid⟩
  have live := least_read_edge_live least c6_nonconstant c6_depends c6_restrict_nonconstant valid
  have distinct := predecessors_nodup least c6_nonconstant
  have h3 := c6_three_branches least.hcl outWire live distinct least.hev
  set branches := circuitBranchWires (n := 6) gs
  have hbb := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (6 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hbb
  have hct := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at hct
  omega

theorem c6_clean_eight_bipartite {gs : List Gate} (clean : CleanL 6 gs)
    (out : Fin (6 + gs.length))
    (live : ∀ w : Fin (6 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (eval : ∀ x : Fin 6 → Bool, vl gs x out.val = c6Fun x)
    (hbr : (circuitBranchWires (n := 6) gs).card ≤ 3) :
    let label := firstInputBoundary clean out live
    let branches := circuitBranchWires (n := 6) gs
    branches.card = 3 ∧
    (∀ r ∈ branches, (BranchGroupsLean.bucket label r).card = 1) ∧
    ((BranchGroupsLean.bucket label out = ({0, 4, 5} : Finset (Fin 6)) ∧
      branches.biUnion (BranchGroupsLean.bucket label) = ({1, 2, 3} : Finset (Fin 6))) ∨
     (BranchGroupsLean.bucket label out = ({1, 2, 3} : Finset (Fin 6)) ∧
      branches.biUnion (BranchGroupsLean.bucket label) = ({0, 4, 5} : Finset (Fin 6)))) := by
  classical
  set label := firstInputBoundary clean out live
  set branches := circuitBranchWires (n := 6) gs
  have h3 := c6_three_branches clean out live distinct eval
  change 3 ≤ branches.card at h3
  change branches.card ≤ 3 at hbr
  have hcard : branches.card = 3 := by omega
  have hle1 := c6_bucket_card_le_one clean out live distinct eval hbr
  let D : Finset (Fin 6) := branches.biUnion (BranchGroupsLean.bucket label)
  have hDcard : D.card ≤ 3 := by
    calc D.card ≤ ∑ r ∈ branches, (BranchGroupsLean.bucket label r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ branches, 1 := Finset.sum_le_sum fun r hr => hle1 r hr
      _ = branches.card := by simp
      _ = 3 := hcard
  have computes (x : Fin 6 → Bool) : vl gs x out.val = PetersenScratch.edgeValue c6Graph x := by
    rw [eval, Bool.eq_iff_iff, c6Fun_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have hind : BranchGraph.Independent c6Graph (BranchGroupsLean.bucket label out) :=
    firstInputGroup_independent clean out live distinct c6Graph computes c6_alt_neighbors out
  have hbefore (r) (hr : r ∈ branches) : r < out := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp hr
    exact lt_of_lt_of_le (read_order clean path) (wire_le_output clean out live a)
  have hcomp : BranchGroupsLean.bucket label out = Finset.univ \ D := by
    ext u
    simp only [BranchGroupsLean.bucket, D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_biUnion, not_exists, not_and]
    constructor
    · intro hu r hr hru
      exact ne_of_lt (hbefore r hr) (hru.symm.trans hu)
    · intro hnot
      rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs u) with h | h
      · exact h
      · exact (hnot (label u) (in_circuit_branches.mpr h) rfl).elim
  have hedge : BranchGraph.EdgelessAfter c6Graph D := by
    intro u v hu hv
    have huo : u ∈ BranchGroupsLean.bucket label out := by rw [hcomp]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩
    have hvo : v ∈ BranchGroupsLean.bucket label out := by rw [hcomp]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
    exact hind u huo v hvo
  have hD_eq := c6_cover_eq3 D hDcard hedge
  have hD3 : D.card = 3 := by rcases hD_eq with h | h <;> rw [h] <;> decide
  have heq1 : ∀ r ∈ branches, (BranchGroupsLean.bucket label r).card = 1 := by
    intro r hr
    by_contra hne
    have h0 : (BranchGroupsLean.bucket label r).card = 0 := by
      have h1 := hle1 r hr
      change (BranchGroupsLean.bucket label r).card ≤ 1 at h1
      omega
    have hsum : ∑ q ∈ branches, (BranchGroupsLean.bucket label q).card ≤ 2 := by
      rw [← Finset.add_sum_erase _ _ hr, h0, zero_add]
      calc ∑ q ∈ branches.erase r, (BranchGroupsLean.bucket label q).card
          ≤ ∑ _q ∈ branches.erase r, 1 := Finset.sum_le_sum fun q hq => hle1 q (Finset.mem_of_mem_erase hq)
        _ = (branches.erase r).card := by simp
        _ = 2 := by rw [Finset.card_erase_of_mem hr, hcard]
    have hle := Finset.card_biUnion_le (s := branches) (t := BranchGroupsLean.bucket label)
    change D.card ≤ _ at hle
    omega
  refine ⟨hcard, heq1, ?_⟩
  rcases hD_eq with hD | hD
  · left
    refine ⟨?_, hD⟩
    rw [hcomp, hD]; decide
  · right
    refine ⟨?_, hD⟩
    rw [hcomp, hD]; decide

end C6Lower

namespace Step1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup C6Lower
open Relation

def thetaFun (x : Fin 7 → Bool) : Bool :=
  [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun e =>
    x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))

def lift6 (x : Fin 6 → Bool) : Fin 7 → Bool
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => x 1
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => x 2
  | ⟨4, _⟩ => x 3
  | ⟨5, _⟩ => x 4
  | ⟨6, _⟩ => x 5

def lift6T (x : Fin 6 → Bool) : Fin 7 → Bool
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => x 1
  | ⟨2, _⟩ => true
  | ⟨3, _⟩ => x 2
  | ⟨4, _⟩ => x 3
  | ⟨5, _⟩ => x 4
  | ⟨6, _⟩ => x 5

lemma theta_lift6 (x : Fin 6 → Bool) : thetaFun (lift6 x) = c6Fun x := by
  simp [thetaFun, c6Fun, c6Edges, lift6]

def EditGate (x4 x5 : ℕ) (g2 g3 : Gate) : Prop :=
  g2.op = g3.op ∧
    List.Forall₂ (fun a b => b = a + 1 ∨ b = 0 ∧ (a = x4 ∨ a = x5)) g2.inputs g3.inputs

lemma forall2_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ (k : ℕ) (h1 : k < l1.length) (h2 : k < l2.length), R l1[k] l2[k]
  | _, _, List.Forall₂.nil, _, h1, _ => (Nat.not_lt_zero _ h1).elim
  | _, _, List.Forall₂.cons h _, 0, _, _ => h
  | _, _, List.Forall₂.cons _ hr, k + 1, h1, h2 =>
      forall2_getElem hr k (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

lemma forall2_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ {a : α}, a ∈ l1 → ∃ b ∈ l2, R a b
  | _, _, List.Forall₂.nil, _, ha => by simp at ha
  | _, _, List.Forall₂.cons hab hrest, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨_, List.mem_cons_self, hab⟩
      · obtain ⟨b, hb, hr⟩ := forall2_mem_left hrest ha'
        exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

def initSt : List Stat :=
  [Stat.const true, Stat.wire 0, Stat.wire 1, Stat.const false,
   Stat.wire 2, Stat.wire 3, Stat.wire 4, Stat.wire 5]

lemma inv_initSt (x : Fin 6 → Bool) :
    Inv 6 (List.ofFn x) (true :: List.ofFn (lift6 x)) (initSt, []) := by
  refine ⟨by simp [initSt], ?_⟩
  intro i
  match i with
  | 0 => simp [initSt, Stat.Valid, Stat.val, wiresFrom]
  | 1 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | 2 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | 3 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | 4 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | 5 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | 6 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | 7 => simp [initSt, Stat.Valid, Stat.val, wiresFrom, lift6]
  | k + 8 =>
    rw [List.getD_eq_default _ _ (by simp [initSt]),
        List.getD_eq_default _ _ (by simp)]
    exact ⟨trivial, rfl⟩

lemma edit_ok {x4 x5 : ℕ} {g2 g3 : Gate} (hok : Ok g2) (hed : EditGate x4 x5 g2 g3) : Ok g3 :=
  ⟨hed.1 ▸ hok.1, hed.2.length_eq ▸ hok.2⟩

def elimPrefix (gs : List Gate) (k : ℕ) : List Stat × List Gate :=
  elim 6 (gs.take k) (initSt, [])

def gateRes (gs : List Gate) (k : ℕ) : Option Gate × Stat :=
  let pre := elimPrefix gs k
  match gs[k]? with
  | none => (none, Stat.const false)
  | some g => simplify g.op (6 + pre.2.length) (g.inputs.map fun i => pre.1.getD i (Stat.const false))

def isEmitted (gs : List Gate) (k : ℕ) : Bool := (gateRes gs k).1.isSome

def isEmitNN (gs : List Gate) (k : ℕ) : Bool :=
  match gs[k]? with
  | none => false
  | some g => isEmitted gs k && !(isNotGate g.op)

lemma elim_fst_len (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim 6 gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    change (elim 6 gs (elimStep 6 acc g)).1.length = _
    rw [ih, elimStep]; simp; omega

lemma elim_fst_prefix (gs : List Gate) : ∀ acc : List Stat × List Gate,
    acc.1 <+: (elim 6 gs acc).1 := by
  induction gs with
  | nil => intro acc; exact List.prefix_rfl
  | cons g gs ih =>
    intro acc
    change acc.1 <+: (elim 6 gs (elimStep 6 acc g)).1
    exact (List.prefix_append acc.1 _).trans (ih (elimStep 6 acc g))

lemma elim_snd_prefix (gs : List Gate) : ∀ acc : List Stat × List Gate,
    acc.2 <+: (elim 6 gs acc).2 := by
  induction gs with
  | nil => intro acc; exact List.prefix_rfl
  | cons g gs ih =>
    intro acc
    change acc.2 <+: (elim 6 gs (elimStep 6 acc g)).2
    exact (List.prefix_append acc.2 _).trans (ih (elimStep 6 acc g))

lemma elimPrefix_succ (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    elimPrefix gs (k + 1) =
      ((elimPrefix gs k).1 ++ [(gateRes gs k).2], (elimPrefix gs k).2 ++ (gateRes gs k).1.toList) := by
  unfold elimPrefix gateRes
  rw [List.take_succ_eq_append_getElem hk, List.getElem?_eq_getElem hk]
  simp only [elim, List.foldl_append, List.foldl_cons, List.foldl_nil, elimStep]
  rfl

lemma elimPrefix_fst_len (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) :
    (elimPrefix gs k).1.length = 8 + k := by
  unfold elimPrefix
  rw [elim_fst_len, List.length_take_of_le hk]; simp [initSt]

lemma take_split_le {α : Type*} (gs : List α) {j k : ℕ} (hjk : j ≤ k) :
    gs.take k = gs.take j ++ (gs.drop j).take (k - j) := by
  conv_lhs => rw [← List.take_append_drop j gs]
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  by_cases hj : j ≤ gs.length
  · rw [List.length_take_of_le hj]
  · simp [List.drop_eq_nil_of_le (by omega : gs.length ≤ j)]

lemma elimPrefix_fst_prefix (gs : List Gate) {j k : ℕ} (hjk : j ≤ k) :
    (elimPrefix gs j).1 <+: (elimPrefix gs k).1 := by
  unfold elimPrefix
  rw [take_split_le gs hjk]
  simp only [elim, List.foldl_append]
  exact elim_fst_prefix ((gs.drop j).take (k - j)) (elim 6 (gs.take j) (initSt, []))

lemma elimPrefix_snd_prefix (gs : List Gate) {j k : ℕ} (hjk : j ≤ k) :
    (elimPrefix gs j).2 <+: (elimPrefix gs k).2 := by
  unfold elimPrefix
  rw [take_split_le gs hjk]
  simp only [elim, List.foldl_append]
  exact elim_snd_prefix ((gs.drop j).take (k - j)) (elim 6 (gs.take j) (initSt, []))

lemma getD_of_prefix {α : Type*} {l1 l2 : List α} (hp : l1 <+: l2) {i : ℕ} (hi : i < l1.length) (d : α) :
    l1.getD i d = l2.getD i d := by
  obtain ⟨t, rfl⟩ := hp
  exact (List.getD_append l1 t d i hi).symm

lemma getElem?_of_prefix {α : Type*} {l1 l2 : List α} (hp : l1 <+: l2) {i : ℕ} (hi : i < l1.length) :
    l1[i]? = l2[i]? := by
  obtain ⟨t, rfl⟩ := hp
  exact (List.getElem?_append_left hi).symm

lemma elimPrefix_st_at (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    (elim 6 gs (initSt, [])).1.getD (8 + k) (Stat.const false) = (gateRes gs k).2 := by
  have hfull : elimPrefix gs gs.length = elim 6 gs (initSt, []) := by simp [elimPrefix]
  have hp := elimPrefix_fst_prefix gs (j := k + 1) (k := gs.length) (by omega)
  rw [hfull] at hp
  have h1 := getD_of_prefix hp (i := 8 + k) (by rw [elimPrefix_fst_len gs (k + 1) (by omega)]; omega) (Stat.const false)
  rw [← h1, elimPrefix_succ gs k hk]
  exact getD_snoc_len _ _ _ _ (elimPrefix_fst_len gs k (by omega))

lemma elimPrefix_len_eq (gs : List Gate) (hlen : gs.length = 11) (m : ℕ) (hm : m ≤ 11) :
    (elimPrefix gs m).2.length =
      (Finset.univ.filter fun k : Fin 11 => k.val < m ∧ isEmitted gs k.val = true).card := by
  induction m with
  | zero => simp [elimPrefix, elim]
  | succ m ih =>
    have hsucc := elimPrefix_succ gs m (by omega)
    have hstep : (elimPrefix gs (m + 1)).2.length =
        (elimPrefix gs m).2.length + (if isEmitted gs m = true then 1 else 0) := by
      rw [hsucc, List.length_append]
      unfold isEmitted
      cases (gateRes gs m).1 <;> simp
    rw [hstep, ih (by omega)]
    let km : Fin 11 := ⟨m, by omega⟩
    by_cases hem : isEmitted gs m = true
    · have hfilt : (Finset.univ.filter fun k : Fin 11 => k.val < m + 1 ∧ isEmitted gs k.val = true) =
          insert km (Finset.univ.filter fun k : Fin 11 => k.val < m ∧ isEmitted gs k.val = true) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hk1, hk2⟩
          by_cases hkm : k.val = m
          · left; exact Fin.ext hkm
          · right; exact ⟨by omega, hk2⟩
        · rintro (rfl | ⟨hk1, hk2⟩)
          · exact ⟨by simp [km], hem⟩
          · exact ⟨by omega, hk2⟩
      rw [hfilt, Finset.card_insert_of_notMem (by simp [km]), if_pos hem]
    · have hfilt : (Finset.univ.filter fun k : Fin 11 => k.val < m + 1 ∧ isEmitted gs k.val = true) =
          Finset.univ.filter fun k : Fin 11 => k.val < m ∧ isEmitted gs k.val = true := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hk1, hk2⟩
          have hne : k.val ≠ m := fun heq => hem (heq ▸ hk2)
          exact ⟨by omega, hk2⟩
        · rintro ⟨hk1, hk2⟩; exact ⟨by omega, hk2⟩
      rw [hfilt, ite_eq_right_iff.mpr (fun h => (hem h).elim), Nat.add_zero]

lemma elimPrefix_nn_eq (gs : List Gate) (hlen : gs.length = 11) (m : ℕ) (hm : m ≤ 11) :
    nonNotCount (elimPrefix gs m).2 =
      (Finset.univ.filter fun k : Fin 11 => k.val < m ∧ isEmitNN gs k.val = true).card := by
  induction m with
  | zero => simp [elimPrefix, elim, nonNotCount]
  | succ m ih =>
    have hsucc := elimPrefix_succ gs m (by omega)
    have hstep : nonNotCount (elimPrefix gs (m + 1)).2 =
        nonNotCount (elimPrefix gs m).2 + (if isEmitNN gs m = true then 1 else 0) := by
      rw [hsucc]
      simp only [nonNotCount, List.countP_append]
      unfold isEmitNN isEmitted
      rw [List.getElem?_eq_getElem (by omega : m < gs.length)]
      cases hopt : (gateRes gs m).1 with
      | none => simp
      | some mg =>
        have hgr : (simplify gs[m].op (6 + (elimPrefix gs m).2.length)
            (gs[m].inputs.map fun i => (elimPrefix gs m).1.getD i (Stat.const false))).1 = some mg := by
          unfold gateRes at hopt
          rw [List.getElem?_eq_getElem (by omega : m < gs.length)] at hopt
          exact hopt
        have hop_eq := simplify_same_op _ _ _ mg (Option.mem_def.mpr hgr)
        simp only [Option.toList_some, List.countP_cons, List.countP_nil, Option.isSome_some,
          Bool.true_and, hop_eq]
        cases isNotGate gs[m].op <;> simp
    rw [hstep, ih (by omega)]
    let km : Fin 11 := ⟨m, by omega⟩
    by_cases hem : isEmitNN gs m = true
    · have hfilt : (Finset.univ.filter fun k : Fin 11 => k.val < m + 1 ∧ isEmitNN gs k.val = true) =
          insert km (Finset.univ.filter fun k : Fin 11 => k.val < m ∧ isEmitNN gs k.val = true) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hk1, hk2⟩
          by_cases hkm : k.val = m
          · left; exact Fin.ext hkm
          · right; exact ⟨by omega, hk2⟩
        · rintro (rfl | ⟨hk1, hk2⟩)
          · exact ⟨by simp [km], hem⟩
          · exact ⟨by omega, hk2⟩
      rw [hfilt, Finset.card_insert_of_notMem (by simp [km]), if_pos hem]
    · have hfilt : (Finset.univ.filter fun k : Fin 11 => k.val < m + 1 ∧ isEmitNN gs k.val = true) =
          Finset.univ.filter fun k : Fin 11 => k.val < m ∧ isEmitNN gs k.val = true := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hk1, hk2⟩
          have hne : k.val ≠ m := fun heq => hem (heq ▸ hk2)
          exact ⟨by omega, hk2⟩
        · rintro ⟨hk1, hk2⟩; exact ⟨by omega, hk2⟩
      rw [hfilt, ite_eq_right_iff.mpr (fun h => (hem h).elim), Nat.add_zero]

lemma simplify_some_bin {op : GateOp} {m : ℕ} {ins : List Stat} {mg : Gate}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hs : (simplify op m ins).1 = some mg) :
    (simplify op m ins).2 = Stat.wire m ∧
    ∃ j k, ins = [Stat.wire j, Stat.wire k] ∧ mg = ⟨op, [j, k]⟩ := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simplify, simpAnd] at hs
    · cases a <;> simp [simplify, simpAnd] at hs
    · cases a <;> cases b <;> simp only [simplify, simpAnd, Option.some.injEq] at hs
      · cases hs
      · cases hs
      · cases hs
      · subst hs; exact ⟨rfl, _, _, rfl, rfl⟩
    · simp [simplify, simpAnd] at hs
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simplify, simpOr] at hs
    · cases a <;> simp [simplify, simpOr] at hs
    · cases a <;> cases b <;> simp only [simplify, simpOr, Option.some.injEq] at hs
      · cases hs
      · cases hs
      · cases hs
      · subst hs; exact ⟨rfl, _, _, rfl, rfl⟩
    · simp [simplify, simpOr] at hs

lemma simplify_none_of_const_bin {op : GateOp} {m : ℕ} {ins : List Stat}
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hcm⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hcm
    · cases a <;> simp [simplify, simpAnd]
    · cases a <;> cases b <;> simp [simplify, simpAnd] at hcm ⊢
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hcm
    · cases a <;> simp [simplify, simpOr]
    · cases a <;> cases b <;> simp [simplify, simpOr] at hcm ⊢
    · simp at hlen

lemma simplify_wire_of_const_true {op : GateOp} {m : ℕ} {ins : List Stat} {j : ℕ}
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hc : Stat.const true ∈ ins)
    (hnone : (simplify op m ins).1 = none)
    (hw : (simplify op m ins).2 = Stat.wire j) :
    op = GateOp.and ∧ (ins = [Stat.const true, Stat.wire j] ∨ ins = [Stat.wire j, Stat.const true]) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpAnd] at hc hw
    · cases a with
      | const c1 =>
        cases b with
        | const c2 => simp [simplify, simpAnd] at hw
        | wire k =>
          cases c1 <;> simp [simplify, simpAnd] at hc hw
          subst hw; exact ⟨rfl, Or.inl rfl⟩
      | wire k =>
        cases b with
        | const c2 =>
          cases c2 <;> simp [simplify, simpAnd] at hc hw
          subst hw; exact ⟨rfl, Or.inr rfl⟩
        | wire k2 => simp [simplify, simpAnd] at hnone
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simplify, simpOr] at hc hw
    · cases a with
      | const c1 =>
        cases b with
        | const c2 => simp [simplify, simpOr] at hw
        | wire k => cases c1 <;> simp [simplify, simpOr] at hc hw
      | wire k =>
        cases b with
        | const c2 => cases c2 <;> simp [simplify, simpOr] at hc hw
        | wire k2 => simp [simplify, simpOr] at hnone
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp at hc
    · cases a <;> simp [simplify, simpNot] at hnone hw

lemma op_eval_tf_iff {op : GateOp}
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) :
    op.eval [true, false] = true ↔ op = GateOp.or := by
  rcases hop with rfl | rfl | rfl <;> simp [GateOp.eval]

lemma clean_fanInTwo {n : ℕ} {gs : List Gate} {o : ℕ} (hcl : CleanL n gs) :
    FanInTwo ⟨gs, o⟩ := by
  intro g hg
  have hok := (clean_nok n gs hcl g hg).1
  refine ⟨?_, hok.2⟩
  rcases hok.1 with h | h | h <;> simp [h]

lemma wiresFrom_take_succ (gs : List Gate) (w0 : List Bool) (k : ℕ) (hk : k < gs.length) :
    wiresFrom (gs.take (k + 1)) w0 =
      wiresFrom (gs.take k) w0 ++
        [gs[k].op.eval (gs[k].inputs.map fun i => (wiresFrom (gs.take k) w0).getD i false)] := by
  rw [List.take_succ_eq_append_getElem hk, wiresFrom_append]; rfl

lemma wiresFrom_getD_of_lt (gs : List Gate) (w0 : List Bool) (k j : ℕ) (hk : k ≤ gs.length)
    (hj : j < w0.length + k) :
    (wiresFrom gs w0).getD j false = (wiresFrom (gs.take k) w0).getD j false := by
  conv_lhs => rw [← List.take_append_drop k gs, wiresFrom_append]
  rw [getD_wiresFrom]
  rw [length_wiresFrom, List.length_take_of_le hk]; exact hj

lemma wiresFrom_gate_val (gs : List Gate) (w0 : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w0).getD (w0.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (wiresFrom (gs.take k) w0).getD i false) := by
  rw [wiresFrom_getD_of_lt gs w0 (k + 1) (w0.length + k) (by omega) (by omega),
      wiresFrom_take_succ gs w0 k hk, getD_snoc_len]
  rw [length_wiresFrom, List.length_take_of_le (by omega)]

lemma forall2_edit_no_zero {x4 x5 : ℕ} {l1 l2 : List ℕ}
    (h12 : List.Forall₂ (fun a b => b = a + 1 ∨ b = 0 ∧ (a = x4 ∨ a = x5)) l1 l2)
    (hno0 : 0 ∉ l2) :
    l2 = l1.map (fun a => a + 1) := by
  induction h12 with
  | nil => rfl
  | cons hab hrest ih =>
    rename_i a b l1' l2'
    have hb0 : b ≠ 0 := fun h => hno0 (by simp [h])
    have hb : b = a + 1 := hab.resolve_right (fun h => hb0 h.1)
    subst hb
    simp only [List.map_cons]
    congr 1
    exact ih (fun h => hno0 (List.mem_cons_of_mem _ h))

def SideNoTopBranch (ms : List Gate) (S : Finset (Fin 6)) : Prop :=
  ∀ r : Fin (6 + ms.length), FirstBranchRoute.Branches (readEdge ms) r →
    ∀ v ∈ S, ¬ ReflTransGen (readEdge ms) (inputWire ms v) r

def origWire (emitInv : Fin 8 → Fin 11) (u : Fin 14) : ℕ :=
  match u.val with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | 5 => 7
  | q + 6 => if hq : q < 8 then 8 + (emitInv ⟨q, hq⟩).val else 0

def isOr2Gate (g : Gate) : Bool := g.op.eval [true, false] && g.inputs.contains 2

def or2Set (gs : List Gate) : Finset (Fin 11) :=
  Finset.univ.filter fun k : Fin 11 => (gs[k.val]?.map isOr2Gate).getD false = true

def zeroSet (gs : List Gate) : Finset (Fin 11) :=
  Finset.univ.filter fun k : Fin 11 => (gs[k.val]?.map fun g => g.inputs.contains 0).getD false = true

lemma mem_zeroSet_iff {gs : List Gate} (hlen : gs.length = 11) (k : Fin 11) :
    k ∈ zeroSet gs ↔ 0 ∈ (gs[k.val]'(by omega)).inputs := by
  simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and,
    List.getElem?_eq_getElem (by omega : k.val < gs.length), Option.map_some, Option.getD_some,
    List.contains_iff_mem]

lemma list_filter_len_eq_finset_card {α : Type*} {l : List α} (hlen : l.length = 11) (p : α → Bool) :
    (l.filter p).length = (Finset.univ.filter fun k : Fin 11 => (l[k.val]?.map p).getD false = true).card := by
  have hgen : ∀ (n : ℕ) (xs : List α), xs.length = n →
      (xs.filter p).length = (Finset.univ.filter fun k : Fin n => (xs[k.val]?.map p).getD false = true).card := by
    intro n xs hxs
    subst hxs
    induction xs with
    | nil => simp
    | cons a t ih =>
      simp only [List.length_cons, List.filter_cons]
      have hsplit : (Finset.univ : Finset (Fin (t.length + 1))) =
          insert 0 (Finset.univ.image Fin.succ) := by
        ext k; cases k using Fin.cases <;> simp
      have hcard : (Finset.univ.filter fun k : Fin (t.length + 1) => ((a :: t)[k.val]?.map p).getD false = true).card =
          (if p a = true then 1 else 0) +
          (Finset.univ.filter fun k : Fin t.length => (t[k.val]?.map p).getD false = true).card := by
        rw [hsplit, Finset.filter_insert]
        have hnotmem : (0 : Fin (t.length + 1)) ∉ (Finset.univ.image Fin.succ).filter
            (fun k : Fin (t.length + 1) => ((a :: t)[k.val]?.map p).getD false = true) := by simp
        have himg : ((Finset.univ.image Fin.succ).filter
            (fun k : Fin (t.length + 1) => ((a :: t)[k.val]?.map p).getD false = true)).card =
            (Finset.univ.filter fun k : Fin t.length => (t[k.val]?.map p).getD false = true).card := by
          rw [Finset.filter_image, Finset.card_image_of_injective _ (Fin.succ_injective _)]
          rfl
        have h0 : ((a :: t)[(0 : Fin (t.length + 1)).val]?.map p).getD false = p a := rfl
        rw [h0]
        by_cases hpa : p a = true
        · rw [if_pos hpa, if_pos hpa, Finset.card_insert_of_notMem hnotmem, himg]; omega
        · rw [ite_eq_right_iff.mpr (fun h => (hpa h).elim), ite_eq_right_iff.mpr (fun h => (hpa h).elim), himg, Nat.zero_add]
      rw [hcard, ← ih]
      cases p a <;> simp; omega
  exact hgen 11 l hlen

def e2In : Fin 7 → Bool := fun i => decide (i = 2)

lemma theta_e2 : thetaFun e2In = false := by decide

lemma e2_at2 : e2In 2 = true := by decide

lemma or2_e2_vals {x2 x3 : Circuit} {x4 x5 : ℕ}
    (hlen2 : x2.gates.length = 11) (hlen3 : x3.gates.length = 11)
    (hok2 : ∀ g ∈ x2.gates, Ok g)
    (hed : ∀ k : Fin 11, EditGate x4 x5 (x2.gates[k.val]'(by omega)) (x3.gates[k.val]'(by omega)))
    (k : Fin 11) (hk : k ∈ or2Set x2.gates) :
    (x2.gates[k.val]'(by omega)).op = GateOp.or ∧
    2 ∈ (x2.gates[k.val]'(by omega)).inputs ∧
    (x2.wires (List.ofFn e2In)).getD (7 + k.val) false = true ∧
    (x3.wires (true :: List.ofFn e2In)).getD (8 + k.val) false = true := by
  have hk' : isOr2Gate (x2.gates[k.val]'(by omega)) = true := by
    simp only [or2Set, Finset.mem_filter, Finset.mem_univ, true_and,
      List.getElem?_eq_getElem (by omega : k.val < x2.gates.length), Option.map_some, Option.getD_some] at hk
    exact hk
  simp only [isOr2Gate, Bool.and_eq_true, List.contains_iff_mem] at hk'
  have hok := hok2 _ (List.mem_iff_getElem.mpr ⟨k.val, by omega, rfl⟩)
  have hop2 : (x2.gates[k.val]'(by omega)).op = GateOp.or := (op_eval_tf_iff hok.1).mp hk'.1
  have hmem2 : 2 ∈ (x2.gates[k.val]'(by omega)).inputs := hk'.2
  have hop3 : (x3.gates[k.val]'(by omega)).op = GateOp.or := (hed k).1.symm.trans hop2
  refine ⟨hop2, hmem2, ?_, ?_⟩
  · change (wiresFrom x2.gates (List.ofFn e2In)).getD (7 + k.val) false = true
    have hgw := wiresFrom_gate_val x2.gates (List.ofFn e2In) k.val (by omega)
    simp only [List.length_ofFn] at hgw
    rw [hgw, hop2, GateOp.eval, List.any_eq_true]
    refine ⟨true, List.mem_map.mpr ⟨2, hmem2, ?_⟩, rfl⟩
    rw [getD_wiresFrom _ _ 2 (by simp)]; simp [e2In]
  · change (wiresFrom x3.gates (true :: List.ofFn e2In)).getD (8 + k.val) false = true
    have hgw := wiresFrom_gate_val x3.gates (true :: List.ofFn e2In) k.val (by omega)
    simp only [List.length_cons, List.length_ofFn] at hgw
    rw [hgw, hop3, GateOp.eval, List.any_eq_true]
    obtain ⟨b, hbmem, hbrel⟩ := forall2_mem_left (hed k).2 hmem2
    refine ⟨true, List.mem_map.mpr ⟨b, hbmem, ?_⟩, rfl⟩
    rcases hbrel with rfl | ⟨rfl, _⟩
    · rw [getD_wiresFrom _ _ 3 (by simp)]; simp [e2In]
    · rw [getD_wiresFrom _ _ 0 (by simp)]; rfl

lemma find_first_e2_diff {x2 x3 : Circuit} {x4 x5 : ℕ}
    (hlen2 : x2.gates.length = 11) (hlen3 : x3.gates.length = 11)
    (hok2 : ∀ g ∈ x2.gates, Ok g) (hok3 : ∀ g ∈ x3.gates, Ok g)
    (heval2 : circuitFun 7 x2 = thetaFun)
    (hed : ∀ k : Fin 11, EditGate x4 x5 (x2.gates[k.val]'(by omega)) (x3.gates[k.val]'(by omega)))
    (heval3 : ∀ x : Fin 7 → Bool, (x3.wires (true :: List.ofFn x)).getD (x2.output + 1) false = (thetaFun x || x 2)) :
    x2.output < 18 ∧
    ∃ h : Fin 11,
      h ∉ or2Set x2.gates ∧
      h ∈ zeroSet x3.gates ∧
      isEmitted x3.gates h.val = false := by
  classical
  have hw2_out : (x2.wires (List.ofFn e2In)).getD x2.output false = false := by
    change x2.eval (List.ofFn e2In) = false
    have h := congrFun heval2 e2In
    change x2.eval (List.ofFn e2In) = thetaFun e2In at h
    rw [h, theta_e2]
  have hw3_out : (x3.wires (true :: List.ofFn e2In)).getD (x2.output + 1) false = true := by
    rw [heval3 e2In, theta_e2, e2_at2]; rfl
  have hout_lt : x2.output < 18 := by
    by_contra hge
    have h2 : (x3.wires (true :: List.ofFn e2In)).getD (x2.output + 1) false = false :=
      List.getD_eq_default _ _ (by
        change (wiresFrom x3.gates (true :: List.ofFn e2In)).length ≤ _
        rw [length_wiresFrom]; simp [hlen3]; omega)
    rw [h2] at hw3_out; exact Bool.noConfusion hw3_out
  have hex_nat : ∃ k : ℕ, k < 11 ∧
      (x2.wires (List.ofFn e2In)).getD (7 + k) false ≠
      (x3.wires (true :: List.ofFn e2In)).getD (8 + k) false := by
    by_contra hall; push_neg at hall
    have heq : (x2.wires (List.ofFn e2In)).getD x2.output false =
        (x3.wires (true :: List.ofFn e2In)).getD (x2.output + 1) false := by
      by_cases hlt7 : x2.output < 7
      · change (wiresFrom x2.gates (List.ofFn e2In)).getD x2.output false =
          (wiresFrom x3.gates (true :: List.ofFn e2In)).getD (x2.output + 1) false
        rw [getD_wiresFrom _ _ x2.output (by simp [hlt7]),
            getD_wiresFrom _ _ (x2.output + 1) (by simp; omega)]; rfl
      · have h1 := hall (x2.output - 7) (by omega)
        have ha : 7 + (x2.output - 7) = x2.output := by omega
        have hb : 8 + (x2.output - 7) = x2.output + 1 := by omega
        simpa only [ha, hb] using h1
    rw [hw2_out, hw3_out] at heq; exact Bool.noConfusion heq
  let hN := Nat.find hex_nat
  have hh_spec := Nat.find_spec hex_nat
  let h : Fin 11 := ⟨hN, hh_spec.1⟩
  have hh_pre_eq : ∀ a : ℕ,
      (wiresFrom (x2.gates.take h.val) (List.ofFn e2In)).getD a false =
      (wiresFrom (x3.gates.take h.val) (true :: List.ofFn e2In)).getD (a + 1) false := by
    intro a
    by_cases ha : a < 7 + h.val
    · rw [← wiresFrom_getD_of_lt x2.gates (List.ofFn e2In) h.val a (by omega) (by simp; omega),
          ← wiresFrom_getD_of_lt x3.gates (true :: List.ofFn e2In) h.val (a + 1) (by omega) (by simp; omega)]
      by_cases ha7 : a < 7
      · rw [getD_wiresFrom _ _ a (by simp [ha7]),
            getD_wiresFrom _ _ (a + 1) (by simp; omega)]; rfl
      · have hlt_h : a - 7 < hN := by change a < 7 + hN at ha; omega
        have hnot := Nat.find_min hex_nat hlt_h
        push_neg at hnot
        have h1 := hnot (by omega)
        have ha' : 7 + (a - 7) = a := by omega
        have hb' : 8 + (a - 7) = a + 1 := by omega
        change (x2.wires (List.ofFn e2In)).getD a false =
          (x3.wires (true :: List.ofFn e2In)).getD (a + 1) false
        simpa only [ha', hb'] using h1
    · rw [List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_take_of_le (by omega)]; simp; omega),
          List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_take_of_le (by omega)]; simp; omega)]
  have hh_not_or2 : h ∉ or2Set x2.gates := by
    intro hmem
    have hv := or2_e2_vals hlen2 hlen3 hok2 hed h hmem
    exact hh_spec.2 (hv.2.2.1.trans hv.2.2.2.symm)
  have h0mem : 0 ∈ (x3.gates[h.val]'(by omega)).inputs := by
    by_contra hno0
    apply hh_spec.2
    change (wiresFrom x2.gates (List.ofFn e2In)).getD (7 + h.val) false =
      (wiresFrom x3.gates (true :: List.ofFn e2In)).getD (8 + h.val) false
    have hgw2 := wiresFrom_gate_val x2.gates (List.ofFn e2In) h.val (by omega)
    have hgw3 := wiresFrom_gate_val x3.gates (true :: List.ofFn e2In) h.val (by omega)
    simp only [List.length_ofFn, List.length_cons] at hgw2 hgw3
    rw [hgw2, hgw3, (hed h).1]
    congr 1
    rw [forall2_edit_no_zero (hed h).2 hno0, List.map_map]
    exact List.map_congr_left fun a _ => hh_pre_eq a
  have hh_zero : h ∈ zeroSet x3.gates := (mem_zeroSet_iff hlen3 h).mpr h0mem
  have hh_not_emit : isEmitted x3.gates h.val = false := by
    have hok := hok3 _ (List.mem_iff_getElem.mpr ⟨h.val, by omega, rfl⟩)
    have hp0 := elim_fst_prefix (x3.gates.take h.val) (initSt, [])
    have hst0 : (elimPrefix x3.gates h.val).1.getD 0 (Stat.const false) = Stat.const true := by
      unfold elimPrefix; rw [← getD_of_prefix hp0 (i := 0) (by simp [initSt])]; rfl
    unfold isEmitted gateRes
    rw [List.getElem?_eq_getElem (by omega : h.val < x3.gates.length)]
    rcases hok.1 with hop | hop | hop
    · have hc : ∃ c, Stat.const c ∈ ((x3.gates[h.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates h.val).1.getD i (Stat.const false)) :=
        ⟨true, List.mem_map.mpr ⟨0, h0mem, hst0⟩⟩
      rw [simplify_none_of_const_bin (Or.inl hop) (by simpa using hok.2) hc]; rfl
    · have hc : ∃ c, Stat.const c ∈ ((x3.gates[h.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates h.val).1.getD i (Stat.const false)) :=
        ⟨true, List.mem_map.mpr ⟨0, h0mem, hst0⟩⟩
      rw [simplify_none_of_const_bin (Or.inr hop) (by simpa using hok.2) hc]; rfl
    · cases hins3 : (x3.gates[h.val]'(by omega)).inputs with
      | nil => rw [hins3] at h0mem; simp at h0mem
      | cons b rest3 =>
        by_cases hb0 : b = 0
        · subst hb0
          dsimp only
          rw [hop, hins3]
          simp only [List.map_cons, hst0, simplify, simpNot]
          rfl
        · exfalso
          have hfor := (hed h).2
          rw [hins3] at hfor
          cases hins2 : (x2.gates[h.val]'(by omega)).inputs with
          | nil => rw [hins2] at hfor; cases hfor
          | cons a rest2 =>
            rw [hins2] at hfor
            have hb_eq : b = a + 1 := (List.forall₂_cons.mp hfor).1.resolve_right (fun hc => hb0 hc.1)
            apply hh_spec.2
            change (wiresFrom x2.gates (List.ofFn e2In)).getD (7 + h.val) false =
              (wiresFrom x3.gates (true :: List.ofFn e2In)).getD (8 + h.val) false
            have hgw2 := wiresFrom_gate_val x2.gates (List.ofFn e2In) h.val (by omega)
            have hgw3 := wiresFrom_gate_val x3.gates (true :: List.ofFn e2In) h.val (by omega)
            simp only [List.length_ofFn, List.length_cons] at hgw2 hgw3
            rw [hgw2, hgw3, (hed h).1, hop, hins2, hins3, hb_eq]
            simp only [List.map_cons, GateOp.eval, List.headD_cons]
            rw [hh_pre_eq a]
  exact ⟨hout_lt, h, hh_not_or2, hh_zero, hh_not_emit⟩

lemma h_not_const {x2 x3 : Circuit} {x4 x5 : ℕ}
    (hlen2 : x2.gates.length = 11) (hlen3 : x3.gates.length = 11)
    (hok2 : ∀ g ∈ x2.gates, Ok g) (hok3 : ∀ g ∈ x3.gates, Ok g)
    (heval2 : circuitFun 7 x2 = thetaFun)
    (hed : ∀ k : Fin 11, EditGate x4 x5 (x2.gates[k.val]'(by omega)) (x3.gates[k.val]'(by omega)))
    (heval3 : ∀ x : Fin 7 → Bool, (x3.wires (true :: List.ofFn x)).getD (x2.output + 1) false = (thetaFun x || x 2))
    (hout_lt : x2.output < 18) (h : Fin 11) {outN : ℕ}
    (hout_st : (elim 6 x3.gates (initSt, [])).1.getD (x2.output + 1) (Stat.const false) = Stat.wire outN)
    (hno0_out : ∀ k : Fin 11, k ∉ insert h (or2Set x2.gates) → 0 ∉ (x3.gates[k.val]'(by omega)).inputs)
    (hemit_out : ∀ k : Fin 11, k ∉ insert h (or2Set x2.gates) → isEmitted x3.gates k.val = true)
    (hop_out : ∀ k : Fin 11, k ∉ insert h (or2Set x2.gates) →
      (x3.gates[k.val]'(by omega)).op = GateOp.and ∨ (x3.gates[k.val]'(by omega)).op = GateOp.or) :
    ∃ jhN : ℕ, (elim 6 x3.gates (initSt, [])).1.getD (8 + h.val) (Stat.const false) = Stat.wire jhN := by
  cases hsh : (elim 6 x3.gates (initSt, [])).1.getD (8 + h.val) (Stat.const false) with
  | wire j => exact ⟨j, rfl⟩
  | const c =>
    exfalso
    have hagree : ∀ j : ℕ, j < 18 → j ≠ 7 + h.val →
        (x2.wires (List.ofFn e2In)).getD j false =
        (x3.wires (true :: List.ofFn e2In)).getD (j + 1) false := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hj18 hjne
        by_cases hj7 : j < 7
        · change (wiresFrom x2.gates (List.ofFn e2In)).getD j false =
            (wiresFrom x3.gates (true :: List.ofFn e2In)).getD (j + 1) false
          rw [getD_wiresFrom _ _ j (by simp [hj7]),
              getD_wiresFrom _ _ (j + 1) (by simp; omega)]; rfl
        · let k : Fin 11 := ⟨j - 7, by omega⟩
          have hj_eq : j = 7 + k.val := by dsimp [k]; omega
          have hj1_eq : 7 + k.val + 1 = 8 + k.val := by omega
          rw [hj_eq, hj1_eq]
          by_cases hko : k ∈ or2Set x2.gates
          · have hv := or2_e2_vals hlen2 hlen3 hok2 hed k hko
            exact hv.2.2.1.trans hv.2.2.2.symm
          · have hkD : k ∉ insert h (or2Set x2.gates) := by
              intro hmem; rcases Finset.mem_insert.mp hmem with rfl | hko'
              · exact hjne hj_eq
              · exact hko hko'
            have hno0 := hno0_out k hkD
            change (wiresFrom x2.gates (List.ofFn e2In)).getD (7 + k.val) false =
              (wiresFrom x3.gates (true :: List.ofFn e2In)).getD (8 + k.val) false
            have hgw2 := wiresFrom_gate_val x2.gates (List.ofFn e2In) k.val (by omega)
            have hgw3 := wiresFrom_gate_val x3.gates (true :: List.ofFn e2In) k.val (by omega)
            simp only [List.length_ofFn, List.length_cons] at hgw2 hgw3
            rw [hgw2, hgw3, (hed k).1]
            congr 1
            rw [forall2_edit_no_zero (hed k).2 hno0, List.map_map]
            apply List.map_congr_left
            intro a ha
            by_cases hak : a < 7 + k.val
            · have hane : a ≠ 7 + h.val := by
                intro haeq
                have hfull : elimPrefix x3.gates 11 = elim 6 x3.gates (initSt, []) := by
                  unfold elimPrefix; rw [List.take_of_length_le (by omega)]
                have hp := elimPrefix_fst_prefix x3.gates (j := k.val) (k := 11) (by omega)
                rw [hfull] at hp
                have hst_in : (elimPrefix x3.gates k.val).1.getD (a + 1) (Stat.const false) = Stat.const c := by
                  rw [getD_of_prefix hp (i := a + 1) (by rw [elimPrefix_fst_len x3.gates k.val (by omega)]; omega)]
                  rw [haeq, show 7 + h.val + 1 = 8 + h.val by omega]; exact hsh
                have hmem3 : a + 1 ∈ (x3.gates[k.val]'(by omega)).inputs := by
                  rw [forall2_edit_no_zero (hed k).2 hno0]
                  exact List.mem_map.mpr ⟨a, ha, rfl⟩
                have hc : ∃ c', Stat.const c' ∈ ((x3.gates[k.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates k.val).1.getD i (Stat.const false)) :=
                  ⟨c, List.mem_map.mpr ⟨a + 1, hmem3, hst_in⟩⟩
                have hok := hok3 _ (List.mem_iff_getElem.mpr ⟨k.val, by omega, rfl⟩)
                have hnone := simplify_none_of_const_bin (m := 6 + (elimPrefix x3.gates k.val).2.length) (hop_out k hkD) (by simpa using hok.2) hc
                have hem := hemit_out k hkD
                unfold isEmitted gateRes at hem
                rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length), hnone] at hem
                simp at hem
              dsimp only [Function.comp_apply]
              rw [← wiresFrom_getD_of_lt x2.gates (List.ofFn e2In) k.val a (by omega) (by simp; omega),
                  ← wiresFrom_getD_of_lt x3.gates (true :: List.ofFn e2In) k.val (a + 1) (by omega) (by simp; omega)]
              exact ih a (by omega) (by omega) hane
            · dsimp only [Function.comp_apply]
              rw [List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_take_of_le (by omega)]; simp; omega),
                  List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_take_of_le (by omega)]; simp; omega)]
    have hout_ne_h : x2.output ≠ 7 + h.val := by
      intro heq
      have h1 : x2.output + 1 = 8 + h.val := by omega
      rw [h1, hsh] at hout_st; exact Stat.noConfusion hout_st
    have heq := hagree x2.output hout_lt hout_ne_h
    have hw2_out : (x2.wires (List.ofFn e2In)).getD x2.output false = false := by
      change x2.eval (List.ofFn e2In) = false
      have h' := congrFun heval2 e2In
      change x2.eval (List.ofFn e2In) = thetaFun e2In at h'
      rw [h', theta_e2]
    have hw3_out : (x3.wires (true :: List.ofFn e2In)).getD (x2.output + 1) false = true := by
      rw [heval3 e2In, theta_e2, e2_at2]; rfl
    rw [hw2_out, hw3_out] at heq; exact Bool.noConfusion heq

lemma h_gate_struct {x2 x3 : Circuit} {x4 x5 : ℕ}
    (hlen2 : x2.gates.length = 11) (hlen3 : x3.gates.length = 11)
    (hok3 : ∀ g ∈ x3.gates, Ok g)
    (hed : ∀ k : Fin 11, EditGate x4 x5 (x2.gates[k.val]'(by omega)) (x3.gates[k.val]'(by omega)))
    (h : Fin 11) (jhN : ℕ)
    (hh_zero : h ∈ zeroSet x3.gates)
    (hh_not_emit : isEmitted x3.gates h.val = false)
    (hh_st : (elim 6 x3.gates (initSt, [])).1.getD (8 + h.val) (Stat.const false) = Stat.wire jhN) :
    ∃ w3 a2, 1 ≤ w3 ∧ w3 < 8 + h.val ∧
      (elim 6 x3.gates (initSt, [])).1.getD w3 (Stat.const false) = Stat.wire jhN ∧
      (x2.gates[h.val]'(by omega)).op = GateOp.and ∧
      (x3.gates[h.val]'(by omega)).op = GateOp.and ∧
      (((x3.gates[h.val]'(by omega)).inputs = [0, w3] ∧ (x2.gates[h.val]'(by omega)).inputs = [a2, w3 - 1]) ∨
       ((x3.gates[h.val]'(by omega)).inputs = [w3, 0] ∧ (x2.gates[h.val]'(by omega)).inputs = [w3 - 1, a2])) := by
  have h0mem : 0 ∈ (x3.gates[h.val]'(by omega)).inputs := (mem_zeroSet_iff hlen3 h).mp hh_zero
  have hok := hok3 _ (List.mem_iff_getElem.mpr ⟨h.val, by omega, rfl⟩)
  have hp0 := elim_fst_prefix (x3.gates.take h.val) (initSt, [])
  have hst0 : (elimPrefix x3.gates h.val).1.getD 0 (Stat.const false) = Stat.const true := by
    unfold elimPrefix; rw [← getD_of_prefix hp0 (i := 0) (by simp [initSt])]; rfl
  have hc_in : Stat.const true ∈ ((x3.gates[h.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates h.val).1.getD i (Stat.const false)) :=
    List.mem_map.mpr ⟨0, h0mem, hst0⟩
  have hnone : (gateRes x3.gates h.val).1 = none := by
    unfold isEmitted at hh_not_emit
    cases hopt : (gateRes x3.gates h.val).1 with
    | none => rfl
    | some _ => simp [hopt] at hh_not_emit
  have hres2 : (gateRes x3.gates h.val).2 = Stat.wire jhN :=
    (elimPrefix_st_at x3.gates h.val (by omega)).symm.trans hh_st
  unfold gateRes at hnone hres2
  rw [List.getElem?_eq_getElem (by omega : h.val < x3.gates.length)] at hnone hres2
  obtain ⟨hop3, hins_eq⟩ := simplify_wire_of_const_true hok.1 (by simpa using hok.2) hc_in hnone hres2
  have hop2 : (x2.gates[h.val]'(by omega)).op = GateOp.and := (hed h).1.trans hop3
  have hfull : elimPrefix x3.gates 11 = elim 6 x3.gates (initSt, []) := by
    unfold elimPrefix; rw [List.take_of_length_le (by omega)]
  have hp_h := elimPrefix_fst_prefix x3.gates (j := h.val) (k := 11) (by omega)
  rw [hfull] at hp_h
  have hget_wire : ∀ u, (elimPrefix x3.gates h.val).1.getD u (Stat.const false) = Stat.wire jhN →
      1 ≤ u ∧ u < 8 + h.val ∧ (elim 6 x3.gates (initSt, [])).1.getD u (Stat.const false) = Stat.wire jhN := by
    intro u hu
    have hu_lt : u < 8 + h.val := by
      by_contra hge
      rw [List.getD_eq_default _ _ (by rw [elimPrefix_fst_len x3.gates h.val (by omega)]; omega)] at hu
      exact Stat.noConfusion hu
    have hu_ge1 : 1 ≤ u := by
      by_contra hlt1
      have hu0 : u = 0 := by omega
      subst hu0; rw [hst0] at hu; exact Stat.noConfusion hu
    refine ⟨hu_ge1, hu_lt, ?_⟩
    rw [← getD_of_prefix hp_h (i := u) (by rw [elimPrefix_fst_len x3.gates h.val (by omega)]; omega)]
    exact hu
  rcases hins_eq with hl | hr
  · rcases h3in : (x3.gates[h.val]'(by omega)).inputs with _ | ⟨u1, _ | ⟨u2, _ | ⟨_, _⟩⟩⟩
    · rw [h3in] at hl; simp at hl
    · rw [h3in] at hl; simp at hl
    · rw [h3in] at hl
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
      have hu1_0 : u1 = 0 := by
        rw [h3in] at h0mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at h0mem
        rcases h0mem with rfl | rfl
        · rfl
        · rw [hst0] at hl; exact Stat.noConfusion hl.2
      subst hu1_0
      obtain ⟨hu2_ge1, hu2_lt, hu2_st⟩ := hget_wire u2 hl.2
      have hfor := (hed h).2; rw [h3in] at hfor
      rcases h2in : (x2.gates[h.val]'(by omega)).inputs with _ | ⟨v1, _ | ⟨v2, _ | ⟨_, _⟩⟩⟩
      · rw [h2in] at hfor; have hl := hfor.length_eq; simp at hl
      · rw [h2in] at hfor; have hl := hfor.length_eq; simp at hl
      · rw [h2in] at hfor
        have hv2 : u2 = v2 + 1 := (List.forall₂_cons.mp (List.forall₂_cons.mp hfor).2).1.resolve_right (fun hc => by omega)
        refine ⟨u2, v1, hu2_ge1, hu2_lt, hu2_st, hop2, hop3, Or.inl ⟨rfl, ?_⟩⟩
        congr 2; omega
      · rw [h2in] at hfor; have hl := hfor.length_eq; simp at hl
    · rw [h3in] at hl; simp at hl
  · rcases h3in : (x3.gates[h.val]'(by omega)).inputs with _ | ⟨u1, _ | ⟨u2, _ | ⟨_, _⟩⟩⟩
    · rw [h3in] at hr; simp at hr
    · rw [h3in] at hr; simp at hr
    · rw [h3in] at hr
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
      have hu2_0 : u2 = 0 := by
        rw [h3in] at h0mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at h0mem
        rcases h0mem with rfl | rfl
        · rw [hst0] at hr; exact Stat.noConfusion hr.1
        · rfl
      subst hu2_0
      obtain ⟨hu1_ge1, hu1_lt, hu1_st⟩ := hget_wire u1 hr.1
      have hfor := (hed h).2; rw [h3in] at hfor
      rcases h2in : (x2.gates[h.val]'(by omega)).inputs with _ | ⟨v1, _ | ⟨v2, _ | ⟨_, _⟩⟩⟩
      · rw [h2in] at hfor; have hl := hfor.length_eq; simp at hl
      · rw [h2in] at hfor; have hl := hfor.length_eq; simp at hl
      · rw [h2in] at hfor
        have hv1 : u1 = v1 + 1 := (List.forall₂_cons.mp hfor).1.resolve_right (fun hc => by omega)
        refine ⟨u1, v2, hu1_ge1, hu1_lt, hu1_st, hop2, hop3, Or.inr ⟨rfl, ?_⟩⟩
        congr 1; omega
      · rw [h2in] at hfor; have hl := hfor.length_eq; simp at hl
    · rw [h3in] at hr; simp at hr

structure ElimData (x2 x3 : Circuit) (x4 x5 : ℕ) where
  st : List Stat
  ms : List Gate
  outM : Fin 14
  g1 : Fin 11
  g2 : Fin 11
  h : Fin 11
  w3 : ℕ
  jh : Fin 14
  a2 : ℕ
  emitInv : Fin 8 → Fin 11
  hst_eq : (st, ms) = elim 6 x3.gates (initSt, [])
  hms_len : ms.length = 8
  hcl : CleanL 6 ms
  hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or
  hout_st : st.getD (x2.output + 1) (Stat.const false) = Stat.wire outM.val
  hout_lt : x2.output < 18
  hleast : Least 6 c6Fun ms outM.val
  hdistinct : g1 ≠ g2 ∧ g1 ≠ h ∧ g2 ≠ h
  hor2_1 : ∀ g, x2.gates[g1.val]? = some g → g.op = GateOp.or ∧ 2 ∈ g.inputs
  hor2_2 : ∀ g, x2.gates[g2.val]? = some g → g.op = GateOp.or ∧ 2 ∈ g.inputs
  hw3_ge : 1 ≤ w3
  hw3_lt : w3 < 8 + h.val
  hw3_st : st.getD w3 (Stat.const false) = Stat.wire jh.val
  hh_st : st.getD (8 + h.val) (Stat.const false) = Stat.wire jh.val
  hh_gate : ∀ g2g g3g, x2.gates[h.val]? = some g2g → x3.gates[h.val]? = some g3g →
    g2g.op = GateOp.and ∧ g3g.op = GateOp.and ∧
    ((g3g.inputs = [0, w3] ∧ g2g.inputs = [a2, w3 - 1]) ∨
     (g3g.inputs = [w3, 0] ∧ g2g.inputs = [w3 - 1, a2]))
  hemit_inj : Function.Injective emitInv
  hemit_disj : ∀ q : Fin 8, emitInv q ≠ g1 ∧ emitInv q ≠ g2 ∧ emitInv q ≠ h
  hemit_st : ∀ q : Fin 8, st.getD (8 + (emitInv q).val) (Stat.const false) = Stat.wire (6 + q.val)
  hemit_gate : ∀ (q : Fin 8) g2g g3g mg,
    x2.gates[(emitInv q).val]? = some g2g →
    x3.gates[(emitInv q).val]? = some g3g →
    ms[q.val]? = some mg →
    g2g.op = mg.op ∧ g3g.op = mg.op ∧
    ∃ i1 i2 j1 j2,
      g2g.inputs = [i1, i2] ∧
      g3g.inputs = [i1 + 1, i2 + 1] ∧
      mg.inputs = [j1, j2] ∧
      i1 + 1 < 8 + (emitInv q).val ∧
      i2 + 1 < 8 + (emitInv q).val ∧
      st.getD (i1 + 1) (Stat.const false) = Stat.wire j1 ∧
      st.getD (i2 + 1) (Stat.const false) = Stat.wire j2
  hst_wire_cases : ∀ (i : ℕ) (u : Fin 14),
    st.getD i (Stat.const false) = Stat.wire u.val →
    i = origWire emitInv u ∨ i = 8 + g1.val ∨ i = 8 + g2.val ∨ i = 8 + h.val
  hside : SideNoTopBranch ms ({1, 2, 3} : Finset (Fin 6)) ∨
          SideNoTopBranch ms ({0, 4, 5} : Finset (Fin 6))

lemma extract_elim_data (x2 x3 : Circuit) (x4 x5 : ℕ)
    (hfan : FanInTwo x2) (hsz : x2.size = 11)
    (heval2 : circuitFun 7 x2 = thetaFun)
    (hedit : List.Forall₂ (EditGate x4 x5) x2.gates x3.gates)
    (heval3 : ∀ x : Fin 7 → Bool, (x3.wires (true :: List.ofFn x)).getD (x2.output + 1) false = (thetaFun x || x 2))
    (hor2 : (x2.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length = 2) :
    Nonempty (ElimData x2 x3 x4 x5) := by
  classical
  have hlen2 : x2.gates.length = 11 := hsz
  have hlen3 : x3.gates.length = 11 := hedit.length_eq.symm.trans hlen2
  have hok2 : ∀ g ∈ x2.gates, Ok g := hfan
  have hed : ∀ k : Fin 11, EditGate x4 x5 (x2.gates[k.val]'(by omega)) (x3.gates[k.val]'(by omega)) :=
    fun k => forall2_getElem hedit k.val (by omega) (by omega)
  have hok3 : ∀ g ∈ x3.gates, Ok g := by
    intro g hg; obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    exact edit_ok (hok2 _ (List.mem_iff_getElem.mpr ⟨k, by omega, rfl⟩)) (hed ⟨k, by omega⟩)
  set resAll := elim 6 x3.gates (initSt, []) with hresAll
  set st := resAll.1 with hst
  set ms := resAll.2 with hms
  have hfull : elimPrefix x3.gates 11 = (st, ms) := by
    unfold elimPrefix; rw [List.take_of_length_le (by omega)]
  have hst_len : st.length = 19 := by rw [hst, hresAll, elim_fst_len]; simp [initSt, hlen3]
  have hinv : ∀ x : Fin 6 → Bool,
      Inv 6 (List.ofFn x) (wiresFrom x3.gates (true :: List.ofFn (lift6 x))) (st, ms) :=
    fun x => inv_elim 6 (List.ofFn x) (by simp) x3.gates (true :: List.ofFn (lift6 x)) (initSt, []) hok3 (inv_initSt x)
  have hcl : CleanL 6 ms :=
    clean_elim 6 (List.ofFn fun _ : Fin 6 => false) (by simp) x3.gates _ (initSt, []) hok3 (inv_initSt _)
      (by intro p g hp; simp at hp)
  have hval_out : ∀ x : Fin 6 → Bool,
      (st.getD (x2.output + 1) (Stat.const false)).val (wiresFrom ms (List.ofFn x)) = c6Fun x := by
    intro x
    have h1 := ((hinv x).2 (x2.output + 1)).2
    have h2 : (wiresFrom x3.gates (true :: List.ofFn (lift6 x))).getD (x2.output + 1) false = c6Fun x := by
      change (x3.wires (true :: List.ofFn (lift6 x))).getD (x2.output + 1) false = c6Fun x
      rw [heval3 (lift6 x), theta_lift6]; simp [lift6]
    exact h1.trans h2
  obtain ⟨outN, hout_st⟩ : ∃ outN : ℕ, st.getD (x2.output + 1) (Stat.const false) = Stat.wire outN := by
    cases hs : st.getD (x2.output + 1) (Stat.const false) with
    | const c =>
      exfalso; obtain ⟨x, y, hxy⟩ := c6_nonconstant
      apply hxy; rw [← hval_out x, ← hval_out y, hs]; rfl
    | wire j => exact ⟨j, rfl⟩
  have hout_eval : ∀ x : Fin 6 → Bool, vl ms x outN = c6Fun x := by
    intro x; have h1 := hval_out x; rw [hout_st] at h1; exact h1
  have hge8 : 8 ≤ nonNotCount ms := c6_nonNot_ge_8 ⟨ms, outN⟩ (clean_fanInTwo hcl) hout_eval
  have hSor2_card : (or2Set x2.gates).card = 2 := (list_filter_len_eq_finset_card hlen2 isOr2Gate).symm.trans hor2
  obtain ⟨hout_lt, h, hh_not_or2, hh_zero, hh_not_emit⟩ :=
    find_first_e2_diff hlen2 hlen3 hok2 hok3 heval2 hed heval3
  have hSor2_not_emit : ∀ k ∈ or2Set x2.gates, isEmitted x3.gates k.val = false := by
    intro k hk
    have hv := or2_e2_vals hlen2 hlen3 hok2 hed k hk
    have hop3 : (x3.gates[k.val]'(by omega)).op = GateOp.or := (hed k).1.symm.trans hv.1
    obtain ⟨b, hbmem, hbrel⟩ := forall2_mem_left (hed k).2 hv.2.1
    have hp0 := elim_fst_prefix (x3.gates.take k.val) (initSt, [])
    have hc : ∃ c, Stat.const c ∈ ((x3.gates[k.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates k.val).1.getD i (Stat.const false)) := by
      rcases hbrel with rfl | ⟨rfl, _⟩
      · exact ⟨false, List.mem_map.mpr ⟨3, hbmem, by unfold elimPrefix; rw [← getD_of_prefix hp0 (i := 3) (by simp [initSt])]; rfl⟩⟩
      · exact ⟨true, List.mem_map.mpr ⟨0, hbmem, by unfold elimPrefix; rw [← getD_of_prefix hp0 (i := 0) (by simp [initSt])]; rfl⟩⟩
    have hok := hok3 _ (List.mem_iff_getElem.mpr ⟨k.val, by omega, rfl⟩)
    unfold isEmitted gateRes
    rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length),
        simplify_none_of_const_bin (Or.inr hop3) (by simpa using hok.2) hc]; rfl
  have hSzero_not_nn : ∀ k ∈ zeroSet x3.gates, isEmitNN x3.gates k.val = false := by
    intro k hk
    have h0mem : 0 ∈ (x3.gates[k.val]'(by omega)).inputs := (mem_zeroSet_iff hlen3 k).mp hk
    have hok := hok3 _ (List.mem_iff_getElem.mpr ⟨k.val, by omega, rfl⟩)
    unfold isEmitNN
    rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length)]
    rcases hok.1 with hop | hop | hop
    · have hp0 := elim_fst_prefix (x3.gates.take k.val) (initSt, [])
      have hc : ∃ c, Stat.const c ∈ ((x3.gates[k.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates k.val).1.getD i (Stat.const false)) :=
        ⟨true, List.mem_map.mpr ⟨0, h0mem, by unfold elimPrefix; rw [← getD_of_prefix hp0 (i := 0) (by simp [initSt])]; rfl⟩⟩
      have hne : isEmitted x3.gates k.val = false := by
        unfold isEmitted gateRes
        rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length),
            simplify_none_of_const_bin (Or.inl hop) (by simpa using hok.2) hc]; rfl
      simp [hne]
    · have hp0 := elim_fst_prefix (x3.gates.take k.val) (initSt, [])
      have hc : ∃ c, Stat.const c ∈ ((x3.gates[k.val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates k.val).1.getD i (Stat.const false)) :=
        ⟨true, List.mem_map.mpr ⟨0, h0mem, by unfold elimPrefix; rw [← getD_of_prefix hp0 (i := 0) (by simp [initSt])]; rfl⟩⟩
      have hne : isEmitted x3.gates k.val = false := by
        unfold isEmitted gateRes
        rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length),
            simplify_none_of_const_bin (Or.inr hop) (by simpa using hok.2) hc]; rfl
      simp [hne]
    · dsimp only; rw [hop]; unfold isNotGate; simp
  let D : Finset (Fin 11) := insert h (or2Set x2.gates)
  have hD_card : D.card = 3 := by rw [Finset.card_insert_of_notMem hh_not_or2, hSor2_card]
  have hUD_card : (Finset.univ \ D).card = 8 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hD_card]
  let S_bad : Finset (Fin 11) := or2Set x2.gates ∪ zeroSet x3.gates
  have hD_sub : D ⊆ S_bad := by
    intro k hk; rcases Finset.mem_insert.mp hk with rfl | hko
    · exact Finset.mem_union_right _ hh_zero
    · exact Finset.mem_union_left _ hko
  let E_nn : Finset (Fin 11) := Finset.univ.filter fun k : Fin 11 => isEmitNN x3.gates k.val = true
  have hnn_eq : nonNotCount ms = E_nn.card := by
    have h1 := elimPrefix_nn_eq x3.gates hlen3 11 le_rfl
    rw [hfull] at h1; rw [h1]; congr 1
  have hdisj : Disjoint E_nn S_bad := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    have h1 : isEmitNN x3.gates k.val = true := (Finset.mem_filter.mp hk1).2
    rcases Finset.mem_union.mp hk2 with ho | hz
    · have hne := hSor2_not_emit k ho
      unfold isEmitNN at h1
      rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length), hne] at h1
      simp at h1
    · rw [hSzero_not_nn k hz] at h1; exact Bool.noConfusion h1
  have hsum_le : E_nn.card + S_bad.card ≤ 11 := by
    have h1 := Finset.card_le_univ (E_nn ∪ S_bad)
    rw [Finset.card_union_of_disjoint hdisj] at h1; simpa using h1
  have hSbad_ge3 : 3 ≤ S_bad.card := hD_card ▸ Finset.card_le_card hD_sub
  have hEnn_card : E_nn.card = 8 := by omega
  have hSbad_eq_D : S_bad = D := (Finset.eq_of_subset_of_card_le hD_sub (by omega)).symm
  have hEnn_eq : E_nn = Finset.univ \ D := by
    have hsub : E_nn ⊆ Finset.univ \ D := fun k hk =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, fun hkd => Finset.disjoint_left.mp hdisj hk (hD_sub hkd)⟩
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have hno0_out : ∀ k : Fin 11, k ∉ D → 0 ∉ (x3.gates[k.val]'(by omega)).inputs := by
    intro k hk h0
    have hm : k ∈ S_bad := Finset.mem_union_right _ ((mem_zeroSet_iff hlen3 k).mpr h0)
    rw [hSbad_eq_D] at hm; exact hk hm
  have hemit_iff : ∀ k : Fin 11, isEmitted x3.gates k.val = true ↔ k ∉ D := by
    intro k; constructor
    · intro hem hkd; rcases Finset.mem_insert.mp hkd with rfl | hko
      · rw [hh_not_emit] at hem; exact Bool.noConfusion hem
      · rw [hSor2_not_emit k hko] at hem; exact Bool.noConfusion hem
    · intro hnot
      have hm : k ∈ E_nn := by rw [hEnn_eq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hnot⟩
      have hnn : isEmitNN x3.gates k.val = true := (Finset.mem_filter.mp hm).2
      unfold isEmitNN at hnn
      rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length)] at hnn
      exact ((Bool.and_eq_true _ _).mp hnn).1
  have hop_out : ∀ k : Fin 11, k ∉ D →
      (x3.gates[k.val]'(by omega)).op = GateOp.and ∨ (x3.gates[k.val]'(by omega)).op = GateOp.or := by
    intro k hnot
    have hm : k ∈ E_nn := by rw [hEnn_eq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hnot⟩
    have hnn : isEmitNN x3.gates k.val = true := (Finset.mem_filter.mp hm).2
    unfold isEmitNN at hnn
    rw [List.getElem?_eq_getElem (by omega : k.val < x3.gates.length)] at hnn
    have hnotnot : isNotGate (x3.gates[k.val]'(by omega)).op = false := by
      simpa using ((Bool.and_eq_true _ _).mp hnn).2
    rcases (hok3 _ (List.mem_iff_getElem.mpr ⟨k.val, by omega, rfl⟩)).1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · rw [h1] at hnotnot; simp [isNotGate] at hnotnot
  have hms_len : ms.length = 8 := by
    have h1 := elimPrefix_len_eq x3.gates hlen3 11 le_rfl
    rw [hfull] at h1; rw [h1]
    have hfe : (Finset.univ.filter fun k : Fin 11 => k.val < 11 ∧ isEmitted x3.gates k.val = true) = Finset.univ \ D := by
      ext k; simp [hemit_iff]
    rw [hfe, hUD_card]
  have hnot_zero : notGateCount ms = 0 := by
    have hct := nonNotCount_add_notCount ms
    change nonNotCount ms + notGateCount ms = ms.length at hct
    rw [hnn_eq, hEnn_card, hms_len] at hct; omega
  have hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases (clean_nok 6 ms hcl g hg).1.1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      have hpos : 0 < (ms.filter fun g' => isNotGate g'.op).length :=
        List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, by rw [h1]; rfl⟩)
      change (ms.filter fun g' => isNotGate g'.op).length = 0 at hnot_zero; omega
  obtain ⟨jhN, hh_st⟩ := h_not_const hlen2 hlen3 hok2 hok3 heval2 hed heval3 hout_lt h hout_st
    hno0_out (fun k hk => (hemit_iff k).mpr hk) hop_out
  obtain ⟨w3, a2, hw3_ge, hw3_lt, hw3_st, hh_op2, hh_op3, hh_ins⟩ :=
    h_gate_struct hlen2 hlen3 hok3 hed h jhN hh_zero hh_not_emit hh_st
  have hjh_lt : jhN < 14 := by
    have hval := ((hinv (fun _ => false)).2 (8 + h.val)).1
    rw [hh_st] at hval; change jhN < 6 + ms.length at hval; omega
  have hout_lt14 : outN < 14 := by
    have hval := ((hinv (fun _ => false)).2 (x2.output + 1)).1
    rw [hout_st] at hval; change outN < 6 + ms.length at hval; omega
  let outM : Fin 14 := ⟨outN, hout_lt14⟩
  let jh : Fin 14 := ⟨jhN, hjh_lt⟩
  obtain ⟨g1, g2, hg12_ne, hSor2_eq⟩ := Finset.card_eq_two.mp hSor2_card
  have hg1_in : g1 ∈ or2Set x2.gates := by rw [hSor2_eq]; simp
  have hg2_in : g2 ∈ or2Set x2.gates := by rw [hSor2_eq]; simp
  have hg1_ne_h : g1 ≠ h := fun heq => hh_not_or2 (heq ▸ hg1_in)
  have hg2_ne_h : g2 ≠ h := fun heq => hh_not_or2 (heq ▸ hg2_in)
  have hD_mem : ∀ k : Fin 11, k ∈ D ↔ k = g1 ∨ k = g2 ∨ k = h := by
    intro k; simp only [D, hSor2_eq, Finset.mem_insert, Finset.mem_singleton]; tauto
  let E_set : Finset (Fin 11) := Finset.univ \ D
  have hstep_lt8 : ∀ k : {k : Fin 11 // k ∈ E_set}, (elimPrefix x3.gates k.val.val).2.length < 8 := by
    intro k
    have hem := (hemit_iff k.val).mpr (Finset.mem_sdiff.mp k.property).2
    have hsucc : (elimPrefix x3.gates (k.val.val + 1)).2.length = (elimPrefix x3.gates k.val.val).2.length + 1 := by
      rw [elimPrefix_succ x3.gates k.val.val (by omega), List.length_append]
      unfold isEmitted at hem
      cases hopt : (gateRes x3.gates k.val.val).1 with
      | none => simp [hopt] at hem
      | some _ => simp
    have hle : (elimPrefix x3.gates (k.val.val + 1)).2.length ≤ ms.length := by
      have hp := elimPrefix_snd_prefix x3.gates (j := k.val.val + 1) (k := 11) (by omega)
      rw [hfull] at hp; exact hp.length_le
    omega
  let emitFwd : {k : Fin 11 // k ∈ E_set} → Fin 8 := fun k => ⟨(elimPrefix x3.gates k.val.val).2.length, hstep_lt8 k⟩
  have hemitFwd_inj : Function.Injective emitFwd := by
    intro a b hab
    have hval : (elimPrefix x3.gates a.val.val).2.length = (elimPrefix x3.gates b.val.val).2.length := congrArg Fin.val hab
    have hlt_imp : ∀ x y : {k : Fin 11 // k ∈ E_set}, x.val.val < y.val.val →
        (elimPrefix x3.gates x.val.val).2.length < (elimPrefix x3.gates y.val.val).2.length := by
      intro x y hxy
      have hem := (hemit_iff x.val).mpr (Finset.mem_sdiff.mp x.property).2
      have hsucc : (elimPrefix x3.gates (x.val.val + 1)).2.length = (elimPrefix x3.gates x.val.val).2.length + 1 := by
        rw [elimPrefix_succ x3.gates x.val.val (by omega), List.length_append]
        unfold isEmitted at hem
        cases hopt : (gateRes x3.gates x.val.val).1 with
        | none => simp [hopt] at hem
        | some _ => simp
      have hle := (elimPrefix_snd_prefix x3.gates (j := x.val.val + 1) (k := y.val.val) (by omega)).length_le
      omega
    rcases lt_trichotomy a.val.val b.val.val with hlt | heq | hgt
    · exfalso; have := hlt_imp a b hlt; omega
    · exact Subtype.ext (Fin.ext heq)
    · exfalso; have := hlt_imp b a hgt; omega
  have hemitFwd_bij : Function.Bijective emitFwd :=
    (Fintype.bijective_iff_injective_and_card emitFwd).mpr ⟨hemitFwd_inj, by rw [Fintype.card_coe, hUD_card, Fintype.card_fin]⟩
  let emitEquiv : {k : Fin 11 // k ∈ E_set} ≃ Fin 8 := Equiv.ofBijective emitFwd hemitFwd_bij
  let emitInv : Fin 8 → Fin 11 := fun q => (emitEquiv.symm q).val
  have hemit_notD : ∀ q : Fin 8, emitInv q ∉ D := fun q => (Finset.mem_sdiff.mp (emitEquiv.symm q).property).2
  have hemit_step_len : ∀ q : Fin 8, (elimPrefix x3.gates (emitInv q).val).2.length = q.val := fun q =>
    congrArg Fin.val (emitEquiv.apply_symm_apply q)
  have hemit_full : ∀ q : Fin 8,
      st.getD (8 + (emitInv q).val) (Stat.const false) = Stat.wire (6 + q.val) ∧
      ∃ mg, ms[q.val]? = some mg ∧ (gateRes x3.gates (emitInv q).val).1 = some mg := by
    intro q
    have hnot := hemit_notD q
    have hem := (hemit_iff (emitInv q)).mpr hnot
    unfold isEmitted at hem
    cases hopt : (gateRes x3.gates (emitInv q).val).1 with
    | none => simp [hopt] at hem
    | some mg =>
      have hopt' : (simplify (x3.gates[(emitInv q).val]'(by omega)).op (6 + (elimPrefix x3.gates (emitInv q).val).2.length)
          ((x3.gates[(emitInv q).val]'(by omega)).inputs.map fun i => (elimPrefix x3.gates (emitInv q).val).1.getD i (Stat.const false))).1 = some mg := by
        unfold gateRes at hopt
        rw [List.getElem?_eq_getElem (by omega : (emitInv q).val < x3.gates.length)] at hopt
        exact hopt
      have hbin := simplify_some_bin (hop_out (emitInv q) hnot) hopt'
      have hst_q : st.getD (8 + (emitInv q).val) (Stat.const false) = Stat.wire (6 + q.val) := by
        rw [elimPrefix_st_at x3.gates (emitInv q).val (by omega)]
        unfold gateRes
        rw [List.getElem?_eq_getElem (by omega : (emitInv q).val < x3.gates.length), hbin.1, hemit_step_len q]
      have hms_q : ms[q.val]? = some mg := by
        have hp := elimPrefix_snd_prefix x3.gates (j := (emitInv q).val + 1) (k := 11) (by omega)
        rw [hfull] at hp
        have hlen_q1 : (elimPrefix x3.gates ((emitInv q).val + 1)).2.length = q.val + 1 := by
          rw [elimPrefix_succ x3.gates (emitInv q).val (by omega), List.length_append, hopt, hemit_step_len q]; simp
        rw [← getElem?_of_prefix hp (i := q.val) (by omega),
            elimPrefix_succ x3.gates (emitInv q).val (by omega), hopt,
            List.getElem?_append_right (by rw [hemit_step_len q])]
        simp [hemit_step_len q]
      exact ⟨hst_q, mg, hms_q, rfl⟩
  have hemit_gate : ∀ (q : Fin 8) g2g g3g mg,
      x2.gates[(emitInv q).val]? = some g2g →
      x3.gates[(emitInv q).val]? = some g3g →
      ms[q.val]? = some mg →
      g2g.op = mg.op ∧ g3g.op = mg.op ∧
      ∃ i1 i2 j1 j2,
        g2g.inputs = [i1, i2] ∧
        g3g.inputs = [i1 + 1, i2 + 1] ∧
        mg.inputs = [j1, j2] ∧
        i1 + 1 < 8 + (emitInv q).val ∧
        i2 + 1 < 8 + (emitInv q).val ∧
        st.getD (i1 + 1) (Stat.const false) = Stat.wire j1 ∧
        st.getD (i2 + 1) (Stat.const false) = Stat.wire j2 := by
    intro q g2g g3g mg hg2g hg3g hmg
    let k := emitInv q
    have hk11 : k.val < 11 := k.isLt
    have hnot := hemit_notD q
    have hg2_eq : x2.gates[k.val]'(by omega) = g2g := by
      have h1 := List.getElem?_eq_getElem (i := k.val) (by omega : k.val < x2.gates.length)
      rw [hg2g] at h1; exact Option.some.inj h1.symm
    have hg3_eq : x3.gates[k.val]'(by omega) = g3g := by
      have h1 := List.getElem?_eq_getElem (i := k.val) (by omega : k.val < x3.gates.length)
      rw [hg3g] at h1; exact Option.some.inj h1.symm
    obtain ⟨_, mg', hmg', hopt⟩ := hemit_full q
    have hmg_eq : mg' = mg := Option.some.inj (hmg'.symm.trans hmg)
    subst hmg_eq
    have hopt' : (simplify g3g.op (6 + (elimPrefix x3.gates k.val).2.length)
        (g3g.inputs.map fun i => (elimPrefix x3.gates k.val).1.getD i (Stat.const false))).1 = some mg' := by
      unfold gateRes at hopt; rw [hg3g] at hopt; exact hopt
    have hbin := simplify_some_bin (hg3_eq ▸ hop_out k hnot) hopt'
    obtain ⟨j1, j2, hins_map, hmg_def⟩ := hbin.2
    have hop_g3 : g3g.op = mg'.op := by rw [hmg_def]
    have hop_g2 : g2g.op = mg'.op := by rw [← hop_g3, ← hg2_eq, ← hg3_eq]; exact (hed k).1
    have h3map := forall2_edit_no_zero (hed k).2 (hno0_out k hnot)
    rw [hg2_eq, hg3_eq] at h3map
    rw [h3map, List.map_map] at hins_map
    rcases h2in : g2g.inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨_, _⟩⟩⟩
    · rw [h2in] at hins_map; simp at hins_map
    · rw [h2in] at hins_map; simp at hins_map
    · rw [h2in] at hins_map h3map
      simp only [List.map_cons, List.map_nil, Function.comp_apply, List.cons.injEq, and_true] at hins_map h3map
      have hp_k := elimPrefix_fst_prefix x3.gates (j := k.val) (k := 11) (by omega)
      rw [hfull] at hp_k
      have hlen_pre : (elimPrefix x3.gates k.val).1.length = 8 + k.val := elimPrefix_fst_len x3.gates k.val (by omega)
      have hi1_lt : i1 + 1 < 8 + k.val := by
        by_contra hge
        have hdef := List.getD_eq_default (elimPrefix x3.gates k.val).1 (Stat.const false) (n := i1 + 1) (by omega)
        rw [hdef] at hins_map; exact Stat.noConfusion hins_map.1
      have hi2_lt : i2 + 1 < 8 + k.val := by
        by_contra hge
        have hdef := List.getD_eq_default (elimPrefix x3.gates k.val).1 (Stat.const false) (n := i2 + 1) (by omega)
        rw [hdef] at hins_map; exact Stat.noConfusion hins_map.2
      have hst1 : st.getD (i1 + 1) (Stat.const false) = Stat.wire j1 := by
        rw [← getD_of_prefix hp_k (i := i1 + 1) (by omega)]; exact hins_map.1
      have hst2 : st.getD (i2 + 1) (Stat.const false) = Stat.wire j2 := by
        rw [← getD_of_prefix hp_k (i := i2 + 1) (by omega)]; exact hins_map.2
      exact ⟨hop_g2, hop_g3, i1, i2, j1, j2, rfl, h3map, by rw [hmg_def], hi1_lt, hi2_lt, hst1, hst2⟩
    · rw [h2in] at hins_map; simp at hins_map
  have hst_wire_cases : ∀ (i : ℕ) (u : Fin 14),
      st.getD i (Stat.const false) = Stat.wire u.val →
      i = origWire emitInv u ∨ i = 8 + g1.val ∨ i = 8 + g2.val ∨ i = 8 + h.val := by
    intro i u hiu
    have hi19 : i < 19 := by
      by_contra hge
      rw [List.getD_eq_default st (Stat.const false) (n := i) (by omega)] at hiu
      exact Stat.noConfusion hiu
    have hp0 := elim_fst_prefix x3.gates (initSt, [])
    change initSt <+: st at hp0
    by_cases hi8 : i < 8
    · have hi0 : initSt.getD i (Stat.const false) = Stat.wire u.val := by
        rw [getD_of_prefix hp0 (i := i) (by simp [initSt]; omega)]; exact hiu
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      · simp [initSt] at hi0
      · simp [initSt] at hi0; left; simp [origWire, ← hi0]
      · simp [initSt] at hi0; left; simp [origWire, ← hi0]
      · simp [initSt] at hi0
      · simp [initSt] at hi0; left; simp [origWire, ← hi0]
      · simp [initSt] at hi0; left; simp [origWire, ← hi0]
      · simp [initSt] at hi0; left; simp [origWire, ← hi0]
      · simp [initSt] at hi0; left; simp [origWire, ← hi0]
      · omega
    · let k : Fin 11 := ⟨i - 8, by omega⟩
      have hi_eq : i = 8 + k.val := by dsimp [k]; omega
      by_cases hkD : k ∈ D
      · rw [hD_mem] at hkD
        rcases hkD with hk' | hk' | hk'
        · right; left; rw [hi_eq, hk']
        · right; right; left; rw [hi_eq, hk']
        · right; right; right; rw [hi_eq, hk']
      · left
        let q : Fin 8 := emitEquiv ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hkD⟩⟩
        have hq8 : q.val < 8 := q.isLt
        have hinv_q : emitInv q = k := congrArg Subtype.val (emitEquiv.symm_apply_apply _)
        have hst_q := (hemit_full q).1
        rw [hinv_q, ← hi_eq, hiu] at hst_q
        have hu_eq : u.val = 6 + q.val := Stat.wire.inj hst_q
        have hu_fin : u = ⟨q.val + 6, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hu_fin]; simp only [origWire, hq8, ↓reduceDIte, hinv_q]; exact hi_eq
  have hleast : Least 6 c6Fun ms outM.val := by
    refine ⟨hcl, hout_eval, ?_⟩
    intro gs' o' hcl' hev' _
    have h8 : 8 ≤ nonNotCount gs' := c6_nonNot_ge_8 ⟨gs', o'⟩ (clean_fanInTwo hcl') hev'
    have hct := nonNotCount_add_notCount gs'
    omega
  have hside : SideNoTopBranch ms ({1, 2, 3} : Finset (Fin 6)) ∨
               SideNoTopBranch ms ({0, 4, 5} : Finset (Fin 6)) := by
    have valid : outM.val < 6 + ms.length := by rw [hms_len]; exact outM.isLt
    let outWire : Fin (6 + ms.length) := ⟨outM.val, valid⟩
    have live := least_read_edge_live hleast c6_nonconstant c6_depends c6_restrict_nonconstant valid
    have distinct := predecessors_nodup hleast c6_nonconstant
    set branches := circuitBranchWires (n := 6) ms
    have hbb := branching_budget hcl valid (fun w hw hne => by
        let wire : Fin (6 + ms.length) := ⟨w, hw⟩
        obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
        exact ⟨p, g, hg, hw'⟩)
      (branches.image Fin.val) (fun w hw => by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
    rw [Finset.card_image_of_injective _ Fin.val_injective] at hbb
    have hbr : branches.card ≤ 3 := by omega
    have hbip := c6_clean_eight_bipartite hcl outWire live distinct hout_eval hbr
    have hbefore : ∀ r : Fin (6 + ms.length), FirstBranchRoute.Branches (readEdge ms) r → r < outWire := by
      intro r hr; obtain ⟨a, _, path, _, _⟩ := hr
      exact lt_of_lt_of_le (read_order hcl path) (wire_le_output hcl outWire live a)
    rcases hbip.2.2 with ⟨hbB, _⟩ | ⟨hbA, _⟩
    · right; intro r hr v hv path
      have hle := FirstBranchRoute.ancestor_first_le (readEdge ms) outWire (read_order hcl) live path (Or.inr hr)
      change firstInputBoundary hcl outWire live v ≤ r at hle
      have hv_out : firstInputBoundary hcl outWire live v = outWire :=
        (Finset.mem_filter.mp (hbB ▸ hv : v ∈ BranchGroupsLean.bucket (firstInputBoundary hcl outWire live) outWire)).2
      rw [hv_out] at hle; exact not_lt_of_ge hle (hbefore r hr)
    · left; intro r hr v hv path
      have hle := FirstBranchRoute.ancestor_first_le (readEdge ms) outWire (read_order hcl) live path (Or.inr hr)
      change firstInputBoundary hcl outWire live v ≤ r at hle
      have hv_out : firstInputBoundary hcl outWire live v = outWire :=
        (Finset.mem_filter.mp (hbA ▸ hv : v ∈ BranchGroupsLean.bucket (firstInputBoundary hcl outWire live) outWire)).2
      rw [hv_out] at hle; exact not_lt_of_ge hle (hbefore r hr)
  refine ⟨⟨st, ms, outM, g1, g2, h, w3, jh, a2, emitInv, rfl, hms_len, hcl, hmono,
    hout_st, hout_lt, hleast, ⟨hg12_ne, hg1_ne_h, hg2_ne_h⟩, ?_, ?_, hw3_ge, hw3_lt, hw3_st,
    hh_st, ?_, Subtype.val_injective.comp emitEquiv.symm.injective, fun q => by
      have hnot := hemit_notD q; rw [hD_mem] at hnot; push_neg at hnot; exact hnot,
    fun q => (hemit_full q).1, hemit_gate, hst_wire_cases, hside⟩⟩
  · intro g hg
    have h1 := List.getElem?_eq_getElem (i := g1.val) (by omega : g1.val < x2.gates.length)
    rw [hg] at h1; rw [Option.some.inj h1]
    have hv := or2_e2_vals hlen2 hlen3 hok2 hed g1 hg1_in; exact ⟨hv.1, hv.2.1⟩
  · intro g hg
    have h1 := List.getElem?_eq_getElem (i := g2.val) (by omega : g2.val < x2.gates.length)
    rw [hg] at h1; rw [Option.some.inj h1]
    have hv := or2_e2_vals hlen2 hlen3 hok2 hed g2 hg2_in; exact ⟨hv.1, hv.2.1⟩
  · intro g2g g3g hg2g hg3g
    have h1 := List.getElem?_eq_getElem (i := h.val) (by omega : h.val < x2.gates.length)
    rw [hg2g] at h1
    have h2 := List.getElem?_eq_getElem (i := h.val) (by omega : h.val < x3.gates.length)
    rw [hg3g] at h2
    rw [Option.some.inj h1, Option.some.inj h2]
    exact ⟨hh_op2, hh_op3, hh_ins⟩

end Step1


namespace Step2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup C6Lower Step1
open Relation

def canonL (ord : Fin 3) : Fin 8 → Fin 14
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => match ord with | 0 => 9 | 1 => 9 | 2 => 10
  | ⟨7, _⟩ => 12

def canonR (ord : Fin 3) : Fin 8 → Fin 14
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 8
  | ⟨6, _⟩ => match ord with | 0 => 10 | 1 => 11 | 2 => 11
  | ⟨7, _⟩ => match ord with | 0 => 11 | 1 => 10 | 2 => 9

def canonOp : Fin 8 → GateOp
  | ⟨0, _⟩ => GateOp.or
  | ⟨1, _⟩ => GateOp.or
  | ⟨2, _⟩ => GateOp.or
  | ⟨3, _⟩ => GateOp.and
  | ⟨4, _⟩ => GateOp.and
  | ⟨5, _⟩ => GateOp.and
  | ⟨6, _⟩ => GateOp.or
  | ⟨7, _⟩ => GateOp.or

def sideA : Finset (Fin 6) := {1, 2, 3}
def sideB : Finset (Fin 6) := {0, 4, 5}

def star : Fin 6 → Finset (Fin 6)
  | ⟨1, _⟩ => {0, 4}
  | ⟨2, _⟩ => {4, 5}
  | ⟨3, _⟩ => {0, 5}
  | _ => ∅

def starFun (v : Fin 6) (x : Fin 6 → Bool) : Bool :=
  decide (∃ b ∈ star v, x b = true)

lemma star_common : ∀ v1 ∈ sideA, ∀ v2 ∈ sideA, v1 ≠ v2 →
    ∃ c ∈ star v1, c ∈ star v2 ∧ c ∈ sideB := by decide

lemma star_sub_sideB : ∀ v ∈ sideA, star v ⊆ sideB := by decide

lemma star_union_ge2 : ∀ S : Finset (Fin 6), S ⊆ sideA → 2 ≤ S.card →
    ∀ b ∈ sideB, ∃ v ∈ S, b ∈ star v := by decide

lemma star_bad : ∀ v ∈ sideA,
    ∃ b0 ∈ sideB, b0 ∉ star v ∧ ∀ b ∈ sideB, b ∈ star v ∨ b = b0 := by decide

lemma sideA_union_sideB : ∀ i : Fin 6, i ∈ sideA ∨ i ∈ sideB := by decide
lemma sideA_sideB_disj : ∀ i : Fin 6, i ∈ sideA → i ∈ sideB → False := by decide

lemma c6_good_edges : ∀ v ∈ sideA, ∀ b ∈ star v, c6Fun (setInput {v, b}) = true := by decide
lemma c6_good_nonedges : ∀ v ∈ sideA, ∀ b ∈ sideB, b ∉ star v → c6Fun (setInput {v, b}) = false := by decide
lemma c6_good_sideB : c6Fun (setInput sideB) = false := by decide

lemma starFun_sep_12 : starFun 1 (setInput {0}) = true ∧ starFun 2 (setInput {0}) = false := by decide
lemma starFun_sep_13 : starFun 1 (setInput {5}) = false ∧ starFun 3 (setInput {5}) = true := by decide
lemma starFun_sep_23 : starFun 2 (setInput {4}) = true ∧ starFun 3 (setInput {4}) = false := by decide

lemma starFun_not_input : ∀ v ∈ sideA, ∀ i : Fin 6, ∃ x : Fin 6 → Bool, starFun v x ≠ x i := by decide

def botFunc : Fin 6 → (Fin 3 → Bool) → Bool
  | ⟨0, _⟩, x => x 0
  | ⟨1, _⟩, x => x 1
  | ⟨2, _⟩, x => x 2
  | ⟨3, _⟩, x => x 0 || x 1
  | ⟨4, _⟩, x => x 1 || x 2
  | ⟨5, _⟩, x => x 0 || x 2

def mk3 (b0 b1 b2 : Bool) : Fin 3 → Bool
  | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2

def botGateCheck : Bool :=
  (List.finRange 3).all fun t =>
    [false, true].all fun isOr =>
      (List.finRange 6).all fun i =>
        (List.finRange 6).all fun j =>
          if i.val == t.val + 3 || j.val == t.val + 3 || i == j then true
          else if !([false, true].all fun b0 => [false, true].all fun b1 => [false, true].all fun b2 =>
              (if isOr then botFunc i (mk3 b0 b1 b2) || botFunc j (mk3 b0 b1 b2)
               else botFunc i (mk3 b0 b1 b2) && botFunc j (mk3 b0 b1 b2)) ==
                botFunc ⟨t.val + 3, by have := t.isLt; omega⟩ (mk3 b0 b1 b2)) then true
          else isOr &&
            ((t.val == 0 && ((i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0))) ||
             ((t.val == 1 && ((i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1))) ||
              (t.val == 2 && ((i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0)))))

lemma botGateCheck_true : botGateCheck = true := by decide

lemma bot_gate_forced :
    ∀ (t : Fin 3) (isOr : Bool) (i j : Fin 6),
      i.val ≠ t.val + 3 → j.val ≠ t.val + 3 → i ≠ j →
      (∀ b0 b1 b2 : Bool,
        (if isOr then botFunc i (mk3 b0 b1 b2) || botFunc j (mk3 b0 b1 b2)
         else botFunc i (mk3 b0 b1 b2) && botFunc j (mk3 b0 b1 b2)) =
          botFunc ⟨t.val + 3, by omega⟩ (mk3 b0 b1 b2)) →
      isOr = true ∧
      ((t.val = 0 ∧ ((i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0))) ∨
       (t.val = 1 ∧ ((i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1))) ∨
       (t.val = 2 ∧ ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0)))) := by
  intro t isOr i j h1 h2 h3 hfeq
  have h := List.all_eq_true.mp botGateCheck_true t (List.mem_finRange t)
  have h := List.all_eq_true.mp h isOr (by cases isOr <;> simp)
  have h := List.all_eq_true.mp h i (List.mem_finRange i)
  have h := List.all_eq_true.mp h j (List.mem_finRange j)
  have hc1 : (i.val == t.val + 3 || j.val == t.val + 3 || i == j) = false := by
    rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hc2 : ([false, true].all fun b0 => [false, true].all fun b1 => [false, true].all fun b2 =>
      (if isOr then botFunc i (mk3 b0 b1 b2) || botFunc j (mk3 b0 b1 b2)
       else botFunc i (mk3 b0 b1 b2) && botFunc j (mk3 b0 b1 b2)) ==
        botFunc ⟨t.val + 3, by have := t.isLt; omega⟩ (mk3 b0 b1 b2)) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, hfeq, beq_self_eq_true]
  rw [hc1, hc2] at h
  simp only [Bool.false_eq_true, Bool.not_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h

lemma vl_mono {ms : List Gate} (hcl : CleanL 6 ms)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : Fin 6 → Bool} (hxy : ∀ i, x i = true → y i = true) :
    ∀ w : ℕ, vl ms x w = true → vl ms y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hxw
    by_cases hw6 : w < 6
    · rw [vl_input ms x w hw6] at hxw
      rw [vl_input ms y w hw6]
      exact hxy ⟨w, hw6⟩ hxw
    · let p := w - 6
      have hwp : w = 6 + p := by dsimp [p]; omega
      rw [hwp] at hxw ⊢
      cases hp : ms[p]? with
      | none =>
        have hge : ms.length ≤ p := List.getElem?_eq_none_iff.mp hp
        rw [vl_beyond ms x (6 + p) (by omega)] at hxw
        exact Bool.noConfusion hxw
      | some g =>
        rw [vl_gate ms hcl x p g hp] at hxw
        rw [vl_gate ms hcl y p g hp]
        have hgm : g ∈ ms := List.mem_iff_getElem?.mpr ⟨p, hp⟩
        rcases hcl p g hp with ⟨hop, _⟩ | ⟨hop, a, b, ha, hb, hin⟩
        · exfalso; rcases hmono g hgm with h1 | h1 <;> rw [hop] at h1 <;> cases h1
        · rw [hin] at hxw ⊢
          rcases hop with hop | hop
          · rw [hop] at hxw ⊢
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hxw ⊢
            exact ⟨ih a (by omega) hxw.1, ih b (by omega) hxw.2⟩
          · rw [hop] at hxw ⊢
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true] at hxw ⊢
            rcases hxw with h1 | h2
            · exact Or.inl (ih a (by omega) h1)
            · exact Or.inr (ih b (by omega) h2)

lemma gate_inputs_pair {ms : List Gate} {outN : ℕ}
    (hleast : Least 6 c6Fun ms outN)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : Fin (6 + ms.length)) (hw : 6 ≤ w.val) :
    ∃ (g : Gate) (a b : Fin (6 + ms.length)),
      ms[w.val - 6]? = some g ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs = [a.val, b.val] ∧
      a < w ∧ b < w ∧ a ≠ b ∧
      readEdge ms a w ∧ readEdge ms b w ∧
      (∀ u, readEdge ms u w ↔ u = a ∨ u = b) ∧
      (∀ x : Fin 6 → Bool, vl ms x w.val = g.op.eval [vl ms x a.val, vl ms x b.val]) := by
  let p := w.val - 6
  have hp : p < ms.length := by have := w.isLt; dsimp [p]; omega
  have hwp : w.val = 6 + p := by dsimp [p]; omega
  let g := ms[p]'hp
  have hgp : ms[p]? = some g := List.getElem?_eq_getElem hp
  have hgm : g ∈ ms := List.mem_iff_getElem?.mpr ⟨p, hgp⟩
  rcases hleast.hcl p g hgp with ⟨hop, _⟩ | ⟨hop, aN, bN, haN, hbN, hin⟩
  · exfalso; rcases hmono g hgm with h1 | h1 <;> rw [hop] at h1 <;> cases h1
  · have hne : aN ≠ bN := CircuitProof.RunAsm.pq2f_nodup hleast c6_nonconstant hgp hop hin
    let a : Fin (6 + ms.length) := ⟨aN, by omega⟩
    let b : Fin (6 + ms.length) := ⟨bN, by omega⟩
    refine ⟨g, a, b, hgp, hop, hin, ?_, ?_, fun h => hne (congrArg Fin.val h),
      ⟨p, g, hgp, hwp, by simp [hin, a]⟩, ⟨p, g, hgp, hwp, by simp [hin, b]⟩, ?_, ?_⟩
    · change aN < w.val; omega
    · change bN < w.val; omega
    · intro u
      constructor
      · rintro ⟨q, g', hqg, hwq, hu⟩
        have hqp : q = p := by omega
        subst hqp
        rw [hgp] at hqg
        have hgeq := Option.some.inj hqg
        subst hgeq
        rw [hin] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with h1 | h2
        · left; exact Fin.ext h1
        · right; exact Fin.ext h2
      · rintro (rfl | rfl)
        · exact ⟨p, g, hgp, hwp, by simp [hin, a]⟩
        · exact ⟨p, g, hgp, hwp, by simp [hin, b]⟩
    · intro x
      rw [hwp, vl_gate ms hleast.hcl x p g hgp, hin]
      rfl

noncomputable def topVars (ms : List Gate) (w : Fin (6 + ms.length)) : Finset (Fin 6) := by
  classical
  exact sideA.filter fun v => ReflTransGen (readEdge ms) (inputWire ms v) w

noncomputable def topAnc (ms : List Gate) (w : Fin (6 + ms.length)) : Finset (Fin (6 + ms.length)) := by
  classical
  exact Finset.univ.filter fun z => 6 ≤ z.val ∧ (topVars ms z).Nonempty ∧ ReflTransGen (readEdge ms) z w

lemma mem_topVars {ms : List Gate} {w : Fin (6 + ms.length)} {v : Fin 6} :
    v ∈ topVars ms w ↔ v ∈ sideA ∧ ReflTransGen (readEdge ms) (inputWire ms v) w := by
  classical
  simp [topVars]

lemma mem_topAnc {ms : List Gate} {w z : Fin (6 + ms.length)} :
    z ∈ topAnc ms w ↔ 6 ≤ z.val ∧ (topVars ms z).Nonempty ∧ ReflTransGen (readEdge ms) z w := by
  classical
  simp [topAnc]

lemma top_no_branch {ms : List Gate} (hSideA : SideNoTopBranch ms sideA)
    {z : Fin (6 + ms.length)} (hz : (topVars ms z).Nonempty) :
    ¬ FirstBranchRoute.Branches (readEdge ms) z := by
  intro hbr
  obtain ⟨v, hv⟩ := hz
  obtain ⟨hvA, hpath⟩ := mem_topVars.mp hv
  exact hSideA z hbr v hvA hpath

lemma readEdge_le_of_path {ms : List Gate} (hcl : CleanL 6 ms)
    {a b : Fin (6 + ms.length)} (p : ReflTransGen (readEdge ms) a b) : a.val ≤ b.val := by
  induction p with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (read_order hcl edge))

lemma top_children_disjoint {ms : List Gate} (hcl : CleanL 6 ms)
    (hSideA : SideNoTopBranch ms sideA)
    {w a b : Fin (6 + ms.length)} (hab : a ≠ b)
    (hre_a : readEdge ms a w) (hre_b : readEdge ms b w)
    (z : Fin (6 + ms.length)) (hz : (topVars ms z).Nonempty)
    (pa : ReflTransGen (readEdge ms) z a) (pb : ReflTransGen (readEdge ms) z b) : False := by
  revert hz pa pb
  induction z using (measure (fun q : Fin (6 + ms.length) => (6 + ms.length) - q.val)).wf.induction with
  | h z ih =>
    intro hz pa pb
    have hnb := top_no_branch hSideA hz
    by_cases hza : z = a
    · subst hza
      rcases pb.cases_head with rfl | ⟨u, hzu, hub⟩
      · exact hab rfl
      · have hle : u.val ≤ b.val := readEdge_le_of_path hcl hub
        have hlt : b.val < w.val := read_order hcl hre_b
        have huw : u ≠ w := fun heq => by rw [heq] at hle; omega
        exact hnb ⟨u, w, hzu, hre_a, huw⟩
    · by_cases hzb : z = b
      · subst hzb
        rcases pa.cases_head with rfl | ⟨u, hzu, hua⟩
        · exact hza rfl
        · have hle : u.val ≤ a.val := readEdge_le_of_path hcl hua
          have hlt : a.val < w.val := read_order hcl hre_a
          have huw : u ≠ w := fun heq => by rw [heq] at hle; omega
          exact hnb ⟨u, w, hzu, hre_b, huw⟩
      · rcases pa.cases_head with rfl | ⟨u1, hzu1, hu1a⟩
        · exact hza rfl
        · rcases pb.cases_head with rfl | ⟨u2, hzu2, hu2b⟩
          · exact hzb rfl
          · by_cases hu12 : u1 = u2
            · subst hu12
              have htop1 : (topVars ms u1).Nonempty := by
                obtain ⟨v, hv⟩ := hz
                obtain ⟨hvA, hvp⟩ := mem_topVars.mp hv
                exact ⟨v, mem_topVars.mpr ⟨hvA, hvp.tail hzu1⟩⟩
              have hord := read_order hcl hzu1
              have hdec : (6 + ms.length) - u1.val < (6 + ms.length) - z.val := by
                have := u1.isLt; omega
              exact ih u1 hdec htop1 hu1a hu2b
            · exact hnb ⟨u1, u2, hzu1, hzu2, hu12⟩

lemma topVars_gate {ms : List Gate} (hcl : CleanL 6 ms) (hSideA : SideNoTopBranch ms sideA)
    {w a b : Fin (6 + ms.length)} (hw : 6 ≤ w.val) (hab : a ≠ b)
    (hre_a : readEdge ms a w) (hre_b : readEdge ms b w)
    (hre_iff : ∀ u, readEdge ms u w ↔ u = a ∨ u = b) :
    topVars ms w = topVars ms a ∪ topVars ms b ∧ Disjoint (topVars ms a) (topVars ms b) := by
  constructor
  · ext v
    simp only [Finset.mem_union, mem_topVars]
    constructor
    · rintro ⟨hvA, hpath⟩
      rcases hpath.cases_tail with hrefl | ⟨u, hvu, huw⟩
      · exfalso; have hlt : (inputWire ms v).val < 6 := v.isLt; rw [← hrefl] at hlt; omega
      · rcases (hre_iff u).mp huw with rfl | rfl
        · left; exact ⟨hvA, hvu⟩
        · right; exact ⟨hvA, hvu⟩
    · rintro (⟨hvA, hpa⟩ | ⟨hvA, hpb⟩)
      · exact ⟨hvA, hpa.tail hre_a⟩
      · exact ⟨hvA, hpb.tail hre_b⟩
  · rw [Finset.disjoint_left]
    intro v hva hvb
    obtain ⟨hvA, hpa⟩ := mem_topVars.mp hva
    obtain ⟨_, hpb⟩ := mem_topVars.mp hvb
    have htop_v : (topVars ms (inputWire ms v)).Nonempty :=
      ⟨v, mem_topVars.mpr ⟨hvA, ReflTransGen.refl⟩⟩
    exact top_children_disjoint hcl hSideA hab hre_a hre_b (inputWire ms v) htop_v hpa hpb

lemma topAnc_gate {ms : List Gate} (hcl : CleanL 6 ms) (hSideA : SideNoTopBranch ms sideA)
    {w a b : Fin (6 + ms.length)} (hw : 6 ≤ w.val) (hab : a ≠ b)
    (hre_a : readEdge ms a w) (hre_b : readEdge ms b w)
    (hre_iff : ∀ u, readEdge ms u w ↔ u = a ∨ u = b)
    (htop : (topVars ms w).Nonempty) :
    (topAnc ms w).card = 1 + (topAnc ms a).card + (topAnc ms b).card := by
  have heq : topAnc ms w = insert w (topAnc ms a ∪ topAnc ms b) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union, mem_topAnc]
    constructor
    · rintro ⟨hz6, hztop, hpath⟩
      rcases hpath.cases_tail with rfl | ⟨u, hzu, huw⟩
      · left; rfl
      · right
        rcases (hre_iff u).mp huw with rfl | rfl
        · left; exact ⟨hz6, hztop, hzu⟩
        · right; exact ⟨hz6, hztop, hzu⟩
    · rintro (rfl | ⟨hz6, hztop, hpa⟩ | ⟨hz6, hztop, hpb⟩)
      · exact ⟨hw, htop, ReflTransGen.refl⟩
      · exact ⟨hz6, hztop, hpa.tail hre_a⟩
      · exact ⟨hz6, hztop, hpb.tail hre_b⟩
  have hw_not_mem : w ∉ topAnc ms a ∪ topAnc ms b := by
    intro hmem
    rcases Finset.mem_union.mp hmem with ha | hb
    · have hle := readEdge_le_of_path hcl (mem_topAnc.mp ha).2.2
      have hlt := read_order hcl hre_a
      omega
    · have hle := readEdge_le_of_path hcl (mem_topAnc.mp hb).2.2
      have hlt := read_order hcl hre_b
      omega
  have hdisj : Disjoint (topAnc ms a) (topAnc ms b) := by
    rw [Finset.disjoint_left]
    intro z hza hzb
    exact top_children_disjoint hcl hSideA hab hre_a hre_b z
      (mem_topAnc.mp hza).2.1 (mem_topAnc.mp hza).2.2 (mem_topAnc.mp hzb).2.2
  rw [heq, Finset.card_insert_of_notMem hw_not_mem, Finset.card_union_of_disjoint hdisj]
  omega

lemma vl_indep_outside_topVars {ms : List Gate} (hcl : CleanL 6 ms)
    (w : Fin (6 + ms.length)) (x y : Fin 6 → Bool)
    (hagree : ∀ i : Fin 6, i ∈ sideB ∨ i ∈ topVars ms w → x i = y i) :
    vl ms x w.val = vl ms y w.val := by
  apply agree_on_input_ancestors hcl x y w
  intro i hanc
  apply hagree i
  rcases sideA_union_sideB i with hiA | hiB
  · exact Or.inr (mem_topVars.mpr ⟨hiA, hanc⟩)
  · exact Or.inl hiB

structure Good (ms : List Gate) (S : Finset (Fin 6)) (w : Fin (6 + ms.length)) : Prop where
  sub : S ⊆ sideA
  nonempty : S.Nonempty
  vars : topVars ms w = S
  edges : ∀ v ∈ S, ∀ b ∈ star v, vl ms (setInput {v, b}) w.val = true
  nonedges : ∀ v ∈ S, ∀ b ∈ sideB, b ∉ star v → vl ms (setInput {v, b}) w.val = false
  botZero : vl ms (setInput sideB) w.val = false

lemma good_not_input {ms : List Gate} (hcl : CleanL 6 ms) {S : Finset (Fin 6)}
    {w : Fin (6 + ms.length)} (hg : Good ms S w) : 6 ≤ w.val := by
  by_contra hlt6
  have hw6 : w.val < 6 := by omega
  let i : Fin 6 := ⟨w.val, hw6⟩
  have htv : ∀ v : Fin 6, v ∈ topVars ms w ↔ v ∈ sideA ∧ v = i := by
    intro v; rw [mem_topVars]; constructor
    · rintro ⟨hvA, hpath⟩
      have hle := readEdge_le_of_path hcl hpath
      rcases hpath.cases_tail with hrefl | ⟨u, _, huw⟩
      · exact ⟨hvA, Fin.ext (congrArg Fin.val hrefl).symm⟩
      · exfalso; obtain ⟨p, g, _, hwp, _⟩ := huw; omega
    · rintro ⟨hvA, rfl⟩
      exact ⟨hvA, by have : inputWire ms i = w := Fin.ext rfl; rw [this]⟩
  obtain ⟨v, hvS⟩ := hg.nonempty
  have hv_eq : v = i := ((htv v).mp (hg.vars.symm ▸ hvS)).2
  have hvA : v ∈ sideA := hg.sub hvS
  obtain ⟨b0, hb0B, hb0_ns, _⟩ := star_bad v hvA
  have hne := hg.nonedges v hvS b0 hb0B hb0_ns
  rw [vl_input ms (setInput {v, b0}) w.val hw6] at hne
  have hi_eq : (⟨w.val, hw6⟩ : Fin 6) = v := hv_eq.symm
  rw [hi_eq] at hne
  simp [setInput] at hne

lemma vl_setInput_mono {ms : List Gate} (hcl : CleanL 6 ms)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    {A B : Finset (Fin 6)} (hAB : A ⊆ B) (w : ℕ)
    (hA : vl ms (setInput A) w = true) : vl ms (setInput B) w = true :=
  vl_mono hcl hmono (fun i hi => by
    simp only [setInput, decide_eq_true_eq] at hi ⊢
    exact hAB hi) w hA

lemma sep_and_both_nonempty_false {ms : List Gate} (hcl : CleanL 6 ms)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    {S : Finset (Fin 6)} {w a b : Fin (6 + ms.length)}
    (hg : Good ms S w)
    (hdisj : Disjoint (topVars ms a) (topVars ms b))
    (hun : topVars ms a ∪ topVars ms b = S)
    (hval : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x a.val && vl ms x b.val))
    (hna : (topVars ms a).Nonempty) (hnb : (topVars ms b).Nonempty) : False := by
  obtain ⟨v1, hv1⟩ := hna
  obtain ⟨v2, hv2⟩ := hnb
  have hv1S : v1 ∈ S := hun ▸ Finset.mem_union_left _ hv1
  have hv2S : v2 ∈ S := hun ▸ Finset.mem_union_right _ hv2
  have hv12 : v1 ≠ v2 := fun heq => Finset.disjoint_left.mp hdisj hv1 (heq ▸ hv2)
  obtain ⟨c, hc1, hc2, hcB⟩ := star_common v1 (hg.sub hv1S) v2 (hg.sub hv2S) hv12
  have ha_sideB : vl ms (setInput sideB) a.val = true := by
    have he2 := hg.edges v2 hv2S c hc2
    rw [hval, Bool.and_eq_true] at he2
    have h1 : vl ms (setInput (insert v2 sideB)) a.val = true :=
      vl_setInput_mono hcl hmono (fun i hi => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
        rcases hi with rfl | rfl
        · left; rfl
        · right; exact hcB) a.val he2.1
    rw [← vl_indep_outside_topVars hcl a (setInput sideB) (setInput (insert v2 sideB)) (fun i hi => by
      have hiv2 : i ≠ v2 := by
        rintro rfl
        rcases hi with hiB | hiA
        · exact sideA_sideB_disj _ (hg.sub hv2S) hiB
        · exact Finset.disjoint_left.mp hdisj hiA hv2
      simp [setInput, hiv2])] at h1
    exact h1
  have hb_sideB : vl ms (setInput sideB) b.val = true := by
    have he1 := hg.edges v1 hv1S c hc1
    rw [hval, Bool.and_eq_true] at he1
    have h1 : vl ms (setInput (insert v1 sideB)) b.val = true :=
      vl_setInput_mono hcl hmono (fun i hi => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
        rcases hi with rfl | rfl
        · left; rfl
        · right; exact hcB) b.val he1.2
    rw [← vl_indep_outside_topVars hcl b (setInput sideB) (setInput (insert v1 sideB)) (fun i hi => by
      have hiv1 : i ≠ v1 := by
        rintro rfl
        rcases hi with hiB | hiA
        · exact sideA_sideB_disj _ (hg.sub hv1S) hiB
        · exact Finset.disjoint_left.mp hdisj hv1 hiA
      simp [setInput, hiv1])] at h1
    exact h1
  have hbot := hg.botZero
  rw [hval, ha_sideB, hb_sideB] at hbot
  exact Bool.noConfusion hbot

lemma bot_wire_eq_starFun {ms : List Gate} (hcl : CleanL 6 ms)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    {a : Fin (6 + ms.length)} (haBot : topVars ms a = ∅)
    {v : Fin 6} (hvA : v ∈ sideA)
    (htrue : ∀ b ∈ star v, vl ms (setInput {b}) a.val = true)
    {b0 : Fin 6} (hb0B : b0 ∈ sideB) (hb0_ns : b0 ∉ star v)
    (hbad : ∀ b ∈ sideB, b ∈ star v ∨ b = b0)
    (hfalse : vl ms (setInput {b0}) a.val = false) :
    6 ≤ a.val ∧ ∀ x : Fin 6 → Bool, vl ms x a.val = starFun v x := by
  have hfun : ∀ x : Fin 6 → Bool, vl ms x a.val = starFun v x := by
    intro x
    by_cases hex : ∃ b ∈ star v, x b = true
    · obtain ⟨b, hbs, hxb⟩ := hex
      have hst : starFun v x = true := by simp [starFun]; exact ⟨b, hbs, hxb⟩
      rw [hst]
      exact vl_mono hcl hmono (fun i hi => by
        simp only [setInput, Finset.mem_singleton, decide_eq_true_eq] at hi
        subst hi; exact hxb) a.val (htrue b hbs)
    · push_neg at hex
      have hst : starFun v x = false := by
        simp only [starFun, decide_eq_false_iff_not, not_exists, not_and]
        intro b hbs hxb; exact hex b hbs hxb
      rw [hst]
      cases hva : vl ms x a.val with
      | false => rfl
      | true =>
        exfalso
        let x' : Fin 6 → Bool := fun i => decide (i ∈ sideB ∧ x i = true)
        have hx' : vl ms x' a.val = true := by
          rw [← vl_indep_outside_topVars hcl a x x' (fun i hi => by
            rcases hi with hiB | hiT
            · simp [x', hiB]
            · rw [haBot] at hiT; exact (Finset.notMem_empty _ hiT).elim)]
          exact hva
        have hle_b0 : vl ms (setInput {b0}) a.val = true :=
          vl_mono hcl hmono (fun i hi => by
            simp only [x', decide_eq_true_eq] at hi
            simp only [setInput, Finset.mem_singleton, decide_eq_true_eq]
            rcases hbad i hi.1 with his | rfl
            · exact (hex i his hi.2).elim
            · rfl) a.val hx'
        rw [hfalse] at hle_b0; exact Bool.noConfusion hle_b0
  refine ⟨?_, hfun⟩
  by_contra hlt6
  have ha6 : a.val < 6 := by omega
  obtain ⟨x, hx⟩ := starFun_not_input v hvA ⟨a.val, ha6⟩
  have h1 := hfun x
  rw [vl_input ms x a.val ha6] at h1
  exact hx h1.symm

lemma sep_struct {ms : List Gate} {outN : ℕ}
    (hleast : Least 6 c6Fun ms outN)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hSideA : SideNoTopBranch ms sideA) :
    ∀ (w : Fin (6 + ms.length)) (S : Finset (Fin 6)), Good ms S w →
      2 * S.card - 1 ≤ (topAnc ms w).card ∧
      ∀ v ∈ S, ∃ u : Fin (6 + ms.length), 6 ≤ u.val ∧ topVars ms u = ∅ ∧
        ∀ x : Fin 6 → Bool, vl ms x u.val = starFun v x := by
  intro w
  induction w using (measure (fun q : Fin (6 + ms.length) => q.val)).wf.induction with
  | h w ih =>
    intro S hg
    have hw6 : 6 ≤ w.val := good_not_input hleast.hcl hg
    obtain ⟨g, a, b, hgp, hg_op, hg_in, haw, hbw, hab, hre_a, hre_b, hre_iff, hval⟩ :=
      gate_inputs_pair hleast hmono w hw6
    obtain ⟨htv_eq, htv_disj⟩ := topVars_gate hleast.hcl hSideA hw6 hab hre_a hre_b hre_iff
    have hun : topVars ms a ∪ topVars ms b = S := htv_eq.symm.trans hg.vars
    have htop_w : (topVars ms w).Nonempty := hg.vars.symm ▸ hg.nonempty
    have hanc_eq := topAnc_gate hleast.hcl hSideA hw6 hab hre_a hre_b hre_iff htop_w
    rcases hg_op with hop | hop
    · have hval_and : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x a.val && vl ms x b.val) := by
        intro x; rw [hval x, hop]; simp [GateOp.eval]
      have handle_bot : ∀ (u1 u2 : Fin (6 + ms.length)),
          u2 < w → topVars ms u1 = ∅ → topVars ms u2 = S →
          (∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x u1.val && vl ms x u2.val)) →
          (topAnc ms w).card = 1 + (topAnc ms u1).card + (topAnc ms u2).card →
          2 * S.card - 1 ≤ (topAnc ms w).card ∧
          ∀ v ∈ S, ∃ u : Fin (6 + ms.length), 6 ≤ u.val ∧ topVars ms u = ∅ ∧
            ∀ x : Fin 6 → Bool, vl ms x u.val = starFun v x := by
        intro u1 u2 hu2w hu1Bot hu2S hval' hanc'
        have hu1_star : ∀ v ∈ S, ∀ c ∈ star v, vl ms (setInput {c}) u1.val = true := by
          intro v hvS c hcs
          have he := hg.edges v hvS c hcs
          rw [hval', Bool.and_eq_true] at he
          rw [← vl_indep_outside_topVars hleast.hcl u1 (setInput {c}) (setInput {v, c}) (fun i hi => by
            rcases hi with hiB | hiT
            · have hiv : i ≠ v := fun h => sideA_sideB_disj i (h ▸ hg.sub hvS) hiB
              simp [setInput, hiv]
            · rw [hu1Bot] at hiT; exact (Finset.notMem_empty _ hiT).elim)] at he
          exact he.1
        by_cases hS1 : S.card = 1
        · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hS1
          have hvA : v ∈ sideA := hg.sub (by simp)
          obtain ⟨b0, hb0B, hb0_ns, hb0_all⟩ := star_bad v hvA
          by_cases hu1_b0 : vl ms (setInput {b0}) u1.val = true
          · have hu2_good : Good ms {v} u2 := by
              refine ⟨hg.sub, hg.nonempty, hu2S, ?_, ?_, ?_⟩
              · intro v' hv' c hc; have he := hg.edges v' hv' c hc; rw [hval', Bool.and_eq_true] at he; exact he.2
              · intro v' hv' c hcB hcns
                have hv'eq : v' = v := Finset.mem_singleton.mp hv'
                subst v'
                have hcb0 : c = b0 := (hb0_all c hcB).resolve_left hcns
                subst c
                have h1 : vl ms (setInput {v, b0}) u1.val = true :=
                  vl_setInput_mono hleast.hcl hmono (Finset.singleton_subset_iff.mpr (by simp)) u1.val hu1_b0
                have hne := hg.nonedges v (by simp) b0 hb0B hb0_ns
                rw [hval', h1, Bool.true_and] at hne; exact hne
              · have h1 : vl ms (setInput sideB) u1.val = true :=
                  vl_setInput_mono hleast.hcl hmono (Finset.singleton_subset_iff.mpr hb0B) u1.val hu1_b0
                have hbot := hg.botZero
                rw [hval', h1, Bool.true_and] at hbot; exact hbot
            obtain ⟨hc2, hu2_stars⟩ := ih u2 hu2w {v} hu2_good
            exact ⟨by omega, hu2_stars⟩
          · have hu1_false : vl ms (setInput {b0}) u1.val = false := Bool.eq_false_iff.mpr hu1_b0
            obtain ⟨hu1_6, hu1_fun⟩ := bot_wire_eq_starFun hleast.hcl hmono hu1Bot hvA
              (hu1_star v (by simp)) hb0B hb0_ns hb0_all hu1_false
            refine ⟨by simp only [Finset.card_singleton]; omega, ?_⟩
            intro v' hv'
            have hv'eq : v' = v := Finset.mem_singleton.mp hv'
            subst hv'eq
            exact ⟨u1, hu1_6, hu1Bot, hu1_fun⟩
        · have hS2 : 2 ≤ S.card := by have := hg.nonempty.card_pos; omega
          have hu1_allB : ∀ c ∈ sideB, vl ms (setInput {c}) u1.val = true := by
            intro c hcB
            obtain ⟨v, hvS, hcs⟩ := star_union_ge2 S hg.sub hS2 c hcB
            exact hu1_star v hvS c hcs
          have hu2_good : Good ms S u2 := by
            refine ⟨hg.sub, hg.nonempty, hu2S, ?_, ?_, ?_⟩
            · intro v hvS c hcs; have he := hg.edges v hvS c hcs; rw [hval', Bool.and_eq_true] at he; exact he.2
            · intro v hvS c hcB hcns
              have h1 : vl ms (setInput {v, c}) u1.val = true :=
                vl_setInput_mono hleast.hcl hmono (by simp) u1.val (hu1_allB c hcB)
              have hne := hg.nonedges v hvS c hcB hcns
              rw [hval', h1, Bool.true_and] at hne; exact hne
            · have h1 : vl ms (setInput sideB) u1.val = true :=
                vl_setInput_mono hleast.hcl hmono (by decide) u1.val (hu1_allB 0 (by decide))
              have hbot := hg.botZero
              rw [hval', h1, Bool.true_and] at hbot; exact hbot
          obtain ⟨hc2, hu2_stars⟩ := ih u2 hu2w S hu2_good
          exact ⟨by omega, hu2_stars⟩
      by_cases haE : topVars ms a = ∅
      · exact handle_bot a b hbw haE (by rw [haE, Finset.empty_union] at hun; exact hun) hval_and hanc_eq
      · by_cases hbE : topVars ms b = ∅
        · exact handle_bot b a haw hbE (by rw [hbE, Finset.union_empty] at hun; exact hun)
            (fun x => by rw [hval_and x, Bool.and_comm]) (by omega)
        · exfalso
          exact sep_and_both_nonempty_false hleast.hcl hmono hg htv_disj hun hval_and
            (Finset.nonempty_iff_ne_empty.mpr haE) (Finset.nonempty_iff_ne_empty.mpr hbE)
    · have hval_or : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x a.val || vl ms x b.val) := by
        intro x; rw [hval x, hop]; simp [GateOp.eval]
      have handle_or_bot : ∀ (u1 u2 : Fin (6 + ms.length)),
          u2 < w → topVars ms u1 = ∅ → topVars ms u2 = S →
          (∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x u1.val || vl ms x u2.val)) →
          (topAnc ms w).card = 1 + (topAnc ms u1).card + (topAnc ms u2).card →
          2 * S.card - 1 ≤ (topAnc ms w).card ∧
          ∀ v ∈ S, ∃ u : Fin (6 + ms.length), 6 ≤ u.val ∧ topVars ms u = ∅ ∧
            ∀ x : Fin 6 → Bool, vl ms x u.val = starFun v x := by
        intro u1 u2 hu2w hu1Bot hu2S hval' hanc'
        have hu1_zero : ∀ x : Fin 6 → Bool, vl ms x u1.val = false := by
          intro x
          have hbot := hg.botZero
          rw [hval', Bool.or_eq_false_iff] at hbot
          cases h1 : vl ms x u1.val with
          | false => rfl
          | true =>
            exfalso
            have h2 : vl ms (setInput sideB) u1.val = true := by
              have hx' : vl ms (fun i => decide (i ∈ sideB ∧ x i = true)) u1.val = true := by
                rw [← vl_indep_outside_topVars hleast.hcl u1 x _ (fun i hi => by
                  rcases hi with hiB | hiT
                  · simp [hiB]
                  · rw [hu1Bot] at hiT; exact (Finset.notMem_empty _ hiT).elim)]
                exact h1
              exact vl_mono hleast.hcl hmono (fun i hi => by
                simp only [decide_eq_true_eq] at hi
                simp [setInput, hi.1]) u1.val hx'
            rw [hbot.1] at h2; exact Bool.noConfusion h2
        have hu2_good : Good ms S u2 := by
          refine ⟨hg.sub, hg.nonempty, hu2S, ?_, ?_, ?_⟩
          · intro v hvS c hcs; have he := hg.edges v hvS c hcs; rw [hval', hu1_zero, Bool.false_or] at he; exact he
          · intro v hvS c hcB hcns; have hne := hg.nonedges v hvS c hcB hcns; rw [hval', hu1_zero, Bool.false_or] at hne; exact hne
          · have hbot := hg.botZero; rw [hval', hu1_zero, Bool.false_or] at hbot; exact hbot
        obtain ⟨hc2, hu2_stars⟩ := ih u2 hu2w S hu2_good
        exact ⟨by omega, hu2_stars⟩
      by_cases haE : topVars ms a = ∅
      · exact handle_or_bot a b hbw haE (by rw [haE, Finset.empty_union] at hun; exact hun) hval_or hanc_eq
      · by_cases hbE : topVars ms b = ∅
        · exact handle_or_bot b a haw hbE (by rw [hbE, Finset.union_empty] at hun; exact hun)
            (fun x => by rw [hval_or x, Bool.or_comm]) (by omega)
        · have hna : (topVars ms a).Nonempty := Finset.nonempty_iff_ne_empty.mpr haE
          have hnb : (topVars ms b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hbE
          have hsub_a : topVars ms a ⊆ sideA := (hun ▸ Finset.subset_union_left).trans hg.sub
          have hsub_b : topVars ms b ⊆ sideA := (hun ▸ Finset.subset_union_right).trans hg.sub
          have hbot_or := hg.botZero
          rw [hval_or, Bool.or_eq_false_iff] at hbot_or
          have hga : Good ms (topVars ms a) a := by
            refine ⟨hsub_a, hna, rfl, ?_, ?_, hbot_or.1⟩
            · intro v hva c hcs
              have hvS : v ∈ S := hun ▸ Finset.mem_union_left _ hva
              have he := hg.edges v hvS c hcs
              rw [hval_or, Bool.or_eq_true] at he
              have hb_f : vl ms (setInput {v, c}) b.val = false := by
                cases hbv : vl ms (setInput {v, c}) b.val with
                | false => rfl
                | true =>
                  exfalso
                  have h1 : vl ms (setInput {c}) b.val = true := by
                    rw [vl_indep_outside_topVars hleast.hcl b (setInput {c}) (setInput {v, c}) (fun i hi => by
                      have hiv : i ≠ v := by
                        rintro rfl
                        rcases hi with hiB | hiT
                        · exact sideA_sideB_disj _ (hsub_a hva) hiB
                        · exact Finset.disjoint_left.mp htv_disj hva hiT
                      simp [setInput, hiv])]
                    exact hbv
                  have hcB : c ∈ sideB := star_sub_sideB v (hsub_a hva) hcs
                  have h2 := vl_setInput_mono hleast.hcl hmono (Finset.singleton_subset_iff.mpr hcB) b.val h1
                  rw [hbot_or.2] at h2; exact Bool.noConfusion h2
              rcases he with h1 | h2
              · exact h1
              · rw [hb_f] at h2; exact Bool.noConfusion h2
            · intro v hva c hcB hcns
              have hvS : v ∈ S := hun ▸ Finset.mem_union_left _ hva
              have hne := hg.nonedges v hvS c hcB hcns
              rw [hval_or, Bool.or_eq_false_iff] at hne; exact hne.1
          have hgb : Good ms (topVars ms b) b := by
            refine ⟨hsub_b, hnb, rfl, ?_, ?_, hbot_or.2⟩
            · intro v hvb c hcs
              have hvS : v ∈ S := hun ▸ Finset.mem_union_right _ hvb
              have he := hg.edges v hvS c hcs
              rw [hval_or, Bool.or_eq_true] at he
              have ha_f : vl ms (setInput {v, c}) a.val = false := by
                cases hav : vl ms (setInput {v, c}) a.val with
                | false => rfl
                | true =>
                  exfalso
                  have h1 : vl ms (setInput {c}) a.val = true := by
                    rw [vl_indep_outside_topVars hleast.hcl a (setInput {c}) (setInput {v, c}) (fun i hi => by
                      have hiv : i ≠ v := by
                        rintro rfl
                        rcases hi with hiB | hiT
                        · exact sideA_sideB_disj _ (hsub_b hvb) hiB
                        · exact Finset.disjoint_left.mp htv_disj hiT hvb
                      simp [setInput, hiv])]
                    exact hav
                  have hcB : c ∈ sideB := star_sub_sideB v (hsub_b hvb) hcs
                  have h2 := vl_setInput_mono hleast.hcl hmono (Finset.singleton_subset_iff.mpr hcB) a.val h1
                  rw [hbot_or.1] at h2; exact Bool.noConfusion h2
              rcases he with h1 | h2
              · rw [ha_f] at h1; exact Bool.noConfusion h1
              · exact h2
            · intro v hvb c hcB hcns
              have hvS : v ∈ S := hun ▸ Finset.mem_union_right _ hvb
              have hne := hg.nonedges v hvS c hcB hcns
              rw [hval_or, Bool.or_eq_false_iff] at hne; exact hne.2
          obtain ⟨hca, hsa⟩ := ih a haw (topVars ms a) hga
          obtain ⟨hcb, hsb⟩ := ih b hbw (topVars ms b) hgb
          have hcardS : S.card = (topVars ms a).card + (topVars ms b).card := by
            rw [← hun, Finset.card_union_of_disjoint htv_disj]
          have hposA := hna.card_pos
          have hposB := hnb.card_pos
          refine ⟨by omega, ?_⟩
          intro v hvS
          rw [← hun] at hvS
          rcases Finset.mem_union.mp hvS with hva | hvb
          · exact hsa v hva
          · exact hsb v hvb

lemma sep_tight_one {ms : List Gate} {outN : ℕ}
    (hleast : Least 6 c6Fun ms outN)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hSideA : SideNoTopBranch ms sideA)
    {w : Fin (6 + ms.length)} {v : Fin 6}
    (hg : Good ms {v} w) (htight : (topAnc ms w).card = 1) :
    ∃ (g : Gate) (u : Fin (6 + ms.length)),
      ms[w.val - 6]? = some g ∧ g.op = GateOp.and ∧
      6 ≤ u.val ∧ topVars ms u = ∅ ∧
      (∀ x : Fin 6 → Bool, vl ms x u.val = starFun v x) ∧
      (g.inputs = [v.val, u.val] ∨ g.inputs = [u.val, v.val]) := by
  have hw6 : 6 ≤ w.val := good_not_input hleast.hcl hg
  obtain ⟨g, a, b, hgp, hg_op, hg_in, haw, hbw, hab, hre_a, hre_b, hre_iff, hval⟩ :=
    gate_inputs_pair hleast hmono w hw6
  obtain ⟨htv_eq, htv_disj⟩ := topVars_gate hleast.hcl hSideA hw6 hab hre_a hre_b hre_iff
  have hun : topVars ms a ∪ topVars ms b = {v} := htv_eq.symm.trans hg.vars
  have hanc_eq := topAnc_gate hleast.hcl hSideA hw6 hab hre_a hre_b hre_iff (hg.vars.symm ▸ hg.nonempty)
  have hca0 : (topAnc ms a).card = 0 := by omega
  have hcb0 : (topAnc ms b).card = 0 := by omega
  have hvA : v ∈ sideA := hg.sub (by simp)
  have hnot_top_gate : ∀ z : Fin (6 + ms.length), (topAnc ms z).card = 0 → topVars ms z = {v} → z.val = v.val := by
    intro z hz0 hzv
    have hz_lt6 : z.val < 6 := by
      by_contra hge
      have hmem : z ∈ topAnc ms z := mem_topAnc.mpr ⟨by omega, hzv ▸ ⟨v, by simp⟩, ReflTransGen.refl⟩
      have hpos : 0 < (topAnc ms z).card := Finset.card_pos.mpr ⟨z, hmem⟩
      omega
    have hv_path : ReflTransGen (readEdge ms) (inputWire ms v) z :=
      (mem_topVars.mp (hzv.symm ▸ Finset.mem_singleton_self v)).2
    rcases hv_path.cases_tail with hrefl | ⟨u, _, huz⟩
    · exact congrArg Fin.val hrefl
    · exfalso; obtain ⟨p, _, _, hzp, _⟩ := huz; omega
  have handle_one : ∀ (u1 u2 : Fin (6 + ms.length)),
      topVars ms u1 = ∅ → topVars ms u2 = {v} → (topAnc ms u2).card = 0 →
      (g.inputs = [u1.val, u2.val] ∨ g.inputs = [u2.val, u1.val]) →
      (∀ x : Fin 6 → Bool, vl ms x w.val = g.op.eval [vl ms x u1.val, vl ms x u2.val]) →
      ∃ (g' : Gate) (u : Fin (6 + ms.length)),
        ms[w.val - 6]? = some g' ∧ g'.op = GateOp.and ∧
        6 ≤ u.val ∧ topVars ms u = ∅ ∧
        (∀ x : Fin 6 → Bool, vl ms x u.val = starFun v x) ∧
        (g'.inputs = [v.val, u.val] ∨ g'.inputs = [u.val, v.val]) := by
    intro u1 u2 hu1Bot hu2v hu2c0 hins hval'
    have hu2_eq : u2.val = v.val := hnot_top_gate u2 hu2c0 hu2v
    rcases hg_op with hop | hop
    · have hval_and : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x u1.val && vl ms x u2.val) := by
        intro x; rw [hval' x, hop]; simp [GateOp.eval]
      obtain ⟨b0, hb0B, hb0_ns, hb0_all⟩ := star_bad v hvA
      have hu1_star : ∀ c ∈ star v, vl ms (setInput {c}) u1.val = true := by
        intro c hcs
        have he := hg.edges v (by simp) c hcs
        rw [hval_and, Bool.and_eq_true] at he
        rw [← vl_indep_outside_topVars hleast.hcl u1 (setInput {c}) (setInput {v, c}) (fun i hi => by
          rcases hi with hiB | hiT
          · have hiv : i ≠ v := fun h => sideA_sideB_disj i (h ▸ hvA) hiB
            simp [setInput, hiv]
          · rw [hu1Bot] at hiT; exact (Finset.notMem_empty _ hiT).elim)] at he
        exact he.1
      have hu1_b0 : vl ms (setInput {b0}) u1.val = false := by
        cases h1 : vl ms (setInput {b0}) u1.val with
        | false => rfl
        | true =>
          exfalso
          have h1' : vl ms (setInput {v, b0}) u1.val = true :=
            vl_setInput_mono hleast.hcl hmono (by simp) u1.val h1
          have h2 : vl ms (setInput {v, b0}) u2.val = true := by
            rw [hu2_eq, vl_input ms _ v.val v.isLt]; simp [setInput]
          have hne := hg.nonedges v (by simp) b0 hb0B hb0_ns
          rw [hval_and, h1', h2] at hne; exact Bool.noConfusion hne
      obtain ⟨hu1_6, hu1_fun⟩ := bot_wire_eq_starFun hleast.hcl hmono hu1Bot hvA hu1_star hb0B hb0_ns hb0_all hu1_b0
      refine ⟨g, u1, hgp, hop, hu1_6, hu1Bot, hu1_fun, ?_⟩
      rcases hins with h1 | h2
      · right; rw [h1, hu2_eq]
      · left; rw [h2, hu2_eq]
    · exfalso
      have hval_or : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x u1.val || vl ms x u2.val) := by
        intro x; rw [hval' x, hop]; simp [GateOp.eval]
      obtain ⟨b0, hb0B, hb0_ns, _⟩ := star_bad v hvA
      have h2 : vl ms (setInput {v, b0}) u2.val = true := by
        rw [hu2_eq, vl_input ms _ v.val v.isLt]; simp [setInput]
      have hne := hg.nonedges v (by simp) b0 hb0B hb0_ns
      rw [hval_or, h2, Bool.or_true] at hne; exact Bool.noConfusion hne
  by_cases haE : topVars ms a = ∅
  · exact handle_one a b haE (by rw [haE, Finset.empty_union] at hun; exact hun) hcb0 (Or.inl hg_in) hval
  · by_cases hbE : topVars ms b = ∅
    · exact handle_one b a hbE (by rw [hbE, Finset.union_empty] at hun; exact hun) hca0 (Or.inr hg_in)
        (fun x => by rw [hval x]; rcases hg_op with hop | hop <;> simp [hop, GateOp.eval, Bool.and_comm, Bool.or_comm])
    · exfalso
      have h1 : 1 ≤ (topVars ms a).card := (Finset.nonempty_iff_ne_empty.mpr haE).card_pos
      have h2 : 1 ≤ (topVars ms b).card := (Finset.nonempty_iff_ne_empty.mpr hbE).card_pos
      have hsum : (topVars ms a).card + (topVars ms b).card = 1 := by
        rw [← Finset.card_union_of_disjoint htv_disj, hun, Finset.card_singleton]
      omega

lemma sep_tight_ge2 {ms : List Gate} {outN : ℕ}
    (hleast : Least 6 c6Fun ms outN)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hSideA : SideNoTopBranch ms sideA)
    {w : Fin (6 + ms.length)} {S : Finset (Fin 6)}
    (hg : Good ms S w) (hS2 : 2 ≤ S.card) (htight : (topAnc ms w).card = 2 * S.card - 1) :
    ∃ (g : Gate) (a b : Fin (6 + ms.length)),
      ms[w.val - 6]? = some g ∧ g.op = GateOp.or ∧ g.inputs = [a.val, b.val] ∧
      Good ms (topVars ms a) a ∧ Good ms (topVars ms b) b ∧
      Disjoint (topVars ms a) (topVars ms b) ∧ topVars ms a ∪ topVars ms b = S ∧
      (topAnc ms a).card = 2 * (topVars ms a).card - 1 ∧
      (topAnc ms b).card = 2 * (topVars ms b).card - 1 := by
  have hw6 : 6 ≤ w.val := good_not_input hleast.hcl hg
  obtain ⟨g, a, b, hgp, hg_op, hg_in, haw, hbw, hab, hre_a, hre_b, hre_iff, hval⟩ :=
    gate_inputs_pair hleast hmono w hw6
  obtain ⟨htv_eq, htv_disj⟩ := topVars_gate hleast.hcl hSideA hw6 hab hre_a hre_b hre_iff
  have hun : topVars ms a ∪ topVars ms b = S := htv_eq.symm.trans hg.vars
  have hanc_eq := topAnc_gate hleast.hcl hSideA hw6 hab hre_a hre_b hre_iff (hg.vars.symm ▸ hg.nonempty)
  rcases hg_op with hop | hop
  · exfalso
    have hval_and : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x a.val && vl ms x b.val) := by
      intro x; rw [hval x, hop]; simp [GateOp.eval]
    have kill_bot : ∀ (u1 u2 : Fin (6 + ms.length)),
        topVars ms u1 = ∅ → topVars ms u2 = S →
        (∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x u1.val && vl ms x u2.val)) →
        (topAnc ms w).card = 1 + (topAnc ms u1).card + (topAnc ms u2).card → False := by
      intro u1 u2 hu1Bot hu2S hval' hanc'
      have hu1_allB : ∀ c ∈ sideB, vl ms (setInput {c}) u1.val = true := by
        intro c hcB
        obtain ⟨v, hvS, hcs⟩ := star_union_ge2 S hg.sub hS2 c hcB
        have he := hg.edges v hvS c hcs
        rw [hval', Bool.and_eq_true] at he
        rw [← vl_indep_outside_topVars hleast.hcl u1 (setInput {c}) (setInput {v, c}) (fun i hi => by
          rcases hi with hiB | hiT
          · have hiv : i ≠ v := fun h => sideA_sideB_disj i (h ▸ hg.sub hvS) hiB
            simp [setInput, hiv]
          · rw [hu1Bot] at hiT; exact (Finset.notMem_empty _ hiT).elim)] at he
        exact he.1
      have hu2_good : Good ms S u2 := by
        refine ⟨hg.sub, hg.nonempty, hu2S, ?_, ?_, ?_⟩
        · intro v hvS c hcs; have he := hg.edges v hvS c hcs; rw [hval', Bool.and_eq_true] at he; exact he.2
        · intro v hvS c hcB hcns
          have h1 := vl_setInput_mono hleast.hcl hmono (by simp : {c} ⊆ ({v, c} : Finset (Fin 6))) u1.val (hu1_allB c hcB)
          have hne := hg.nonedges v hvS c hcB hcns; rw [hval', h1, Bool.true_and] at hne; exact hne
        · have h1 := vl_setInput_mono hleast.hcl hmono (by decide : {0} ⊆ sideB) u1.val (hu1_allB 0 (by decide))
          have hbot := hg.botZero; rw [hval', h1, Bool.true_and] at hbot; exact hbot
      have hge := (sep_struct hleast hmono hSideA u2 S hu2_good).1
      omega
    by_cases haE : topVars ms a = ∅
    · exact kill_bot a b haE (by rw [haE, Finset.empty_union] at hun; exact hun) hval_and hanc_eq
    · by_cases hbE : topVars ms b = ∅
      · exact kill_bot b a hbE (by rw [hbE, Finset.union_empty] at hun; exact hun)
          (fun x => by rw [hval_and x, Bool.and_comm]) (by omega)
      · exact sep_and_both_nonempty_false hleast.hcl hmono hg htv_disj hun hval_and
          (Finset.nonempty_iff_ne_empty.mpr haE) (Finset.nonempty_iff_ne_empty.mpr hbE)
  · have hval_or : ∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x a.val || vl ms x b.val) := by
      intro x; rw [hval x, hop]; simp [GateOp.eval]
    have kill_or_bot : ∀ (u1 u2 : Fin (6 + ms.length)),
        topVars ms u1 = ∅ → topVars ms u2 = S →
        (∀ x : Fin 6 → Bool, vl ms x w.val = (vl ms x u1.val || vl ms x u2.val)) →
        (topAnc ms w).card = 1 + (topAnc ms u1).card + (topAnc ms u2).card → False := by
      intro u1 u2 hu1Bot hu2S hval' hanc'
      have hu1_zero : ∀ x : Fin 6 → Bool, vl ms x u1.val = false := by
        intro x
        have hbot := hg.botZero; rw [hval', Bool.or_eq_false_iff] at hbot
        cases h1 : vl ms x u1.val with
        | false => rfl
        | true =>
          exfalso
          have hx' : vl ms (fun i => decide (i ∈ sideB ∧ x i = true)) u1.val = true := by
            rw [← vl_indep_outside_topVars hleast.hcl u1 x _ (fun i hi => by
              rcases hi with hiB | hiT
              · simp [hiB]
              · rw [hu1Bot] at hiT; exact (Finset.notMem_empty _ hiT).elim)]
            exact h1
          have h2 : vl ms (setInput sideB) u1.val = true :=
            vl_mono hleast.hcl hmono (fun i hi => by
              simp only [decide_eq_true_eq] at hi; simp [setInput, hi.1]) u1.val hx'
          rw [hbot.1] at h2; exact Bool.noConfusion h2
      have hu2_good : Good ms S u2 := by
        refine ⟨hg.sub, hg.nonempty, hu2S, ?_, ?_, ?_⟩
        · intro v hvS c hcs; have he := hg.edges v hvS c hcs; rw [hval', hu1_zero, Bool.false_or] at he; exact he
        · intro v hvS c hcB hcns; have hne := hg.nonedges v hvS c hcB hcns; rw [hval', hu1_zero, Bool.false_or] at hne; exact hne
        · have hbot := hg.botZero; rw [hval', hu1_zero, Bool.false_or] at hbot; exact hbot
      have hge := (sep_struct hleast hmono hSideA u2 S hu2_good).1
      omega
    have haNE : topVars ms a ≠ ∅ := fun haE =>
      kill_or_bot a b haE (by rw [haE, Finset.empty_union] at hun; exact hun) hval_or hanc_eq
    have hbNE : topVars ms b ≠ ∅ := fun hbE =>
      kill_or_bot b a hbE (by rw [hbE, Finset.union_empty] at hun; exact hun)
        (fun x => by rw [hval_or x, Bool.or_comm]) (by omega)
    have hna : (topVars ms a).Nonempty := Finset.nonempty_iff_ne_empty.mpr haNE
    have hnb : (topVars ms b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hbNE
    have hsub_a : topVars ms a ⊆ sideA := (hun ▸ Finset.subset_union_left).trans hg.sub
    have hsub_b : topVars ms b ⊆ sideA := (hun ▸ Finset.subset_union_right).trans hg.sub
    have hbot_or := hg.botZero; rw [hval_or, Bool.or_eq_false_iff] at hbot_or
    have hga : Good ms (topVars ms a) a := by
      refine ⟨hsub_a, hna, rfl, ?_, ?_, hbot_or.1⟩
      · intro v hva c hcs
        have hvS : v ∈ S := hun ▸ Finset.mem_union_left _ hva
        have he := hg.edges v hvS c hcs; rw [hval_or, Bool.or_eq_true] at he
        have hb_f : vl ms (setInput {v, c}) b.val = false := by
          cases hbv : vl ms (setInput {v, c}) b.val with
          | false => rfl
          | true =>
            exfalso
            have h1 : vl ms (setInput {c}) b.val = true := by
              rw [vl_indep_outside_topVars hleast.hcl b (setInput {c}) (setInput {v, c}) (fun i hi => by
                have hiv : i ≠ v := by
                  rintro rfl; rcases hi with hiB | hiT
                  · exact sideA_sideB_disj _ (hsub_a hva) hiB
                  · exact Finset.disjoint_left.mp htv_disj hva hiT
                simp [setInput, hiv])]
              exact hbv
            have h2 := vl_setInput_mono hleast.hcl hmono (Finset.singleton_subset_iff.mpr (star_sub_sideB v (hsub_a hva) hcs)) b.val h1
            rw [hbot_or.2] at h2; exact Bool.noConfusion h2
        rcases he with h1 | h2
        · exact h1
        · rw [hb_f] at h2; exact Bool.noConfusion h2
      · intro v hva c hcB hcns
        have hne := hg.nonedges v (hun ▸ Finset.mem_union_left _ hva) c hcB hcns
        rw [hval_or, Bool.or_eq_false_iff] at hne; exact hne.1
    have hgb : Good ms (topVars ms b) b := by
      refine ⟨hsub_b, hnb, rfl, ?_, ?_, hbot_or.2⟩
      · intro v hvb c hcs
        have hvS : v ∈ S := hun ▸ Finset.mem_union_right _ hvb
        have he := hg.edges v hvS c hcs; rw [hval_or, Bool.or_eq_true] at he
        have ha_f : vl ms (setInput {v, c}) a.val = false := by
          cases hav : vl ms (setInput {v, c}) a.val with
          | false => rfl
          | true =>
            exfalso
            have h1 : vl ms (setInput {c}) a.val = true := by
              rw [vl_indep_outside_topVars hleast.hcl a (setInput {c}) (setInput {v, c}) (fun i hi => by
                have hiv : i ≠ v := by
                  rintro rfl; rcases hi with hiB | hiT
                  · exact sideA_sideB_disj _ (hsub_b hvb) hiB
                  · exact Finset.disjoint_left.mp htv_disj hiT hvb
                simp [setInput, hiv])]
              exact hav
            have h2 := vl_setInput_mono hleast.hcl hmono (Finset.singleton_subset_iff.mpr (star_sub_sideB v (hsub_b hvb) hcs)) a.val h1
            rw [hbot_or.1] at h2; exact Bool.noConfusion h2
        rcases he with h1 | h2
        · rw [ha_f] at h1; exact Bool.noConfusion h1
        · exact h2
      · intro v hvb c hcB hcns
        have hne := hg.nonedges v (hun ▸ Finset.mem_union_right _ hvb) c hcB hcns
        rw [hval_or, Bool.or_eq_false_iff] at hne; exact hne.2
    have hca := (sep_struct hleast hmono hSideA a (topVars ms a) hga).1
    have hcb := (sep_struct hleast hmono hSideA b (topVars ms b) hgb).1
    have hcardS : S.card = (topVars ms a).card + (topVars ms b).card := by
      rw [← hun, Finset.card_union_of_disjoint htv_disj]
    have hpa := hna.card_pos; have hpb := hnb.card_pos
    exact ⟨g, a, b, hgp, hop, hg_in, hga, hgb, htv_disj, hun, by omega, by omega⟩

lemma canon_iso {ms : List Gate} (hms_len : ms.length = 8) (outM : Fin 14)
    (hleast : Least 6 c6Fun ms outM.val)
    (hmono : ∀ g ∈ ms, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hSideA : SideNoTopBranch ms sideA) :
    ∃ (ord : Fin 3) (π : Fin 14 ≃ Fin 14),
      (∀ i : Fin 6, π ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩) ∧
      π 13 = outM ∧
      (∀ c : Fin 8, 6 ≤ (π ⟨6 + c.val, by omega⟩).val) ∧
      (∀ c : Fin 8, ∃ mg,
        ms[(π ⟨6 + c.val, by omega⟩).val - 6]? = some mg ∧
        mg.op = canonOp c ∧
        (mg.inputs = [(π (canonL ord c)).val, (π (canonR ord c)).val] ∨
         mg.inputs = [(π (canonR ord c)).val, (π (canonL ord c)).val])) := by
  classical
  have hm14 : 6 + ms.length = 14 := by omega
  let outW : Fin (6 + ms.length) := ⟨outM.val, by omega⟩
  have htv_out : topVars ms outW = sideA := by
    ext v
    rw [mem_topVars]
    constructor
    · exact fun h => h.1
    · intro hvA
      refine ⟨hvA, ?_⟩
      by_contra hno
      obtain ⟨x, hx⟩ := c6_depends v
      apply hx
      rw [← hleast.hev, ← hleast.hev]
      exact agree_on_input_ancestors hleast.hcl _ _ outW (fun i hanc => by
        have hiv : i ≠ v := fun heq => hno (heq ▸ hanc)
        exact Function.update_of_ne hiv _ x)
  have hout_good : Good ms sideA outW := by
    refine ⟨Finset.Subset.refl _, by decide, htv_out, ?_, ?_, ?_⟩
    · intro v hvA b hbs; rw [hleast.hev]; exact c6_good_edges v hvA b hbs
    · intro v hvA b hbB hbns; rw [hleast.hev]; exact c6_good_nonedges v hvA b hbB hbns
    · rw [hleast.hev]; exact c6_good_sideB
  obtain ⟨hanc_ge5, hstars⟩ := sep_struct hleast hmono hSideA outW sideA hout_good
  obtain ⟨u1, hu1_6, hu1_bot, hu1_fun⟩ := hstars 1 (by decide)
  obtain ⟨u2, hu2_6, hu2_bot, hu2_fun⟩ := hstars 2 (by decide)
  obtain ⟨u3, hu3_6, hu3_bot, hu3_fun⟩ := hstars 3 (by decide)
  have hu12 : u1 ≠ u2 := by
    intro h; have h1 := hu1_fun (setInput {0}); have h2 := hu2_fun (setInput {0})
    rw [h] at h1; rw [h1, starFun_sep_12.1, starFun_sep_12.2] at h2; exact Bool.noConfusion h2
  have hu13 : u1 ≠ u3 := by
    intro h; have h1 := hu1_fun (setInput {5}); have h2 := hu3_fun (setInput {5})
    rw [h] at h1; rw [h1, starFun_sep_13.1, starFun_sep_13.2] at h2; exact Bool.noConfusion h2
  have hu23 : u2 ≠ u3 := by
    intro h; have h1 := hu2_fun (setInput {4}); have h2 := hu3_fun (setInput {4})
    rw [h] at h1; rw [h1, starFun_sep_23.1, starFun_sep_23.2] at h2; exact Bool.noConfusion h2
  let gates : Finset (Fin (6 + ms.length)) := Finset.univ.filter fun z => 6 ≤ z.val
  have hgates_card : gates.card = 8 := by
    have heq : gates = Finset.univ.image (fun q : Fin ms.length => (⟨6 + q.val, by have := q.isLt; omega⟩ : Fin (6 + ms.length))) := by
      ext z; simp only [gates, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hz6; exact ⟨⟨z.val - 6, by have := z.isLt; omega⟩, Fin.ext (by dsimp; omega)⟩
      · rintro ⟨q, rfl⟩; simp
    rw [heq, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)),
        Finset.card_univ, Fintype.card_fin, hms_len]
  let botG : Finset (Fin (6 + ms.length)) := gates.filter fun z => topVars ms z = ∅
  let topG : Finset (Fin (6 + ms.length)) := gates.filter fun z => (topVars ms z).Nonempty
  have hsub_u : ({u1, u2, u3} : Finset (Fin (6 + ms.length))) ⊆ botG := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [botG, gates, hu1_6, hu1_bot, hu2_6, hu2_bot, hu3_6, hu3_bot]
  have hcard_u : ({u1, u2, u3} : Finset (Fin (6 + ms.length))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hu12, hu13]),
        Finset.card_insert_of_notMem (by simp [hu23]), Finset.card_singleton]
  have hbot_ge3 : 3 ≤ botG.card := hcard_u ▸ Finset.card_le_card hsub_u
  have hanc_sub_top : topAnc ms outW ⊆ topG := by
    intro z hz; obtain ⟨hz6, hzt, _⟩ := mem_topAnc.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz6⟩, hzt⟩
  have hdisj_bt : Disjoint botG topG := by
    rw [Finset.disjoint_left]; intro z hb ht
    have h1 := (Finset.mem_filter.mp hb).2; have h2 := (Finset.mem_filter.mp ht).2
    rw [h1] at h2; exact Finset.not_nonempty_empty h2
  have hun_bt : botG ∪ topG ⊆ gates := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum_le8 : botG.card + topG.card ≤ 8 := by
    rw [← Finset.card_union_of_disjoint hdisj_bt, ← hgates_card]
    exact Finset.card_le_card hun_bt
  have hanc_le_top : (topAnc ms outW).card ≤ topG.card := Finset.card_le_card hanc_sub_top
  have hsideA_card : sideA.card = 3 := by decide
  rw [hsideA_card] at hanc_ge5
  have hanc_eq5 : (topAnc ms outW).card = 5 := by omega
  have hbot_eq3 : botG.card = 3 := by omega
  have hbot_eq : botG = {u1, u2, u3} := (Finset.eq_of_subset_of_card_le hsub_u (by omega)).symm
  have hbot_gate_eq : ∀ (u : Fin (6 + ms.length)), 6 ≤ u.val → topVars ms u = ∅ →
      u = u1 ∨ u = u2 ∨ u = u3 := by
    intro u hu6 hub
    have hm : u ∈ botG := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu6⟩, hub⟩
    rw [hbot_eq] at hm
    simpa [Finset.mem_insert, Finset.mem_singleton] using hm
  have hbot_wire_code : ∀ (z : Fin (6 + ms.length)), topVars ms z = ∅ →
      ∃ i : Fin 6,
        (i.val = 0 ∧ z.val = 0) ∨ (i.val = 1 ∧ z.val = 4) ∨ (i.val = 2 ∧ z.val = 5) ∨
        (i.val = 3 ∧ z = u1) ∨ (i.val = 4 ∧ z = u2) ∨ (i.val = 5 ∧ z = u3) := by
    intro z hzbot
    by_cases hz6 : 6 ≤ z.val
    · rcases hbot_gate_eq z hz6 hzbot with rfl | rfl | rfl
      · exact ⟨3, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
      · exact ⟨5, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩
    · have hzlt : z.val < 6 := by omega
      let v : Fin 6 := ⟨z.val, hzlt⟩
      have hv_notA : v ∉ sideA := by
        intro hvA
        have hm : v ∈ topVars ms z := mem_topVars.mpr ⟨hvA, by
          have : inputWire ms v = z := Fin.ext rfl; rw [this]⟩
        rw [hzbot] at hm; exact Finset.notMem_empty _ hm
      have hvB : v ∈ sideB := (sideA_union_sideB v).resolve_left hv_notA
      have hv_cases : z.val = 0 ∨ z.val = 4 ∨ z.val = 5 := by
        simp only [sideB, Finset.mem_insert, Finset.mem_singleton] at hvB
        rcases hvB with h | h | h
        · left; exact congrArg Fin.val h
        · right; left; exact congrArg Fin.val h
        · right; right; exact congrArg Fin.val h
      rcases hv_cases with h0 | h4 | h5
      · exact ⟨0, Or.inl ⟨rfl, h0⟩⟩
      · exact ⟨1, Or.inr (Or.inl ⟨rfl, h4⟩)⟩
      · exact ⟨2, Or.inr (Or.inr (Or.inl ⟨rfl, h5⟩))⟩
  let embed3 (y : Fin 3 → Bool) : Fin 6 → Bool
    | ⟨0, _⟩ => y 0
    | ⟨4, _⟩ => y 1
    | ⟨5, _⟩ => y 2
    | _ => false
  have hcode_val : ∀ (z : Fin (6 + ms.length)) (i : Fin 6),
      ((i.val = 0 ∧ z.val = 0) ∨ (i.val = 1 ∧ z.val = 4) ∨ (i.val = 2 ∧ z.val = 5) ∨
       (i.val = 3 ∧ z = u1) ∨ (i.val = 4 ∧ z = u2) ∨ (i.val = 5 ∧ z = u3)) →
      ∀ y : Fin 3 → Bool, vl ms (embed3 y) z.val = botFunc i y := by
    intro z i hc y
    rcases hc with ⟨hi, hz⟩ | ⟨hi, hz⟩ | ⟨hi, hz⟩ | ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨hi, rfl⟩
    · have hi' : i = 0 := Fin.ext hi; subst hi'; rw [hz, vl_input ms _ 0 (by omega)]; rfl
    · have hi' : i = 1 := Fin.ext hi; subst hi'; rw [hz, vl_input ms _ 4 (by omega)]; rfl
    · have hi' : i = 2 := Fin.ext hi; subst hi'; rw [hz, vl_input ms _ 5 (by omega)]; rfl
    · have hi' : i = 3 := Fin.ext hi; subst hi'; rw [hu1_fun]
      have hy : y = mk3 (y 0) (y 1) (y 2) := funext fun k => by fin_cases k <;> rfl
      rw [hy]; cases y 0 <;> cases y 1 <;> cases y 2 <;> decide
    · have hi' : i = 4 := Fin.ext hi; subst hi'; rw [hu2_fun]
      have hy : y = mk3 (y 0) (y 1) (y 2) := funext fun k => by fin_cases k <;> rfl
      rw [hy]; cases y 0 <;> cases y 1 <;> cases y 2 <;> decide
    · have hi' : i = 5 := Fin.ext hi; subst hi'; rw [hu3_fun]
      have hy : y = mk3 (y 0) (y 1) (y 2) := funext fun k => by fin_cases k <;> rfl
      rw [hy]; cases y 0 <;> cases y 1 <;> cases y 2 <;> decide
  have hbot_spec : ∀ (t : Fin 3) (ut : Fin (6 + ms.length)),
      ((t.val = 0 ∧ ut = u1) ∨ (t.val = 1 ∧ ut = u2) ∨ (t.val = 2 ∧ ut = u3)) →
      ∃ mg, ms[ut.val - 6]? = some mg ∧ mg.op = GateOp.or ∧
        ((t.val = 0 ∧ (mg.inputs = [0, 4] ∨ mg.inputs = [4, 0])) ∨
         (t.val = 1 ∧ (mg.inputs = [4, 5] ∨ mg.inputs = [5, 4])) ∨
         (t.val = 2 ∧ (mg.inputs = [0, 5] ∨ mg.inputs = [5, 0]))) := by
    intro t ut ht
    have hut6 : 6 ≤ ut.val := by rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    have hut_bot : topVars ms ut = ∅ := by rcases ht with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    obtain ⟨g, a, b, hgp, hg_op, hg_in, haw, hbw, hab, hre_a, hre_b, hre_iff, hval⟩ :=
      gate_inputs_pair hleast hmono ut hut6
    have htv := (topVars_gate hleast.hcl hSideA hut6 hab hre_a hre_b hre_iff).1
    rw [hut_bot] at htv
    have ha_bot : topVars ms a = ∅ := (Finset.union_eq_empty.mp htv.symm).1
    have hb_bot : topVars ms b = ∅ := (Finset.union_eq_empty.mp htv.symm).2
    obtain ⟨ia, hca⟩ := hbot_wire_code a ha_bot
    obtain ⟨ib, hcb⟩ := hbot_wire_code b hb_bot
    have hia_ne : ia.val ≠ t.val + 3 := by
      intro heq
      have ha_eq : a = ut := by
        rcases ht with ⟨ht0, rfl⟩ | ⟨ht1, rfl⟩ | ⟨ht2, rfl⟩ <;>
        rcases hca with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ <;>
        first | rfl | omega
      exact ne_of_lt haw ha_eq
    have hib_ne : ib.val ≠ t.val + 3 := by
      intro heq
      have hb_eq : b = ut := by
        rcases ht with ⟨ht0, rfl⟩ | ⟨ht1, rfl⟩ | ⟨ht2, rfl⟩ <;>
        rcases hcb with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ <;>
        first | rfl | omega
      exact ne_of_lt hbw hb_eq
    have hiab : ia ≠ ib := by
      intro heq; subst heq
      apply hab
      rcases hca with ⟨h0, ha0⟩ | ⟨h0, ha0⟩ | ⟨h0, ha0⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩ <;>
      rcases hcb with ⟨h1, hb0⟩ | ⟨h1, hb0⟩ | ⟨h1, hb0⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      first | rfl | (exact Fin.ext (by omega)) | omega
    let isOr : Bool := match g.op with | GateOp.or => true | _ => false
    have hfeq : ∀ y : Fin 3 → Bool,
        (if isOr then botFunc ia y || botFunc ib y else botFunc ia y && botFunc ib y) =
          botFunc ⟨t.val + 3, by omega⟩ y := by
      intro y
      have h1 := hval (embed3 y)
      rw [hcode_val a ia hca y, hcode_val b ib hcb y] at h1
      have h2 : vl ms (embed3 y) ut.val = botFunc ⟨t.val + 3, by omega⟩ y := by
        rcases ht with ⟨ht0, hut⟩ | ⟨ht1, hut⟩ | ⟨ht2, hut⟩
        · have ht' : (⟨t.val + 3, by have := t.isLt; omega⟩ : Fin 6) = 3 := Fin.ext (by dsimp; omega)
          rw [ht', hut]; exact hcode_val u1 3 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) y
        · have ht' : (⟨t.val + 3, by have := t.isLt; omega⟩ : Fin 6) = 4 := Fin.ext (by dsimp; omega)
          rw [ht', hut]; exact hcode_val u2 4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) y
        · have ht' : (⟨t.val + 3, by have := t.isLt; omega⟩ : Fin 6) = 5 := Fin.ext (by dsimp; omega)
          rw [ht', hut]; exact hcode_val u3 5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) y
      rw [← h2, h1]
      rcases hg_op with hop | hop <;> simp [isOr, hop, GateOp.eval]
    obtain ⟨hisOr, hpair⟩ := bot_gate_forced t isOr ia ib hia_ne hib_ne hiab (fun b0 b1 b2 => hfeq (mk3 b0 b1 b2))
    have hop_or : g.op = GateOp.or := by
      rcases hg_op with hop | hop
      · simp [isOr, hop] at hisOr
      · exact hop
    refine ⟨g, hgp, hop_or, ?_⟩
    have get_val : ∀ (z : Fin (6 + ms.length)) (i : Fin 6),
        ((i.val = 0 ∧ z.val = 0) ∨ (i.val = 1 ∧ z.val = 4) ∨ (i.val = 2 ∧ z.val = 5) ∨
         (i.val = 3 ∧ z = u1) ∨ (i.val = 4 ∧ z = u2) ∨ (i.val = 5 ∧ z = u3)) →
        (i.val = 0 → z.val = 0) ∧ (i.val = 1 → z.val = 4) ∧ (i.val = 2 → z.val = 5) := by
      intro z i hc; rcases hc with ⟨h0, hz⟩ | ⟨h0, hz⟩ | ⟨h0, hz⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩ <;>
        exact ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩
    have ha_v := get_val a ia hca; have hb_v := get_val b ib hcb
    rcases hpair with ⟨ht0, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨ht1, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨ht2, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · left; exact ⟨ht0, Or.inl (by rw [hg_in, ha_v.1 h1, hb_v.2.1 h2])⟩
    · left; exact ⟨ht0, Or.inr (by rw [hg_in, ha_v.2.1 h1, hb_v.1 h2])⟩
    · right; left; exact ⟨ht1, Or.inl (by rw [hg_in, ha_v.2.1 h1, hb_v.2.2 h2])⟩
    · right; left; exact ⟨ht1, Or.inr (by rw [hg_in, ha_v.2.2 h1, hb_v.2.1 h2])⟩
    · right; right; exact ⟨ht2, Or.inl (by rw [hg_in, ha_v.1 h1, hb_v.2.2 h2])⟩
    · right; right; exact ⟨ht2, Or.inr (by rw [hg_in, ha_v.2.2 h1, hb_v.1 h2])⟩
  obtain ⟨gOut, wA0, wB0, hgpOut, hopOut, hinOut, hgA0, hgB0, hdisjOut, hunOut, hancA0, hancB0⟩ :=
    sep_tight_ge2 hleast hmono hSideA hout_good (by decide) (by rw [hanc_eq5, hsideA_card])
  have hcardOut : (topVars ms wA0).card + (topVars ms wB0).card = 3 := by
    rw [← Finset.card_union_of_disjoint hdisjOut, hunOut, hsideA_card]
  have hpa0 := hgA0.nonempty.card_pos; have hpb0 := hgB0.nonempty.card_pos
  have hsplit_out : ∃ (w2 w1 : Fin (6 + ms.length)),
      (gOut.inputs = [w2.val, w1.val] ∨ gOut.inputs = [w1.val, w2.val]) ∧
      Good ms (topVars ms w2) w2 ∧ Good ms (topVars ms w1) w1 ∧
      Disjoint (topVars ms w2) (topVars ms w1) ∧ topVars ms w2 ∪ topVars ms w1 = sideA ∧
      (topVars ms w2).card = 2 ∧ (topVars ms w1).card = 1 ∧
      (topAnc ms w2).card = 3 ∧ (topAnc ms w1).card = 1 := by
    by_cases h2 : (topVars ms wA0).card = 2
    · exact ⟨wA0, wB0, Or.inl hinOut, hgA0, hgB0, hdisjOut, hunOut, h2, by omega, by omega, by omega⟩
    · exact ⟨wB0, wA0, Or.inr hinOut, hgB0, hgA0, hdisjOut.symm, Finset.union_comm (topVars ms wA0) (topVars ms wB0) ▸ hunOut, by omega, by omega, by omega, by omega⟩
  obtain ⟨w12, wSingle, hinOut', hg12, hgSingle, hdisj12, hun12, hc12, hcSingle, hanc12, hancSingle⟩ := hsplit_out
  obtain ⟨g12, wP, wQ, hgp12, hop12, hin12, hgP, hgQ, hdisjPQ, hunPQ, hancP, hancQ⟩ :=
    sep_tight_ge2 hleast hmono hSideA hg12 (by omega) (by omega)
  have hcardPQ : (topVars ms wP).card + (topVars ms wQ).card = 2 := by
    rw [← Finset.card_union_of_disjoint hdisjPQ, hunPQ, hc12]
  have hcP : (topVars ms wP).card = 1 := by have := hgP.nonempty.card_pos; have := hgQ.nonempty.card_pos; omega
  have hcQ : (topVars ms wQ).card = 1 := by omega
  obtain ⟨vP, hvP⟩ := Finset.card_eq_one.mp hcP
  obtain ⟨vQ, hvQ⟩ := Finset.card_eq_one.mp hcQ
  obtain ⟨vS, hvS⟩ := Finset.card_eq_one.mp hcSingle
  have hv_all : ({vP, vQ, vS} : Finset (Fin 6)) = sideA := by
    rw [← hun12, ← hunPQ, hvP, hvQ, hvS]; ext x; simp
  have hdisj_PQ : vP ≠ vQ := by
    intro h; apply Finset.disjoint_left.mp hdisjPQ (hvP ▸ Finset.mem_singleton_self vP)
    rw [hvQ, h]; exact Finset.mem_singleton_self vQ
  have hdisj_PS : vP ≠ vS := by
    intro h; apply Finset.disjoint_left.mp hdisj12 (hunPQ ▸ Finset.mem_union_left _ (hvP ▸ Finset.mem_singleton_self vP))
    rw [hvS, h]; exact Finset.mem_singleton_self vS
  have hdisj_QS : vQ ≠ vS := by
    intro h; apply Finset.disjoint_left.mp hdisj12 (hunPQ ▸ Finset.mem_union_right _ (hvQ ▸ Finset.mem_singleton_self vQ))
    rw [hvS, h]; exact Finset.mem_singleton_self vS
  have unpack_single : ∀ (w : Fin (6 + ms.length)) (v : Fin 6),
      Good ms {v} w → (topAnc ms w).card = 1 →
      ∃ (g : Gate) (uv : Fin (6 + ms.length)),
        ms[w.val - 6]? = some g ∧ g.op = GateOp.and ∧
        ((v = 1 ∧ uv = u1) ∨ (v = 2 ∧ uv = u2) ∨ (v = 3 ∧ uv = u3)) ∧
        (g.inputs = [v.val, uv.val] ∨ g.inputs = [uv.val, v.val]) := by
    intro w v hgv hanc1
    obtain ⟨g, u, hgp, hop, hu6, hubot, hufun, hgin⟩ := sep_tight_one hleast hmono hSideA hgv hanc1
    have hu_in := hbot_gate_eq u hu6 hubot
    have hvA : v ∈ sideA := hgv.sub (by simp)
    have hv_cases : v = 1 ∨ v = 2 ∨ v = 3 := by simpa [sideA] using hvA
    have hu_match : (v = 1 ∧ u = u1) ∨ (v = 2 ∧ u = u2) ∨ (v = 3 ∧ u = u3) := by
      rcases hv_cases with rfl | rfl | rfl <;> rcases hu_in with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exfalso; have h1 := hufun (setInput {0}); rw [hu2_fun, starFun_sep_12.1, starFun_sep_12.2] at h1; exact Bool.noConfusion h1
      · exfalso; have h1 := hufun (setInput {5}); rw [hu3_fun, starFun_sep_13.1, starFun_sep_13.2] at h1; exact Bool.noConfusion h1
      · exfalso; have h1 := hufun (setInput {0}); rw [hu1_fun, starFun_sep_12.1, starFun_sep_12.2] at h1; exact Bool.noConfusion h1
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exfalso; have h1 := hufun (setInput {4}); rw [hu3_fun, starFun_sep_23.1, starFun_sep_23.2] at h1; exact Bool.noConfusion h1
      · exfalso; have h1 := hufun (setInput {5}); rw [hu1_fun, starFun_sep_13.1, starFun_sep_13.2] at h1; exact Bool.noConfusion h1
      · exfalso; have h1 := hufun (setInput {4}); rw [hu2_fun, starFun_sep_23.1, starFun_sep_23.2] at h1; exact Bool.noConfusion h1
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    exact ⟨g, u, hgp, hop, hu_match, hgin⟩
  have hbuild : ∀ (ord : Fin 3) (w9 w10 w11 : Fin (6 + ms.length)),
      Good ms {1} w9 → (topAnc ms w9).card = 1 →
      Good ms {2} w10 → (topAnc ms w10).card = 1 →
      Good ms {3} w11 → (topAnc ms w11).card = 1 →
      (match ord with
       | 0 => (g12.inputs = [w9.val, w10.val] ∨ g12.inputs = [w10.val, w9.val]) ∧
              (gOut.inputs = [w12.val, w11.val] ∨ gOut.inputs = [w11.val, w12.val])
       | 1 => (g12.inputs = [w9.val, w11.val] ∨ g12.inputs = [w11.val, w9.val]) ∧
              (gOut.inputs = [w12.val, w10.val] ∨ gOut.inputs = [w10.val, w12.val])
       | 2 => (g12.inputs = [w10.val, w11.val] ∨ g12.inputs = [w11.val, w10.val]) ∧
              (gOut.inputs = [w12.val, w9.val] ∨ gOut.inputs = [w9.val, w12.val])) →
      ∃ (ord' : Fin 3) (π : Fin 14 ≃ Fin 14),
        (∀ i : Fin 6, π ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩) ∧
        π 13 = outM ∧
        (∀ c : Fin 8, 6 ≤ (π ⟨6 + c.val, by omega⟩).val) ∧
        (∀ c : Fin 8, ∃ mg,
          ms[(π ⟨6 + c.val, by omega⟩).val - 6]? = some mg ∧
          mg.op = canonOp c ∧
          (mg.inputs = [(π (canonL ord' c)).val, (π (canonR ord' c)).val] ∨
           mg.inputs = [(π (canonR ord' c)).val, (π (canonL ord' c)).val])) := by
    intro ord w9 w10 w11 hg9 ha9 hg10 ha10 hg11 ha11 hord_ins
    have hw9_6 := good_not_input hleast.hcl hg9
    have hw10_6 := good_not_input hleast.hcl hg10
    have hw11_6 := good_not_input hleast.hcl hg11
    have hw12_6 := good_not_input hleast.hcl hg12
    have hout_6 := good_not_input hleast.hcl hout_good
    let fWire : Fin 14 → Fin (6 + ms.length) := fun c =>
      match c.val with
      | 0 => ⟨0, by omega⟩ | 1 => ⟨1, by omega⟩ | 2 => ⟨2, by omega⟩
      | 3 => ⟨3, by omega⟩ | 4 => ⟨4, by omega⟩ | 5 => ⟨5, by omega⟩
      | 6 => u1 | 7 => u2 | 8 => u3 | 9 => w9 | 10 => w10 | 11 => w11 | 12 => w12 | _ => outW
    let f14 : Fin 14 → Fin 14 := fun c => ⟨(fWire c).val, by omega⟩
    have hf_inj : Function.Injective f14 := by
      let tag (z : Fin (6 + ms.length)) : ℕ :=
        if z.val < 6 then z.val
        else if z = u1 then 6
        else if z = u2 then 7
        else if z = u3 then 8
        else if topVars ms z = {1} then 9
        else if topVars ms z = {2} then 10
        else if topVars ms z = {3} then 11
        else if (topVars ms z).card = 2 then 12
        else 13
      have hne_bot : ∀ (z : Fin (6 + ms.length)), (topVars ms z).Nonempty → z ≠ u1 ∧ z ≠ u2 ∧ z ≠ u3 := by
        intro z hz
        exact ⟨fun h => by subst h; rw [hu1_bot] at hz; exact Finset.not_nonempty_empty hz,
               fun h => by subst h; rw [hu2_bot] at hz; exact Finset.not_nonempty_empty hz,
               fun h => by subst h; rw [hu3_bot] at hz; exact Finset.not_nonempty_empty hz⟩
      have htag : ∀ c : Fin 14, tag (fWire c) = c.val := by
        intro c
        fin_cases c
        · simp [tag, fWire]
        · simp [tag, fWire]
        · simp [tag, fWire]
        · simp [tag, fWire]
        · simp [tag, fWire]
        · simp [tag, fWire]
        · simp [tag, fWire, show ¬ u1.val < 6 by omega]
        · simp [tag, fWire, show ¬ u2.val < 6 by omega, hu12.symm]
        · simp [tag, fWire, show ¬ u3.val < 6 by omega, hu13.symm, hu23.symm]
        · have hb := hne_bot w9 (hg9.vars.symm ▸ hg9.nonempty)
          simp [tag, fWire, show ¬ w9.val < 6 by omega, hb.1, hb.2.1, hb.2.2, hg9.vars]
        · have hb := hne_bot w10 (hg10.vars.symm ▸ hg10.nonempty)
          have h1 : topVars ms w10 ≠ {1} := by rw [hg10.vars]; decide
          simp [tag, fWire, show ¬ w10.val < 6 by omega, hb.1, hb.2.1, hb.2.2, h1, hg10.vars]
        · have hb := hne_bot w11 (hg11.vars.symm ▸ hg11.nonempty)
          have h1 : topVars ms w11 ≠ {1} := by rw [hg11.vars]; decide
          have h2 : topVars ms w11 ≠ {2} := by rw [hg11.vars]; decide
          simp [tag, fWire, show ¬ w11.val < 6 by omega, hb.1, hb.2.1, hb.2.2, h1, h2, hg11.vars]
        · have hb := hne_bot w12 (hg12.vars.symm ▸ hg12.nonempty)
          have h1 : topVars ms w12 ≠ {1} := fun h => by rw [h] at hc12; simp at hc12
          have h2 : topVars ms w12 ≠ {2} := fun h => by rw [h] at hc12; simp at hc12
          have h3 : topVars ms w12 ≠ {3} := fun h => by rw [h] at hc12; simp at hc12
          simp [tag, fWire, show ¬ w12.val < 6 by omega, hb.1, hb.2.1, hb.2.2, h1, h2, h3, hc12]
        · have hb := hne_bot outW (hout_good.vars.symm ▸ hout_good.nonempty)
          have h1 : topVars ms outW ≠ {1} := by rw [hout_good.vars]; decide
          have h2 : topVars ms outW ≠ {2} := by rw [hout_good.vars]; decide
          have h3 : topVars ms outW ≠ {3} := by rw [hout_good.vars]; decide
          have h4 : (topVars ms outW).card ≠ 2 := by rw [hout_good.vars, hsideA_card]; omega
          simp [tag, fWire, show ¬ outW.val < 6 by omega, hb.1, hb.2.1, hb.2.2, h1, h2, h3, h4]
      intro c1 c2 heq
      have hfw : fWire c1 = fWire c2 := Fin.ext (by simpa [f14] using congrArg Fin.val heq)
      have ht := congrArg tag hfw
      rw [htag c1, htag c2] at ht
      exact Fin.ext ht
    let π : Fin 14 ≃ Fin 14 := Equiv.ofBijective f14 ((Fintype.bijective_iff_injective_and_card f14).mpr ⟨hf_inj, rfl⟩)
    refine ⟨ord, π, ?_, Fin.ext rfl, ?_, ?_⟩
    · intro i; fin_cases i <;> rfl
    · intro c; fin_cases c <;> simp [π, f14, fWire, hu1_6, hu2_6, hu3_6, hw9_6, hw10_6, hw11_6, hw12_6, hout_6]
    · intro c
      fin_cases c
      · obtain ⟨mg, hmg, hop, hs⟩ := hbot_spec 0 u1 (Or.inl ⟨rfl, rfl⟩)
        rcases hs with ⟨_, hi⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact ⟨mg, hmg, hop, hi⟩
        · simp at h0
        · simp at h0
      · obtain ⟨mg, hmg, hop, hs⟩ := hbot_spec 1 u2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        rcases hs with ⟨h0, _⟩ | ⟨_, hi⟩ | ⟨h0, _⟩
        · simp at h0
        · exact ⟨mg, hmg, hop, hi⟩
        · simp at h0
      · obtain ⟨mg, hmg, hop, hs⟩ := hbot_spec 2 u3 (Or.inr (Or.inr ⟨rfl, rfl⟩))
        rcases hs with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, hi⟩
        · simp at h0
        · simp at h0
        · exact ⟨mg, hmg, hop, hi⟩
      · obtain ⟨mg, uv, hmg, hop, hm, hi⟩ := unpack_single w9 1 hg9 ha9
        rcases hm with ⟨_, rfl⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · exact ⟨mg, hmg, hop, hi⟩
        · cases h0
        · cases h0
      · obtain ⟨mg, uv, hmg, hop, hm, hi⟩ := unpack_single w10 2 hg10 ha10
        rcases hm with ⟨h0, _⟩ | ⟨_, rfl⟩ | ⟨h0, _⟩
        · cases h0
        · exact ⟨mg, hmg, hop, hi⟩
        · cases h0
      · obtain ⟨mg, uv, hmg, hop, hm, hi⟩ := unpack_single w11 3 hg11 ha11
        rcases hm with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, rfl⟩
        · cases h0
        · cases h0
        · exact ⟨mg, hmg, hop, hi⟩
      · refine ⟨g12, hgp12, hop12, ?_⟩
        fin_cases ord <;> exact hord_ins.1
      · refine ⟨gOut, hgpOut, hopOut, ?_⟩
        fin_cases ord <;> exact hord_ins.2
  have hvS_cases : vS = 1 ∨ vS = 2 ∨ vS = 3 := by
    have hm : vS ∈ sideA := by rw [← hv_all]; simp
    simpa [sideA] using hm
  have hvP_cases : vP = 1 ∨ vP = 2 ∨ vP = 3 := by
    have hm : vP ∈ sideA := by rw [← hv_all]; simp
    simpa [sideA] using hm
  have hvQ_cases : vQ = 1 ∨ vQ = 2 ∨ vQ = 3 := by
    have hm : vQ ∈ sideA := by rw [← hv_all]; simp
    simpa [sideA] using hm
  rw [hvP] at hgP; rw [hvQ] at hgQ; rw [hvS] at hgSingle
  rcases hvS_cases with rfl | rfl | rfl <;>
  rcases hvP_cases with rfl | rfl | rfl <;>
  rcases hvQ_cases with rfl | rfl | rfl
  all_goals first
    | exact (hdisj_PQ rfl).elim
    | exact (hdisj_PS rfl).elim
    | exact (hdisj_QS rfl).elim
    | exact hbuild 0 wP wQ wSingle hgP (by rw [hvP] at hancP; exact hancP) hgQ (by rw [hvQ] at hancQ; exact hancQ) hgSingle hancSingle ⟨Or.inl hin12, hinOut'⟩
    | exact hbuild 0 wQ wP wSingle hgQ (by rw [hvQ] at hancQ; exact hancQ) hgP (by rw [hvP] at hancP; exact hancP) hgSingle hancSingle ⟨Or.inr hin12, hinOut'⟩
    | exact hbuild 1 wP wSingle wQ hgP (by rw [hvP] at hancP; exact hancP) hgSingle hancSingle hgQ (by rw [hvQ] at hancQ; exact hancQ) ⟨Or.inl hin12, hinOut'⟩
    | exact hbuild 1 wQ wSingle wP hgQ (by rw [hvQ] at hancQ; exact hancQ) hgSingle hancSingle hgP (by rw [hvP] at hancP; exact hancP) ⟨Or.inr hin12, hinOut'⟩
    | exact hbuild 2 wSingle wP wQ hgSingle hancSingle hgP (by rw [hvP] at hancP; exact hancP) hgQ (by rw [hvQ] at hancQ; exact hancQ) ⟨Or.inl hin12, hinOut'⟩
    | exact hbuild 2 wSingle wQ wP hgSingle hancSingle hgQ (by rw [hvQ] at hancQ; exact hancQ) hgP (by rw [hvP] at hancP; exact hancP) ⟨Or.inr hin12, hinOut'⟩

end Step2


namespace Step3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup C6Lower Step1 Step2
open Relation

def rowInput : Fin 13 → Fin 6 → Bool
  | ⟨0, _⟩ => fun _ => false
  | ⟨1, _⟩ => fun i => match i.val with | 1 => true | _ => false
  | ⟨2, _⟩ => fun i => match i.val with | 5 => true | _ => false
  | ⟨3, _⟩ => fun i => match i.val with | 0 => true | _ => false
  | ⟨4, _⟩ => fun i => match i.val with | 2 => true | _ => false
  | ⟨5, _⟩ => fun i => match i.val with | 3 => true | _ => false
  | ⟨6, _⟩ => fun i => match i.val with | 4 => true | _ => false
  | ⟨7, _⟩ => fun i => match i.val with | 0 | 4 => true | _ => false
  | ⟨8, _⟩ => fun i => match i.val with | 0 | 2 => true | _ => false
  | ⟨9, _⟩ => fun i => match i.val with | 2 | 3 => true | _ => false
  | ⟨10, _⟩ => fun i => match i.val with | 3 | 4 => true | _ => false
  | ⟨11, _⟩ => fun i => match i.val with | 0 | 3 => true | _ => false
  | ⟨12, _⟩ => fun i => match i.val with | 2 | 4 => true | _ => false

def rowTarget : Fin 13 → Bool
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => true
  | ⟨11, _⟩ => true
  | ⟨12, _⟩ => true
  | _ => false

lemma theta_lift6T_row : ∀ r : Fin 13, thetaFun (lift6T (rowInput r)) = rowTarget r := by decide

def maskHasN (m s : Nat) : Bool :=
  if m == 0 then false
  else if m == 18 then (s == 0) || (s == 4)
  else if m == 19 then (s == 1) || (s == 2)
  else if m == 20 then (s == 3) || (s == 5)
  else s + 1 == m

def maskHas (m : Fin 21) (s : Fin 17) : Bool :=
  maskHasN m.val s.val

lemma maskHas_zero (s : Fin 17) : maskHas 0 s = false := rfl

lemma maskHas_single (s0 s : Fin 17) :
    maskHas ⟨s0.val + 1, by have := s0.isLt; omega⟩ s = decide (s.val = s0.val) := by
  fin_cases s0 <;> fin_cases s <;> decide

lemma maskHas_18 (s : Fin 17) : maskHas 18 s = decide (s.val = 0 ∨ s.val = 4) := by
  fin_cases s <;> decide

lemma maskHas_19 (s : Fin 17) : maskHas 19 s = decide (s.val = 1 ∨ s.val = 2) := by
  fin_cases s <;> decide

lemma maskHas_20 (s : Fin 17) : maskHas 20 s = decide (s.val = 3 ∨ s.val = 5) := by
  fin_cases s <;> decide

def allNat : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allNat n f

lemma allNat_true : ∀ (n : Nat) (f : Nat → Bool), allNat n f = true → ∀ k, k < n → f k = true
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, f, h, k, hk => by
    have h' : f n = true ∧ allNat n f = true := Bool.and_eq_true_iff.mp h
    by_cases hkn : k = n
    · subst hkn; exact h'.1
    · exact allNat_true n f h'.2 k (by omega)

def evalM3B (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool)
    (x0 x1 x2 x3 x4 x5 : Bool) : Fin 14 → Bool :=
  let v6 := (b0 || x0) || (b1 || x4)
  let v7 := (b2 || x4) || (b3 || x5)
  let v8 := (b4 || x0) || (b5 || x5)
  let v9 := (b6 || x1) && (b7 || v6)
  let v10 := (b8 || x2) && (b9 || v7)
  let v11 := (b10 || x3) && (b11 || v8)
  let a12 := match ord with | 0 => v9 | 1 => v9 | 2 => v10
  let b12v := match ord with | 0 => v10 | 1 => v11 | 2 => v11
  let c13 := match ord with | 0 => v11 | 1 => v10 | 2 => v9
  let v12 := (b12 || a12) || (b13 || b12v)
  let v13 := (b14 || v12) || (b15 || c13)
  fun c => match c.val with
    | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | 5 => x5
    | 6 => v6 | 7 => v7 | 8 => v8 | 9 => v9 | 10 => v10 | 11 => v11
    | 12 => v12 | _ => v13

def evalAvB (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool)
    (a : Fin 16) (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  if ha : a.val < 14 then
    evalM3B ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 x0 x1 x2 x3 x4 x5 ⟨a.val, ha⟩
  else if a.val == 14 then true else false

def evalRow2 (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 : Bool)
    (av x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  let v6 := ((b0 || x0) && (!h0 || av)) || ((b1 || x4) && (!h1 || av))
  let v7 := ((b2 || x4) && (!h2 || av)) || ((b3 || x5) && (!h3 || av))
  let v8 := ((b4 || x0) && (!h4 || av)) || ((b5 || x5) && (!h5 || av))
  let v9 := ((b6 || x1) && (!h6 || av)) && ((b7 || v6) && (!h7 || av))
  let v10 := ((b8 || x2) && (!h8 || av)) && ((b9 || v7) && (!h9 || av))
  let v11 := ((b10 || x3) && (!h10 || av)) && ((b11 || v8) && (!h11 || av))
  let a12 := match ord with | 0 => v9 | 1 => v9 | 2 => v10
  let b12v := match ord with | 0 => v10 | 1 => v11 | 2 => v11
  let c13 := match ord with | 0 => v11 | 1 => v10 | 2 => v9
  let v12 := ((b12 || a12) && (!h12 || av)) || ((b13 || b12v) && (!h13 || av))
  let v13 := ((b14 || v12) && (!h14 || av)) || ((b15 || c13) && (!h15 || av))
  (b16 || v13) && (!h16 || av)

def evalM3 (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool) : Fin 14 → Bool :=
  evalM3B ord
    (maskHas m1 0 || maskHas m2 0) (maskHas m1 1 || maskHas m2 1)
    (maskHas m1 2 || maskHas m2 2) (maskHas m1 3 || maskHas m2 3)
    (maskHas m1 4 || maskHas m2 4) (maskHas m1 5 || maskHas m2 5)
    (maskHas m1 6 || maskHas m2 6) (maskHas m1 7 || maskHas m2 7)
    (maskHas m1 8 || maskHas m2 8) (maskHas m1 9 || maskHas m2 9)
    (maskHas m1 10 || maskHas m2 10) (maskHas m1 11 || maskHas m2 11)
    (maskHas m1 12 || maskHas m2 12) (maskHas m1 13 || maskHas m2 13)
    (maskHas m1 14 || maskHas m2 14) (maskHas m1 15 || maskHas m2 15)
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def evalOut3 (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool) : Bool :=
  maskHas m1 16 || maskHas m2 16 || evalM3 ord m1 m2 x 13

def evalAv (ord : Fin 3) (m1 m2 : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) : Bool :=
  evalAvB ord
    (maskHas m1 0 || maskHas m2 0) (maskHas m1 1 || maskHas m2 1)
    (maskHas m1 2 || maskHas m2 2) (maskHas m1 3 || maskHas m2 3)
    (maskHas m1 4 || maskHas m2 4) (maskHas m1 5 || maskHas m2 5)
    (maskHas m1 6 || maskHas m2 6) (maskHas m1 7 || maskHas m2 7)
    (maskHas m1 8 || maskHas m2 8) (maskHas m1 9 || maskHas m2 9)
    (maskHas m1 10 || maskHas m2 10) (maskHas m1 11 || maskHas m2 11)
    (maskHas m1 12 || maskHas m2 12) (maskHas m1 13 || maskHas m2 13)
    (maskHas m1 14 || maskHas m2 14) (maskHas m1 15 || maskHas m2 15)
    a (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def evalM2 (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) : Fin 14 → Bool :=
  let av := evalAv ord m1 m2 a x
  let f (s : Fin 17) (v : Bool) := ((maskHas m1 s || maskHas m2 s) || v) && (!maskHas mh s || av)
  let v0 := x 0
  let v1 := x 1
  let v2 := x 2
  let v3 := x 3
  let v4 := x 4
  let v5 := x 5
  let v6 := f 0 v0 || f 1 v4
  let v7 := f 2 v4 || f 3 v5
  let v8 := f 4 v0 || f 5 v5
  let v9 := f 6 v1 && f 7 v6
  let v10 := f 8 v2 && f 9 v7
  let v11 := f 10 v3 && f 11 v8
  let a12 := match ord with | 0 => v9 | 1 => v9 | 2 => v10
  let b12 := match ord with | 0 => v10 | 1 => v11 | 2 => v11
  let c13 := match ord with | 0 => v11 | 1 => v10 | 2 => v9
  let v12 := f 12 a12 || f 13 b12
  let v13 := f 14 v12 || f 15 c13
  fun c => match c.val with
    | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3 | 4 => v4 | 5 => v5
    | 6 => v6 | 7 => v7 | 8 => v8 | 9 => v9 | 10 => v10 | 11 => v11
    | 12 => v12 | _ => v13

def evalOut2 (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) : Bool :=
  evalRow2 ord
    (maskHas m1 0 || maskHas m2 0) (maskHas m1 1 || maskHas m2 1)
    (maskHas m1 2 || maskHas m2 2) (maskHas m1 3 || maskHas m2 3)
    (maskHas m1 4 || maskHas m2 4) (maskHas m1 5 || maskHas m2 5)
    (maskHas m1 6 || maskHas m2 6) (maskHas m1 7 || maskHas m2 7)
    (maskHas m1 8 || maskHas m2 8) (maskHas m1 9 || maskHas m2 9)
    (maskHas m1 10 || maskHas m2 10) (maskHas m1 11 || maskHas m2 11)
    (maskHas m1 12 || maskHas m2 12) (maskHas m1 13 || maskHas m2 13)
    (maskHas m1 14 || maskHas m2 14) (maskHas m1 15 || maskHas m2 15)
    (maskHas m1 16 || maskHas m2 16)
    (maskHas mh 0) (maskHas mh 1) (maskHas mh 2) (maskHas mh 3)
    (maskHas mh 4) (maskHas mh 5) (maskHas mh 6) (maskHas mh 7)
    (maskHas mh 8) (maskHas mh 9) (maskHas mh 10) (maskHas mh 11)
    (maskHas mh 12) (maskHas mh 13) (maskHas mh 14) (maskHas mh 15) (maskHas mh 16)
    (evalAv ord m1 m2 a x) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

lemma evalOut2_eq_m2 (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) :
    evalOut2 ord m1 m2 mh a x =
      ((maskHas m1 16 || maskHas m2 16 || evalM2 ord m1 m2 mh a x 13) &&
        (!maskHas mh 16 || evalAv ord m1 m2 a x)) := rfl

lemma evalM3_comm (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool) :
    evalM3 ord m1 m2 x = evalM3 ord m2 m1 x := by
  unfold evalM3
  simp only [Bool.or_comm (maskHas m1 _)]

lemma evalOut3_comm (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool) :
    evalOut3 ord m1 m2 x = evalOut3 ord m2 m1 x := by
  unfold evalOut3
  rw [evalM3_comm, Bool.or_comm (maskHas m1 16)]

lemma evalAv_comm (ord : Fin 3) (m1 m2 : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) :
    evalAv ord m1 m2 a x = evalAv ord m2 m1 a x := by
  unfold evalAv
  simp only [Bool.or_comm (maskHas m1 _)]

lemma evalOut2_comm (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) :
    evalOut2 ord m1 m2 mh a x = evalOut2 ord m2 m1 mh a x := by
  unfold evalOut2
  rw [evalAv_comm]
  simp only [Bool.or_comm (maskHas m1 _)]

lemma evalOut2_of_av_true (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool)
    (hav : evalAv ord m1 m2 a x = true) :
    evalOut2 ord m1 m2 mh a x = evalOut3 ord m1 m2 x := by
  unfold evalOut2 evalOut3 evalRow2 evalM3 evalM3B
  simp only [hav, Bool.or_true, Bool.and_true]

lemma evalOut2_of_mh_zero (ord : Fin 3) (m1 m2 : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) :
    evalOut2 ord m1 m2 0 a x = evalOut3 ord m1 m2 x := by
  unfold evalOut2 evalOut3 evalRow2 evalM3 evalM3B
  simp only [maskHas_zero, Bool.not_false, Bool.true_or, Bool.and_true]

def evalM3Out (ord : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool) : Bool :=
  let v6 := b0 || b1
  let v7 := b2 || b3
  let v8 := b4 || b5
  let v9 := b6 && (b7 || v6)
  let v10 := b8 && (b9 || v7)
  let v11 := b10 && (b11 || v8)
  let a12 := if ord == 0 then v9 else if ord == 1 then v9 else v10
  let b12v := if ord == 0 then v10 else v11
  let c13 := if ord == 0 then v11 else if ord == 1 then v10 else v9
  let v12 := (b12 || a12) || (b13 || b12v)
  let v13 := (b14 || v12) || (b15 || c13)
  b16 || v13

def evalZero2 (ord : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 : Bool)
    (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  let v6 := ((b0 || x0) && !h0) || ((b1 || x4) && !h1)
  let v7 := ((b2 || x4) && !h2) || ((b3 || x5) && !h3)
  let v8 := ((b4 || x0) && !h4) || ((b5 || x5) && !h5)
  let v9 := ((b6 || x1) && !h6) && ((b7 || v6) && !h7)
  let v10 := ((b8 || x2) && !h8) && ((b9 || v7) && !h9)
  let v11 := ((b10 || x3) && !h10) && ((b11 || v8) && !h11)
  let a12 := if ord == 0 then v9 else if ord == 1 then v9 else v10
  let b12v := if ord == 0 then v10 else v11
  let c13 := if ord == 0 then v11 else if ord == 1 then v10 else v9
  let v12 := ((b12 || a12) && !h12) || ((b13 || b12v) && !h13)
  let v13 := ((b14 || v12) && !h14) || ((b15 || c13) && !h15)
  (b16 || v13) && !h16

def evalAvN (ord : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool)
    (a : Nat) (x0 x1 x2 x3 x4 x5 : Bool) : Bool :=
  if a == 0 then x0 else if a == 1 then x1 else if a == 2 then x2
  else if a == 3 then x3 else if a == 4 then x4 else if a == 5 then x5
  else if a == 14 then true else if a == 15 then false
  else
    let v6 := (b0 || x0) || (b1 || x4)
    let v7 := (b2 || x4) || (b3 || x5)
    let v8 := (b4 || x0) || (b5 || x5)
    let v9 := (b6 || x1) && (b7 || v6)
    let v10 := (b8 || x2) && (b9 || v7)
    let v11 := (b10 || x3) && (b11 || v8)
    let a12 := if ord == 0 then v9 else if ord == 1 then v9 else v10
    let b12v := if ord == 0 then v10 else v11
    let c13 := if ord == 0 then v11 else if ord == 1 then v10 else v9
    let v12 := (b12 || a12) || (b13 || b12v)
    let v13 := (b14 || v12) || (b15 || c13)
    if a == 6 then v6 else if a == 7 then v7 else if a == 8 then v8
    else if a == 9 then v9 else if a == 10 then v10 else if a == 11 then v11
    else if a == 12 then v12 else v13

lemma evalM3Out_eq (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool) :
    evalM3Out ord.val b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 =
      (b16 || evalM3B ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
        false false false false false false 13) := by
  fin_cases ord <;> simp only [evalM3Out, evalM3B, Bool.or_false] <;> rfl

lemma evalZero2_eq (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool)
    (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 : Bool)
    (x0 x1 x2 x3 x4 x5 : Bool) :
    evalZero2 ord.val b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 x0 x1 x2 x3 x4 x5 =
      evalRow2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
        h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false x0 x1 x2 x3 x4 x5 := by
  fin_cases ord <;> simp only [evalZero2, evalRow2, Bool.or_false] <;> rfl

lemma evalAvN_eq (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool)
    (a : Fin 16) (x0 x1 x2 x3 x4 x5 : Bool) :
    evalAvN ord.val b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a.val x0 x1 x2 x3 x4 x5 =
      evalAvB ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a x0 x1 x2 x3 x4 x5 := by
  fin_cases ord <;> fin_cases a <;> rfl

def bLe (u v : Bool) : Prop := u = true → v = true

lemma bLe_refl (u : Bool) : bLe u u := id

lemma bLe_or_false (b x : Bool) : bLe (b || false) (b || x) := by
  cases b <;> cases x <;> simp [bLe]

lemma bLe_or {a b c d : Bool} (h1 : bLe a c) (h2 : bLe b d) : bLe (a || b) (c || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [bLe]

lemma bLe_and {a b c d : Bool} (h1 : bLe a c) (h2 : bLe b d) : bLe (a && b) (c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [bLe]

lemma evalM3B_mono (ord : Fin 3)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool)
    (x0 x1 x2 x3 x4 x5 : Bool) :
    bLe (evalM3B ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          false false false false false false 13)
        (evalM3B ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
          x0 x1 x2 x3 x4 x5 13) := by
  have hv6 := bLe_or (bLe_or_false b0 x0) (bLe_or_false b1 x4)
  have hv7 := bLe_or (bLe_or_false b2 x4) (bLe_or_false b3 x5)
  have hv8 := bLe_or (bLe_or_false b4 x0) (bLe_or_false b5 x5)
  have hv9 := bLe_and (bLe_or_false b6 x1) (bLe_or (bLe_refl b7) hv6)
  have hv10 := bLe_and (bLe_or_false b8 x2) (bLe_or (bLe_refl b9) hv7)
  have hv11 := bLe_and (bLe_or_false b10 x3) (bLe_or (bLe_refl b11) hv8)
  fin_cases ord
  · exact bLe_or (bLe_or (bLe_refl b14) (bLe_or (bLe_or (bLe_refl b12) hv9) (bLe_or (bLe_refl b13) hv10)))
      (bLe_or (bLe_refl b15) hv11)
  · exact bLe_or (bLe_or (bLe_refl b14) (bLe_or (bLe_or (bLe_refl b12) hv9) (bLe_or (bLe_refl b13) hv11)))
      (bLe_or (bLe_refl b15) hv10)
  · exact bLe_or (bLe_or (bLe_refl b14) (bLe_or (bLe_or (bLe_refl b12) hv10) (bLe_or (bLe_refl b13) hv11)))
      (bLe_or (bLe_refl b15) hv9)

lemma evalOut3_mono (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool)
    (h0 : evalOut3 ord m1 m2 (rowInput 0) = true) :
    evalOut3 ord m1 m2 x = true := by
  unfold evalOut3 evalM3 at h0 ⊢
  exact bLe_or (bLe_refl _) (evalM3B_mono ord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) h0

lemma evalOut2_eq_or (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool)
    (ho3 : evalOut3 ord m1 m2 (rowInput 0) = true) :
    evalOut2 ord m1 m2 mh a x =
      (evalZero2 ord.val
        (maskHasN m1.val 0 || maskHasN m2.val 0) (maskHasN m1.val 1 || maskHasN m2.val 1)
        (maskHasN m1.val 2 || maskHasN m2.val 2) (maskHasN m1.val 3 || maskHasN m2.val 3)
        (maskHasN m1.val 4 || maskHasN m2.val 4) (maskHasN m1.val 5 || maskHasN m2.val 5)
        (maskHasN m1.val 6 || maskHasN m2.val 6) (maskHasN m1.val 7 || maskHasN m2.val 7)
        (maskHasN m1.val 8 || maskHasN m2.val 8) (maskHasN m1.val 9 || maskHasN m2.val 9)
        (maskHasN m1.val 10 || maskHasN m2.val 10) (maskHasN m1.val 11 || maskHasN m2.val 11)
        (maskHasN m1.val 12 || maskHasN m2.val 12) (maskHasN m1.val 13 || maskHasN m2.val 13)
        (maskHasN m1.val 14 || maskHasN m2.val 14) (maskHasN m1.val 15 || maskHasN m2.val 15)
        (maskHasN m1.val 16 || maskHasN m2.val 16)
        (maskHasN mh.val 0) (maskHasN mh.val 1) (maskHasN mh.val 2) (maskHasN mh.val 3)
        (maskHasN mh.val 4) (maskHasN mh.val 5) (maskHasN mh.val 6) (maskHasN mh.val 7)
        (maskHasN mh.val 8) (maskHasN mh.val 9) (maskHasN mh.val 10) (maskHasN mh.val 11)
        (maskHasN mh.val 12) (maskHasN mh.val 13) (maskHasN mh.val 14) (maskHasN mh.val 15)
        (maskHasN mh.val 16)
        (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) ||
      evalAvN ord.val
        (maskHasN m1.val 0 || maskHasN m2.val 0) (maskHasN m1.val 1 || maskHasN m2.val 1)
        (maskHasN m1.val 2 || maskHasN m2.val 2) (maskHasN m1.val 3 || maskHasN m2.val 3)
        (maskHasN m1.val 4 || maskHasN m2.val 4) (maskHasN m1.val 5 || maskHasN m2.val 5)
        (maskHasN m1.val 6 || maskHasN m2.val 6) (maskHasN m1.val 7 || maskHasN m2.val 7)
        (maskHasN m1.val 8 || maskHasN m2.val 8) (maskHasN m1.val 9 || maskHasN m2.val 9)
        (maskHasN m1.val 10 || maskHasN m2.val 10) (maskHasN m1.val 11 || maskHasN m2.val 11)
        (maskHasN m1.val 12 || maskHasN m2.val 12) (maskHasN m1.val 13 || maskHasN m2.val 13)
        (maskHasN m1.val 14 || maskHasN m2.val 14) (maskHasN m1.val 15 || maskHasN m2.val 15)
        a.val (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)) := by
  cases hav : evalAv ord m1 m2 a x with
  | true =>
    have h1 := evalOut2_of_av_true ord m1 m2 mh a x hav
    have h2 := evalOut3_mono ord m1 m2 x ho3
    rw [h1, h2, evalAvN_eq]
    change true = (_ || evalAv ord m1 m2 a x)
    rw [hav, Bool.or_true]
  | false =>
    rw [evalAvN_eq]
    change evalOut2 ord m1 m2 mh a x = (_ || evalAv ord m1 m2 a x)
    rw [hav, Bool.or_false]
    unfold evalOut2
    rw [hav]
    exact (evalZero2_eq ord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

def checkA (ord : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool)
    (z1 z2 z11 z12 : Bool) (a : Nat) : Bool :=
  if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false false false false false then true
  else if !z1 && !evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false true false false false false then true
  else if !z2 && !evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false false false false true then true
  else if !z11 && !evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a true false false true false false then true
  else if !z12 && !evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false true false true false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a true false false false false false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false true false false false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false false true false false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false false false true false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a true false false false true false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a true false true false false false then true
  else if evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false true true false false then true
  else evalAvN ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 a false false false true true false

def checkMh (ord : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool)
    (mh : Nat) : Bool :=
  if mh == 0 then true
  else
    let h0 := maskHasN mh 0; let h1 := maskHasN mh 1; let h2 := maskHasN mh 2; let h3 := maskHasN mh 3
    let h4 := maskHasN mh 4; let h5 := maskHasN mh 5; let h6 := maskHasN mh 6; let h7 := maskHasN mh 7
    let h8 := maskHasN mh 8; let h9 := maskHasN mh 9; let h10 := maskHasN mh 10; let h11 := maskHasN mh 11
    let h12 := maskHasN mh 12; let h13 := maskHasN mh 13; let h14 := maskHasN mh 14; let h15 := maskHasN mh 15
    let h16 := maskHasN mh 16
    if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false false false false false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 true false false false false false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false true false false false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false false true false false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false false false true false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 true false false false true false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 true false true false false false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false true true false false then true
    else if evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false false true true false then true
    else
      let z1 := evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false true false false false false
      let z2 := evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false false false false true
      let z11 := evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 true false false true false false
      let z12 := evalZero2 ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 false false true false true false
      allNat 16 (checkA ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 z1 z2 z11 z12)

def checkPair (ord m1 m2 : Nat) : Bool :=
  if m2 < m1 then true
  else
    let b0 := maskHasN m1 0 || maskHasN m2 0
    let b1 := maskHasN m1 1 || maskHasN m2 1
    let b2 := maskHasN m1 2 || maskHasN m2 2
    let b3 := maskHasN m1 3 || maskHasN m2 3
    let b4 := maskHasN m1 4 || maskHasN m2 4
    let b5 := maskHasN m1 5 || maskHasN m2 5
    let b6 := maskHasN m1 6 || maskHasN m2 6
    let b7 := maskHasN m1 7 || maskHasN m2 7
    let b8 := maskHasN m1 8 || maskHasN m2 8
    let b9 := maskHasN m1 9 || maskHasN m2 9
    let b10 := maskHasN m1 10 || maskHasN m2 10
    let b11 := maskHasN m1 11 || maskHasN m2 11
    let b12 := maskHasN m1 12 || maskHasN m2 12
    let b13 := maskHasN m1 13 || maskHasN m2 13
    let b14 := maskHasN m1 14 || maskHasN m2 14
    let b15 := maskHasN m1 15 || maskHasN m2 15
    let b16 := maskHasN m1 16 || maskHasN m2 16
    if !evalM3Out ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 then true
    else allNat 21 (checkMh ord b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16)

def checkOrd (ord : Nat) : Bool :=
  allNat 21 fun m1 => allNat 21 fun m2 => checkPair ord m1 m2

lemma checkOrd_0 : checkOrd 0 = true := by decide +kernel
lemma checkOrd_1 : checkOrd 1 = true := by decide +kernel
lemma checkOrd_2 : checkOrd 2 = true := by decide +kernel

lemma checkOrd_all (ord : Fin 3) : checkOrd ord.val = true := by
  fin_cases ord
  · exact checkOrd_0
  · exact checkOrd_1
  · exact checkOrd_2

lemma step3_no_solution (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16)
    (ho3 : evalOut3 ord m1 m2 (rowInput 0) = true)
    (ho2 : ∀ r : Fin 13, evalOut2 ord m1 m2 mh a (rowInput r) = rowTarget r) : False := by
  have wlog_le : ∀ (p1 p2 : Fin 21), p1.val ≤ p2.val →
      evalOut3 ord p1 p2 (rowInput 0) = true →
      (∀ r : Fin 13, evalOut2 ord p1 p2 mh a (rowInput r) = rowTarget r) → False := by
    intro p1 p2 hle hp3 hp2
    by_cases hmh0 : mh.val = 0
    · have hmh : mh = 0 := Fin.ext hmh0
      subst hmh
      have h0 := hp2 0
      rw [evalOut2_of_mh_zero, hp3] at h0
      exact Bool.noConfusion h0
    · have hchk := allNat_true 21 _ (allNat_true 21 _ (checkOrd_all ord) p1.val p1.isLt) p2.val p2.isLt
      unfold checkPair at hchk
      have hnotlt : ¬ p2.val < p1.val := by omega
      rw [if_neg hnotlt] at hchk
      dsimp only at hchk
      have hp3' : evalM3Out ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          (maskHasN p1.val 16 || maskHasN p2.val 16) = true := by
        rw [evalM3Out_eq]; exact hp3
      rw [hp3'] at hchk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hchk
      have hmh_chk := allNat_true 21 _ hchk mh.val mh.isLt
      unfold checkMh at hmh_chk
      have hne0 : (mh.val == 0) = false := beq_false_of_ne hmh0
      rw [hne0] at hmh_chk
      simp only [Bool.false_eq_true, ↓reduceIte] at hmh_chk
      have hrow : ∀ r : Fin 13,
          (evalZero2 ord.val
            (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
            (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
            (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
            (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
            (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
            (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
            (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
            (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
            (maskHasN p1.val 16 || maskHasN p2.val 16)
            (maskHasN mh.val 0) (maskHasN mh.val 1) (maskHasN mh.val 2) (maskHasN mh.val 3)
            (maskHasN mh.val 4) (maskHasN mh.val 5) (maskHasN mh.val 6) (maskHasN mh.val 7)
            (maskHasN mh.val 8) (maskHasN mh.val 9) (maskHasN mh.val 10) (maskHasN mh.val 11)
            (maskHasN mh.val 12) (maskHasN mh.val 13) (maskHasN mh.val 14) (maskHasN mh.val 15)
            (maskHasN mh.val 16)
            (rowInput r 0) (rowInput r 1) (rowInput r 2) (rowInput r 3) (rowInput r 4) (rowInput r 5) ||
          evalAvN ord.val
            (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
            (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
            (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
            (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
            (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
            (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
            (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
            (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
            a.val (rowInput r 0) (rowInput r 1) (rowInput r 2) (rowInput r 3) (rowInput r 4) (rowInput r 5)) = rowTarget r := by
        intro r
        rw [← evalOut2_eq_or ord p1 p2 mh a (rowInput r) hp3]
        exact hp2 r
      have hr0 := Bool.or_eq_false_iff.mp (hrow 0)
      have hr3 := Bool.or_eq_false_iff.mp (hrow 3)
      have hr4 := Bool.or_eq_false_iff.mp (hrow 4)
      have hr5 := Bool.or_eq_false_iff.mp (hrow 5)
      have hr6 := Bool.or_eq_false_iff.mp (hrow 6)
      have hr7 := Bool.or_eq_false_iff.mp (hrow 7)
      have hr8 := Bool.or_eq_false_iff.mp (hrow 8)
      have hr9 := Bool.or_eq_false_iff.mp (hrow 9)
      have hr10 := Bool.or_eq_false_iff.mp (hrow 10)
      have hr1 := hrow 1
      have hr2 := hrow 2
      have hr11 := hrow 11
      have hr12 := hrow 12
      have hv0 : (0 : Fin 6).val = 0 := rfl
      have hv1 : (1 : Fin 6).val = 1 := rfl
      have hv2 : (2 : Fin 6).val = 2 := rfl
      have hv3 : (3 : Fin 6).val = 3 := rfl
      have hv4 : (4 : Fin 6).val = 4 := rfl
      have hv5 : (5 : Fin 6).val = 5 := rfl
      simp only [rowInput, rowTarget, hv0, hv1, hv2, hv3, hv4, hv5] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12
      rw [hr0.1, hr3.1, hr4.1, hr5.1, hr6.1, hr7.1, hr8.1, hr9.1, hr10.1] at hmh_chk
      simp only [Bool.false_eq_true, ↓reduceIte] at hmh_chk
      have ha_chk := allNat_true 16 _ hmh_chk a.val a.isLt
      unfold checkA at ha_chk
      rw [hr0.2, hr3.2, hr4.2, hr5.2, hr6.2, hr7.2, hr8.2, hr9.2, hr10.2] at ha_chk
      have hnt1 : (!evalZero2 ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          (maskHasN p1.val 16 || maskHasN p2.val 16)
          (maskHasN mh.val 0) (maskHasN mh.val 1) (maskHasN mh.val 2) (maskHasN mh.val 3)
          (maskHasN mh.val 4) (maskHasN mh.val 5) (maskHasN mh.val 6) (maskHasN mh.val 7)
          (maskHasN mh.val 8) (maskHasN mh.val 9) (maskHasN mh.val 10) (maskHasN mh.val 11)
          (maskHasN mh.val 12) (maskHasN mh.val 13) (maskHasN mh.val 14) (maskHasN mh.val 15)
          (maskHasN mh.val 16) false true false false false false &&
        !evalAvN ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          a.val false true false false false false) = false := by
        rw [← Bool.not_or, hr1]; rfl
      have hnt2 : (!evalZero2 ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          (maskHasN p1.val 16 || maskHasN p2.val 16)
          (maskHasN mh.val 0) (maskHasN mh.val 1) (maskHasN mh.val 2) (maskHasN mh.val 3)
          (maskHasN mh.val 4) (maskHasN mh.val 5) (maskHasN mh.val 6) (maskHasN mh.val 7)
          (maskHasN mh.val 8) (maskHasN mh.val 9) (maskHasN mh.val 10) (maskHasN mh.val 11)
          (maskHasN mh.val 12) (maskHasN mh.val 13) (maskHasN mh.val 14) (maskHasN mh.val 15)
          (maskHasN mh.val 16) false false false false false true &&
        !evalAvN ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          a.val false false false false false true) = false := by
        rw [← Bool.not_or, hr2]; rfl
      have hnt11 : (!evalZero2 ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          (maskHasN p1.val 16 || maskHasN p2.val 16)
          (maskHasN mh.val 0) (maskHasN mh.val 1) (maskHasN mh.val 2) (maskHasN mh.val 3)
          (maskHasN mh.val 4) (maskHasN mh.val 5) (maskHasN mh.val 6) (maskHasN mh.val 7)
          (maskHasN mh.val 8) (maskHasN mh.val 9) (maskHasN mh.val 10) (maskHasN mh.val 11)
          (maskHasN mh.val 12) (maskHasN mh.val 13) (maskHasN mh.val 14) (maskHasN mh.val 15)
          (maskHasN mh.val 16) true false false true false false &&
        !evalAvN ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          a.val true false false true false false) = false := by
        rw [← Bool.not_or, hr11]; rfl
      have hnt12 : (!evalZero2 ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          (maskHasN p1.val 16 || maskHasN p2.val 16)
          (maskHasN mh.val 0) (maskHasN mh.val 1) (maskHasN mh.val 2) (maskHasN mh.val 3)
          (maskHasN mh.val 4) (maskHasN mh.val 5) (maskHasN mh.val 6) (maskHasN mh.val 7)
          (maskHasN mh.val 8) (maskHasN mh.val 9) (maskHasN mh.val 10) (maskHasN mh.val 11)
          (maskHasN mh.val 12) (maskHasN mh.val 13) (maskHasN mh.val 14) (maskHasN mh.val 15)
          (maskHasN mh.val 16) false false true false true false &&
        !evalAvN ord.val
          (maskHasN p1.val 0 || maskHasN p2.val 0) (maskHasN p1.val 1 || maskHasN p2.val 1)
          (maskHasN p1.val 2 || maskHasN p2.val 2) (maskHasN p1.val 3 || maskHasN p2.val 3)
          (maskHasN p1.val 4 || maskHasN p2.val 4) (maskHasN p1.val 5 || maskHasN p2.val 5)
          (maskHasN p1.val 6 || maskHasN p2.val 6) (maskHasN p1.val 7 || maskHasN p2.val 7)
          (maskHasN p1.val 8 || maskHasN p2.val 8) (maskHasN p1.val 9 || maskHasN p2.val 9)
          (maskHasN p1.val 10 || maskHasN p2.val 10) (maskHasN p1.val 11 || maskHasN p2.val 11)
          (maskHasN p1.val 12 || maskHasN p2.val 12) (maskHasN p1.val 13 || maskHasN p2.val 13)
          (maskHasN p1.val 14 || maskHasN p2.val 14) (maskHasN p1.val 15 || maskHasN p2.val 15)
          a.val false false true false true false) = false := by
        rw [← Bool.not_or, hr12]; rfl
      rw [hnt1, hnt2, hnt11, hnt12] at ha_chk
      simp at ha_chk
  by_cases hle : m1.val ≤ m2.val
  · exact wlog_le m1 m2 hle ho3 ho2
  · exact wlog_le m2 m1 (by omega) (evalOut3_comm ord m1 m2 (rowInput 0) ▸ ho3)
      (fun r => evalOut2_comm ord m1 m2 mh a (rowInput r) ▸ ho2 r)

def slotWire (ord : Fin 3) (s : Fin 17) : Fin 14 :=
  if hs : s.val < 16 then
    if s.val % 2 = 0 then canonL ord ⟨s.val / 2, by omega⟩
    else canonR ord ⟨s.val / 2, by omega⟩
  else 13

def uniqueSlot (ord : Fin 3) (u : Fin 14) : Fin 17 :=
  match u.val with
  | 1 => 6 | 2 => 8 | 3 => 10
  | 6 => 7 | 7 => 9 | 8 => 11
  | 9 => match ord with | 0 => 12 | 1 => 12 | 2 => 15
  | 10 => match ord with | 0 => 13 | 1 => 15 | 2 => 12
  | 11 => match ord with | 0 => 15 | 1 => 13 | 2 => 13
  | 12 => 14 | 13 => 16 | _ => 0

lemma slotWire_char : ∀ (ord : Fin 3) (s : Fin 17),
    (slotWire ord s = 0 → s = 0 ∨ s = 4) ∧
    (slotWire ord s = 4 → s = 1 ∨ s = 2) ∧
    (slotWire ord s = 5 → s = 3 ∨ s = 5) ∧
    (∀ u : Fin 14, u ≠ 0 → u ≠ 4 → u ≠ 5 → slotWire ord s = u → s = uniqueSlot ord u) := by
  decide

lemma exists_mask_of_slotWire (ord : Fin 3) (u : Fin 14) (P : Fin 17 → Bool)
    (hP : ∀ s : Fin 17, P s = true → slotWire ord s = u) :
    ∃ m : Fin 21, ∀ s : Fin 17, maskHas m s = P s := by
  have single_mk : ∀ (s0 : Fin 17), (∀ s : Fin 17, P s = true → s = s0) →
      ∃ m : Fin 21, ∀ s : Fin 17, maskHas m s = P s := by
    intro s0 honly
    cases hp0 : P s0 with
    | false =>
      refine ⟨0, fun s => ?_⟩
      rw [maskHas_zero]
      cases hps : P s with
      | false => rfl
      | true => rw [honly s hps, hp0] at hps; exact Bool.noConfusion hps
    | true =>
      refine ⟨⟨s0.val + 1, by have := s0.isLt; omega⟩, fun s => ?_⟩
      rw [maskHas_single s0 s]
      by_cases hs : s = s0
      · subst hs; simp [hp0]
      · have hps : P s = false := by
          cases h : P s with
          | false => rfl
          | true => exact (hs (honly s h)).elim
        rw [hps]; simp only [decide_eq_false_iff_not]; exact fun h => hs (Fin.ext h)
  have pair_mk : ∀ (s1 s2 : Fin 17) (mp : Fin 21),
      (∀ s, maskHas mp s = decide (s.val = s1.val ∨ s.val = s2.val)) →
      (∀ s, P s = true → s = s1 ∨ s = s2) →
      ∃ m : Fin 21, ∀ s : Fin 17, maskHas m s = P s := by
    intro s1 s2 mp hmp hpair
    cases hp1 : P s1 <;> cases hp2 : P s2
    · refine ⟨0, fun s => ?_⟩
      rw [maskHas_zero]
      cases hps : P s with
      | false => rfl
      | true => rcases hpair s hps with rfl | rfl <;> simp_all
    · exact single_mk s2 (fun s hs => (hpair s hs).resolve_left (fun h => by rw [h, hp1] at hs; exact Bool.noConfusion hs))
    · exact single_mk s1 (fun s hs => (hpair s hs).resolve_right (fun h => by rw [h, hp2] at hs; exact Bool.noConfusion hs))
    · refine ⟨mp, fun s => ?_⟩
      rw [hmp s]
      by_cases hs : s = s1 ∨ s = s2
      · rcases hs with rfl | rfl
        · rw [hp1]; simp
        · rw [hp2]; simp
      · have hps : P s = false := by
          cases h : P s with
          | false => rfl
          | true => exact (hs (hpair s h)).elim
        rw [hps]; simp only [decide_eq_false_iff_not, not_or]
        exact ⟨fun h => hs (Or.inl (Fin.ext h)), fun h => hs (Or.inr (Fin.ext h))⟩
  by_cases hu0 : u = 0
  · subst hu0; exact pair_mk 0 4 18 maskHas_18 (fun s hs => (slotWire_char ord s).1 (hP s hs))
  · by_cases hu4 : u = 4
    · subst hu4; exact pair_mk 1 2 19 maskHas_19 (fun s hs => (slotWire_char ord s).2.1 (hP s hs))
    · by_cases hu5 : u = 5
      · subst hu5; exact pair_mk 3 5 20 maskHas_20 (fun s hs => (slotWire_char ord s).2.2.1 (hP s hs))
      · exact single_mk (uniqueSlot ord u) (fun s hs => (slotWire_char ord s).2.2.2 u hu0 hu4 hu5 (hP s hs))

lemma evalM3_in (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool) (i : Fin 6) :
    evalM3 ord m1 m2 x ⟨i.val, by have := i.isLt; omega⟩ = x i := by
  fin_cases i <;> rfl

lemma evalM2_in (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) (i : Fin 6) :
    evalM2 ord m1 m2 mh a x ⟨i.val, by have := i.isLt; omega⟩ = x i := by
  fin_cases i <;> rfl

lemma evalM3_gate_step (ord : Fin 3) (m1 m2 : Fin 21) (x : Fin 6 → Bool) (c : Fin 8) :
    evalM3 ord m1 m2 x ⟨6 + c.val, by omega⟩ =
      (canonOp c).eval
        [(maskHas m1 ⟨2 * c.val, by omega⟩ || maskHas m2 ⟨2 * c.val, by omega⟩ ||
            evalM3 ord m1 m2 x (canonL ord c)),
         (maskHas m1 ⟨2 * c.val + 1, by omega⟩ || maskHas m2 ⟨2 * c.val + 1, by omega⟩ ||
            evalM3 ord m1 m2 x (canonR ord c))] := by
  fin_cases c <;> fin_cases ord <;> simp [evalM3, evalM3B, canonOp, canonL, canonR, GateOp.eval]

lemma evalM2_gate_step (ord : Fin 3) (m1 m2 mh : Fin 21) (a : Fin 16) (x : Fin 6 → Bool) (c : Fin 8) :
    evalM2 ord m1 m2 mh a x ⟨6 + c.val, by omega⟩ =
      (canonOp c).eval
        [((maskHas m1 ⟨2 * c.val, by omega⟩ || maskHas m2 ⟨2 * c.val, by omega⟩ ||
            evalM2 ord m1 m2 mh a x (canonL ord c)) &&
          (!maskHas mh ⟨2 * c.val, by omega⟩ || evalAv ord m1 m2 a x)),
         ((maskHas m1 ⟨2 * c.val + 1, by omega⟩ || maskHas m2 ⟨2 * c.val + 1, by omega⟩ ||
            evalM2 ord m1 m2 mh a x (canonR ord c)) &&
          (!maskHas mh ⟨2 * c.val + 1, by omega⟩ || evalAv ord m1 m2 a x))] := by
  fin_cases c <;> fin_cases ord <;> simp [evalM2, canonOp, canonL, canonR, GateOp.eval]

lemma canonL_lt (ord : Fin 3) (q : Fin 8) : (canonL ord q).val < 6 + q.val := by
  fin_cases q <;> fin_cases ord <;> decide

lemma canonR_lt (ord : Fin 3) (q : Fin 8) : (canonR ord q).val < 6 + q.val := by
  fin_cases q <;> fin_cases ord <;> decide

lemma slotWire_even (ord : Fin 3) (q : Fin 8) :
    slotWire ord ⟨2 * q.val, by have := q.isLt; omega⟩ = canonL ord q := by
  fin_cases q <;> fin_cases ord <;> decide

lemma slotWire_odd (ord : Fin 3) (q : Fin 8) :
    slotWire ord ⟨2 * q.val + 1, by have := q.isLt; omega⟩ = canonR ord q := by
  fin_cases q <;> fin_cases ord <;> decide

lemma origWire_in_lt8 (emitInv : Fin 8 → Fin 11) (i : Fin 6) :
    origWire emitInv ⟨i.val, by have := i.isLt; omega⟩ < 8 ∧
    1 ≤ origWire emitInv ⟨i.val, by have := i.isLt; omega⟩ := by
  fin_cases i <;> simp [origWire]

lemma origWire_ne_bad (emitInv : Fin 8 → Fin 11) (b : Fin 11)
    (hdisj : ∀ q : Fin 8, emitInv q ≠ b) (u : Fin 14) :
    origWire emitInv u ≠ 8 + b.val := by
  by_cases hu : u.val < 6
  · have hlt : origWire emitInv u < 8 := by
      have hu' : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 ∨ u.val = 4 ∨ u.val = 5 := by omega
      rcases hu' with h | h | h | h | h | h <;> simp [origWire, h]
    omega
  · let q : Fin 8 := ⟨u.val - 6, by have := u.isLt; omega⟩
    have huq : u.val = q.val + 6 := by dsimp [q]; omega
    unfold origWire
    rw [huq]
    simp only [q.isLt, ↓reduceDIte]
    intro h
    change 8 + (emitInv q).val = 8 + b.val at h
    exact hdisj q (Fin.ext (by omega))

lemma lift6T_in_val (x : Fin 6 → Bool) (i : Fin 6) (emitInv : Fin 8 → Fin 11) :
    (List.ofFn (lift6T x)).getD (origWire emitInv ⟨i.val, by omega⟩ - 1) false = x i ∧
    (true :: List.ofFn (lift6T x)).getD (origWire emitInv ⟨i.val, by omega⟩) false = x i := by
  fin_cases i <;> simp [origWire, lift6T]

lemma sideA_impossible (x2 x3 : Circuit) (x4 x5 : ℕ)
    (hfan : FanInTwo x2) (hsz : x2.size = 11)
    (heval2 : circuitFun 7 x2 = thetaFun)
    (hedit : List.Forall₂ (EditGate x4 x5) x2.gates x3.gates)
    (heval3 : ∀ x : Fin 7 → Bool, (x3.wires (true :: List.ofFn x)).getD (x2.output + 1) false = (thetaFun x || x 2))
    (D : ElimData x2 x3 x4 x5)
    (hSideA : SideNoTopBranch D.ms sideA) : False := by
  classical
  have hlen2 : x2.gates.length = 11 := hsz
  have hlen3 : x3.gates.length = 11 := hedit.length_eq.symm.trans hlen2
  have hed : ∀ k : Fin 11, EditGate x4 x5 (x2.gates[k.val]'(by omega)) (x3.gates[k.val]'(by omega)) :=
    fun k => forall2_getElem hedit k.val (by omega) (by omega)
  obtain ⟨ord, π, hπ_in, hπ_out, hπ_gate, hπ_spec⟩ :=
    canon_iso D.hms_len D.outM D.hleast D.hmono hSideA
  let qOf (c : Fin 8) : Fin 8 := ⟨(π ⟨6 + c.val, by omega⟩).val - 6, by
    have := (π ⟨6 + c.val, by omega⟩).isLt; have := hπ_gate c; omega⟩
  let kOf (c : Fin 8) : Fin 11 := D.emitInv (qOf c)
  have horig_gate : ∀ c : Fin 8, origWire D.emitInv (π ⟨6 + c.val, by omega⟩) = 8 + (kOf c).val := by
    intro c
    have h6 := hπ_gate c
    have hlt := (π ⟨6 + c.val, by omega⟩).isLt
    have heq : (π ⟨6 + c.val, by omega⟩).val = (qOf c).val + 6 := by dsimp [qOf]; omega
    unfold origWire
    rw [heq]
    simp only [(qOf c).isLt, ↓reduceDIte]
    rfl
  have horig_in : ∀ i : Fin 6, origWire D.emitInv (π ⟨i.val, by omega⟩) = origWire D.emitInv ⟨i.val, by omega⟩ := by
    intro i; rw [hπ_in i]
  have hgate_data : ∀ c : Fin 8, ∃ iL iR : ℕ,
      1 ≤ iL ∧ 1 ≤ iR ∧
      iL < 8 + (kOf c).val ∧ iR < 8 + (kOf c).val ∧
      D.st.getD iL (Stat.const false) = Stat.wire (π (canonL ord c)).val ∧
      D.st.getD iR (Stat.const false) = Stat.wire (π (canonR ord c)).val ∧
      (∀ w : List Bool, (x3.gates[(kOf c).val]'(by omega)).op.eval
          ((x3.gates[(kOf c).val]'(by omega)).inputs.map fun i => w.getD i false) =
        (canonOp c).eval [w.getD iL false, w.getD iR false]) ∧
      (∀ w : List Bool, (x2.gates[(kOf c).val]'(by omega)).op.eval
          ((x2.gates[(kOf c).val]'(by omega)).inputs.map fun i => w.getD i false) =
        (canonOp c).eval [w.getD (iL - 1) false, w.getD (iR - 1) false]) := by
    intro c
    obtain ⟨mg, hmg, hop, hmin⟩ := hπ_spec c
    have hmg' : D.ms[(qOf c).val]? = some mg := hmg
    have hg2? : x2.gates[(kOf c).val]? = some (x2.gates[(kOf c).val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hg3? : x3.gates[(kOf c).val]? = some (x3.gates[(kOf c).val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨hop2, hop3, i1, i2, j1, j2, h2in, h3in, hmgin, hi1lt, hi2lt, hst1, hst2⟩ :=
      D.hemit_gate (qOf c) _ _ mg hg2? hg3? hmg'
    rw [hmgin] at hmin
    have hop_or_and : canonOp c = GateOp.and ∨ canonOp c = GateOp.or := by fin_cases c <;> simp [canonOp]
    rcases hmin with hlr | hrl
    · simp only [List.cons.injEq, and_true] at hlr
      refine ⟨i1 + 1, i2 + 1, by omega, by omega, hi1lt, hi2lt, hlr.1 ▸ hst1, hlr.2 ▸ hst2, ?_, ?_⟩
      · intro w; rw [hop3, hop, h3in]; rfl
      · intro w; rw [hop2, hop, h2in]; simp
    · simp only [List.cons.injEq, and_true] at hrl
      refine ⟨i2 + 1, i1 + 1, by omega, by omega, hi2lt, hi1lt, hrl.2 ▸ hst2, hrl.1 ▸ hst1, ?_, ?_⟩
      · intro w; rw [hop3, hop, h3in]
        rcases hop_or_and with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
      · intro w; rw [hop2, hop, h2in]
        rcases hop_or_and with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
  let inL (c : Fin 8) : ℕ := (hgate_data c).choose
  let inR (c : Fin 8) : ℕ := (hgate_data c).choose_spec.choose
  have hin_spec : ∀ c : Fin 8,
      1 ≤ inL c ∧ 1 ≤ inR c ∧
      inL c < 8 + (kOf c).val ∧ inR c < 8 + (kOf c).val ∧
      D.st.getD (inL c) (Stat.const false) = Stat.wire (π (canonL ord c)).val ∧
      D.st.getD (inR c) (Stat.const false) = Stat.wire (π (canonR ord c)).val ∧
      (∀ w : List Bool, (x3.gates[(kOf c).val]'(by omega)).op.eval
          ((x3.gates[(kOf c).val]'(by omega)).inputs.map fun i => w.getD i false) =
        (canonOp c).eval [w.getD (inL c) false, w.getD (inR c) false]) ∧
      (∀ w : List Bool, (x2.gates[(kOf c).val]'(by omega)).op.eval
          ((x2.gates[(kOf c).val]'(by omega)).inputs.map fun i => w.getD i false) =
        (canonOp c).eval [w.getD (inL c - 1) false, w.getD (inR c - 1) false]) :=
    fun c => (hgate_data c).choose_spec.choose_spec
  let slotX3 (s : Fin 17) : ℕ :=
    if hs : s.val < 16 then
      if s.val % 2 = 0 then inL ⟨s.val / 2, by omega⟩
      else inR ⟨s.val / 2, by omega⟩
    else x2.output + 1
  have hslotX3_even : ∀ q : Fin 8, slotX3 ⟨2 * q.val, by have := q.isLt; omega⟩ = inL q := by
    intro q; dsimp [slotX3]
    have h1 : 2 * q.val < 16 := by have := q.isLt; omega
    have h2 : (2 * q.val) % 2 = 0 := by omega
    rw [dif_pos h1, if_pos h2]
    congr 1; exact Fin.ext (by dsimp; omega)
  have hslotX3_odd : ∀ q : Fin 8, slotX3 ⟨2 * q.val + 1, by have := q.isLt; omega⟩ = inR q := by
    intro q; dsimp [slotX3]
    have h1 : 2 * q.val + 1 < 16 := by have := q.isLt; omega
    have h2 : ¬ (2 * q.val + 1) % 2 = 0 := by omega
    rw [dif_pos h1, ite_eq_right_iff.mpr (fun h => (h2 h).elim)]
    congr 1; exact Fin.ext (by dsimp; omega)
  have hslot_st : ∀ s : Fin 17,
      D.st.getD (slotX3 s) (Stat.const false) = Stat.wire (π (slotWire ord s)).val := by
    intro s
    unfold slotX3 slotWire
    by_cases hs : s.val < 16
    · simp only [hs, ↓reduceDIte]
      by_cases hev : s.val % 2 = 0
      · simp only [hev, ↓reduceIte]; exact (hin_spec ⟨s.val / 2, by omega⟩).2.2.2.2.1
      · simp only [hev, ↓reduceIte]; exact (hin_spec ⟨s.val / 2, by omega⟩).2.2.2.2.2.1
    · simp only [hs, ↓reduceDIte, hπ_out]; exact D.hout_st
  have hslot_cases : ∀ s : Fin 17,
      slotX3 s = origWire D.emitInv (π (slotWire ord s)) ∨
      slotX3 s = 8 + D.g1.val ∨ slotX3 s = 8 + D.g2.val ∨ slotX3 s = 8 + D.h.val :=
    fun s => D.hst_wire_cases (slotX3 s) (π (slotWire ord s)) (hslot_st s)
  let P1 (s : Fin 17) : Bool := decide (slotX3 s = 8 + D.g1.val ∨ (D.w3 = 8 + D.g1.val ∧ slotX3 s = 8 + D.h.val))
  let P2 (s : Fin 17) : Bool := decide (slotX3 s = 8 + D.g2.val ∨ (D.w3 = 8 + D.g2.val ∧ slotX3 s = 8 + D.h.val))
  let Ph (s : Fin 17) : Bool := decide (slotX3 s = 8 + D.h.val)
  have mk_mask : ∀ (P : Fin 17 → Bool) (tgt : ℕ),
      (∀ s, P s = true → D.st.getD tgt (Stat.const false) = D.st.getD (slotX3 s) (Stat.const false)) →
      ∃ m : Fin 21, ∀ s : Fin 17, maskHas m s = P s := by
    intro P tgt hsame
    by_cases hex : ∃ s0 : Fin 17, P s0 = true
    · obtain ⟨s0, hs0⟩ := hex
      refine exists_mask_of_slotWire ord (slotWire ord s0) P (fun s hs => ?_)
      have h1 := (hsame s hs).symm.trans (hsame s0 hs0)
      rw [hslot_st s, hslot_st s0] at h1
      exact π.injective (Fin.ext (Stat.wire.inj h1))
    · push_neg at hex
      exact ⟨0, fun s => by rw [maskHas_zero]; exact (Bool.eq_false_iff.mpr (hex s)).symm⟩
  obtain ⟨m1, hm1⟩ := mk_mask P1 (8 + D.g1.val) (fun s hs => by
    simp only [P1, decide_eq_true_eq] at hs
    rcases hs with h1 | ⟨hw1, hh1⟩
    · rw [h1]
    · rw [hh1, D.hh_st, ← D.hw3_st, hw1])
  obtain ⟨m2, hm2⟩ := mk_mask P2 (8 + D.g2.val) (fun s hs => by
    simp only [P2, decide_eq_true_eq] at hs
    rcases hs with h1 | ⟨hw1, hh1⟩
    · rw [h1]
    · rw [hh1, D.hh_st, ← D.hw3_st, hw1])
  obtain ⟨mh, hmh⟩ := mk_mask Ph (8 + D.h.val) (fun s hs => by
    simp only [Ph, decide_eq_true_eq] at hs; rw [hs])
  have hg12_valT : ∀ x : Fin 6 → Bool,
      (x2.wires (List.ofFn (lift6T x))).getD (7 + D.g1.val) false = true ∧
      (x3.wires (true :: List.ofFn (lift6T x))).getD (8 + D.g1.val) false = true ∧
      (x2.wires (List.ofFn (lift6T x))).getD (7 + D.g2.val) false = true ∧
      (x3.wires (true :: List.ofFn (lift6T x))).getD (8 + D.g2.val) false = true := by
    have one : ∀ (g : Fin 11) (x : Fin 6 → Bool),
        (∀ gg, x2.gates[g.val]? = some gg → gg.op = GateOp.or ∧ 2 ∈ gg.inputs) →
        (x2.wires (List.ofFn (lift6T x))).getD (7 + g.val) false = true ∧
        (x3.wires (true :: List.ofFn (lift6T x))).getD (8 + g.val) false = true := by
      intro g x hg_or
      obtain ⟨hop2, hmem2⟩ := hg_or _ (List.getElem?_eq_getElem (by omega : g.val < x2.gates.length))
      have hop3 : (x3.gates[g.val]'(by omega)).op = GateOp.or := (hed g).1.symm.trans hop2
      constructor
      · change (wiresFrom x2.gates (List.ofFn (lift6T x))).getD (7 + g.val) false = true
        have hgw := wiresFrom_gate_val x2.gates (List.ofFn (lift6T x)) g.val (by omega)
        simp only [List.length_ofFn] at hgw
        rw [hgw, hop2, GateOp.eval, List.any_eq_true]
        refine ⟨true, List.mem_map.mpr ⟨2, hmem2, ?_⟩, rfl⟩
        rw [getD_wiresFrom _ _ 2 (by simp)]; simp [lift6T]
      · change (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD (8 + g.val) false = true
        have hgw := wiresFrom_gate_val x3.gates (true :: List.ofFn (lift6T x)) g.val (by omega)
        simp only [List.length_cons, List.length_ofFn] at hgw
        rw [hgw, hop3, GateOp.eval, List.any_eq_true]
        obtain ⟨b, hbmem, hbrel⟩ := forall2_mem_left (hed g).2 hmem2
        refine ⟨true, List.mem_map.mpr ⟨b, hbmem, ?_⟩, rfl⟩
        rcases hbrel with rfl | ⟨rfl, _⟩
        · rw [getD_wiresFrom _ _ 3 (by simp)]; simp [lift6T]
        · rw [getD_wiresFrom _ _ 0 (by simp)]; rfl
    intro x
    exact ⟨(one D.g1 x D.hor2_1).1, (one D.g1 x D.hor2_1).2, (one D.g2 x D.hor2_2).1, (one D.g2 x D.hor2_2).2⟩
  have hh3_valT : ∀ x : Fin 6 → Bool,
      (x3.wires (true :: List.ofFn (lift6T x))).getD (8 + D.h.val) false =
      (x3.wires (true :: List.ofFn (lift6T x))).getD D.w3 false := by
    intro x
    obtain ⟨_, hop3, hins⟩ := D.hh_gate _ _
      (List.getElem?_eq_getElem (by omega : D.h.val < x2.gates.length))
      (List.getElem?_eq_getElem (by omega : D.h.val < x3.gates.length))
    change (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD (8 + D.h.val) false =
      (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD D.w3 false
    have hgw := wiresFrom_gate_val x3.gates (true :: List.ofFn (lift6T x)) D.h.val (by omega)
    simp only [List.length_cons, List.length_ofFn] at hgw
    rw [hgw, hop3]
    have hw0 : (wiresFrom (x3.gates.take D.h.val) (true :: List.ofFn (lift6T x))).getD 0 false = true := by
      rw [getD_wiresFrom _ _ 0 (by simp)]; rfl
    have hww : (wiresFrom (x3.gates.take D.h.val) (true :: List.ofFn (lift6T x))).getD D.w3 false =
        (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD D.w3 false :=
      (wiresFrom_getD_of_lt x3.gates (true :: List.ofFn (lift6T x)) D.h.val D.w3 (by omega) (by simp; have := D.hw3_lt; omega)).symm
    rcases hins with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;>
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, Bool.true_and, hw0, hww]
  have hw3_cases : D.w3 = origWire D.emitInv D.jh ∨ D.w3 = 8 + D.g1.val ∨ D.w3 = 8 + D.g2.val := by
    rcases D.hst_wire_cases D.w3 D.jh D.hw3_st with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
    · exfalso; have := D.hw3_lt; omega
  have hval3_eq : ∀ (x : Fin 6 → Bool) (c : Fin 14),
      (x3.wires (true :: List.ofFn (lift6T x))).getD (origWire D.emitInv (π c)) false = evalM3 ord m1 m2 x c := by
    intro x c
    induction c using (measure (fun q : Fin 14 => q.val)).wf.induction with
    | h c ih =>
      by_cases hc6 : c.val < 6
      · let i : Fin 6 := ⟨c.val, hc6⟩
        have hc_eq : c = ⟨i.val, by omega⟩ := Fin.ext rfl
        rw [hc_eq, horig_in i, evalM3_in ord m1 m2 x i]
        have hi_lt := (origWire_in_lt8 D.emitInv i).1
        change (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD _ false = _
        rw [getD_wiresFrom _ _ _ (by simp; omega), (lift6T_in_val x i D.emitInv).2]
      · let q : Fin 8 := ⟨c.val - 6, by have := c.isLt; omega⟩
        have hq_val : 6 + q.val = c.val := by dsimp [q]; omega
        have hc_eq : c = ⟨6 + q.val, by omega⟩ := Fin.ext hq_val.symm
        rw [hc_eq, horig_gate q, evalM3_gate_step ord m1 m2 x q]
        change (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD (8 + (kOf q).val) false = _
        have hgw := wiresFrom_gate_val x3.gates (true :: List.ofFn (lift6T x)) (kOf q).val (by omega)
        simp only [List.length_cons, List.length_ofFn] at hgw
        rw [hgw, (hin_spec q).2.2.2.2.2.2.1]
        have hpre : ∀ j < 8 + (kOf q).val,
            (wiresFrom (x3.gates.take (kOf q).val) (true :: List.ofFn (lift6T x))).getD j false =
            (x3.wires (true :: List.ofFn (lift6T x))).getD j false := fun j hj =>
          (wiresFrom_getD_of_lt x3.gates (true :: List.ofFn (lift6T x)) (kOf q).val j (by omega) (by simp; omega)).symm
        rw [hpre (inL q) (hin_spec q).2.2.1, hpre (inR q) (hin_spec q).2.2.2.1]
        have hslot_val : ∀ (s : Fin 17), (slotWire ord s).val < 6 + q.val →
            (x3.wires (true :: List.ofFn (lift6T x))).getD (slotX3 s) false =
            (maskHas m1 s || maskHas m2 s || evalM3 ord m1 m2 x (slotWire ord s)) := by
          intro s hlt
          rw [hm1 s, hm2 s]
          rcases hslot_cases s with ho | hg1 | hg2 | hh
          · have hp1 : P1 s = false := by
              simp only [P1, decide_eq_false_iff_not, not_or, not_and]
              exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _,
                fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
            have hp2 : P2 s = false := by
              simp only [P2, decide_eq_false_iff_not, not_or, not_and]
              exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _,
                fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
            rw [hp1, hp2, ho, Bool.false_or, Bool.false_or]
            exact ih (slotWire ord s) (by change (slotWire ord s).val < c.val; omega)
          · have hp1 : P1 s = true := by simp [P1, hg1]
            rw [hp1, hg1, (hg12_valT x).2.1]; rfl
          · have hp2 : P2 s = true := by simp [P2, hg2]
            rw [hp2, hg2, (hg12_valT x).2.2.2, Bool.or_true]; rfl
          · rw [hh, hh3_valT x]
            have hjh_eq : D.jh = π (slotWire ord s) := by
              have h1 := D.hh_st.symm.trans (hh ▸ hslot_st s)
              exact Fin.ext (Stat.wire.inj h1)
            rcases hw3_cases with hwo | hwg1 | hwg2
            · have hp1 : P1 s = false := by
                simp only [P1, decide_eq_false_iff_not, not_or, not_and]
                exact ⟨hh ▸ fun h => D.hdistinct.2.1 (Fin.ext (by omega)),
                  fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _) h).elim⟩
              have hp2 : P2 s = false := by
                simp only [P2, decide_eq_false_iff_not, not_or, not_and]
                exact ⟨hh ▸ fun h => D.hdistinct.2.2 (Fin.ext (by omega)),
                  fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _) h).elim⟩
              rw [hp1, hp2, hwo, hjh_eq, Bool.false_or, Bool.false_or]
              exact ih (slotWire ord s) (by change (slotWire ord s).val < c.val; omega)
            · have hp1 : P1 s = true := by simp [P1, hh, hwg1]
              rw [hp1, hwg1, (hg12_valT x).2.1]; rfl
            · have hp2 : P2 s = true := by simp [P2, hh, hwg2]
              rw [hp2, hwg2, (hg12_valT x).2.2.2, Bool.or_true]; rfl
        have hltL := canonL_lt ord q
        have hltR := canonR_lt ord q
        have hsL := hslotX3_even q
        have hsR := hslotX3_odd q
        have hwL := slotWire_even ord q
        have hwR := slotWire_odd ord q
        rw [← hsL, ← hsR, hslot_val ⟨2 * q.val, by have := q.isLt; omega⟩ (hwL ▸ hltL),
            hslot_val ⟨2 * q.val + 1, by have := q.isLt; omega⟩ (hwR ▸ hltR), hwL, hwR]
  have hout3_0 : evalOut3 ord m1 m2 (rowInput 0) = true := by
    have h1 : (x3.wires (true :: List.ofFn (lift6T (rowInput 0)))).getD (x2.output + 1) false = true := by
      rw [heval3 (lift6T (rowInput 0))]; simp [lift6T]
    have hslot16 : slotX3 16 = x2.output + 1 ∧ slotWire ord 16 = 13 := ⟨rfl, rfl⟩
    have h2 : (x3.wires (true :: List.ofFn (lift6T (rowInput 0)))).getD (slotX3 16) false =
        evalOut3 ord m1 m2 (rowInput 0) := by
      unfold evalOut3
      rw [hm1 16, hm2 16]
      rcases hslot_cases 16 with ho | hg1 | hg2 | hh
      · have hp1 : P1 16 = false := by
          simp only [P1, decide_eq_false_iff_not, not_or, not_and]
          exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _,
            fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
        have hp2 : P2 16 = false := by
          simp only [P2, decide_eq_false_iff_not, not_or, not_and]
          exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _,
            fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
        rw [hp1, hp2, ho, hslot16.2, Bool.false_or, Bool.false_or]
        exact hval3_eq (rowInput 0) 13
      · have hp1 : P1 16 = true := by simp [P1, hg1]
        rw [hp1, hg1, (hg12_valT (rowInput 0)).2.1]; rfl
      · have hp2 : P2 16 = true := by simp [P2, hg2]
        rw [hp2, hg2, (hg12_valT (rowInput 0)).2.2.2, Bool.or_true]; rfl
      · rw [hh, hh3_valT (rowInput 0)]
        have hjh_eq : D.jh = π 13 := by
          have h3 := D.hh_st.symm.trans (hh ▸ hslot_st 16)
          exact Fin.ext (Stat.wire.inj h3)
        rcases hw3_cases with hwo | hwg1 | hwg2
        · have hp1 : P1 16 = false := by
            simp only [P1, decide_eq_false_iff_not, not_or, not_and]
            exact ⟨hh ▸ fun h => D.hdistinct.2.1 (Fin.ext (by omega)),
              fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _) h).elim⟩
          have hp2 : P2 16 = false := by
            simp only [P2, decide_eq_false_iff_not, not_or, not_and]
            exact ⟨hh ▸ fun h => D.hdistinct.2.2 (Fin.ext (by omega)),
              fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _) h).elim⟩
          rw [hp1, hp2, hwo, hjh_eq, Bool.false_or, Bool.false_or]
          exact hval3_eq (rowInput 0) 13
        · have hp1 : P1 16 = true := by simp [P1, hh, hwg1]
          rw [hp1, hwg1, (hg12_valT (rowInput 0)).2.1]; rfl
        · have hp2 : P2 16 = true := by simp [P2, hh, hwg2]
          rw [hp2, hwg2, (hg12_valT (rowInput 0)).2.2.2, Bool.or_true]; rfl
    rw [← h2, hslot16.1, h1]
  have hpre_h_eq : ∀ (x : Fin 6 → Bool) (j : ℕ), j < 7 + D.h.val →
      (x2.wires (List.ofFn (lift6T x))).getD j false =
      (x3.wires (true :: List.ofFn (lift6T x))).getD (j + 1) false := by
    intro x j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      by_cases hj7 : j < 7
      · change (wiresFrom x2.gates (List.ofFn (lift6T x))).getD j false =
          (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD (j + 1) false
        rw [getD_wiresFrom _ _ j (by simp [hj7]),
            getD_wiresFrom _ _ (j + 1) (by simp; omega)]; rfl
      · let k : Fin 11 := ⟨j - 7, by omega⟩
        have hj_eq : j = 7 + k.val := by dsimp [k]; omega
        have hj1_eq : 7 + k.val + 1 = 8 + k.val := by omega
        rw [hj_eq, hj1_eq]
        by_cases hkg1 : k = D.g1
        · rw [hkg1]; exact (hg12_valT x).1.trans (hg12_valT x).2.1.symm
        · by_cases hkg2 : k = D.g2
          · rw [hkg2]; exact (hg12_valT x).2.2.1.trans (hg12_valT x).2.2.2.symm
          · have hkh : k ≠ D.h := fun heq => by rw [hj_eq, heq] at hj; omega
            have hq_ex : ∃ q : Fin 8, D.emitInv q = k := by
              let img : Finset (Fin 11) := Finset.univ.image D.emitInv
              let bad : Finset (Fin 11) := {D.g1, D.g2, D.h}
              have hdisj : Disjoint img bad := by
                rw [Finset.disjoint_left]; intro z hz1 hz2
                obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz1
                simp only [bad, Finset.mem_insert, Finset.mem_singleton] at hz2
                have hd := D.hemit_disj q
                rcases hz2 with h | h | h
                · exact hd.1 h
                · exact hd.2.1 h
                · exact hd.2.2 h
              have hcard_img : img.card = 8 := by
                rw [Finset.card_image_of_injective _ D.hemit_inj, Finset.card_univ, Fintype.card_fin]
              have hcard_bad : bad.card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp [D.hdistinct.1, D.hdistinct.2.1]),
                    Finset.card_insert_of_notMem (by simp [D.hdistinct.2.2]), Finset.card_singleton]
              have hun : img ∪ bad = Finset.univ :=
                Finset.eq_univ_of_card _ (by rw [Finset.card_union_of_disjoint hdisj, hcard_img, hcard_bad]; rfl)
              have hk_in : k ∈ img ∪ bad := hun.symm ▸ Finset.mem_univ k
              have hk_nbad : k ∉ bad := by simp [bad, hkg1, hkg2, hkh]
              obtain ⟨q, _, hqk⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hk_in).resolve_right hk_nbad)
              exact ⟨q, hqk⟩
            obtain ⟨q, hqk⟩ := hq_ex
            have hmg? : D.ms[q.val]? = some (D.ms[q.val]'(by rw [D.hms_len]; exact q.isLt)) :=
              List.getElem?_eq_getElem (by rw [D.hms_len]; exact q.isLt)
            have hk2 : x2.gates[(D.emitInv q).val]? = some (x2.gates[k.val]'(by omega)) := by
              rw [hqk]; exact List.getElem?_eq_getElem (by omega)
            have hk3 : x3.gates[(D.emitInv q).val]? = some (x3.gates[k.val]'(by omega)) := by
              rw [hqk]; exact List.getElem?_eq_getElem (by omega)
            obtain ⟨hop2, hop3, i1, i2, j1, j2, h2in, h3in, _, hi1lt, hi2lt, _, _⟩ :=
              D.hemit_gate q _ _ _ hk2 hk3 hmg?
            rw [hqk] at hi1lt hi2lt
            change (wiresFrom x2.gates (List.ofFn (lift6T x))).getD (7 + k.val) false =
              (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD (8 + k.val) false
            have hgw2 := wiresFrom_gate_val x2.gates (List.ofFn (lift6T x)) k.val (by omega)
            have hgw3 := wiresFrom_gate_val x3.gates (true :: List.ofFn (lift6T x)) k.val (by omega)
            simp only [List.length_ofFn, List.length_cons] at hgw2 hgw3
            rw [hgw2, hgw3, hop2, hop3, h2in, h3in]
            simp only [List.map_cons, List.map_nil]
            have hstep : ∀ i, i + 1 < 8 + k.val →
                (wiresFrom (x2.gates.take k.val) (List.ofFn (lift6T x))).getD i false =
                (wiresFrom (x3.gates.take k.val) (true :: List.ofFn (lift6T x))).getD (i + 1) false := by
              intro i hi
              rw [← wiresFrom_getD_of_lt x2.gates (List.ofFn (lift6T x)) k.val i (by omega) (by simp; omega),
                  ← wiresFrom_getD_of_lt x3.gates (true :: List.ofFn (lift6T x)) k.val (i + 1) (by omega) (by simp; omega)]
              exact ih i (by omega) (by omega)
            rw [hstep i1 hi1lt, hstep i2 hi2lt]
  have ha_ex : ∃ a : Fin 16, ∀ x : Fin 6 → Bool,
      (wiresFrom (x2.gates.take D.h.val) (List.ofFn (lift6T x))).getD D.a2 false =
      evalAv ord m1 m2 a x := by
    by_cases ha_lt : D.a2 < 7 + D.h.val
    · have hval_a2 : ∀ x : Fin 6 → Bool,
          (wiresFrom (x2.gates.take D.h.val) (List.ofFn (lift6T x))).getD D.a2 false =
          (x3.wires (true :: List.ofFn (lift6T x))).getD (D.a2 + 1) false := fun x => by
        rw [← wiresFrom_getD_of_lt x2.gates (List.ofFn (lift6T x)) D.h.val D.a2 (by omega) (by simp; omega)]
        exact hpre_h_eq x D.a2 ha_lt
      by_cases ha2 : D.a2 = 2
      · refine ⟨14, fun x => ?_⟩
        rw [hval_a2 x, ha2]
        change (wiresFrom x3.gates (true :: List.ofFn (lift6T x))).getD 3 false = true
        rw [getD_wiresFrom _ _ 3 (by simp)]; simp [lift6T]
      · by_cases ha_g1 : D.a2 + 1 = 8 + D.g1.val
        · refine ⟨14, fun x => ?_⟩
          rw [hval_a2 x, ha_g1, (hg12_valT x).2.1]; rfl
        · by_cases ha_g2 : D.a2 + 1 = 8 + D.g2.val
          · refine ⟨14, fun x => ?_⟩
            rw [hval_a2 x, ha_g2, (hg12_valT x).2.2.2]; rfl
          · have hst_a : ∃ u : Fin 14, D.a2 + 1 = origWire D.emitInv u := by
              by_cases ha7 : D.a2 < 7
              · rcases ha2_val : D.a2 with _ | _ | _ | _ | _ | _ | _ | n
                · exact ⟨0, rfl⟩
                · exact ⟨1, rfl⟩
                · exact (ha2 ha2_val).elim
                · exact ⟨2, rfl⟩
                · exact ⟨3, rfl⟩
                · exact ⟨4, rfl⟩
                · exact ⟨5, rfl⟩
                · omega
              · let k : Fin 11 := ⟨D.a2 - 7, by omega⟩
                have hk_eq : D.a2 + 1 = 8 + k.val := by dsimp [k]; omega
                have hkg1 : k ≠ D.g1 := fun h => ha_g1 (by rw [hk_eq, h])
                have hkg2 : k ≠ D.g2 := fun h => ha_g2 (by rw [hk_eq, h])
                have hkh : k ≠ D.h := fun h => by have hk := congrArg Fin.val h; omega
                have hq_ex : ∃ q : Fin 8, D.emitInv q = k := by
                  let img : Finset (Fin 11) := Finset.univ.image D.emitInv
                  let bad : Finset (Fin 11) := {D.g1, D.g2, D.h}
                  have hdisj : Disjoint img bad := by
                    rw [Finset.disjoint_left]; intro z hz1 hz2
                    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz1
                    simp only [bad, Finset.mem_insert, Finset.mem_singleton] at hz2
                    have hd := D.hemit_disj q
                    rcases hz2 with h | h | h
                    · exact hd.1 h
                    · exact hd.2.1 h
                    · exact hd.2.2 h
                  have hun : img ∪ bad = Finset.univ := Finset.eq_univ_of_card _ (by
                    rw [Finset.card_union_of_disjoint hdisj,
                        Finset.card_image_of_injective _ D.hemit_inj, Finset.card_univ, Fintype.card_fin,
                        Finset.card_insert_of_notMem (by simp [D.hdistinct.1, D.hdistinct.2.1]),
                        Finset.card_insert_of_notMem (by simp [D.hdistinct.2.2]), Finset.card_singleton]; rfl)
                  obtain ⟨q, _, hqk⟩ := Finset.mem_image.mp ((Finset.mem_union.mp (hun.symm ▸ Finset.mem_univ k)).resolve_right (by simp [bad, hkg1, hkg2, hkh]))
                  exact ⟨q, hqk⟩
                obtain ⟨q, hqk⟩ := hq_ex
                have hq8 := q.isLt
                refine ⟨⟨q.val + 6, by omega⟩, ?_⟩
                simp only [origWire, hq8, ↓reduceDIte, hqk]; exact hk_eq
            obtain ⟨u, hu⟩ := hst_a
            obtain ⟨c, rfl⟩ := π.surjective u
            refine ⟨⟨c.val, by have := c.isLt; omega⟩, fun x => ?_⟩
            rw [hval_a2 x, hu, hval3_eq x c]
            unfold evalAv evalAvB evalM3
            simp only [c.isLt, ↓reduceDIte]
    · refine ⟨15, fun x => ?_⟩
      rw [List.getD_eq_default _ false (by rw [length_wiresFrom, List.length_take_of_le (by omega)]; simp; omega)]
      rfl
  obtain ⟨a, ha_eq⟩ := ha_ex
  have hh2_valT : ∀ x : Fin 6 → Bool,
      (x2.wires (List.ofFn (lift6T x))).getD (7 + D.h.val) false =
      ((x2.wires (List.ofFn (lift6T x))).getD (D.w3 - 1) false && evalAv ord m1 m2 a x) := by
    intro x
    obtain ⟨hop2, _, hins⟩ := D.hh_gate _ _
      (List.getElem?_eq_getElem (by omega : D.h.val < x2.gates.length))
      (List.getElem?_eq_getElem (by omega : D.h.val < x3.gates.length))
    change (wiresFrom x2.gates (List.ofFn (lift6T x))).getD (7 + D.h.val) false = _
    have hgw := wiresFrom_gate_val x2.gates (List.ofFn (lift6T x)) D.h.val (by omega)
    simp only [List.length_ofFn] at hgw
    rw [hgw, hop2]
    have hww : (wiresFrom (x2.gates.take D.h.val) (List.ofFn (lift6T x))).getD (D.w3 - 1) false =
        (x2.wires (List.ofFn (lift6T x))).getD (D.w3 - 1) false :=
      (wiresFrom_getD_of_lt x2.gates (List.ofFn (lift6T x)) D.h.val (D.w3 - 1) (by omega) (by simp; have := D.hw3_lt; omega)).symm
    rcases hins with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, ha_eq x, hww]
      exact Bool.and_comm _ _
    · rw [h2]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, ha_eq x, hww]
  have hval2_eq : ∀ (x : Fin 6 → Bool) (c : Fin 14),
      (x2.wires (List.ofFn (lift6T x))).getD (origWire D.emitInv (π c) - 1) false = evalM2 ord m1 m2 mh a x c := by
    intro x c
    induction c using (measure (fun q : Fin 14 => q.val)).wf.induction with
    | h c ih =>
      by_cases hc6 : c.val < 6
      · let i : Fin 6 := ⟨c.val, hc6⟩
        have hc_eq : c = ⟨i.val, by omega⟩ := Fin.ext rfl
        rw [hc_eq, horig_in i, evalM2_in ord m1 m2 mh a x i]
        have hi_lt := (origWire_in_lt8 D.emitInv i).1
        have hi_ge := (origWire_in_lt8 D.emitInv i).2
        change (wiresFrom x2.gates (List.ofFn (lift6T x))).getD _ false = _
        rw [getD_wiresFrom _ _ _ (by simp; omega), (lift6T_in_val x i D.emitInv).1]
      · let q : Fin 8 := ⟨c.val - 6, by have := c.isLt; omega⟩
        have hq_val : 6 + q.val = c.val := by dsimp [q]; omega
        have hc_eq : c = ⟨6 + q.val, by omega⟩ := Fin.ext hq_val.symm
        rw [hc_eq, horig_gate q, show 8 + (kOf q).val - 1 = 7 + (kOf q).val by omega,
            evalM2_gate_step ord m1 m2 mh a x q]
        change (wiresFrom x2.gates (List.ofFn (lift6T x))).getD (7 + (kOf q).val) false = _
        have hgw := wiresFrom_gate_val x2.gates (List.ofFn (lift6T x)) (kOf q).val (by omega)
        simp only [List.length_ofFn] at hgw
        rw [hgw, (hin_spec q).2.2.2.2.2.2.2]
        have hpre : ∀ j < 7 + (kOf q).val,
            (wiresFrom (x2.gates.take (kOf q).val) (List.ofFn (lift6T x))).getD j false =
            (x2.wires (List.ofFn (lift6T x))).getD j false := fun j hj =>
          (wiresFrom_getD_of_lt x2.gates (List.ofFn (lift6T x)) (kOf q).val j (by omega) (by simp; omega)).symm
        rw [hpre (inL q - 1) (by have := (hin_spec q).1; have := (hin_spec q).2.2.1; omega),
            hpre (inR q - 1) (by have := (hin_spec q).2.1; have := (hin_spec q).2.2.2.1; omega)]
        have hslot_val : ∀ (s : Fin 17), (slotWire ord s).val < 6 + q.val →
            (x2.wires (List.ofFn (lift6T x))).getD (slotX3 s - 1) false =
            ((maskHas m1 s || maskHas m2 s || evalM2 ord m1 m2 mh a x (slotWire ord s)) &&
             (!maskHas mh s || evalAv ord m1 m2 a x)) := by
          intro s hlt
          rw [hm1 s, hm2 s, hmh s]
          rcases hslot_cases s with ho | hg1 | hg2 | hh
          · have hp1 : P1 s = false := by
              simp only [P1, decide_eq_false_iff_not, not_or, not_and]
              exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _,
                fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
            have hp2 : P2 s = false := by
              simp only [P2, decide_eq_false_iff_not, not_or, not_and]
              exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _,
                fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
            have hph : Ph s = false := by
              simp only [Ph, decide_eq_false_iff_not]
              exact ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _
            rw [hp1, hp2, hph, ho]
            simp only [Bool.false_or, Bool.not_false, Bool.true_or, Bool.and_true]
            exact ih (slotWire ord s) (by change (slotWire ord s).val < c.val; omega)
          · have hp1 : P1 s = true := by simp [P1, hg1]
            have hph : Ph s = false := by simp only [Ph, decide_eq_false_iff_not, hg1]; intro h; exact D.hdistinct.2.1 (Fin.ext (by omega))
            rw [hp1, hph, hg1, show 8 + D.g1.val - 1 = 7 + D.g1.val by omega, (hg12_valT x).1]; rfl
          · have hp2 : P2 s = true := by simp [P2, hg2]
            have hph : Ph s = false := by simp only [Ph, decide_eq_false_iff_not, hg2]; intro h; exact D.hdistinct.2.2 (Fin.ext (by omega))
            rw [hp2, hph, hg2, show 8 + D.g2.val - 1 = 7 + D.g2.val by omega, (hg12_valT x).2.2.1]; simp
          · have hph : Ph s = true := by simp [Ph, hh]
            rw [hph, hh, show 8 + D.h.val - 1 = 7 + D.h.val by omega, hh2_valT x]
            simp only [Bool.not_true, Bool.false_or]
            have hjh_eq : D.jh = π (slotWire ord s) := by
              have h1 := D.hh_st.symm.trans (hh ▸ hslot_st s)
              exact Fin.ext (Stat.wire.inj h1)
            rcases hw3_cases with hwo | hwg1 | hwg2
            · have hp1 : P1 s = false := by
                simp only [P1, decide_eq_false_iff_not, not_or, not_and]
                exact ⟨hh ▸ fun h => D.hdistinct.2.1 (Fin.ext (by omega)),
                  fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _) h).elim⟩
              have hp2 : P2 s = false := by
                simp only [P2, decide_eq_false_iff_not, not_or, not_and]
                exact ⟨hh ▸ fun h => D.hdistinct.2.2 (Fin.ext (by omega)),
                  fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _) h).elim⟩
              rw [hp1, hp2, hwo, hjh_eq, Bool.false_or, Bool.false_or]
              rw [ih (slotWire ord s) (by change (slotWire ord s).val < c.val; omega)]
            · have hp1 : P1 s = true := by simp [P1, hh, hwg1]
              rw [hp1, hwg1, show 8 + D.g1.val - 1 = 7 + D.g1.val by omega, (hg12_valT x).1]; rfl
            · have hp2 : P2 s = true := by simp [P2, hh, hwg2]
              rw [hp2, hwg2, show 8 + D.g2.val - 1 = 7 + D.g2.val by omega, (hg12_valT x).2.2.1]; simp
        have hltL := canonL_lt ord q
        have hltR := canonR_lt ord q
        have hsL := hslotX3_even q
        have hsR := hslotX3_odd q
        have hwL := slotWire_even ord q
        have hwR := slotWire_odd ord q
        rw [← hsL, ← hsR, hslot_val ⟨2 * q.val, by have := q.isLt; omega⟩ (hwL ▸ hltL),
            hslot_val ⟨2 * q.val + 1, by have := q.isLt; omega⟩ (hwR ▸ hltR), hwL, hwR]
  have hout2_all : ∀ r : Fin 13, evalOut2 ord m1 m2 mh a (rowInput r) = rowTarget r := by
    intro r
    let x := rowInput r
    have h1 : (x2.wires (List.ofFn (lift6T x))).getD x2.output false = rowTarget r := by
      change x2.eval (List.ofFn (lift6T x)) = rowTarget r
      have h := congrFun heval2 (lift6T x)
      change x2.eval (List.ofFn (lift6T x)) = thetaFun (lift6T x) at h
      rw [h]; exact theta_lift6T_row r
    have hslot16 : slotX3 16 = x2.output + 1 ∧ slotWire ord 16 = 13 := ⟨rfl, rfl⟩
    have h2 : (x2.wires (List.ofFn (lift6T x))).getD (slotX3 16 - 1) false = evalOut2 ord m1 m2 mh a x := by
      rw [evalOut2_eq_m2, hm1 16, hm2 16, hmh 16]
      rcases hslot_cases 16 with ho | hg1 | hg2 | hh
      · have hp1 : P1 16 = false := by
          simp only [P1, decide_eq_false_iff_not, not_or, not_and]
          exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _,
            fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
        have hp2 : P2 16 = false := by
          simp only [P2, decide_eq_false_iff_not, not_or, not_and]
          exact ⟨ho ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _,
            fun _ => ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _⟩
        have hph : Ph 16 = false := by
          simp only [Ph, decide_eq_false_iff_not]
          exact ho ▸ origWire_ne_bad D.emitInv D.h (fun r => (D.hemit_disj r).2.2) _
        rw [hp1, hp2, hph, ho, hslot16.2]
        simp only [Bool.false_or, Bool.not_false, Bool.true_or, Bool.and_true]
        exact hval2_eq x 13
      · have hp1 : P1 16 = true := by simp [P1, hg1]
        have hph : Ph 16 = false := by simp only [Ph, decide_eq_false_iff_not, hg1]; intro h; exact D.hdistinct.2.1 (Fin.ext (by omega))
        rw [hp1, hph, hg1, show 8 + D.g1.val - 1 = 7 + D.g1.val by omega, (hg12_valT x).1]; rfl
      · have hp2 : P2 16 = true := by simp [P2, hg2]
        have hph : Ph 16 = false := by simp only [Ph, decide_eq_false_iff_not, hg2]; intro h; exact D.hdistinct.2.2 (Fin.ext (by omega))
        rw [hp2, hph, hg2, show 8 + D.g2.val - 1 = 7 + D.g2.val by omega, (hg12_valT x).2.2.1]; simp
      · have hph : Ph 16 = true := by simp [Ph, hh]
        rw [hph, hh, show 8 + D.h.val - 1 = 7 + D.h.val by omega, hh2_valT x]
        simp only [Bool.not_true, Bool.false_or]
        have hjh_eq : D.jh = π 13 := by
          have h3 := D.hh_st.symm.trans (hh ▸ hslot_st 16)
          exact Fin.ext (Stat.wire.inj h3)
        rcases hw3_cases with hwo | hwg1 | hwg2
        · have hp1 : P1 16 = false := by
            simp only [P1, decide_eq_false_iff_not, not_or, not_and]
            exact ⟨hh ▸ fun h => D.hdistinct.2.1 (Fin.ext (by omega)),
              fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g1 (fun r => (D.hemit_disj r).1) _) h).elim⟩
          have hp2 : P2 16 = false := by
            simp only [P2, decide_eq_false_iff_not, not_or, not_and]
            exact ⟨hh ▸ fun h => D.hdistinct.2.2 (Fin.ext (by omega)),
              fun h => ((hwo ▸ origWire_ne_bad D.emitInv D.g2 (fun r => (D.hemit_disj r).2.1) _) h).elim⟩
          rw [hp1, hp2, hwo, hjh_eq, Bool.false_or, Bool.false_or, hval2_eq x 13]
        · have hp1 : P1 16 = true := by simp [P1, hh, hwg1]
          rw [hp1, hwg1, show 8 + D.g1.val - 1 = 7 + D.g1.val by omega, (hg12_valT x).1]; rfl
        · have hp2 : P2 16 = true := by simp [P2, hh, hwg2]
          rw [hp2, hwg2, show 8 + D.g2.val - 1 = 7 + D.g2.val by omega, (hg12_valT x).2.2.1]; simp
    rw [← h2, hslot16.1]; simpa using h1
  exact step3_no_solution ord m1 m2 mh a hout3_0 hout2_all

def sigma7 : Fin 7 → Fin 7
  | ⟨0, _⟩ => 4 | ⟨1, _⟩ => 6 | ⟨2, _⟩ => 2 | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 3 | ⟨6, _⟩ => 1

def sigma6 : Fin 6 → Fin 6
  | ⟨0, _⟩ => 3 | ⟨1, _⟩ => 5 | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 0 | ⟨4, _⟩ => 2 | ⟨5, _⟩ => 1

lemma sigma7_invol : ∀ i : Fin 7, sigma7 (sigma7 i) = i := by decide
lemma sigma6_invol : ∀ i : Fin 6, sigma6 (sigma6 i) = i := by decide
lemma sigma6_sideA : ∀ v : Fin 6, v ∈ sideA ↔ sigma6 v ∈ sideB := by decide

def mk7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Fin 7 → Bool
  | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4 | ⟨5, _⟩ => b5 | ⟨6, _⟩ => b6

lemma theta_sigma7_bits : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    thetaFun (fun i => mk7 b0 b1 b2 b3 b4 b5 b6 (sigma7 i)) = thetaFun (mk7 b0 b1 b2 b3 b4 b5 b6) := by
  decide

lemma theta_sigma7 (x : Fin 7 → Bool) : thetaFun (fun i => x (sigma7 i)) = thetaFun x := by
  have hx : x = mk7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) := by
    funext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  exact theta_sigma7_bits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def permW2 (w : ℕ) : ℕ := if h : w < 7 then (sigma7 ⟨w, h⟩).val else w
def permW3 (w : ℕ) : ℕ := if h : 1 ≤ w ∧ w < 8 then (sigma7 ⟨w - 1, by omega⟩).val + 1 else w
def permW6 (w : ℕ) : ℕ := if h : w < 6 then (sigma6 ⟨w, h⟩).val else w

def permStat : Stat → Stat
  | Stat.const c => Stat.const c
  | Stat.wire j => Stat.wire (permW6 j)

def permG2 (g : Gate) : Gate := ⟨g.op, g.inputs.map permW2⟩
def permG3 (g : Gate) : Gate := ⟨g.op, g.inputs.map permW3⟩
def permG6 (g : Gate) : Gate := ⟨g.op, g.inputs.map permW6⟩

lemma permW2_invol (w : ℕ) : permW2 (permW2 w) = w := by
  unfold permW2
  by_cases h : w < 7
  · simp only [h, ↓reduceDIte, (sigma7 ⟨w, h⟩).isLt]
    exact congrArg Fin.val (sigma7_invol ⟨w, h⟩)
  · simp [h]

lemma permW3_invol (w : ℕ) : permW3 (permW3 w) = w := by
  unfold permW3
  by_cases h : 1 ≤ w ∧ w < 8
  · have hlt := (sigma7 ⟨w - 1, by omega⟩).isLt
    simp only [h, and_self, ↓reduceDIte]
    have h2 : 1 ≤ (sigma7 ⟨w - 1, by omega⟩).val + 1 ∧ (sigma7 ⟨w - 1, by omega⟩).val + 1 < 8 := by omega
    simp only [h2, and_self, ↓reduceDIte]
    have hs := congrArg Fin.val (sigma7_invol ⟨w - 1, by omega⟩)
    simp only [Nat.add_sub_cancel]
    have hfin : (⟨(sigma7 ⟨w - 1, by omega⟩).val, by omega⟩ : Fin 7) = sigma7 ⟨w - 1, by omega⟩ := Fin.ext rfl
    rw [hfin]
    dsimp only at hs; omega
  · simp [h]

lemma permW6_invol (w : ℕ) : permW6 (permW6 w) = w := by
  unfold permW6
  by_cases h : w < 6
  · simp only [h, ↓reduceDIte, (sigma6 ⟨w, h⟩).isLt]
    exact congrArg Fin.val (sigma6_invol ⟨w, h⟩)
  · simp [h]

lemma permW3_succ (a : ℕ) : permW3 (a + 1) = permW2 a + 1 := by
  unfold permW3 permW2
  by_cases ha : a < 7
  · have h1 : 1 ≤ a + 1 ∧ a + 1 < 8 := by omega
    simp only [ha, h1, and_self, ↓reduceDIte, Nat.add_sub_cancel]
  · have h1 : ¬ (1 ≤ a + 1 ∧ a + 1 < 8) := by omega
    rw [dif_neg h1, dif_neg ha]

lemma permW2_eq_two_iff (a : ℕ) : permW2 a = 2 ↔ a = 2 := by
  constructor
  · intro h; have := congrArg permW2 h; rw [permW2_invol] at this; exact this
  · rintro rfl; rfl

lemma wiresFrom_perm2 (gs : List Gate) (w w' : List Bool)
    (hlen : w.length = w'.length) (hge : 7 ≤ w.length)
    (hrel : ∀ j, w'.getD (permW2 j) false = w.getD j false) :
    ∀ j, (wiresFrom (gs.map permG2) w').getD (permW2 j) false = (wiresFrom gs w).getD j false := by
  induction gs generalizing w w' with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.map_cons, wiresFrom, List.foldl_cons]
    have hins : ((permG2 g).inputs.map fun i => w'.getD i false) = g.inputs.map fun i => w.getD i false := by
      simp only [permG2, List.map_map]
      exact List.map_congr_left fun a _ => hrel a
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro j
    by_cases hjl : j = w.length
    · subst hjl
      have hp : permW2 w.length = w'.length := by unfold permW2; rw [dif_neg (by omega), hlen]
      rw [hp, getD_snoc_eq, getD_snoc_eq, hins]; rfl
    · have hpne : permW2 j ≠ w'.length := by
        intro h
        have h1 : permW2 w'.length = w'.length := by unfold permW2; rw [dif_neg (by omega)]
        have h2 := congrArg permW2 h
        rw [permW2_invol, h1] at h2; omega
      rw [getD_snoc_ne _ _ _ _ hpne, getD_snoc_ne _ _ _ _ hjl]
      exact hrel j

lemma wiresFrom_perm3 (gs : List Gate) (w w' : List Bool)
    (hlen : w.length = w'.length) (hge : 8 ≤ w.length)
    (hrel : ∀ j, w'.getD (permW3 j) false = w.getD j false) :
    ∀ j, (wiresFrom (gs.map permG3) w').getD (permW3 j) false = (wiresFrom gs w).getD j false := by
  induction gs generalizing w w' with
  | nil => exact hrel
  | cons g gs ih =>
    simp only [List.map_cons, wiresFrom, List.foldl_cons]
    have hins : ((permG3 g).inputs.map fun i => w'.getD i false) = g.inputs.map fun i => w.getD i false := by
      simp only [permG3, List.map_map]
      exact List.map_congr_left fun a _ => hrel a
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro j
    by_cases hjl : j = w.length
    · subst hjl
      have hp : permW3 w.length = w'.length := by unfold permW3; rw [dif_neg (by omega), hlen]
      rw [hp, getD_snoc_eq, getD_snoc_eq, hins]; rfl
    · have hpne : permW3 j ≠ w'.length := by
        intro h
        have h1 : permW3 w'.length = w'.length := by unfold permW3; rw [dif_neg (by omega)]
        have h2 := congrArg permW3 h
        rw [permW3_invol, h1] at h2; omega
      rw [getD_snoc_ne _ _ _ _ hpne, getD_snoc_ne _ _ _ _ hjl]
      exact hrel j

lemma simplify_permStat (op : GateOp) (m : ℕ) (hm : 6 ≤ m) (ins : List Stat) :
    let r := simplify op m ins
    simplify op m (ins.map permStat) = (r.1.map permG6, permStat r.2) := by
  have hpm : permW6 m = m := by unfold permW6; rw [dif_neg (by omega)]
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · rfl
    · cases a <;> rfl
    · cases a with
      | const c1 => cases b with
        | const c2 => cases c1 <;> cases c2 <;> rfl
        | wire j => cases c1 <;> simp [simplify, simpAnd, permStat, permG6, hpm]
      | wire i => cases b with
        | const c2 => cases c2 <;> simp [simplify, simpAnd, permStat, permG6, hpm]
        | wire j => simp [simplify, simpAnd, permStat, permG6, hpm]
    · simp [simplify, simpAnd, permStat, permG6, hpm]
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · rfl
    · cases a <;> rfl
    · cases a with
      | const c1 => cases b with
        | const c2 => cases c1 <;> cases c2 <;> rfl
        | wire j => cases c1 <;> simp [simplify, simpOr, permStat, permG6, hpm]
      | wire i => cases b with
        | const c2 => cases c2 <;> simp [simplify, simpOr, permStat, permG6, hpm]
        | wire j => simp [simplify, simpOr, permStat, permG6, hpm]
    · simp [simplify, simpOr, permStat, permG6, hpm]
  | not =>
    rcases ins with _ | ⟨a, l⟩
    · rfl
    · cases a <;> simp [simplify, simpNot, permStat, permG6, hpm]
  | mod _ => rfl
  | maj => rfl

lemma elim_perm3 (gs : List Gate) (acc acc' : List Stat × List Gate)
    (hlen : acc.1.length = acc'.1.length) (hge : 8 ≤ acc.1.length)
    (hrel : ∀ i, acc'.1.getD (permW3 i) (Stat.const false) = permStat (acc.1.getD i (Stat.const false)))
    (hms : acc'.2 = acc.2.map permG6) :
    (elim 6 (gs.map permG3) acc').2 = (elim 6 gs acc).2.map permG6 := by
  induction gs generalizing acc acc' with
  | nil => exact hms
  | cons g gs ih =>
    simp only [List.map_cons, elim, List.foldl_cons]
    have hmlen : acc'.2.length = acc.2.length := by rw [hms, List.length_map]
    have hins : ((permG3 g).inputs.map fun i => acc'.1.getD i (Stat.const false)) =
        (g.inputs.map fun i => acc.1.getD i (Stat.const false)).map permStat := by
      simp only [permG3, List.map_map]
      exact List.map_congr_left fun a _ => hrel a
    have hsimp := simplify_permStat g.op (6 + acc.2.length) (by omega)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))
    have hop : (permG3 g).op = g.op := rfl
    apply ih (elimStep 6 acc g) (elimStep 6 acc' (permG3 g))
    · simp [elimStep, hlen]
    · simp [elimStep]; omega
    · intro i
      simp only [elimStep]
      rw [hmlen, hins, hop, hsimp]
      by_cases hil : i = acc.1.length
      · subst hil
        have hp : permW3 acc.1.length = acc'.1.length := by unfold permW3; rw [dif_neg (by omega), hlen]
        rw [hp, getD_snoc_eq, getD_snoc_eq]
      · have hpne : permW3 i ≠ acc'.1.length := by
          intro h
          have h1 : permW3 acc'.1.length = acc'.1.length := by unfold permW3; rw [dif_neg (by omega)]
          have h2 := congrArg permW3 h
          rw [permW3_invol, h1] at h2; omega
        rw [getD_snoc_ne _ _ _ _ hpne, getD_snoc_ne _ _ _ _ hil]
        exact hrel i
    · simp only [elimStep]
      rw [hmlen, hins, hop, hsimp, hms, List.map_append]
      congr 1
      generalize (simplify g.op (6 + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = o
      cases o <;> rfl

lemma sideB_to_sideA_ms (ms : List Gate) (hSideB : SideNoTopBranch ms sideB) :
    SideNoTopBranch (ms.map permG6) sideA := by
  let pf (w : Fin (6 + (ms.map permG6).length)) : Fin (6 + ms.length) :=
    ⟨permW6 w.val, by
      have hw : w.val < 6 + ms.length := by simpa [List.length_map] using w.isLt
      unfold permW6; split_ifs with h
      · have := (sigma6 ⟨w.val, h⟩).isLt; omega
      · omega⟩
  have hpf_invol : ∀ w, permW6 (pf w).val = w.val := fun w => permW6_invol w.val
  have hpf_inj : Function.Injective pf := fun a b h => Fin.ext (by
    have h1 := congrArg Fin.val h
    have h2 := congrArg permW6 h1
    rw [hpf_invol, hpf_invol] at h2; exact h2)
  have hre : ∀ a b, readEdge (ms.map permG6) a b → readEdge ms (pf a) (pf b) := by
    intro a b ⟨p, g, hpg, hb, ha⟩
    rw [List.getElem?_map] at hpg
    cases hg0 : ms[p]? with
    | none => rw [hg0] at hpg; cases hpg
    | some g0 =>
      rw [hg0] at hpg
      have hgeq : permG6 g0 = g := Option.some.inj hpg
      subst hgeq
      obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ha
      refine ⟨p, g0, hg0, ?_, ?_⟩
      · change permW6 b.val = 6 + p
        rw [hb]; unfold permW6; rw [dif_neg (by omega)]
      · change permW6 a.val ∈ g0.inputs
        rw [← hxa, permW6_invol]; exact hx
  have hpath : ∀ a b, ReflTransGen (readEdge (ms.map permG6)) a b →
      ReflTransGen (readEdge ms) (pf a) (pf b) := by
    intro a b hp
    induction hp with
    | refl => exact ReflTransGen.refl
    | tail _ edge ih => exact ih.tail (hre _ _ edge)
  intro r ⟨a, b, hra, hrb, hab⟩ v hvA path
  have hbr : FirstBranchRoute.Branches (readEdge ms) (pf r) :=
    ⟨pf a, pf b, hre r a hra, hre r b hrb, fun h => hab (hpf_inj h)⟩
  have hvB : sigma6 v ∈ sideB := (sigma6_sideA v).mp hvA
  have hpf_in : pf (inputWire (ms.map permG6) v) = inputWire ms (sigma6 v) := by
    apply Fin.ext
    change permW6 v.val = (sigma6 v).val
    unfold permW6; rw [dif_pos v.isLt]
  have hp' := hpath _ _ path
  rw [hpf_in] at hp'
  exact hSideB (pf r) hbr (sigma6 v) hvB hp'

theorem L_meta_4797_proof (x2 x3 : Circuit) (x4 x5 : ℕ)
    (hfan : FanInTwo x2) (hsz : x2.size = 11)
    (heval2 : circuitFun 7 x2 = thetaFun)
    (hedit : List.Forall₂ (EditGate x4 x5) x2.gates x3.gates)
    (heval3 : ∀ x : Fin 7 → Bool, (x3.wires (true :: List.ofFn x)).getD (x2.output + 1) false = (thetaFun x || x 2))
    (hor2 : (x2.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length = 2) :
    False := by
  obtain ⟨D⟩ := extract_elim_data x2 x3 x4 x5 hfan hsz heval2 hedit heval3 hor2
  rcases D.hside with hSideA | hSideB
  · exact sideA_impossible x2 x3 x4 x5 hfan hsz heval2 hedit heval3 D hSideA
  · let x2' : Circuit := ⟨x2.gates.map permG2, permW2 x2.output⟩
    let x3' : Circuit := ⟨x3.gates.map permG3, permW3 x3.output⟩
    have hfan' : FanInTwo x2' := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g0 hg0).1, by simp [permG2, (hfan g0 hg0).2]⟩
    have hsz' : x2'.size = 11 := by
      show (x2.gates.map permG2).length = 11
      rw [List.length_map]; exact hsz
    have heval2' : circuitFun 7 x2' = thetaFun := by
      funext x
      change (wiresFrom (x2.gates.map permG2) (List.ofFn x)).getD (permW2 x2.output) false = thetaFun x
      rw [wiresFrom_perm2 x2.gates (List.ofFn (fun i => x (sigma7 i))) (List.ofFn x) (by simp) (by simp) (fun j => by
        by_cases hj : j < 7
        · unfold permW2
          rw [dif_pos hj,
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (sigma7 ⟨j, hj⟩).isLt),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hj)]
          simp only [List.getElem_ofFn]
        · unfold permW2; rw [dif_neg hj, List.getD_eq_default _ false (by simp; omega), List.getD_eq_default _ false (by simp; omega)])]
      have h := congrFun heval2 (fun i => x (sigma7 i))
      change (wiresFrom x2.gates (List.ofFn (fun i => x (sigma7 i)))).getD x2.output false = thetaFun (fun i => x (sigma7 i)) at h
      rw [h, theta_sigma7]
    have hedit' : List.Forall₂ (EditGate (permW2 x4) (permW2 x5)) x2'.gates x3'.gates := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.Forall₂.imp ?_ hedit
      intro g2 g3 ⟨hop, hins⟩
      refine ⟨hop, ?_⟩
      dsimp only [permG2, permG3]
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.Forall₂.imp ?_ hins
      intro a b hab
      rcases hab with rfl | ⟨rfl, ha⟩
      · exact Or.inl (permW3_succ a)
      · right; refine ⟨rfl, ?_⟩
        rcases ha with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    have heval3' : ∀ x : Fin 7 → Bool, (x3'.wires (true :: List.ofFn x)).getD (x2'.output + 1) false = (thetaFun x || x 2) := by
      intro x
      change (wiresFrom (x3.gates.map permG3) (true :: List.ofFn x)).getD (permW2 x2.output + 1) false = _
      rw [← permW3_succ x2.output]
      rw [wiresFrom_perm3 x3.gates (true :: List.ofFn (fun i => x (sigma7 i))) (true :: List.ofFn x) (by simp) (by simp) (fun j => by
        by_cases hj : j = 0
        · subst hj; rfl
        · by_cases hj8 : j < 8
          · have h1 : 1 ≤ j ∧ j < 8 := by omega
            unfold permW3; rw [dif_pos h1]
            have hj_pos : j = (j - 1) + 1 := by omega
            conv_rhs => rw [hj_pos]
            rw [List.getD_cons_succ, List.getD_cons_succ,
                List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (sigma7 ⟨j - 1, by omega⟩).isLt),
                List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega)]
            simp only [List.getElem_ofFn]
          · unfold permW3; rw [dif_neg (by omega), List.getD_eq_default _ false (by simp; omega), List.getD_eq_default _ false (by simp; omega)])]
      have h := heval3 (fun i => x (sigma7 i))
      change (wiresFrom x3.gates (true :: List.ofFn (fun i => x (sigma7 i)))).getD (x2.output + 1) false = _ at h
      rw [h, theta_sigma7]; rfl
    have hor2' : (x2'.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).length = 2 := by
      have hfilt : (x2.gates.map permG2).filter (fun g => g.op.eval [true, false] && g.inputs.contains 2) =
          (x2.gates.filter (fun g => g.op.eval [true, false] && g.inputs.contains 2)).map permG2 := by
        rw [List.filter_map]
        apply congrArg (List.map permG2)
        apply congrArg (fun p => List.filter p x2.gates)
        funext g
        simp only [Function.comp_apply, permG2]
        congr 1
        rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
        constructor
        · rintro ⟨a, ha, ha2⟩; rwa [← (permW2_eq_two_iff a).mp ha2]
        · intro h2; exact ⟨2, h2, rfl⟩
      rw [show x2'.gates = x2.gates.map permG2 from rfl, hfilt, List.length_map, hor2]
    obtain ⟨D'⟩ := extract_elim_data x2' x3' (permW2 x4) (permW2 x5) hfan' hsz' heval2' hedit' heval3' hor2'
    have hms_eq : D'.ms = D.ms.map permG6 := by
      have h1 : D'.ms = (elim 6 (x3.gates.map permG3) (initSt, [])).2 := congrArg Prod.snd D'.hst_eq
      have h2 : D.ms = (elim 6 x3.gates (initSt, [])).2 := congrArg Prod.snd D.hst_eq
      rw [h1, h2]
      exact elim_perm3 x3.gates (initSt, []) (initSt, []) rfl (by simp [initSt]) (fun i => by
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | n
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · have hp : permW3 (n + 8) = n + 8 := by unfold permW3; rw [dif_neg (by omega)]
          rw [hp, List.getD_eq_default _ (Stat.const false) (by simp [initSt])]; rfl) rfl
    have hSideA' : SideNoTopBranch D'.ms sideA := by
      rw [hms_eq]; exact sideB_to_sideA_ms D.ms hSideB
    exact sideA_impossible x2' x3' (permW2 x4) (permW2 x5) hfan' hsz' heval2' hedit' heval3' D' hSideA'

end Step3

end PEqualNP.Outside.L_meta_4797_aux

theorem PEqualNP.Outside.L_meta_4797 : have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length = (2 : ℕ) → False := by
  dsimp only
  intro x2 x3 x4 x5 hfan hsz heval2 hedit heval3 hor2
  exact PEqualNP.Outside.L_meta_4797_aux.Step3.L_meta_4797_proof x2 x3 x4 x5 hfan hsz heval2 hedit heval3 hor2
