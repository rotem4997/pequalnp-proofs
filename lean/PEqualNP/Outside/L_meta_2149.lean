import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2149
namespace Binary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace BranchGraph
variable {V : Type*} [DecidableEq V]
def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I,∃ b ∈ I,G.Adj a b
omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w}:=by
  rintro ⟨a,ha,b,hb,hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab
lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w}↔G.Adj u w:=by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u,by simp,w,by simp,h⟩
def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S,∀ b ∈ S,¬ G.Adj a b
section FiniteGraph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v∧v ∉ removed)
lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u:=by
  intro v membership
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at membership ⊢
  exact ⟨membership.1,fun vIn => membership.2 (h vIn)⟩
lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w:=by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B):=by
    ext z
    simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hz => ⟨⟨hz.1,fun zIn => hz.2 (h zIn)⟩,hz.2⟩,fun hz => ⟨hz.1.1,hz.2⟩⟩
  rw [e u,e w,same]
def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group,∀ w ∈ group,(neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w
def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)
def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed∧(neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed∧neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅
def closeIsolates (removed : Finset V) : Finset V:=removed ∪ isolates G removed
def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)
lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root:=by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root:=by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty:=by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root):=by
    simp [isolates,Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu
theorem dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V,A ∪ Q ⊆ removeClass G B root:=by
  classical
  by_cases someActive : ∃ root ∈ Q,root ∉ B∧(neighborsAfter G B root).Nonempty
  · obtain ⟨root,rootQ,rootOut,rootLive⟩:=someActive
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU:=live.mono (neighborsAfter_subset G smaller u)
      have oldRoot:=rootLive.mono (neighborsAfter_subset G smaller root)
      have same:=neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root:=by simp [maximalClass,rootOut,rootLive,uIn,same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V:=Classical.choice inferInstance
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u,hu,uIn,live⟩)
lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty:=by
  have uOut : u ∉ removed:=fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty:=by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates,Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v,hv⟩:=old
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  refine ⟨v,?_⟩
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨hv.1,fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v:=by
      simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hv.1.symm,uOut⟩
    have none : neighborsAfter G removed v = ∅:=by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness
lemma closeIsolates_idempotent (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed:=by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live:=retained_after_close G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅:=by
      simpa [isolates] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left
def TwinSteps : Finset V → List (Finset V) → Prop
  | _,[] => True
  | removed,group :: rest => TwinGroup G removed group∧TwinSteps (removed ∪ group) rest
def removedThrough : Finset V → List (Finset V) → Finset V
  | removed,[] => removed
  | removed,group :: rest => removedThrough (removed ∪ group) rest
def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0,start,finish => finish = start
  | k + 1,start,finish => ∃ root : V,ClassSteps k (removeClass G start root) finish
theorem dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V,ClassSteps G groups.length B finish∧removedThrough A groups ⊆ finish:=by
  induction groups generalizing A B with
  | nil => exact ⟨B,rfl,smaller⟩
  | cons group rest ih =>
    obtain ⟨twins,next⟩:=steps
    obtain ⟨root,subset⟩:=dominates_step G smaller twins
    obtain ⟨finish,walk,covered⟩:=ih subset next
    exact ⟨finish,⟨root,walk⟩,covered⟩
def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v,u ∉ removed → v ∉ removed → ¬ G.Adj u v
omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B:=by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))
lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ:=by
  ext u
  simp only [Finset.mem_univ,iff_true]
  by_contra out
  obtain ⟨v,hv⟩:=retained_after_close G out
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  exact noEdges u v out hv.2 hv.1
lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V,start = closeIsolates G D) : ∃ D : Finset V,finish = closeIsolates G D:=by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root,after⟩:=walk
    exact ih after ⟨_,rfl⟩
theorem covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ:=by
  obtain ⟨D,steps,subset⟩:=dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges:=edgeless_mono G subset finished
  obtain ⟨A,hD⟩:=classSteps_finish_closed G steps ⟨∅,rfl⟩
  rw [hD] at noEdges
  rwa [hD,closed_edgeless_all G noEdges] at steps
end FiniteGraph
end BranchGraph
namespace BranchGroupsLean
open BranchGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}
def bucket (label : V → Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v = r)
def below (label : V → Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v < r)
def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)
omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅:=by
  ext v
  simp [coveredBy]
lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r:=by
  ext v
  simp [coveredBy,bucket,List.mem_append]
omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V,label v = out∨label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r:=by
  have facts:=List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy,below,Finset.mem_filter,Finset.mem_univ,true_and]
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
    have after:=(List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim
section Graph
variable (G : SimpleGraph V) [DecidableRel G.Adj]
theorem sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V,label v = out∨label v ∈ roots)
    (beforeOut : ∀ r ∈ roots,r < out)
    (twinAt : ∀ r ∈ roots,TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)):=by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots:=complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev:=covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next:=ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_,?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next
lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending):=by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton,ih]
    simp [List.append_assoc]
omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V,label v = out∨label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))):=by
  rw [← coveredBy_nil label,removedThrough_coveredBy,List.nil_append]
  intro u v uNot vNot
  have hu : label u = out:=(allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out:=(allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket,hu]) v (by simp [bucket,hv])
theorem roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V,label v = out∨label v ∈ branches)
    (beforeOut : ∀ r ∈ branches,r < out)
    (twinAt : ∀ r ∈ branches,TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V),TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card:=by
  let roots:=branches.sort
  have sorted : roots.Pairwise (· < ·):=List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out∨label v ∈ roots:=by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out:=beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)):=by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last:=no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last
end Graph
end BranchGroupsLean
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w):=by
  simp [wiresFrom,List.foldl_append]
theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool,wiresFrom gs w = w ++ t∧t.length = gs.length:=by
  induction gs with
  | nil => intro w; exact ⟨[],by simp [wiresFrom],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
    rw [this,ht]; simp
theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length:=by
  obtain ⟨t,ht,hl⟩:=wiresFrom_prefix gs w
  rw [ht]; simp [hl]
theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false:=by
  obtain ⟨t,ht,_⟩:=wiresFrom_prefix gs w
  rw [ht,List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length ≤ 2
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j≠L.length) :
    (L ++ [S]).getD j d = L.getD j d:=by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S:=by
  simp
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def NOk (g : Gate) : Prop:=Ok g∧(g.op = GateOp.not → g.inputs.length ≤ 1)
abbrev Stat:=Sum Bool ℕ
def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none,Sum.inl true)
  | Sum.inl c :: _ => (none,Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none,Sum.inl true)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none,Sum.inl false)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none,Sum.inl false)
theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1,Ok g:=by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg
theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and∨op = GateOp.or∨op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c,Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none:=by
  obtain ⟨c,hc⟩:=hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify,simpAnd]
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify,simpOr]
  · have:=hnot rfl
    rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [simplify,simpNot]
theorem simplify_sound (op : GateOp) (hop : op = GateOp.and∨op = GateOp.or∨op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins,s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)):=by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify,simpAnd,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify,simpOr,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a,l⟩
    · simp [simplify,simpNot,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [simplify,simpNot,Stat.Valid,Stat.val,GateOp.eval,wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S:=by
  subst h; simp
theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1:=by
  cases o <;> simp
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length:=by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1:=ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1:=by
      simp only [elimStep,List.length_append]
      have:=toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g):=rfl
    rw [h3,List.length_cons]; omega
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat,s.Valid m → s.Valid m'
  | Sum.inl _,_ => trivial
  | Sum.inr _,hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat,s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _,_ => rfl
  | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length∧∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false
theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc):=by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl,hi⟩:=h
    set w':=wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length:=by rw [hw',length_wiresFrom,hy]
    set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok:=hok g List.mem_cons_self
    have hs:=simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r:=simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false:=by
      rw [hins,List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w':=by
      rw [wiresFrom_append]
    obtain ⟨t,ht,htl⟩:=wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep,hl],?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew,List.length_append,← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq,hl,getD_snoc_eq]
      exact ⟨hs.1,by rw [hs.2,hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil,getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1,?_⟩
      rw [ht,Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)
lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1,g.op = op:=by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg
lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs:=by
  simp [opCount]
lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0):=by
  by_cases h : test g.op <;> simp [opCount,h]
lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0):=by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1:=by simp [h]
    have he:=simplify_same_op op m ins g hg
    simp [h,opCount_cons,opCount,he]
lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs:=by
  induction gs with
  | nil => intro acc; simp [elim,opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep,opCount_append,opCount_cons]
    have hb:=simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
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
  (g.op = GateOp.not∧∃ j,j < m∧g.inputs = [j]) ∨
  ((g.op = GateOp.and∨g.op = GateOp.or)∧∃ j k,j < m∧k < m∧g.inputs = [j,k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate),gs[p]? = some g → CleanGate (m + p) g
theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g:=by
  rcases h with ⟨h1,j,_,h2⟩ | ⟨h1 | h1,j,k,_,_,h2⟩
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_,?_⟩,?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs,a < m:=by
  intro a ha
  rcases h with ⟨_,j,hj,h2⟩ | ⟨_,j,k,hj,hk,h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs,NOk g:=by
  intro g hg
  obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins,s.Valid m) :
    ∀ g ∈ (simplify op m ins).1,CleanGate m g:=by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl,_,?_,rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0∧a ∈ o:=by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2:=by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g':=hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0,hmem⟩:=toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length:=by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def idStats (n : ℕ) : List Stat:=List.ofFn (fun i : Fin n => Sum.inr i)
theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n,[]):=by
  refine ⟨by simp [idStats],?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats,hlt,Stat.Valid,Stat.val,wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩
theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j:=by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α),l[p]? = some g →
    ∃ pre post,l = pre ++ g :: post∧pre.length = p:=by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[],l,rfl,rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre,post,rfl,rfl⟩:=ih p g h
      exact ⟨x :: pre,post,rfl,rfl⟩
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs,k ∉ g.inputs) → w.length = w'.length →
    (∀ j,j≠k → w.getD j false = w'.getD j false) →
    ∀ j,j≠k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false:=by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno':=hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl,getD_snoc_eq,hl,getD_snoc_eq,e]
    · rw [getD_snoc_ne _ _ _ _ hjl,getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false
theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j,h⟩:=by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j,h⟩
theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)):=by
  have hlt:=(hcl p g hp).lt
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length:=by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]):=by
    rw [wiresFrom_append]; rfl
  have full : ∀ j,j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false:=by
    intro j hj
    rw [e,getD_wiresFrom _ _ j (by simp [hwl]; omega),getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false):=by
    rw [e,getD_wiresFrom _ _ _ (by simp [hwl]),getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs,vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p):=by
  rw [vl_gate gs hcl u p g hp,vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool,S.Valid (k + (elim k pre (idStats k,[])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool,vl (pre ++ g :: post) y o≠vl (pre ++ g :: post) y' o) :
    ∃ gs' o',CleanL k gs'∧gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl (pre ++ g :: post) y o:=by
  have hok : ∀ g' ∈ pre ++ g :: post,Ok g':=fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post,Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool,Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k,[])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool,(wiresFrom pre (List.ofFn y)).length = k + pre.length:=by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool,wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]):=by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool,vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false):=by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull,getD_wiresFrom _ _ _ (by simp [hwl y]),getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool,Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2):=by
    intro y
    obtain ⟨hl,hi⟩:=inv1 y
    refine ⟨by simp [hl],?_⟩
    intro a
    show (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (idStats k,[])).2.length) ∧
      (((elim k pre (idStats k,[])).1 ++ [S]).getD a (Sum.inl false)).val
        (wiresFrom (elim k pre (idStats k,[])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k,[])).1.length
    · rw [hal,getD_snoc_eq,hl,getD_snoc_eq]
      exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal,getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool,Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)):=by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k,[])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k,[])).1 ++ [S],(elim k pre (idStats k,[])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
      (elim k pre (idStats k,[])).2)).2.length + 1 ≤ (pre ++ g :: post).length:=by
    have h1 : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
        (elim k pre (idStats k,[])).2)).2.length
        ≤ (elim k pre (idStats k,[])).2.length + post.length:=elim_len k post _
    have h2 : (elim k pre (idStats k,[])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k,[])
    simp only [List.length_append,List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k,[])).1 ++ [S],
        (elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
          (elim k pre (idStats k,[])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o:=fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k,[])).1 ++ [S],
      (elim k pre (idStats k,[])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨_,j,hc3,hlen,?_,?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k,[])) _)
    · intro y
      have h:=hval y
      rw [hst] at h
      exact h
theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool,vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool,vl gs y o≠vl gs y' o) :
    ∃ gs' o',CleanL k gs'∧gs'.length + 1 ≤ gs.length∧nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]? = some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post:=by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k,[])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre,Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1:=inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1,?_⟩
  rw [(inv1.2 j).2,heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append,getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]
end CircuitProof
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b∧a≠cut∧b≠cut
theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b≠y b → ∃ a,edge a b∧x a≠y a)
    (sameCut : x cut = y cut) {out : W} (different : x out≠y out) :
    ∃ a,input a∧x a≠y a∧Relation.ReflTransGen (avoid edge cut) a out:=by
  classical
  have track : ∀ k b,rank b = k → x b≠y b →
      ∃ a,input a∧x a≠y a∧Relation.ReflTransGen (avoid edge cut) a b:=by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b,hInput,diff,Relation.ReflTransGen.refl⟩
      · obtain ⟨p,hp,dp⟩:=localStep b hInput diff
        have earlier : rank p < k:=(order p b hp).trans_eq hb
        obtain ⟨a,ha,da,path⟩:=ih (rank p) earlier p rfl dp
        have pOff : p≠cut:=by rintro rfl; exact dp sameCut
        have bOff : b≠cut:=by rintro rfl; exact diff sameCut
        exact ⟨a,ha,da,path.tail ⟨hp,pOff,bOff⟩⟩
  exact track (rank out) out rfl different
theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b,edge a b → rank a < rank b)
    (localStep : ∀ b,¬ input b → x b≠y b → ∃ a,edge a b∧x a≠y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a,input a → x a≠y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out:=by
  by_contra different
  obtain ⟨a,ha,da,reaches⟩:=difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches
theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y,w x = w y → f x = f y) :
    ∃ outer : Bool → Bool,∀ x,outer (w x) = f x:=by
  classical
  let outer (b : Bool):=if hb : ∃ a,w a = b then f (Classical.choose hb) else false
  refine ⟨outer,fun x => ?_⟩
  have hx : ∃ a,w a = w x:=⟨x,rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)
def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)
def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate),gs[p]? = some g∧b.val = n + p∧a.val ∈ g.inputs
theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val:=by
  obtain ⟨p,g,hpg,hb,ha⟩:=edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha
private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val≠vl gs y b.val) :
    ∃ a : Fin (n + gs.length),readEdge gs a b∧vl gs x a.val≠vl gs y a.val:=by
  let p:=b.val - n
  have hb : b.val = n + p:=by dsimp [p]; omega
  have hp : p < gs.length:=by have:=b.isLt; omega
  let g:=gs[p]
  have hpg : gs[p]? = some g:=List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs,vl gs x a≠vl gs y a:=by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a,ha,da⟩)
  obtain ⟨a,ha,da⟩:=differingRead
  have ha':=(hcl p g hpg).lt a ha
  refine ⟨⟨a,by have:=b.isLt; omega⟩,⟨p,g,hpg,hb,ha⟩,da⟩
theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n,x i≠y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val:=by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n:=⟨a.val,ha⟩
    have sameWire : inputWire gs i = a:=Fin.ext rfl
    have di : x i≠y i:=by
      rw [vl_input gs x a.val ha,vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di
theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool,∀ x : Fin n → Bool,(∀ i,¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val:=by
  let Fiber:={x : Fin n → Bool // ∀ i,¬ group i → x i = base i}
  obtain ⟨outer,ho⟩:=unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer,fun x agrees => ho ⟨x,agrees⟩⟩
end PetersenCutTrace
namespace CircuitProof.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool,f (Function.update x p (!x p))≠f x
def Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs∧(∀ x : Fin m → Bool,vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' → (∀ x : Fin m → Bool,vl gs' x o' = f x) →
    nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length
def Least.hcl {m f gs o} (h : Least m f gs o):=h.1
def Least.hev {m f gs o} (h : Least m f gs o):=h.2.1
def Least.hmin {m f gs o} (h : Least m f gs o):=h.2.2
def Reads (gs : List Gate) (p w : ℕ) : Prop:=∃ g,gs[p]? = some g∧w ∈ g.inputs
theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool,f x≠f y:=by
  obtain ⟨x,hx⟩:=h
  exact ⟨_,_,hx⟩
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q:=by
  obtain ⟨g,hg,hw⟩:=h
  exact (hcl q g hg).lt w hw
theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false:=by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool,C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y,f x≠f y) :
    ∃ gs o,CleanL n gs∧nonNotCount gs ≤ nonNotCount C.gates∧∀ x,vl gs x o = f x:=by
  have hok : ∀ g ∈ C.gates,Ok g:=hfan
  set acc:=elim n C.gates (idStats n,[]) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y:=by
    intro y
    rw [((hinv y).2 C.output).2,← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨acc.2,j,?_,?_,?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount,hacc] using elim_nonNotCount n C.gates (idStats n,[])
    · intro y
      simpa only [hst,Stat.val,vl] using hval y
theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool,C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y,f x≠f y) :
    ∃ gs o,Least n f gs o∧nonNotCount gs ≤ nonNotCount C.gates:=by
  classical
  let admissible (t : ℕ):=∃ gs o,CleanL n gs∧nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x,vl gs x o = f x)∧gs.length = t
  obtain ⟨gs,o,clean,count,he⟩:=clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t,admissible t:=⟨gs.length,gs,o,clean,count,he,rfl⟩
  obtain ⟨gs',o',hc,hb,he',hl⟩:=Nat.find_spec existsAdmissible
  refine ⟨gs',o',⟨hc,he',?_⟩,hb⟩
  intro testGates testOut testClean testEval testCost
  have lower:=Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates,testOut,testClean,testCost.trans hb,testEval,rfl⟩)
  exact hl.trans_le lower
theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o≠k + p) (hno : ∀ q,¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool,vl gs y o≠vl gs y' o) :
    ∃ gs' o',CleanL k gs'∧gs'.length + 1 ≤ gs.length∧nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k → Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]? = some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p:=by
    rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩ <;> omega
  let g0 : Gate:=⟨GateOp.and,[0,0]⟩
  let gs':=gs.set p g0
  have hlen : gs'.length = gs.length:=by simp [gs']
  have hget_p : gs'[p]? = some g0:=by simp [gs',hp]
  have hget_ne : ∀ r,r≠p → gs'[r]? = gs[r]?:=by
    intro r hr
    simp [gs',Ne.symm hr]
  have hcl' : CleanL k gs':=by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool,∀ w,w≠k + p → vl gs' y w = vl gs y w:=by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk,vl_input gs y w hwk]
      · obtain ⟨r,rfl⟩ : ∃ r,w = k + r:=⟨w - k,by omega⟩
        have hrp : r≠p:=fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega),vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g':=by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr',vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt:=(hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g',hr,e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool,vl gs' y (k + p) = vl gs' y 0:=by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0,GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool,vl gs' y o≠vl gs' y' o:=by
    obtain ⟨y,y',h⟩:=hnc
    exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho]; exact h⟩
  obtain ⟨gs'',o'',hc'',hl'',hcost,he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs:=by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'',o'',hc'',by omega,hcost.trans hkeep,fun y => by rw [he'' y,hagree y o ho]⟩
section LocalSection1
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x≠f y) :
    ∃ y y' : Fin m → Bool,vl gs y o≠vl gs y' o:=by
  obtain ⟨x,y,h⟩:=hnc
  exact ⟨x,y,by rw [L.hev,L.hev]; exact h⟩
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x≠f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool,vl gs u (m + p) = vl gs u j:=by
  intro hall
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x≠f y) (p : ℕ)
    (hp : p < gs.length) (ho : o≠m + p) : ∃ q,p < q∧Reads gs q (m + p):=by
  by_contra hno
  have hno' : ∀ q,¬ Reads gs q (m + p):=by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q,hpq,hq⟩
    · have:=reads_lt L.hcl hq
      omega
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega
theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool,∃ x y : Fin m → Bool,
      f (Function.update x i b)≠f (Function.update y i b)) : ∃ q,Reads gs q i:=by
  by_contra hno
  have hno' : ∀ g ∈ gs,(i : ℕ) ∉ g.inputs:=by
    intro g hg hi
    obtain ⟨q,hq⟩:=List.mem_iff_getElem?.1 hg
    exact hno ⟨q,g,hq,hi⟩
  have hoi : o≠i:=by
    intro e
    obtain ⟨x,y,hxy⟩:=hnc false
    apply hxy
    rw [← L.hev,← L.hev,e,vl_input gs _ i i.isLt,vl_input gs _ i i.isLt]
    simp
  obtain ⟨x,hx⟩:=hd
  apply hx
  rw [← L.hev,← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j,hjm⟩ from getD_ofFn m _ false ⟨j,hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j,hjm⟩ from getD_ofFn m x false ⟨j,hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
end LocalSection1
end CircuitProof.Readers
namespace CircuitProof.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
open CircuitProof.Readers
theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool,f x≠f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and∨g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a,b]) : a≠b:=by
  rintro rfl
  have hcl:=L.hcl p g hg
  have hlt : a < m + p:=by
    rcases hcl with ⟨h1,j,_,h2⟩ | ⟨h1,j,k,hj,hk,h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg,hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
end CircuitProof.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm
theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w≠out) :
    ∃ p,Reads gs p w:=by
  by_cases isInput : w < n
  · let v : Fin n:=⟨w,isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p:=w - n
    have wire : w = n + p:=by dsimp [p]; omega
    have pLt : p < gs.length:=by omega
    have notOut : out≠n + p:=by omega
    obtain ⟨q,_,read⟩:=least.live nonconstant p pLt notOut
    exact ⟨q,wire.symm ▸ read⟩
theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup:=by
  obtain ⟨slot,atSlot⟩:=List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [args]
  · have distinct:=pq2f_nodup least nonconstant atSlot ops args
    simp [args,distinct]
theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val≠out) :
    ∃ (p : Nat) (g : Gate),gs[p]? = some g∧w.val ∈ g.inputs∧n + p < n + gs.length:=by
  obtain ⟨p,g,hit,reads⟩:=least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound:=(List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p,g,hit,reads,by omega⟩
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers
def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; omega
    let g:=gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val,by
      have atSlot : gs[slot]? = some g:=List.getElem?_eq_getElem hs
      have before:=(clean slot g atSlot).lt a.val a.property
      omega⟩
  else []
theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have:=b.isLt; omega)).inputs:=by
  simp [predecessors,internal,List.map_map,Function.comp_def]
theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = []:=by
  simp [predecessors,show ¬ n ≤ b.val by omega]
theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs:=by
  have isGate : n ≤ b.val:=by omega
  have which : b.val - n = p:=by omega
  have located:=(List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which,located] using predecessors_values clean b isGate
theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b↔readEdge gs a b:=by
  by_cases internal : n ≤ b.val
  · let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; dsimp [slot]; omega
    let g:=gs[slot]'hs
    have wire : b.val = n + slot:=by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g:=List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot,g,atSlot,wire,?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a,mem,rfl⟩
    · rintro ⟨q,h,atQ,wireQ,inside⟩
      have same : q = slot:=by omega
      subst q
      have gateSame : h = g:=Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a',mem,equal⟩:=List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = []:=by simp [predecessors,internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot,g,_,wire,_⟩
      omega
theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup:=by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact PEqualNP.Outside.L_meta_2149.Binary.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have:=b.isLt; omega))
  · simp [predecessors,internal]
end PetersenCutTrace
namespace PetersenScratch
open PEqualNP.MetaComplexity
def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q
def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p∨0 < occurrences j p
def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k
def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)
def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a&&b else a||b
noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool:=by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q
noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit:=if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)
private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k,0 < occurrences k p → x k = y k) : p.eval x = p.eval y:=by
  induction p with
  | lit k s =>
    have e:=h k (by simp [occurrences])
    simp [DMFormula.eval,e]
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
    pairValue i j base p a b = pairValue i j base p a' b:=by
  apply eval_agree
  intro k hk
  have ne : k≠i:=by rintro rfl; omega
  simp [pairInput,ne]
private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b':=by
  apply eval_agree
  intro k hk
  have ne : k≠j:=by rintro rfl; omega
  simp [pairInput,ne]
def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b,f false b≠f true b
private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b,Q false b = Q true b) : changes P:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp,hQ])⟩
private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b,P false b = P true b) : changes Q:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq,hP])⟩
private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false:=by
  have hi : occurrences i p = 0:=by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0:=by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)
private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b',binOp conj (P a b) c≠binOp conj (P a' b') c) :
    ∀ a b,binOp conj (P a b) c = P a b:=by
  cases conj <;> cases c <;> simp [binOp] at h ⊢
private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a:=by
  cases conj <;> cases a <;> cases b <;> rfl
private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p∨hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b,pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b,pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b:=by
  classical
  have pl : hasPair i j p → ∀ a b,pairValue i j base p a b = pairKernel i j p a b:=by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b,pairValue i j base q a b = pairKernel i j q a b:=by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b'):=by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine,hp,hq,pl hp,ql hq]
    · rw [constant_pair hq a b]
      have hn:=nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b,pl hp]
      simp [combine,hp,hq]
  · have hq:=present.resolve_left hp
    rw [constant_pair hp a b,bin_comm]
    have hn:=nonconst
    simp_rw [constant_pair hp,bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b,ql hq]
    simp [combine,hp]
private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b,pairValue i j base p a b = pairKernel i j p a b:=by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue,pairKernel,DMFormula.eval,pairInput,hki]
    · have hkj : k = j:=by
        by_contra h
        simp [hasPair,occurrences,hki,h] at present
      simp [pairValue,pairKernel,DMFormula.eval,pairInput,hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p∨hasPair i j q:=by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p∨hasPair i j q:=by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq
theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b,outerA (pairValue i j baseA p a b) = (a&&b))
    (hO : ∀ a b,outerO (pairValue i j baseO p a b) = (a||b)) : False:=by
  have depAi : changes (pairValue i j baseA p):=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b:=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p):=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b:=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have present : hasPair i j p:=by
    left
    by_contra! h
    obtain ⟨b,hb⟩:=depAi
    exact hb (absent_left (by omega) false true b)
  have stableA:=stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO:=stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false≠pairKernel i j p false true:=by
    intro e
    have f:=congrArg outerO e
    rw [hO,hO] at f
    cases f
  have zeros:=hA false false
  have other:=hA false true
  have one:=hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all
noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool:=by
  classical
  exact decide (∃ u v,G.Adj u v∧x u = true∧x v = true)
private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true:=by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u,v,h,hu,hv⟩
private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w,x w = true → w = u∨w = v) :
    edgeValue G x = false:=by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s,t,es,hs,ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es
private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a&&b):=by
  cases a <;> cases b
  · apply edgeValue_false_pair (u:=i) (v:=i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u:=j) (v:=j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput,hki,hkj] at hk ⊢
  · apply edgeValue_false_pair (u:=i) (v:=i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput,hki,hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput,h.ne.symm])
private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i≠j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u∨k = v)) a b) = (a||b):=by
  have hu : pairInput i j (fun k => decide (k = u∨k = v)) a b u = true:=by
    simp [pairInput,hiu.ne.symm,huj]
  have hv : pairInput i j (fun k => decide (k = u∨k = v)) a b v = true:=by
    simp [pairInput,hvi,hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput,hki,hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput,hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu
theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool,∃ outer : Bool → Bool,∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False:=by
  obtain ⟨outerA,ha⟩:=factors (fun _ => false)
  obtain ⟨outerO,ho⟩:=factors (fun k => decide (k = u∨k = v))
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
    (negFormula p).eval x = !(p.eval x):=by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula,DMFormula.eval,e]
  | and a b iha ihb =>
    simp only [negFormula,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p:=by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula,occurrences,iha,ihb]
  | or a b iha ihb => simp [negFormula,occurrences,iha,ihb]
def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w,hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op,g.inputs with
      | .not,[a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _,_ => .lit fallback true
termination_by w
decreasing_by all_goals assumption
theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true:=by
  rw [wireFormula]
  simp [i.isLt]
private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [wireFormula]
  simp [hn,hp,hg,op,inputs,ha]
private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a,b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [wireFormula]
  simp [hn,hp,hg,op,inputs,ha,hb]
private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a,b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [wireFormula]
  simp [hn,hp,hg,op,inputs,ha,hb]
theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w,hi⟩,vl_input gs x w hi]
      rfl
    · obtain ⟨p,rfl⟩ : ∃ p,w = n + p:=⟨w - n,by omega⟩
      have hp : p < gs.length:=by omega
      let g:=gs[p]
      have hg : gs[p]? = some g:=List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha,negFormula_eval,ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),vl_gate gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0:=by
  rw [wireFormula_input]
  rfl
theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum:=by
  rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha,inputs,negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb,inputs,occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb,inputs,occurrences]
theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum:=by
  rw [hb,wireFormula_count_gate fallback hcl chosen hg,← parentsVal,List.map_map]
  rfl
end PetersenCutFormula
namespace PetersenCutIndependent
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch
theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0:=by
  let i : Fin n:=⟨a.val,ha⟩
  have e : i = chosen↔a = inputWire gs chosen:=by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input,e]
theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out∨∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool,∀ x : Fin n → Bool,(∀ i,¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val:=by
  rcases controlled with rfl | blocked
  · exact ⟨id,fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked
theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x,vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out∨∀ k : Fin n,(k = i∨k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False:=by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f,hf⟩:=cut_factors hcl cut out (fun k => k = i∨k = j) base controlled
  refine ⟨f,fun a b => ?_⟩
  have agree : ∀ k,¬ (k = i∨k = j) → pairInput i j base a b k = base k:=by
    intro k hk
    simp [pairInput,show k≠i from fun e => hk (Or.inl e),
      show k≠j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)
end PetersenCutIndependent
namespace FirstBranchRoute
open Relation
variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)
def Branches (v : Fin m) : Prop:=∃ a b,reads v a∧reads v b∧a≠b
def Terminal (v : Fin m) : Prop:=v = output∨Branches reads v
def Follow (v w : Fin m) : Prop:=reads v w∧¬ Terminal reads output v
lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b:=by
  by_contra separate
  exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)
variable (forward : ∀ {v w : Fin m},reads v w → v < w)
variable (live : ∀ v : Fin m,v≠output → ∃ w,reads v w)
include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m,Terminal reads output root∧ReflTransGen (Follow reads output) v root:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v,terminal,ReflTransGen.refl⟩
    obtain ⟨next,edge⟩:=live v (fun e => terminal (Or.inl e))
    have increase:=forward edge
    have closer : distance next < distance v:=by
      dsimp [distance]
      have bounds:=next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root,stopped,route⟩:=ih next closer
    exact ⟨root,stopped,route.head ⟨edge,terminal⟩⟩
include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next,edge,tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_,edgeB,_⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB,edgeB,tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal:=follow_unique reads output edge edgeB
      subst nextB
      have increase:=forward edge.1
      have closer : distance next < distance v:=by
        dsimp [distance]
        have bounds:=next.isLt
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
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w:=by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))
lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))
theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w∧first reads output forward live w = first reads output forward live v:=by
  induction route with
  | refl => exact ⟨ReflTransGen.refl,rfl⟩
  | tail _ edge ih =>
    have predecessorBefore:=lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _:=⟨edge,fun stopped => by
      have self:=first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step,(first_of_follows reads output forward live step).symm.trans label⟩
theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w:=by
  by_contra tooLate
  have earlier:=lt_of_not_ge tooLate
  have same:=(read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b:=by
  have earlier:=lt_of_lt_of_le (forward edge) bound
  have same:=(read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge,fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
def Avoid (cut v w : Fin m) : Prop:=reads v w∧v≠cut
lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v:=by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label:=(read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier:=lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _:=⟨edge.1,fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same:=(first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _
theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after
include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
      · exact bHere
      have equal : next = goal:=follow_unique reads output stepB edgeA
      subst next
      have increasing:=path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
      · subst b
        have equal : nextA = goal:=follow_unique reads output stepA edgeB
        subst nextA
        have increasing:=path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal:=follow_unique reads output stepA stepB
      subst nextB
      have increase:=forward stepA.1
      have closer : distance nextA < distance source:=by
        dsimp [distance]
        have bounds:=nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB
theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b:=by
  have aBound:=le_trans (le_of_lt (forward edgeA)) bound
  have bBound:=le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)
lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs,0 < weight a:=by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a,by simp,h⟩
    have hr : 0 < (rest.map weight).sum:=by
      simp only [List.map_cons,List.sum_cons] at positive
      omega
    obtain ⟨b,hb,hbPos⟩:=ih hr
    exact ⟨b,by simp [hb],hbPos⟩
lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs,weight a ≤ 1)
    (unique : ∀ a ∈ xs,∀ b ∈ xs,0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1:=by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons,List.sum_cons]
    by_cases h : weight a = 0
    · rw [h,Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0:=by
      by_contra some
      obtain ⟨b,hb,hbPos⟩:=witness_of_positive_sum weight rest (by omega)
      have equal:=unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero,Nat.add_zero]
    exact small a (by simp)
section Count
variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m,reads a b↔a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m,v≠source → weight v = ((parents v).map weight).sum)
include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v:=by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a,member,hp⟩:=witness_of_positive_sum weight (parents v) positive
    have edge:=(reads_parent a v).mpr member
    have earlier:=forward edge
    exact (ih a earlier hp).tail edge
include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v,(parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1:=by
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
      have earlier:=forward ((reads_parent a v).mpr member)
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
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut
theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut↔firstInputBoundary clean out live i = cut:=by
  simp [firstInputGroup]
theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out:=by
  let last : Fin (n + gs.length):=⟨n + gs.length - 1,by have:=out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last:=by
    change v.val ≤ n + gs.length - 1
    have:=v.isLt
    omega
  have lastOut : last = out:=by
    by_contra notOutput
    obtain ⟨v,e⟩:=live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w
theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (distinct : ∀ w,(predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1:=by
  let weight (a : Fin (n + gs.length)):=occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n:=chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1:=by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary,ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length),w≠inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum:=by
    intro w other
    by_cases primary : w.val < n
    · simp [weight,wireFormula_count_input_fin fallback chosen w primary,other,
        predecessors_nil_input clean w primary]
    · let p:=w.val - n
      have hp : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have hw : w.val = n + p:=by dsimp [p]; omega
      let g:=gs[p]
      have atSlot : gs[p]? = some g:=List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl
theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out∨∀ k : Fin n,k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out:=by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out:=lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere:=(mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out:=by rwa [firstHere]
  have blocked:=FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1,e.2.1⟩) _ _ path
theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out → ∃ v,readEdge gs w v)
    (distinct : ∀ w,(predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x,vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j,G.Adj i j → ∃ u v,
      G.Adj i u∧G.Adj j v∧u≠j∧v≠i∧¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut):=by
  intro i iIn j jIn adjacent
  obtain ⟨u,v,hiu,hjv,huj,hvi,huv⟩:=witnesses i j adjacent
  have iFirst:=(mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst:=(mem_firstInputGroup clean out live cut j).mp jIn
  have iCount:=firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount:=firstInputBoundary_occurrences_le_one clean out live distinct i j
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
abbrev Vertex:=Fin 9
abbrev Edges:=List (Vertex × Vertex)
def edges : Edges:=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1&&x edge.2)
lemma noLoops : ∀ e ∈ edges,e.1≠e.2:=by decide
lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true↔∃ a b,(a,b) ∈ es∧x a = true∧x b = true:=by
  simp only [edgeFun,List.any_eq_true,Bool.and_eq_true,Prod.exists]
def graph (es : Edges) (noSelf : ∀ e ∈ es,e.1≠e.2) : SimpleGraph Vertex where
  Adj a b:=(a,b) ∈ es∨(b,a) ∈ es
  symm:=⟨fun _ _ => Or.symm⟩
  loopless:=⟨fun v h => h.elim (fun he => noSelf (v,v) he rfl) (fun he => noSelf (v,v) he rfl)⟩
end PetersenNine
namespace PetersenGroupBFS
def MaskGraph:=Nat × (Nat → Nat)
def MaskGraph.width (g : MaskGraph):=g.1
def MaskGraph.adjacency (g : MaskGraph):=g.2
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
        (residualNeighbors g deleted v==residualNeighbors g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0
theorem bit_at (v w : Nat) : (bit v).testBit w = decide (v = w):=by
  simp [bit,Nat.shiftLeft_eq,Nat.testBit_two_pow]
theorem full_at (g : MaskGraph) (w : Nat) :
    (fullMask g).testBit w = decide (w < g.width):=by
  simp [fullMask,bit,Nat.shiftLeft_eq]
theorem neighbor_at (g : MaskGraph) (deleted v w : Nat) (hw : w < g.width) :
    (residualNeighbors g deleted v).testBit w =
      ((g.adjacency v).testBit w&&!(deleted.testBit w)):=by
  simp [residualNeighbors,Nat.testBit_xor,full_at,hw]
private theorem fold_mask_at (vertices : List Nat) (p : Nat → Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w||(vertices.any fun v => decide (p v)&&(v==w))):=by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons,List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h,bit_at,Bool.or_assoc,Bool.beq_eq_decide_eq]
private theorem any_mask_at (p : Nat → Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v)&&(v==w)) =
      (decide (w < n)&&decide (p w)):=by
  rw [Bool.eq_iff_iff,List.any_eq_true,Bool.and_eq_true]
  simp only [List.mem_range,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · rintro ⟨v,hv,hp,rfl⟩
    exact ⟨hv,hp⟩
  · rintro ⟨hw,hp⟩
    exact ⟨w,hw,hp,rfl⟩
theorem close_at (g : MaskGraph) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w||(decide (w < g.width)&&decide (residualNeighbors g deleted w = 0))):=by
  unfold closeIsolates
  rw [fold_mask_at,any_mask_at]
theorem class_at (g : MaskGraph) (deleted v w : Nat) :
    (twinClass g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w)&&(residualNeighbors g deleted w==residualNeighbors g deleted v))):=by
  unfold twinClass
  rw [fold_mask_at,any_mask_at]
  simp [Bool.beq_eq_decide_eq]
theorem bit_eq_power (width : Nat) : bit width = 2 ^ width:=by
  simp [bit,Nat.shiftLeft_eq]
theorem lor_bounded {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width:=by
  rw [bit_eq_power] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb
theorem high_false {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false:=by
  rw [bit_eq_power] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))
theorem mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width,a.testBit w = b.testBit w) : a = b:=by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [high_false ha (Nat.le_of_not_gt hw),high_false hb (Nat.le_of_not_gt hw)]
theorem neighbor_bounded (g : MaskGraph) (deleted v : Nat) (hd : deleted < bit g.width) :
    residualNeighbors g deleted v < bit g.width:=by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [residualNeighbors,full_at,Nat.not_lt_of_ge hw,high_false hd hw]
theorem close_bounded (g : MaskGraph) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width:=by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at,Nat.not_lt_of_ge hw,high_false hd hw]
theorem class_bounded (g : MaskGraph) (deleted v : Nat) :
    twinClass g deleted v < bit g.width:=by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at,Nat.not_lt_of_ge hw]
def step (g : MaskGraph) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v)&&(residualNeighbors g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (twinClass g deleted v)))
    else none
def frontier (g : MaskGraph) : Nat → List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((frontier g depth).flatMap (step g)).eraseDups
theorem advance {g : MaskGraph} {depth deleted next : Nat}
    (hd : deleted ∈ frontier g depth) (hs : next ∈ step g deleted) :
    next ∈ frontier g (depth + 1):=by
  rw [frontier,List.mem_eraseDups,List.mem_flatMap]
  exact ⟨deleted,hd,hs⟩
theorem stay {g : MaskGraph} {depth deleted : Nat} (hd : deleted ∈ frontier g depth) :
    deleted ∈ frontier g (depth + 1) :=
  advance hd (by simp [step])
theorem advance_class {g : MaskGraph} {depth deleted vertex : Nat}
    (hd : deleted ∈ frontier g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : residualNeighbors g deleted vertex≠0) :
    closeIsolates g (Nat.lor deleted (twinClass g deleted vertex)) ∈ frontier g (depth + 1):=by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex,List.mem_range.mpr hv,?_⟩
  simp [hlive,hne]
def petersenNine : MaskGraph :=
  ⟨9,fun v => (#[50,69,138,276,9,385,258,36,104] : Array Nat)[v]?.getD 0⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem petersen_nine_no_four : fullMask petersenNine ∉ frontier petersenNine 4:=by
  decide +kernel
end PetersenGroupBFS
namespace PetersenMaskBridge
open PetersenGroupBFS
open BranchGraph
def decode (g : MaskGraph) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)
@[simp] lemma mem_decode (g : MaskGraph) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask↔mask.testBit v.val = true:=by
  simp [decode]
@[simp] lemma decode_zero (g : MaskGraph) : decode g 0 = ∅:=by
  ext v
  simp
@[simp] lemma decode_full (g : MaskGraph) : decode g (fullMask g) = Finset.univ:=by
  ext v
  simp [full_at,v.isLt]
lemma decode_or (g : MaskGraph) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b:=by
  ext v
  simp [Bool.or_eq_true]
lemma decode_inj (g : MaskGraph) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b:=by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w,hw⟩ : Fin g.width) ∈ decode g a↔(⟨w,hw⟩ : Fin g.width) ∈ decode g b:=by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm
lemma bit_pos (n : Nat) : 0 < bit n:=by
  rw [bit_eq_power]
  exact Nat.two_pow_pos n
lemma full_bounded (g : MaskGraph) : fullMask g < bit g.width:=by
  unfold fullMask
  have:=bit_pos g.width
  omega
section Graph
variable (g : MaskGraph) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width,G.Adj u v↔(g.adjacency u.val).testBit v.val = true)
include adj in
lemma decode_neighbors (deleted : Nat) (u : Fin g.width) :
    decode g (residualNeighbors g deleted u.val) = neighborsAfter G (decode g deleted) u:=by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode,neighborsAfter,neighbor_at g deleted u.val v.val v.isLt,adj,h]
include adj in
lemma residual_zero_iff (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    residualNeighbors g deleted u.val = 0↔neighborsAfter G (decode g deleted) u = ∅:=by
  constructor
  · intro h
    rw [← decode_neighbors g G adj,h,decode_zero]
  · intro h
    apply decode_inj g (neighbor_bounded g deleted u.val bound) (bit_pos g.width)
    rw [decode_neighbors g G adj,h,decode_zero]
include adj in
lemma decode_close (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted):=by
  ext v
  simp [close_at,v.isLt,BranchGraph.closeIsolates,isolates,Bool.or_eq_true,
    residual_zero_iff g G adj deleted bound]
include adj in
lemma decode_class (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (twinClass g deleted root.val) = maximalClass G (decode g deleted) root:=by
  have same (u : Fin g.width) : residualNeighbors g deleted u.val = residualNeighbors g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root:=by
    rw [← decode_neighbors g G adj deleted u,← decode_neighbors g G adj deleted root]
    exact ⟨congrArg (decode g),decode_inj g (neighbor_bounded g deleted u.val bound)
      (neighbor_bounded g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at,v.isLt,maximalClass,outside,live,h,same,Bool.beq_eq_decide_eq]
def Represented (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m,m ∈ frontier g depth∧m < bit g.width∧decode g m = removed
include adj in
lemma initial_rep : Represented g 0 (BranchGraph.closeIsolates G ∅):=by
  refine ⟨PetersenGroupBFS.closeIsolates g 0,?_,
    close_bounded g 0 (bit_pos g.width),?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [decode_close g G adj _ (bit_pos g.width),decode_zero]
include adj in
lemma advance_rep {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : Represented g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    Represented g (depth + 1) (removeClass G removed root):=by
  obtain ⟨m,hm,bounded,same⟩:=rep
  subst removed
  by_cases active : root ∉ decode g m∧(neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false:=by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : residualNeighbors g m root.val≠0:=by
      intro h
      have none:=(residual_zero_iff g G adj m bounded root).mp h
      simpa [none] using active.2
    have united:=lor_bounded bounded (class_bounded g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (twinClass g m root.val)),
      advance_class hm root.isLt live someNeighbor,close_bounded g _ united,?_⟩
    rw [decode_close g G adj _ united,decode_or,decode_class g G adj m bounded root active.1 active.2,
      removeClass]
  · have sameRemoval : removeClass G (decode g m) root = decode g m:=by
      have emptyClass : maximalClass G (decode g m) root = ∅:=ite_eq_right active
      simp only [removeClass,emptyClass,Finset.union_empty,closed]
    exact ⟨m,stay hm,bounded,sameRemoval.symm⟩
include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : ClassSteps G count start finish) (initial : Represented g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : Represented g (depth + count) finish:=by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk,Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root,next⟩:=walk
    have nextClosed : BranchGraph.closeIsolates G (removeClass G start root) = removeClass G start root :=
      closeIsolates_idempotent G _
    have rest:=ih next (advance_rep g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rest
lemma frontier_up {m k r : Nat} (reached : m ∈ frontier g k) (budget : k ≤ r) : m ∈ frontier g r:=by
  induction r with
  | zero =>
    have : k = 0:=by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))
include adj in
theorem groups_exceed_budget [Nonempty (Fin g.width)] (k : Nat) (noFinish : fullMask g ∉ frontier g k)
    (groups : List (Finset (Fin g.width))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : k < groups.length:=by
  by_contra! budget
  have walk:=covering_sequence_reaches_univ G groups twins finished
  obtain ⟨m,reached,bound,allGone⟩ :=
    simulate g G adj walk (initial_rep g G adj) (closeIsolates_idempotent G ∅)
  have equal : m = fullMask g:=decode_inj g bound (full_bounded g) (by simpa using allGone)
  rw [equal,Nat.zero_add] at reached
  exact noFinish (frontier_up g reached budget)
end Graph
theorem petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9,G.Adj u v↔(petersenNine.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 9))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : 5 ≤ groups.length :=
  @groups_exceed_budget petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 petersen_nine_no_four groups twins finished
end PetersenMaskBridge
open PetersenNine
def petersenGraph : SimpleGraph Vertex:=graph edges noLoops
def petersenAdjDecidable : DecidableRel petersenGraph.Adj:=fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ edges∨(b,a) ∈ edges))
theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S:=by
  constructor
  · intro h
    obtain ⟨a,b,edge,ha,hb⟩:=(edgeFun_true edges _).mp h
    exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,Or.inl edge⟩
  · rintro ⟨a,ha,b,hb,adjacent⟩
    change (a,b) ∈ edges∨(b,a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a,b,edge,decide_eq_true ha,decide_eq_true hb⟩
    · exact ⟨b,a,edge,decide_eq_true hb,decide_eq_true ha⟩
theorem petersen_graph_matches_mask :
    ∀ a b : Vertex,petersenGraph.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val = true:=by
  letI : DecidableRel petersenGraph.Adj:=petersenAdjDecidable
  decide
theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex,petersenGraph.Adj i j →
      ∃ u v,petersenGraph.Adj i u∧petersenGraph.Adj j v ∧
        u≠j∧v≠i∧¬ petersenGraph.Adj u v:=by
  letI : DecidableRel petersenGraph.Adj:=petersenAdjDecidable
  decide
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators
def operands (gs : List Gate) : List Nat:=gs.flatMap Gate.inputs
def notGateCount (gs : List Gate) : Nat:=(gs.filter fun g => isNotGate g.op).length
theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs:=by
  obtain ⟨g,gAt,before⟩:=read
  exact List.mem_flatMap.mpr ⟨g,List.mem_iff_getElem?.mpr ⟨slot,gAt⟩,before⟩
theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p≠q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire:=by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g,atGate,_⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands,List.flatMap_cons,List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using first
        have later : Reads rest q wire:=by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire:=List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using second
        have later : Reads rest p wire:=by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire:=List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire:=by simpa [Reads] using first
        have late : Reads rest q wire:=by simpa [Reads] using second
        have different : p≠q:=fun eq => neq (congrArg Nat.succ eq)
        have count:=ih different early late
        simp only [operands] at count
        omega
theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length:=by
  induction gs with
  | nil => simp [operands,notGateCount]
  | cons g gs ih =>
    have gArity:=arity g (by simp)
    have rest:=ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands,notGateCount,h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands,notGateCount,h] at rest ⊢
      omega
theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0) = 2:=by
  intro g gMem
  obtain ⟨p,atGate⟩:=List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [op,args,isNotGate]
  · rcases ops with op | op <;> simp [op,args,isNotGate]
theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches,2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length:=by
  classical
  let W:=(operands gs).toFinset
  have subset : branches ⊆ W:=by
    intro w wm
    have t:=twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0) = branches.card:=by
    have same : (∑ w ∈ W,if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches,if w ∈ branches then (1 : Nat) else 0:=by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W,(operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W,((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W,(operands gs).count w:=by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w:=List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib,aux,total] at bound
  simpa [W] using bound
theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length,w≠out → ∃ p,Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches,∃ p q,p≠q∧Reads gs p w∧Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length:=by
  let W:=(operands gs).toFinset
  let required:=(Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W:=by
    intro w inSet
    have spec:=Finset.mem_erase.mp inSet
    obtain ⟨p,read⟩:=everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1:=by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid),Finset.card_range]
  have twice : ∀ w ∈ branches,2 ≤ (operands gs).count w:=by
    intro w mem
    obtain ⟨p,q,different,pReads,qReads⟩:=twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up:=branch_card_add_wire_card_le_operands gs branches twice
  have used:=Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total:=operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace
theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length),w≠(⟨out,outValid⟩ : Fin (n + gs.length)) → ∃ v,readEdge gs w v:=by
  intro w notOutput
  have notSame : w.val≠out:=fun eq => notOutput (Fin.ext eq)
  obtain ⟨p,g,atSlot,reads,bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p,bound⟩,p,g,atSlot,rfl,reads⟩
theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q,p≠q∧Reads gs p w.val∧Reads gs q w.val:=by
  obtain ⟨first,next,pRead,qRead,separate⟩:=fork
  obtain ⟨p,g,atP,src,ap⟩:=pRead
  obtain ⟨q,h,atQ,dst,aq⟩:=qRead
  refine ⟨p,q,?_,⟨g,atP,ap⟩,⟨h,atQ,aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))
noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)):=by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w
theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs↔FirstBranchRoute.Branches (readEdge gs) w:=by
  classical
  simp [circuitBranchWires]
def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut
def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut
theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut↔label v = cut:=by
  simp [classAt]
theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut↔label v < cut:=by
  simp [classesBefore]
theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V,(∀ i ∈ I,label i = cut) →
      (∀ i ∈ O,cut < label i) → (BranchGraph.containsEdge G (I ∪ O)↔decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut):=by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y:=by
    have ne : label y≠cut:=fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut:=fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y↔decode (code {x}) {y}):=by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut:=by
      have eq : i = x:=Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i:=by
      have eq : i = y:=Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x}≠code ∅:=by
    obtain ⟨y,neighbor⟩:=active
    simp only [BranchGraph.neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at neighbor
    have yLater:=later xGroup neighbor.1 neighbor.2
    have yes:=(single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one:=(factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a:=cannot u uGroup uActive
  have b:=cannot v vGroup vActive
  have sameCode : code {u} = code {v}:=by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨edge,remains⟩
    have pos:=later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_,remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge,remains⟩
    have pos:=later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_,remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds CircuitProof
open Relation
theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i,ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val:=by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n:=⟨w.val,input⟩
      have name : inputWire gs i = w:=Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w:=by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a:=agree i atInput
      simpa only [vl_input gs x w.val input,vl_input gs y w.val input] using a
    · let p:=w.val - n
      have pLt : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p:=by dsimp [p]; omega
      let g:=gs[p]'pLt
      have atGate : gs[p]? = some g:=List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore:=(clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length):=⟨a,by have:=w.isLt; omega⟩
      have read : readEdge gs wire w:=⟨p,g,atGate,gateWire,inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)
end PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation
def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool:=decide (i ∈ S)
theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out → ∃ w,readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool,∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I,label i = cut) → (∀ i ∈ O,cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true↔decode (code I) O):=by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)):=vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n),(∀ j ∈ J,label j = cut)∧code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code,decode,?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I,label i = cut) at groupI
  change (∀ i ∈ O,cut < label i) at afterO
  change (_↔decode (code I) O)
  constructor
  · exact fun yes => ⟨I,groupI,rfl,yes⟩
  · rintro ⟨J,groupJ,sameCode,yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K:=by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O:=fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput,absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out:=lt_of_le_of_ne prior atOutput
    have eq:=circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut:=by
        by_contra offGroup
        have notI : i ∉ I:=fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J:=fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput,notI,notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut:=isGroup
      have forbid:=FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v:=inputWire gs i) (w:=out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b,avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1,h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]
open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace
theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out → ∃ w,readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n),vl gs (setInput S) out.val = true↔BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n):=FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut):=by
  let label (i : Fin n):=FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code,decode,factors⟩:=finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup
abbrev petersenF:=edgeFun edges
private theorem petersen_dependency_samples : ∀ v : Vertex,∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w))))≠petersenF (fun i => decide (i = w)):=by
  decide +kernel
theorem petersen_depends (v : Vertex) : Dep petersenF v:=by
  obtain ⟨w,hw⟩:=petersen_dependency_samples v
  exact ⟨fun i => decide (i = w),hw⟩
theorem petersen_nonconstant : ∃ x y : Vertex → Bool,petersenF x≠petersenF y :=
  dep_nc (petersen_depends 0)
private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true:=by
  decide +kernel
theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y,petersenF (Function.update x v b)≠petersenF (Function.update y v b):=by
  obtain ⟨no,yes⟩:=petersen_cofactor_samples v b
  exact ⟨fun _ => false,fun _ => true,by rw [no,yes]; decide⟩
lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9,petersenGraph.Adj u v∧x u = true∧x v = true:=by
  change PetersenNine.edgeFun PetersenNine.edges x = true↔_
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    exact ⟨a,b,Or.inl edge,ha,hb⟩
  · rintro ⟨a,b,adjacent,ha,hb⟩
    change (a,b) ∈ PetersenNine.edges∨(b,a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a,b,edge,ha,hb⟩
    · exact ⟨b,a,edge,hb,ha⟩
lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length:=by
  by_contra! after
  obtain ⟨x,y,different⟩:=least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)
theorem least_petersen_five_branches (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n:=9) gs).card:=by
  classical
  letI : DecidableRel petersenGraph.Adj:=petersenAdjDecidable
  have outValid:=least_petersen_output_valid least
  let outWire : Fin (9 + gs.length):=⟨out,outValid⟩
  have live:=least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant outValid
  let label : Fin 9 → Fin (9 + gs.length):=firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)):=circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x:=by
    change vl gs x out = _
    rw [least.hev,Bool.eq_iff_iff,petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue,decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge petersenGraph S:=by
    change vl gs (setInput S) out = true↔_
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have labels (v : Fin 9) : label v = outWire∨label v ∈ branches:=by
    have stopped:=FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire:=by
    obtain ⟨a,_,path,_,_⟩:=in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup petersenGraph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required petersenGraph label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five petersenGraph petersen_graph_matches_mask)
lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length:=by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount,List.countP_cons,List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega
theorem petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex → Bool,C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates:=by
  obtain ⟨gs,o,least,budget⟩:=least_with_budget C hfan he petersen_nonconstant
  have valid:=least_petersen_output_valid least
  have live:=least_read_edge_live least petersen_nonconstant petersen_depends
    petersen_restrict_nonconstant valid
  let branches:=circuitBranchWires (n:=9) gs
  have branchLower : 5 ≤ branches.card:=least_petersen_five_branches gs o least
  have branchBudget:=branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length):=⟨w,hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩:=live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal:=nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  omega
end Binary
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero∧a≠one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (target : Sig) : Nat → Nat → Finset Sig → Prop:=fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)),(proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target}:=fun M stop unary binary => @stop  h0
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
theorem Live.induct {target : Sig} {M : (Nat → Nat → Finset Sig → Prop)} {k t S} (h : Live target k t S)
  (stop : proper target → M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → Live target k t (insert (neg a) U) → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → Live target k t (insert (bin d a b) U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S∧M k t S)
  (fun h0 => ⟨@Live.stop target  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
theorem Live.recurse {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig) (proof : Live target k t S),Prop}
  (stop : ∀ (h0 : proper target),M 0 0 {target} (@Live.stop target  h0))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@Live.unary target k t U a h0 h1 h2))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@Live.binary target k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h : Live target k t S) : M k t S h:=by
  have r:=Live.induct (M:=fun k t S => ∀ hh : Live target k t S,M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h
theorem Live.zeroSet {T t S} (h : Live T 0 t S) : S={T}:=by
  have hh:=h (fun k _ W => k=0 → W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma live_size {k t S} (h : Live target k t S) : t ≤ k∧S.card+t ≤ k+1:=by
  induction h using Live.recurse with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop:=v ∈ w∨¬proper v
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma bin_laws (a : Sig) :
    bin false a one=a∧bin true a zero=a ∧
    bin false a zero=zero∧bin true a one=one ∧
    bin false a a=a∧bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma neg_laws : neg zero=one∧neg one=zero:=by simp [neg,zero,one]
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a=zero∨a=one∨a ∈ w∧proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w,proper a∧z=neg a) ∨
  (∃ d a b,a ∈ w∧b ∈ w∧proper a∧proper b∧a≠b∧z=bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b)∨witness w (bin d a b):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    represented w (gv w g)∨witness w (gv w g):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩:=h
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a)∨witness w (neg a):=by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b:=witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b:=witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z∨witness w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧Live target k' t' S'∧∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w∨a=z:=by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (neg a)
        have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U:=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U):=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧Live target k t S∧∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩:=pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
private lemma bit_zero (i) : bit i zero=false:=by simp [bit,zero]
private lemma bit_one (i) : bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type):=R → Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat:=(xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool∨Constant v
def supply {R} (pool xs : List (Wire R)):=∀ a ∈ xs,Available pool a
def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop:=fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
theorem Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots:=fun M start one two => @start
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank):=fun M start one two => @one p bank a (h0 M start one two) h1
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank):=fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
theorem Reach.induct {R} {roots : List (Wire R)} {M : (Nat → List (Wire R) → Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},Reach roots p bank → M p bank → Available bank a → M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),Reach roots p bank → M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank∧M p bank)
  (⟨@Reach.start R roots  ,@start  ⟩)
  (@fun p bank a h0 h1 => ⟨@Reach.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
  (@fun p bank a b op h0 h1 h2 => ⟨@Reach.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
theorem Reach.recurse {R} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)) (proof : Reach roots p bank),Prop}
  (start : M 0 roots (@Reach.start R roots  ))
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a),M (p+1) (inv a :: bank) (@Reach.one R roots p bank a h0 h2))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a) (h3 : Available bank b),M (p+1) (combine op a b :: bank) (@Reach.two R roots p bank a b op h0 h2 h3))
  {p bank} (h : Reach roots p bank) : M p bank h:=by
  have r:=Reach.induct (M:=fun p bank => ∀ hh : Reach roots p bank,M p bank hh) h
    (fun  _ => @start  )
    (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
    (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
  exact r h
def kept {α : Type} (save : Bool) (x : α) (xs : List α):=if save then x::xs else xs
def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop:=fun s ws =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → M s xs → M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),M s (inv a :: kept save a rest) → M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) →
  M s ws
theorem Run.stop {R} {goal : Wire R}   : Run goal 0 [goal]:=fun M stop perm one two => @stop
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
theorem Run.induct {R} {goal : Wire R} {M : (Nat → List (Wire R) → Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → Run goal s xs → M s xs → M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),Run goal s (inv a :: kept save a rest) → M s (inv a :: kept save a rest) → M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),Run goal s (combine op a b :: kept ka a (kept kb b rest)) → M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws∧M s ws)
  (⟨@Run.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
theorem Run.recurse {R} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)) (proof : Run goal s ws),Prop}
  (stop : M 0 [goal] (@Run.stop R goal  ))
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) (ih : M s xs h1),M s zs (@Run.perm R goal s xs zs h0 h1))
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) h0),M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) h0),M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
  {s ws} (h : Run goal s ws) : M s ws h:=by
  have r:=Run.induct (M:=fun s ws => ∀ hh : Run goal s ws,M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a+mass xs:=by
  simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs):=by
  cases k <;> simp [kept,mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a):=by
  obtain ⟨v,rfl⟩:=h
  exact ⟨!v,rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b):=by
  obtain ⟨v,rfl⟩:=h
  obtain ⟨w,rfl⟩:=g
  cases op <;> exact ⟨_,rfl⟩
theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a∨Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b):=by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true,by funext x; simp [combine]⟩
theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next,Reach roots q next∧Available next (inv a) ∧
        (∀ v,Available bank v → Available next v)∧q+cost a ≤ p+1+cost (inv a):=by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩
theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next,Reach roots q next∧Available next (combine op a b) ∧
        (∀ v,Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b):=by
  classical
  by_cases c : Constant a∨Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a:=fun h => c (Or.inl h)
    have cb : ¬Constant b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a∨x∈xs:=by cases k <;> simp_all [kept]
theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next,Reach roots q next∧Available next goal∧q+mass ws ≤ p+s:=by
  classical
  induction h using Run.recurse generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=mass_kept a (kept kb b rest) ka
    have hlen':=mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)):=by
  cases k <;> simp [kept]
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)):=by
  induction h using Run.recurse with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih
theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs,Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L+mass (ws.map (restrictRows rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩:=contraction nc (restrict_run rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f)=f r:=by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v)=v:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩
theorem observe_table (f : Wire Row) : observe (table f)=f:=by
  funext r
  exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a)=inv (observe a):=by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b)=combine d (observe a) (observe b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f=kept d (f a) (l.map f):=by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup:=by cases k <;> simp [kept,hn,ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [kept]
theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset=S) : Run (observe T) k (v.map observe):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=kept save a rest
    have er : rest.toFinset=U.erase a:=by simp [rest]
    have hm : a ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have ht : tail.toFinset=U:=by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=kept_nd save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=kept kb b rest
    let tail:=kept ka a mid
    have er : rest.toFinset=(U.erase a).erase b:=by simp [rest]
    have ar : a ∉ rest:=by simp [rest]
    have br : b ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have bm:=kept_nd kb b rest hr br
    have am : a ∉ mid:=by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd:=kept_nd ka a mid bm am
    have ht : tail.toFinset=U:=by
      change (kept ka a (kept kb b rest)).toFinset=U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f)=neg (table f):=by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g)=bin d (table f) (table g):=by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]
theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a)∨witness w (neg a):=by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z∨witness w z) (hs : ∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1∧Live T k' t' S'∧∀ a ∈ S',a ∈ w:=by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S,a ∈ bank.map table) :
    ∃ l v U,l ≤ p+k∧Live T l v U∧∀ a ∈ U,a ∈ roots.map table:=by
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S,k ≤ p∧Live T k t S∧∀ a ∈ S,a ∈ roots:=by
  have hm:=available_rep hit
  rw [table_observe] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩:=reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs
theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T≠bit s T) : ∃ a ∈ S,bit r a≠bit s a:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩:=ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S,v ∈ roots) (r s : Row) (diff : bit r T≠bit s T)
    (isolated : ∀ v ∈ roots,v≠a → bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩:=live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def oldSeed : Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed : Sig:=inputs.getD 0 zero ||| inputs.getD 4 zero
def sample (r : Row) (j : Fin 9):=bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
theorem edge_table : ∀ r : Row,bit r graph=edge (sample r):=by decide +kernel
theorem seed_table : ∀ r : Row,bit r seed=(sample r 0||sample r 4):=by decide +kernel
theorem graph_proper : proper graph:=by unfold proper; decide +kernel
theorem seed_nonzero : seed≠zero:=by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero)=inputs:=rfl
theorem sampled (r : Row) : List.ofFn (sample r)=inputs.map (bit r):=by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false:=by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l,execute gs ws=ws ++ l:=by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩:=ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def neighbor (i : Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w==inputs.getD i.val zero ||
      bit (absentRow i) w==bit (presentRow i) w)=true:=by decide +kernel
theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S,v ∈ inputs++[seed]) :
    S=inputs.toFinset∨S=(inputs++[seed]).toFinset:=by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S:=by
    have cut:=seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S:=by
    intro v hv
    have hm:=List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩:=hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx:=List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx:=sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed
theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool,(C.wires (List.ofFn y)).getD 9 false=(y 0||y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C=edge) (small : C.size ≤ 15) :
    ∃ k t,k ≤ 14∧(Live graph k t inputs.toFinset∨Live graph k t (inputs++[seed]).toFinset):=by
  have headEq : (execute C.gates inputs).getD 9 zero=seed:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out:=get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn:=out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g=seed:=by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero=seed at headEq
      obtain ⟨l,hl⟩:=exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs,gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧gate.inputs.length≤2:=by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩:=extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15:=by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)
def rename (f : Row → Row) (a : Sig):=table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a)=bit (f r) a:=bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a)=restrictRows f (observe a):=by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a)=neg (rename f a):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a))=bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b)=bin d (rename f a) (rename f b):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b))=bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f):=by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero=zero∧rename f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)):=by
  have inj:=rename_inj f onto
  obtain ⟨fz,fo⟩:=rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.recurse with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
      intro hm
      obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih
theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T=true) (negRow : bit s T=false) :
    ∃ a ∈ S,bit r a=true∧bit s a=false:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩:=ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank,Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row,bit r T≠bit s T∧∀ v ∈ roots,v≠a → bit r v=bit s v
theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots,Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1):=by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩:=reach_live hp h ha
  have he : roots.toFinset=S:=by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:=essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v):=by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v:=by
    have avail : Available ([] : List (Wire Row)) (observe v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b)=mass a+mass b:=by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs,Constant x) :
    mass xs=xs.length:=by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T=G)
    (covered : ∀ a ∈ roots,Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles,Essential T roots a)
    (constant : ∀ a ∈ singles,Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L+singles.card):=by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live pT hh ha
  have subS : singles ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:=necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front:=singles.toList ++ (S \ singles).toList
  have nd : front.Nodup:=by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':=list_run run front nd fe
  have gc : restrictRows r (observe T)=observe G:=(observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)):=by
    simp only [front,List.map_append,mass_append]
    let xs:=(singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs,Constant v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs+_
    rw [sz]
    omega
  omega
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset:=by
  classical
  intro k t hk h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    have mem : T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      have nk:=kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len : (childOne ws a keep).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup:=by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_
      simp [ke]
    have sc:=(live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true∧bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws=BitVec.allOnes width:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩:=live_row_difference h (show bit (r i) T≠bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩:=mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n:=by
  apply cover_sound h rfl correct
  intro hh
  have eq:=of_decide_eq_true hh
  have bound:=(live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank,Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig):=a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m:=masked d a
  m==zero||m==d||(pool.map (masked d)).any (fun v => v==m)
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=masked d b) :
    restrictRows f (observe a)=restrictRows f (observe b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=zero) : restrictRows f (observe a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=d) : restrictRows f (observe a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool,Available bank (restrictRows f (observe a))
theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r,bit (f r) d=true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a=true) : Available bank (restrictRows f (observe a)):=by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice:=Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1&&(c.1==2||availableB d pool c.2.2)
theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r,bit (f r) d=true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c=true) :
    ∃ next,Reach roots (q+1) next∧poolSupply f next (choiceVal c :: pool):=by
  have ok : availableB d pool c.2.1=true∧(c.1==2||availableB d pool c.2.2)=true:=by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha:=availableB_sound dom hs ok.1
  let z:=restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank):=by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz':=Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w)=combine b (restrictRows f v) (restrictRows f w):=by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)
def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r,bit (f r) d=true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs=some result) :
    ∃ next,Reach roots (q+cs.length) next∧poolSupply f next result:=by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩:=pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩:=ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig):=masked d a==zero||masked d a==d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r,bit (f r) d=true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)):=by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)):=by
        have hh : masked d a=zero∨masked d a=d:=by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d))&&ws.all (availableB d pool)
theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs=some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws=true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
  obtain ⟨bank,hr,hs⟩:=makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:=cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b:=projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo:=count_constants dom ws
  have hu:=ineq
  simp only [Nat.zero_add] at b
  omega
abbrev Move:=Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row:=Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig):=(m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val)=bit (shifted d r) a:=by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]
theorem bool_mux (p x y : Bool) : (p&&x||!p&&y)=(if p then x else y):=by cases p <;> simp
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a)=bit (rowMove m r) a:=by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def movedRow (ms : List Move) (r : Row):=ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig):=ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a)=bit (movedRow ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a=rename (movedRow ms) a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig):=w==zero||w==one||roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w=true) :
    Available (roots.map observe) (observe w):=by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T==G&&raw.all (fun a => freeWord base (movedWord ms a))
theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G=true) :
    rename (movedRow ms) T=G ∧
    ∀ a ∈ raw,Available (base.map observe) (observe (rename (movedRow ms) a)):=by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G=true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G=true)
    (all : movedWord ms d=one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L:=by
  obtain ⟨eq,supp⟩:=map_correct ok
  have obs : restrictRows (movedRow ms) (observe T)=observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs=true) : Essential T roots a:=by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)
theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs=true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩:=reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:=essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound:=(live_size run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G&&checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1==zero||movedWord ms a.1==one)
theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs=true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩:=map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat):=(selected m).map Prod.snd
def vertex (m j : Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x:=vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig):=T != zero&&T != one
theorem proper_of (T : Sig) (h : properB T=true) : proper T:=by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs:=graphPairs m hints
  properB (graphGoal m)&&checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L=true) :
    Lower (vars m) (graphGoal m) L:=by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  let count:=(xs.map Prod.fst).toFinset.card
  properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs&&decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior=true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩:=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  change (((properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old)&&properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps=true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L:=by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q):=by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1==q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1==q) e=true:=List.find?_some (p:=fun a : Nat × Nat => a.1==q) (a:=e) h
    have eq : e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (c : BoundPool) : Sig:=c.1
abbrev BoundPool.bound (c : BoundPool) : Nat:=c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat:=c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig:=c.2.2.2
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r,bit (f r) c.domain=true)∧¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws,Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank∧poolSupply f bank c.wires∧True
theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs=some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩:=by
  obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
  obtain ⟨bank,hr,hs⟩:=makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest,availableB c.domain c.wires a=true)
    (buy : if paid then choiceOK c.domain c.wires choice=true
       else availableB c.domain c.wires (choiceVal choice)=true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid
  let ws:=choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n=c.paid+paid.toNat) : False:=by
    have covered : supply out ((ws.map observe).map (restrictRows f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
      exact zs _ ha
    have b:=projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm:=count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩:=pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z:=choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires))&&(!extra||choiceOK c.domain c.wires op)
theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op=true) :
    Impossible T k (choiceVal op::rest).toFinset:=by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L=some c) : ValidPool raw T c:=by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h
    change some _=some c at h
    injection h with h
    subst c
    exact build_valid slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val=bit (r i) v:=by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals:=(ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i,bit (r i) T=true∧bit (s i) T=false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s):=by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor):=x.2=pairSig r s x.1
def dneg (x : Decor) : Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b)=if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x):=by
  change x.2=_ at h
  simp only [faithful,dneg,pairSig,ofRows_neg,h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y):=by
  change x.2=_ at hx
  change y.2=_ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor:=(zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j=(ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j=(ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws,faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws,faithful r s v) :
    ∀ v ∈ decodeBank n bits ws,faithful r s v:=by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:=List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
theorem coordinate1 : ∀ r : Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
theorem coordinate2 : ∀ r : Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
theorem coordinate3 : ∀ r : Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
theorem coordinate4 : ∀ r : Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
theorem coordinate5 : ∀ r : Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
theorem coordinate6 : ∀ r : Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
theorem coordinate7 : ∀ r : Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
theorem coordinate8 : ∀ r : Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9∧a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q,faithful (asRow p) (asRow q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:=selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m)=(liftGoal m v).getLsbD i.val:=by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val=((if m.testBit j then v j else 0) : Bits).getLsbD i.val:=bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v,faithful r s a) :
    (coverage d v).1=covered d (pairSig r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1)=column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)):=by
  cases keep
  · change (coverage d (ws.erase a)).1=takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)):=by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1=takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl
def sameWords (a b : List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws:=choiceVal op::rest
  (links (keySet ws)).any (sameWords ws)||pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
abbrev CovPair:=Cov × Cov
def preCov (ws : List Decor) : CovPair:=(coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool):=if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d=coverage d ws:=by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb:=by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka
theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor):=codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice:=(op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1=choiceVal (movedChoice op a b):=by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b):=by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len>cap then true else
    let d:=len==cap
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb=true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz:=(live_size h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep:=cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap:=by omega
  rw [ce] at sep
  let d:=child.length==cap
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap)=(child.length==cap):=by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length=cap)) (pairSig r s) child=BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by simp [sep]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  have val:=moved_full op a b
  change z.1=_ at val
  change Live T k t child.toFinset at h
  have nd':=ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false&&evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false&&testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs&&testAll ctx bs
theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true∨testPair ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail
theorem testPair_at {ctx a b d} (h : testPair ctx a b d=true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v↔(w=a∧k=true)∨w∈v:=by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k↔w∈v∧(w≠a∨k=true):=by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst∧(v≠a.1∨ka=true)∧(un=true∨v≠b.1∨kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset=(childOne (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset=(childTwo v b a d kb ka).toFinset:=by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws=true) :
    Impossible T cap (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap:=by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d=true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh
theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move):=inputs.all (fun a => movedWord p (movedWord q a)==a)
theorem composed_id {p q} (h : composedOK p q=true) (r : Row) :
    movedRow q (movedRow p r)=r:=by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T==T)&&composedOK p p.reverse&&composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run:=live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def IndexTree (α : Type):=List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α:=xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α:=List.append a b
def IndexTree.read {α} (tree : IndexTree α) (i : Nat):=(show List α from tree)[i]?
def IndexTree.values {α} (tree : IndexTree α) : List α:=tree
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
def Forest:=(Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat:=c.1
def Forest.cap (c : Forest) : Nat:=c.2.1
def Forest.samples (c : Forest) : Nat → Bits × Bits:=c.2.2.1
def Forest.cols (c : Forest) : IndexTree ColumnInfo:=c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat):=c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat → Packing:=c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat → Nat → Option (Nat × Nat):=c.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:=by
  have base:=raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha
def targetOf (g : Forest):=chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m)=(chartSamples m v).getLsbD i.val:=by
  by_cases e : m=1023
  · have u:=asRow_bit v i (0 : Fin 9)
    have w:=asRow_bit v i (1 : Fin 9)
    have h:=bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val=(v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val=(v 1).getLsbD i.val at w
    have seedEq : oldSeed=inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p=BitVec.allOnes 768) (hq : chartSamples m q=0) :
    properPairs (chartGoal m) (asRow p) (asRow q):=by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1==1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
def storedDepth (_g : Forest) (depth : Nat):=depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw:=wiresOf g
  let (_,depth,_,_,_,_,_,data):=g.levels k
  let len:=10*storedDepth g depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i*width) width
  let stored:=recp &&& ((1 <<< len)-1)
  let ops:=stored
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid=some c) :
    ValidPool (vars g.mask) (targetOf g) c:=by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (earlier : ∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair=some out) :
    Impossible (targetOf g) k out.toFinset:=by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let values:=ws.map Prod.fst
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup&&!(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1,Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i=true) : Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN:=checked.1.1
  have hT : targetOf g ∉ stateSet g k i:=by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0:=by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset=S at h
    rw [h.zeroSet] at he
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n)&&block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true:=by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true:=by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1=true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2)==0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : checkedTables g top) :
    ∀ k ≤ top,∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1)&&sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws=true) : Impossible (targetOf g) k ws.toFinset:=by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem lower_forest {g prior i hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask)=true) (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem lower_discard {g prior ci hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior=true)
    (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2)=true) :
    Known (extendKnown old L relabels):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known []:=by simp [Known]
def lanePlace (v : Nat) (upper : Nat):=2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v=lanePlace (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v=lanePlace (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v=lanePlace (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs=combineLanes (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs=combineLanes (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs=combineLanes (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat=combineLanes (fun _ => a) xs:=by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def fullMarks (r packed : Nat):=((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i)=true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i:=by omega
      have ge : ¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne : a.toNat≠2^768-1:=by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
    have hi' : i < xs.length+1:=hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769:=by omega
      have di : 769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev PackedSig:=Nat × Nat
abbrev PackedCov:=Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs)=combineLanes (fun x => column d (s x)) xs:=by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]
def contextWire (c : NodeContext) (i : Nat):=c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a:=contextWire c i
  let b:=contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1==0)||f x)&&onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0:=by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1≠0:=by
        intro he
        have at0:=congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:=Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat):=b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i=packedSig (fun c => (contextWire c i).2) xs:=by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero||m==p.domain||(p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x=availableMasked p (masked p.domain x):=rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p+constantLoss p a keep:=by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un||kb) ≤
    (opKeep un ka kb a b ws).countP p:=by
  have h1:=lossBound p ws a ka
  have h2:=lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega
abbrev QuickPool:=BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p:=s.1
  let un:=op==2
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let z:=choiceVal (movedChoice op a b)
  let zm:=masked p.domain z
  let zc:=isMaskedConstant p.domain z
  let cm:=s.2.1 - constantLoss const a ka - constantLoss const b (un||kb)+zc.toNat
  let free:=zc||zm==masked p.domain a.1||zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true:=by
  let z:=choiceVal (movedChoice op a b)
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let free:=isMaskedConstant p.domain z||masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest:=opKeep (op==2) ka kb a b ws
  have ck:=keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav:=List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true:=by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat:=by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true:=by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const+if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true:=by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1:=by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  have closed:=fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length∧j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true:=by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n-(if ka then 0 else 1)-(if un||kb then 0 else 1))
  if len>k then true else
    let d:=len==k
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true:=by
  let len:=1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d:=len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)):=by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (makeBatch k n xs) i
    let b:=laneWire (makeBatch k n xs) j
    let cov:=if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.1 d) xs:=by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a=_:=laneWire_at k n xs hi
    have cb : b=_:=laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f:=batchMove b xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false&&batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0&&batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js&&batchRows b xs js
theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true:=by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true:=by
  have all:=batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q])=xs[q].2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T : Sig) (c : NodeContext) :=
  let ws:=c.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i=(prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)):=rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat),start ≤ i → i < start+n → nodeVerified g k i=true) :
    block g k start n=true:=by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar&&prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs:=contexts g k start n
  let b:=makeBatch k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true:=by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:=List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true:=by
  let xs:=contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true:=by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok:=rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true:=by
  apply makeBlock
  intro i lo hi
  let xs:=contexts g k start n
  have hm : contextOf g k i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ha : xs[q].2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d∧boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true:=by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v:=rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true∧boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d∧cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true:=by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v:=block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d∧listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat:=0xf
def g15l3 : Packing:=(1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo:=(.leaf [])
def g15autos : Array (List Nat):=Array.mk [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest:=⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat:=0x84001e90fd02fd01fa00
def g31l5 : Packing:=(3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat:=0x11a20bf
def g31l6 : Packing:=(1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest:=⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo:=(.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat):=Array.mk [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest:=⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits):=Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo:=(.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat):=Array.mk [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest:=⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits):=Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo:=(.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat):=Array.mk [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest:=⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat:=0x120ff
def g111l6 : Packing:=(1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits):=Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat):=Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest:=⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits):=Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo:=(.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat):=Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest:=⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat:=0x82000f487f40bfa03fa00
def g189l6 : Packing:=(3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat:=0x1f5859bf
def g189l7 : Packing:=(1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits):=Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest:=⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits):=Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo:=(.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat):=Array.mk [[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest:=⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat:=0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat:=0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat:=0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat:=0x2c
def g191d6 (i : Nat) : Nat:=0x47d6448788a00
def g191l6 : Packing:=(1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat:=0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing:=(28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat:=0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing:=(100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat:=0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing:=(12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat:=0x1f3c11ff
def g191l10 : Packing:=(1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits):=Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest:=⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits):=Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo:=(.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat):=Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest:=⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits):=Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo:=(.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest:=⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat:=0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat:=0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat:=0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat:=0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat:=0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing:=(25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat:=0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing:=(91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat:=0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing:=(41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat:=0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing:=(6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat:=0x11b280e4ff
def g383l12 : Packing:=(1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits):=Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest:=⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1:=size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat):=[]
def known3:=extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3:=extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2:=size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat):=[]
def known7:=extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7:=extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true:=by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1=true:=s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0=true)
  · exact (rfl : block g15 1 0 0=true)
  · exact (rfl : block g15 2 0 0=true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15:=extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15:=extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3:=size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat):=[]
def known45:=extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45:=extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3:=size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat):=[]
def known51:=extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51:=extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true:=by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3=true:=(@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true:=by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1=true:=s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0=true)
  · exact (rfl : block g31 1 0 0=true)
  · exact (rfl : block g31 2 0 0=true)
  · exact (rfl : block g31 3 0 0=true)
  · exact (rfl : block g31 4 0 0=true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31:=extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31:=extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47:=extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47:=extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55:=extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55:=extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63:=extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63:=extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1=true:=s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0=true)
  · exact (rfl : block g111 1 0 0=true)
  · exact (rfl : block g111 2 0 0=true)
  · exact (rfl : block g111 3 0 0=true)
  · exact (rfl : block g111 4 0 0=true)
  · exact (rfl : block g111 5 0 0=true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111:=extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111:=extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119:=extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119:=extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3=true:=(@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true:=by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1=true:=s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0=true)
  · exact (rfl : block g189 1 0 0=true)
  · exact (rfl : block g189 2 0 0=true)
  · exact (rfl : block g189 3 0 0=true)
  · exact (rfl : block g189 4 0 0=true)
  · exact (rfl : block g189 5 0 0=true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189:=extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189:=extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5:=size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat):=[]
def known250:=extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250:=extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127:=extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127:=extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1=true:=s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28=true:=(@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100=true:=(@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12=true:=(@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true:=by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1=true:=s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0=true)
  · exact (rfl : block g191 1 0 0=true)
  · exact (rfl : block g191 2 0 0=true)
  · exact (rfl : block g191 3 0 0=true)
  · exact (rfl : block g191 4 0 0=true)
  · exact (rfl : block g191 5 0 0=true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191:=extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191:=extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251:=extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251:=extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255:=extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255:=extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25=true:=(@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true:=by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91=true:=(@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true:=by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41=true:=(@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true:=by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true:=by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6=true:=(@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true:=by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1=true:=s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12:=by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0=true)
  · exact (rfl : block g383 1 0 0=true)
  · exact (rfl : block g383 2 0 0=true)
  · exact (rfl : block g383 3 0 0=true)
  · exact (rfl : block g383 4 0 0=true)
  · exact (rfl : block g383 5 0 0=true)
  · exact (rfl : block g383 6 0 0=true)
  · exact (rfl : block g383 7 0 0=true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383:=extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat:=0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat:=0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat:=(if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat:=0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat:=0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat:=0x202e0
def deadsamples : Array (Bits × Bits):=Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo:=(.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest:=⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def isNotT (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
private lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w∧proper a∧gv w g=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧gv w g=bin d a b):=by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a)∨∃ x,x∈w∧proper x∧neg a=neg x:=by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
    · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b)∨∃ d' x y,x∈w∧y∈w∧proper x∧proper y∧x≠y∧bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero∧bin true v zero=v:=fun v => ⟨(bin_laws v).2.2.1,(bin_laws v).2.1⟩
    have bone : ∀ v,bin false v one=v∧bin true v one=one:=fun v => ⟨(bin_laws v).1,(bin_laws v).2.2.2.1⟩
    rcases operand_cases ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [bin_comm]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [bin_comm]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases operand_cases hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a=b
        · subst b
          cases d
          · rw [(bin_laws a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(bin_laws a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩:=hg
  rcases ho with ho | ho | ho
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho,isNotT,ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,neg_laws.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)
private lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a,a∈w∧proper a∧z=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧z=bin d a b))
    (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧t' ≤ t+isN.toNat∧Live target k' t' S'∧∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w∨a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩:=hwit
          subst z
          let U:=S.erase (neg a)
          have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U:=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩:=hwit
          subst z
          let U:=S.erase (bin d a b)
          have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U):=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
private lemma extractT (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧t ≤ gs.countP (fun g => isNotT g.op)∧Live target k t S∧∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩:=pull_gateT (isNotT g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega
def ImpossibleT (T : Sig) (cap tmax : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → t ≤ tmax → ¬Live T k t S
theorem imp_to_impT {T cap tmax S} (h : Impossible T cap S) : ImpossibleT T cap tmax S :=
  fun k t hk _ => h k t hk
theorem rotate_excludedT {T n tmax} {ws : List Sig} (hi : ImpossibleT T n tmax ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : ImpossibleT T n tmax (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
  have run:=live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run
theorem enum_stepT {T : Sig} {cap tmax : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tmax > 0 → ∀ a ∈ ws,∀ keep,neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleT T (cap-1) (if (childOne ws a keep).length=cap then 0 else tmax-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap-1) (if (childTwo ws a b d ka kb).length=cap then 0 else tmax)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleT T cap tmax ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [kept_fin,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(live_size tail).2
    have len : (childOne ws a keep).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childOne ws a keep).length=cap then 0 else tmax - 1:=by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases hja : j=a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hab]
      · by_cases hjb : j=b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset=_; simp [ke]
    have sc:=(live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ if (childTwo ws a b d ka kb).length=cap then 0 else tmax:=by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · exact ht
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
theorem closeChildT_sound {raw T pools links k tmax rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag → ImpossibleT T k tmax (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    ImpossibleT T k tmax (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impT (scalarPoolCut_sound (pValid _ hp) nd ok)
def childT (tmax cap len op : Nat) : Nat :=
  if len==cap then 0 else if op==2 then tmax - 1 else tmax
abbrev LinkFn:=Nat → List (List Sig)
abbrev NodeContextT :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn × LinkFn
def ctxWireT (c : NodeContextT) (i : Nat) : Decor:=c.2.2.2.1.getD i defaultDecor
def ctxLinksT (c : NodeContextT) (ct : Nat) : LinkFn :=
  if ct==0 then c.2.2.2.2.2.2.2.1
  else if ct==1 then c.2.2.2.2.2.2.2.2.1
  else c.2.2.2.2.2.2.2.2.2
def evalMoveT (c : NodeContextT) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,cov,pools,qpools,l0,l1,l2):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let ct:=childT tmax cap len op
    let d:=ct==0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      let links:=if ct==0 then l0 else if ct==1 then l1 else l2
      closeChild pools links (cap-1) rest (movedChoice op a b)
theorem evalMoveT_sound {raw T r s ws pools l0 l1 l2 cap tmax a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0 < cap) (htmax : tmax ≤ 2)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag xs,xs ∈ l2 tag → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2)
      op a b (movedDecor op a b) ka kb=true) :
    ImpossibleT T (cap-1)
      (childT tmax cap (moveFront ws op a b ka kb).length op)
      (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=keep_sub _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=moved_full op a b
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz:=(live_size h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMoveT at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  let ct:=childT tmax cap child.length op
  have ht0 : (ct==0)=true → t=0:=by
    intro hct
    have hc0 : ct=0:=beq_iff_eq.mp hct
    change t ≤ ct at ht
    omega
  have sep:=cover_sound h rfl (pair_sep pairs) (ct==0) ht0
  let d:=ct==0
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=rest_coverage ha hb (op==2) ka kb d ne
  have hf:=moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by
    rw [sep,bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else if _ then true else _)=true at test
  rw [be,pp,fr] at test
  simp only [Bool.false_eq_true,ite_false,Bool.not_true,Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩:=List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost_good ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb)=false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb)=true then true else _)=true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true,ite_false] at test
    have hct_le : ct ≤ 2:=by
      dsimp only [ct,childT]; split_ifs <;> omega
    by_cases hct0 : ct=0
    · have hctb : (ct==0)=true:=beq_iff_eq.mpr hct0
      rw [hctb] at test; simp only [ite_true] at test
      exact closeChildT_sound pv lv0 nd' test k t hk (hct0 ▸ ht) h'
    · have hctb0 : (ct==0)=false:=beq_eq_false_iff_ne.mpr hct0
      rw [hctb0] at test; simp only [Bool.false_eq_true,ite_false] at test
      by_cases hct1 : ct=1
      · have hctb1 : (ct==1)=true:=beq_iff_eq.mpr hct1
        rw [hctb1] at test; simp only [ite_true] at test
        exact closeChildT_sound pv lv1 nd' test k t hk (hct1 ▸ ht) h'
      · have hctb1 : (ct==1)=false:=beq_eq_false_iff_ne.mpr hct1
        rw [hctb1] at test; simp only [Bool.false_eq_true,ite_false] at test
        have hct2 : ct=2:=by omega
        exact closeChildT_sound pv lv2 nd' test k t hk (hct2 ▸ ht) h'
def testPairT (ctx : NodeContextT) (a b : Decor) (d : Bool) : Bool :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let f:=evalMoveT ctx op a b z
  f false false&&f true false&&f false true&&f true true
def testRowT (ctx : NodeContextT) (a : Decor) (bs : List Decor) : Bool :=
  let unOk:=if ctx.2.1==0 then true else
    let z:=movedDecor 2 a a
    evalMoveT ctx 2 a a z false false&&evalMoveT ctx 2 a a z true true
  unOk&&bs.all (fun b => testPairT ctx a b false&&testPairT ctx a b true)
def testAllT (ctx : NodeContextT) : List Decor → Bool
  | [] => true
  | a :: bs => testRowT ctx a bs&&testAllT ctx bs
theorem all_unaryT {ctx} {ws : List Decor} (h : testAllT ctx ws=true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveT ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  have hne : (ctx.2.1==0)=false:=beq_eq_false_iff_ne.mpr (by omega)
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,hne,Bool.false_eq_true,ite_false] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm
theorem all_binaryT {ctx} {ws : List Decor} (h : testAllT ctx ws=true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (d : Bool) : testPairT ctx a b d=true∨testPairT ctx b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left; cases d <;> first | exact (h.1.2 _ bm).1 | exact (h.1.2 _ bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right; cases d <;> first | exact (h.1.2 _ haTail).1 | exact (h.1.2 _ haTail).2
      · exact ih h.2 haTail hbTail
theorem testPairT_at {ctx a b d} (h : testPairT ctx a b d=true) (ka kb : Bool) :
    evalMoveT ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPairT,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem nodeT_sound {raw T r s ws pools l0 l1 l2 cap tmax}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag xs,xs ∈ l2 tag → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (htmax : tmax ≤ 2)
    (checks : testAllT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) ws=true) :
    ImpossibleT T cap tmax (ws.map Prod.fst).toFinset:=by
  by_cases hc : cap=0
  · intro k t hk _ h
    have ke : k=0:=by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 → S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply enum_stepT nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=unary_front nd ha keep
    have hev:=evalMoveT_sound (op:=2) pairs faith nd ha ha (by simp) hc' htmax pv lv0 lv1 lv2 pro fresh (all_unaryT checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length=(childOne (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup:=by
        unfold moveFront
        have sub:=keep_sub ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [keep_mem] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
    rw [hf,hlenEq] at hev
    simpa [childT] using hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) a b d=true) :
        ImpossibleT T (cap-1) (if (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length=cap then 0 else tmax)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      have hf:=binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      have hev:=evalMoveT_sound (op:=if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' htmax pv lv0 lv1 lv2
        (eq ▸ pr) (eq ▸ fr) (testPairT_at test ka kb)
      have hop : ((if d then 1 else 0)==2)=false:=by cases d <;> rfl
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup:=by
          unfold moveFront
          have sub:=keep_sub ws a b ((if d then 1 else 0)==2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let r0:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup:=(nd.erase _).erase _
          have ar : a.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0:=by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [keep_mem] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
      rw [hf,hlenEq] at hev
      simpa [childT,hop] using hev
    rcases all_binaryT checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw:=childTwo_swap (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold childTwo
          let rA:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup:=(nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
          have nk:=kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA:=by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
          unfold childTwo
          let rB:=((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup:=(nd.erase b.1).erase a.1
          have br : b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
          have nk:=kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB:=by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd kb b.1 _ nk bx⟩
          rw [bin_comm d b.1 a.1] at hm
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA,←List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ fresh) hh
abbrev PackingT:=Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPackingT : PackingT:=(0,0,0,0,fun _ => 0)
def deadWires : List Decor:=wiresOf dead
def deadSigs : List Sig:=deadWires.map Prod.fst
def decodeSigs (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) zero
    let b:=ws.getD ((bits >>> 4) &&& 15) zero
    let op:=(bits >>> 8) &&& 3
    decodeSigs k (bits >>> 10) (ws ++ [if op=2 then neg a else bin (op==1) a b])
theorem decodeSigs_eq (n bits : Nat) (ws : List Decor) :
    decodeSigs n bits (ws.map Prod.fst)=(decodeBank n bits ws).map Prod.fst:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeSigs,decodeBank]
    have hget : ∀ i,(ws.map Prod.fst).getD i zero=(ws.getD i defaultDecor).1:=by
      intro i
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? <;> rfl
    have hcode : (if ((bits >>> 8) &&& 3)=2 then neg ((ws.map Prod.fst).getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3)==1) ((ws.map Prod.fst).getD (bits &&& 15) zero) ((ws.map Prod.fst).getD ((bits >>> 4) &&& 15) zero)) =
        (codeDecor ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) defaultDecor) (ws.getD ((bits >>> 4) &&& 15) defaultDecor)).1:=by
      rw [hget,hget]
      unfold codeDecor dbin dneg
      split
      · rfl
      · split <;> rfl
    rw [hcode,← List.map_singleton,← List.map_append]
    exact ih (bits >>> 10) _
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    selectLive bits (ws.map f)=(selectLive bits ws).map f:=by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,selectLive]
    split <;> simp [ih]
def readNodeT (levels : Nat → PackingT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw:=deadWires
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def stateSetT (levels : Nat → PackingT) (slot i : Nat) : List Sig :=
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+deadSigs.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (decodeSigs depth ops deadSigs)
theorem stateSetT_eq (levels : Nat → PackingT) (slot i : Nat) :
    stateSetT levels slot i=(readNodeT levels slot i).2.2.map Prod.fst:=by
  unfold stateSetT readNodeT
  rcases levels slot with ⟨num,depth,cw,offw,data⟩
  dsimp only
  have hlen : deadSigs.length=deadWires.length:=by simp [deadSigs]
  rw [hlen]
  dsimp only [deadSigs]
  rw [decodeSigs_eq,selectLive_map]
def linkedSetT (levels : Nat → PackingT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (dead.autos[pair.2]?).map fun perm => (stateSetT levels slot pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSetT_sound (levels : Nat → PackingT) (k tmax : Nat)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (earlier : ∀ i < (levels (3*k+tmax)).1,ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset)
    {pair out} (h : linkedSetT levels (3*k+tmax) pair=some out) :
    ImpossibleT (targetOf dead) k tmax out.toFinset:=by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedT (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def contextOfT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : NodeContextT :=
  let slot:=3 * k+tmax
  let raw:=deadWires
  let (num,depth,cw,offw,data):=levels slot
  let (ops,bank,ws):=readNodeT levels slot i
  let start:=num * (10 * depth+raw.length+depth)
  let pos:=start+num * offw+packedAt data (start+i * offw) offw
  let nr:=packedAt data pos 5
  let st:=pos+5
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule dead ops depth bank a b)
  let ls0:=fun tag => ((idx0 slot tag).bind (linkedSetT levels (3*(k-1)))).toList
  let ls1:=fun tag => ((idx1 slot tag).bind (linkedSetT levels (3*(k-1)+1))).toList
  let ls2:=fun tag => ((idx2 slot tag).bind (linkedSetT levels (3*(k-1)+2))).toList
  (k,tmax,ws.length,ws,preCov ws,rules,rules.map (summarizePool ws),ls0,ls1,ls2)
def prelimT (T : Sig) (c : NodeContextT) : Bool :=
  let ws:=c.2.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
def nodeVerifiedT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : Bool :=
  let c:=contextOfT levels idx0 idx1 idx2 k tmax i
  prelimT (targetOf dead) c&&(if k=0 then true else testAllT c c.2.2.2.1)
theorem nodeVerifiedT_sound (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat)
    (htmax : tmax ≤ 2)
    (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (prior0 : k > 0 → ∀ j < (levels (3*(k-1))).1,ImpossibleT (targetOf dead) (k-1) 0 (stateSetT levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 → ∀ j < (levels (3*(k-1)+1)).1,ImpossibleT (targetOf dead) (k-1) 1 (stateSetT levels (3*(k-1)+1) j).toFinset)
    (prior2 : k > 0 → ∀ j < (levels (3*(k-1)+2)).1,ImpossibleT (targetOf dead) (k-1) 2 (stateSetT levels (3*(k-1)+2) j).toFinset)
    (checked : nodeVerifiedT levels idx0 idx1 idx2 k tmax i=true) :
    ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset:=by
  rw [stateSetT_eq]
  simp only [nodeVerifiedT,prelimT,contextOfT,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at checked
  have hN:=checked.1.1
  have hT : targetOf dead ∉ (readNodeT levels (3*k+tmax) i).2.2.map Prod.fst:=checked.1.2
  by_cases h0 : k=0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k'=0:=by omega
    subst k'
    generalize he : ((readNodeT levels (3*0+tmax) i).2.2.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 → S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply nodeT_sound (raw:=vars dead.mask) samples _ hN hT _ _ _ _ htmax (by simpa only [h0,ite_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful dead) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1))))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1)=3*(k-1)+0:=by omega
    rw [h0'] at h
    exact linkedSetT_sound levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)+1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) 1 names (prior1 (by omega)) h
  · intro tag xs hx
    have e : ((idx2 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)+2)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) 2 names (prior2 (by omega)) h
def blockT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerifiedT levels idx0 idx1 idx2 k tmax start&&blockT levels idx0 idx1 idx2 k tmax (start+1) n
theorem blockT_at {levels idx0 idx1 idx2 k tmax start n} (h : blockT levels idx0 idx1 idx2 k tmax start n=true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+n) : nodeVerifiedT levels idx0 idx1 idx2 k tmax i=true:=by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockT,Bool.and_eq_true] at h
    by_cases eq : i=start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)
theorem blockT_merge {levels idx0 idx1 idx2 k tmax start a b}
    (ha : blockT levels idx0 idx1 idx2 k tmax start a=true)
    (hb : blockT levels idx0 idx1 idx2 k tmax (start+a) b=true) :
    blockT levels idx0 idx1 idx2 k tmax start (a+b)=true:=by
  induction a generalizing start with
  | zero => simpa [blockT] using hb
  | succ a ih =>
    simp only [blockT,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
theorem makeBlockT {levels idx0 idx1 idx2 k tmax start n}
    (h : ∀ i,start ≤ i → i < start+n → nodeVerifiedT levels idx0 idx1 idx2 k tmax i=true) :
    blockT levels idx0 idx1 idx2 k tmax start n=true:=by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockT,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
def checkAtT (c : NodeContextT) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a:=ctxWireT c i
  let b:=ctxWireT c j
  evalMoveT c op a b (movedDecor op a b) ka kb
def combFieldT (c : NodeContextT) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a:=ctxWireT c i
  let b:=ctxWireT c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def fallbackFastT (c : NodeContextT) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,_,pools,qpools,l0,l1,l2):=c
  let a:=ws.getD i defaultDecor
  let b:=ws.getD j defaultDecor
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  let ct:=childT tmax cap len op
  let z1:=choiceVal (movedChoice op a b)
  if !properB z1||ws.any (fun v => v.1==z1) then true else
  if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
    let rest:=(opKeep un ka kb a b ws).map Prod.fst
    let links:=if ct==0 then l0 else if ct==1 then l1 else l2
    closeChild pools links (cap-1) rest (movedChoice op a b)
theorem fallbackFastT_sound {c i j op ka kb}
    (hlen : ¬(1+(c.2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > c.1))
    (h : fallbackFastT c i j op ka kb=true) :
    checkAtT c i j op ka kb=true:=by
  rcases c with ⟨cap,tmax,n,ws,cov,pools,qpools,l0,l1,l2⟩
  dsimp only [checkAtT,evalMoveT,ctxWireT]
  dsimp only at hlen
  rw [if_neg hlen]
  dsimp only [fallbackFastT] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    moved_full op _ _
  set len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  set ct:=childT tmax cap len op
  set d:=ct==0
  by_cases hcomb : ((restCov (getCov cov d) (column d (ws.getD i defaultDecor).2) (column d (ws.getD j defaultDecor).2) (op==2) ka kb ||| column d (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).2) != BitVec.allOnes 768)=true
  · simp only [hcomb,ite_true]
  · simp only [hcomb,ite_false,hz1]
    exact h
def makeBatchT (k n : Nat) (xs : List NodeContextT) : Batch :=
  (k,n,units xs.length,
    (List.range n).map (fun i => packedSig (fun c => (ctxWireT c i).2) xs),
    packedCov (fun c => c.2.2.2.2.1.1) xs,
    packedCov (fun c => c.2.2.2.2.1.2) xs)
theorem laneWireT_at (k n : Nat) (xs : List NodeContextT) {i : Nat} (h : i < n) :
    laneWire (makeBatchT k n xs) i=packedSig (fun c => (ctxWireT c i).2) xs:=by
  simp [laneWire,makeBatchT,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def batchMoveT (b : Batch) (tmax : Nat) (xs : List NodeContextT) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > k then true else
    let ct:=childT tmax k len op
    let d:=ct==0
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r * (BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackFastT c i j op ka kb) mask xs
theorem batchMoveT_at (k tmax n : Nat) (xs : List NodeContextT) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1=k) (ht : xs[q].2.1=tmax) (arity : xs[q].2.2.1=n)
    (pass : batchMoveT (makeBatchT k n xs) tmax xs i j op ka kb=true) :
    checkAtT xs[q] i j op ka kb=true:=by
  let len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  let ct:=childT tmax k len op
  let d:=ct==0
  have eval : checkAtT xs[q] i j op ka kb =
      if len > k then true else if combFieldT xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else fallbackFastT xs[q] i j op ka kb:=by
    rcases hxq : xs[q] with ⟨cap,tm,nn,ws,cov,pools,qpools,l0,l1,l2⟩
    rw [hxq] at budget ht arity
    dsimp only at budget ht arity
    subst budget ht arity
    unfold checkAtT evalMoveT combFieldT fallbackFastT ctxWireT
    dsimp only [len,ct,d]
    have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
        choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)):=moved_full op _ _
    rw [hz1]
  by_cases small : len > k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (makeBatchT k n xs) i
    let b:=laneWire (makeBatchT k n xs) j
    let cov:=if d then packedCov (fun c : NodeContextT => c.2.2.2.2.1.2) xs
               else packedCov (fun c : NodeContextT => c.2.2.2.2.1.1) xs
    change (if len > k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r * (BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.2.1 d) xs:=by
      dsimp only [cov]; cases d <;> rfl
    have ca : a=_:=laneWireT_at k n xs hi
    have cb : b=_:=laneWireT_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combFieldT xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · have hlenq : ¬(1+(xs[q].2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > xs[q].1):=by
        rw [budget,arity]; exact small
      apply fallbackFastT_sound hlenq
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPairT (b : Batch) (tmax : Nat) (xs : List NodeContextT) (i j op : Nat) : Bool :=
  let f:=batchMoveT b tmax xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRowT (b : Batch) (tmax : Nat) (xs : List NodeContextT) (i : Nat) (js : List Nat) : Bool :=
  let unOk:=if tmax==0 then true else
    batchMoveT b tmax xs i i 2 false false&&batchMoveT b tmax xs i i 2 true true
  unOk&&js.all (fun j => batchPairT b tmax xs i j 0&&batchPairT b tmax xs i j 1)
def batchRowsT (b : Batch) (tmax : Nat) (xs : List NodeContextT) : List Nat → Bool
  | [] => true
  | i :: js => batchRowT b tmax xs i js&&batchRowsT b tmax xs js
theorem batchRowsT_at (k tmax n : Nat) (xs : List NodeContextT) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1=k) (ht : xs[q].2.1=tmax) (arity : xs[q].2.2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j < n) (allRows : batchRowsT (makeBatchT k n xs) tmax xs js=true) :
    testAllT xs[q] (js.map (ctxWireT xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRowsT,Bool.and_eq_true,batchRowT,List.all_eq_true] at allRows
    simp only [List.map_cons,testAllT,testRowT,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@batchMoveT_at k tmax n xs
    have hun : (if xs[q].2.1==0 then true else
        evalMoveT xs[q] 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i) (movedDecor 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i)) false false &&
        evalMoveT xs[q] 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i) (movedDecor 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i)) true true)=true:=by
      rw [ht]
      cases htm : (tmax==0)
      · simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true]
        have h1:=allRows.1.1
        simp only [htm,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h1
        exact ⟨check hi hi hq budget ht arity h1.1,check hi hi hq budget ht arity h1.2⟩
      · simp
    refine ⟨⟨hun,?_⟩,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPairT (makeBatchT k n xs) tmax xs i j (if d then 1 else 0)=true) :
        testPairT xs[q] (ctxWireT xs[q] i) (ctxWireT xs[q] j) d=true:=by
      simp only [batchPairT,Bool.and_eq_true] at pass
      simp only [testPairT,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1,check hi hj' hq budget ht arity pass.1.1.2⟩,
        check hi hj' hq budget ht arity pass.1.2⟩,check hi hj' hq budget ht arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def runBatchT (k tmax n : Nat) (xs : List NodeContextT) : Bool :=
  batchRowsT (makeBatchT k n xs) tmax xs (List.range n)
theorem runBatchT_at {k tmax n} {xs : List NodeContextT} {q} (hq : q < xs.length)
    (hb : xs[q].1=k) (ht : xs[q].2.1=tmax) (ha : xs[q].2.2.1=n) (hn : xs[q].2.2.2.1.length=n)
    (pass : runBatchT k tmax n xs=true) : testAllT xs[q] xs[q].2.2.2.1=true:=by
  have all:=batchRowsT_at k tmax n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (ctxWireT xs[q])=xs[q].2.2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [ctxWireT,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def contextsT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n : Nat) : List NodeContextT :=
  ((List.range n).map (start+·)).map (contextOfT levels idx0 idx1 idx2 k tmax)
def headerT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar : Nat) : Bool :=
  (contextsT levels idx0 idx1 idx2 k tmax start n).all (fun c => c.2.2.1==ar&&prelimT (targetOf dead) c)
def rowCutT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar lo len : Nat) : Bool :=
  let xs:=contextsT levels idx0 idx1 idx2 k tmax start n
  let b:=makeBatchT k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRowT b tmax xs i (List.range' (i+1) (ar - (i+1))))
theorem rowCutT_at {levels idx0 idx1 idx2 k tmax start n ar lo len}
    (h : rowCutT levels idx0 idx1 idx2 k tmax start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRowT (makeBatchT k ar (contextsT levels idx0 idx1 idx2 k tmax start n)) tmax
      (contextsT levels idx0 idx1 idx2 k tmax start n) i (List.range' (i+1) (ar - (i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i - lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem cutsRunT {levels idx0 idx1 idx2 k tmax start n ar}
    (h : rowCutT levels idx0 idx1 idx2 k tmax start n ar 0 ar=true) :
    runBatchT k tmax ar (contextsT levels idx0 idx1 idx2 k tmax start n)=true:=by
  let xs:=contextsT levels idx0 idx1 idx2 k tmax start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRowsT (makeBatchT k ar xs) tmax xs (List.range' lo num)=true:=by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRowsT,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok:=rowCutT_at h lo (by omega) (by omega)
      simpa only [show ar - (lo+1)=num by omega] using ok
  unfold runBatchT
  rw [List.range_eq_range']
  exact go 0 ar (by omega)
theorem cutsBlockT {levels idx0 idx1 idx2 k tmax start n ar}
    (hd : headerT levels idx0 idx1 idx2 k tmax start n ar=true)
    (h : rowCutT levels idx0 idx1 idx2 k tmax start n ar 0 ar=true) :
    blockT levels idx0 idx1 idx2 k tmax start n=true:=by
  apply makeBlockT
  intro i lo hi
  let xs:=contextsT levels idx0 idx1 idx2 k tmax start n
  have hm : contextOfT levels idx0 idx1 idx2 k tmax i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ht : xs[q].2.1=tmax:=by rw [e]; rfl
  have ha : xs[q].2.2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.2.1.length=ar:=by rw [e]; exact one.1
  simp only [nodeVerifiedT,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatchT_at hq hb ht ha hn (cutsRunT h)
def chunkCheckT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar : Nat) : Bool :=
  let xs:=contextsT levels idx0 idx1 idx2 k tmax start n
  xs.all (fun c => c.2.2.1==ar&&prelimT (targetOf dead) c) &&
  let b:=makeBatchT k ar xs
  (List.range ar).all (fun i => batchRowT b tmax xs i (List.range' (i+1) (ar - (i+1))))
theorem chunkBlockT {levels idx0 idx1 idx2 k tmax start n ar}
    (h : chunkCheckT levels idx0 idx1 idx2 k tmax start n ar=true) :
    blockT levels idx0 idx1 idx2 k tmax start n=true:=by
  unfold chunkCheckT at h
  rw [Bool.and_eq_true] at h
  exact cutsBlockT h.1 (by simpa [rowCutT,Nat.zero_add] using h.2)
def cellsT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar : Nat) : Nat → Prop
  | 0 => chunkCheckT levels idx0 idx1 idx2 k tmax start n ar=true
  | d+1 => cellsT levels idx0 idx1 idx2 k tmax start (n / 2) ar d∧cellsT levels idx0 idx1 idx2 k tmax (start+n / 2) (n - n / 2) ar d
theorem kT {levels idx0 idx1 idx2 k tmax start n ar}
    (h : chunkCheckT levels idx0 idx1 idx2 k tmax start n ar=true) :
    cellsT levels idx0 idx1 idx2 k tmax start n ar 0:=h
theorem cellsBlockT {levels idx0 idx1 idx2 k tmax start n ar d}
    (h : cellsT levels idx0 idx1 idx2 k tmax start n ar d) :
    blockT levels idx0 idx1 idx2 k tmax start n=true:=by
  induction d generalizing start n with
  | zero => exact chunkBlockT h
  | succ d ih =>
    have v:=blockT_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
theorem forestT_all (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (top : Nat)
    (prior : Nat → Nat)
    (lo : ∀ m,Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior=true)
    (tabs : ∀ k ≤ top,∀ tmax ≤ 2,blockT levels idx0 idx1 idx2 k tmax 0 (levels (3*k+tmax)).1=true) :
    ∀ k ≤ top,∀ tmax ≤ 2,∀ i < (levels (3*k+tmax)).1,ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs:=chart_pairs valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => col_sound ci prior lo (valid.1.2 ci hc)
  have names:=valid.2
  intro k
  induction k with
  | zero =>
    intro hk tmax htmax i hi
    have hb:=tabs 0 hk tmax htmax
    exact nodeVerifiedT_sound levels idx0 idx1 idx2 0 tmax i htmax pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (blockT_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tmax htmax i hi
    have hb:=tabs (k+1) hk tmax htmax
    exact nodeVerifiedT_sound levels idx0 idx1 idx2 (k+1) tmax i htmax pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (fun _ j hj => ih (by omega) 2 (by decide) j hj)
      (blockT_at hb i (Nat.zero_le i) (by simpa using hi))
def qL24F (i : Nat) : Nat:=0x50c1af759b4b3181aa930503b649c6549302e95348140
def qL24 : PackingT:=(2,7,7,4,qL24F)
def qL27F (i : Nat) : Nat:=0x2c00d0170c0000265219a28402c00d13d15e30200002dd360068c0000000000006f365a8cf652e14c873418cbc32168a0461e0c8501e0a028020ff9b8d436a98a40a069fc329815453048140e78edab70aa34610a81eb1d5470da854c215030f7b696630355260a071ed6d181546aa4c140c3deda38a90d5498281f7c13148152605305030dfb74e3174a9a40a06db6719302e95348140fba4a92605d2a690281f749524c153605205032ed996a92a6c1220a07dd254d2060d5244140fbb0a8a40c1aa488281ef91414c1a54c482503df2342982a898904a06bc77295460d5308540f58ed42a8c1aa610a81ed1da75518354c21503dc3b4caa306a9842a07bc6551a060d5308540
def qL27 : PackingT:=(22,6,7,9,qL27F)
def qH0_27F (i : Nat) : Nat:=0x401080008
def qH0_27 (h : Nat) : Option (Nat × Nat):=lookupWord 1 4 3 10 2 4 qH0_27F h
def qL28F (i : Nat) : Nat:=0x30001c00070001c00070001f0007c001928d88837e6c5a483624120093ceea598dcb4610a8185bda7712bb64c815030d7b4ce2576c9842a061cf695c4aed9308540c3dce23415db2610a81e7495354920aa930503cf826290a4155260a079d254d524c2aa48140f3b0a92a28855490281e7615254520aa910503e6c304a9302a8c00a07cf0609326053180140
def qL28 : PackingT:=(12,6,7,8,qL28F)
def qL29F (i : Nat) : Nat:=0xd0028058751ac874484731a012f2186d1aa87148750c4a8d643a242e862546a242e861c486a3590e74312a3590e890ba18951ac874485d0c4d0dd693106baace4390078f46a1814c53048140f68cd3aa8a9a6040a81cf19b5551b068c215035e3388e1b4a98042a06bc67295454d3008540e78cdd2a8a9a6010a81eb19a8551534c021503da334eaa2a698042a07b866995454d3008540
def qL29 : PackingT:=(9,6,7,9,qL29F)
def qL30F (i : Nat) : Nat:=(if i<2 then (if i<1 then 0xe7eda264d82145408ffdcaaed8214540c7fda9aed8214540cfbda4aed82145408ffdcb68c8214540cfddb368c8214540cfdda36e132145408ffdcb6a13214540c7fdba6613214540e7dda36613214540cfedba6093214540ebeda86093214540efcda36093214540aff9ca6093014540efe9a26093014540aff9ca2093014540e5fda76e58508540e6fda66e58508540e7dda36e58508540e7f9a06e58508540e5fda76618508540e6fda66618508540e7dda36618508540e7f9a06618508540e3fda86558508540e5fda76558508540e6fda66558508540e7dda36558508540e7f9a06558508540cbfda8aed8508540cdfda7aed8508540cefda6aed8508540cfdda3aed8508540cff9a0aed8508540ebbda86155408540edbda76155408540eebda66155408540ef9da36155408540efb9a061554085408ffdcb215a308540adfdc7215a308540aefdc6215a308540afddc3215a308540afedc2215a308540aff5c1215a308540aff9c0215a308540a7fdca6159308540e6fda66159308540e77da56159308540e7f9a06159308540e5fda76618308540e6fda66618308540e77da56618308540e7dda36618308540e7f9a06618308540c7fdba6558308540e3fda86558308540e5fda76558308540e6fda66558308540e77da56558308540e7dda36558308540e7f9a06558308540cfbdba5518308540ebbda85518308540edbda75518308540eebda65518308540ef3da55518308540ef9da35518308540efb9a05518308540cbfda8aed8308540cdfda7aed8308540cefda6aed8308540cf7da5aed8308540cfdda3aed8308540cff9a0aed8308540cdfda76e15308540cefda66e15308540cfdda36e15308540cff9a06e15308540cbfdb86a15308540ef3d546a15308540e5fda76615308540e6fda66615308540e7dda36615308540e7f9a06615308540e3fda86555308540e5fda76555308540e6fda66555308540e7dda36555308540e7f9a06555308540eb7da86155308540ed7da76155308540ee7da66155308540ef5da36155308540ef79a06155308540ebbda85515308540edbda75515308540eebda65515308540ef9da35515308540efb9a05515308540afddca60d5308540ebdda860d5308540eddda760d5308540eedda660d5308540ff1d5460d5308540efd9a060d5308540cbfda8aed5308540cdfda7aed5308540cefda6aed5308540cfdda3aed5308540cff9a0aed5308540aff9ca6153008540cff9ba6153008540ebf9a86153008540edf9a76153008540eef9a66153008540ef79a56153008540efd9a36153008540e3fda86568808540e5fda76568808540e6fda66568808540e7dda36568808540e7f9a06568808540ebbda85528808540edbda75528808540eebda65528808540ef9da35528808540efb9a05528808540 else 0xebbdc56a15408540ebbdc36a15408540afdecc6e1a308540afddc52e1a308540e7ddb8661a308540cfddb86d5a308540e7dd986d5a308540afdecc6d5a308540afddc82d5a308540e7ddb8655a308540e7ddb5655a308540afddcb615a308540e7ddb9615a308540ef5db5615a308540afddcb215a308540ef9db8551a308540ef9db5551a308540efd9856c1a308540e77dc869593085408ffecc6e98308540e77dc96958308540ef3dc46958308540cbfdcb6a15308540eb7dc56a15308540ebddc36a15308540ebf9c56a13008540ef79c86953008540efb9a85513008540c7fd85aeda344140c7fd52aeda344140c7fd83aeda244140c7fd53aeda244140c7fd95aeda120940cfbd54aeda120940cff930aeda120940c7fda2aed9520540c7fd95aeda220540cfbd54aeda220540c7fda2aed9314540c7fd98aeda214540c7fd93aeda214540cff930aeda214540c7fd95aeda808540cfbd54aeda808540e3fd95aeda808540ebbd54aeda808540c7fda8aed9508540a7fecc606aa4c140e7f581546aa4c140a7fdc5486aa4c140c7fdb560eaa48140a7fdc854eaa48140e7dd8354eaa48140a7fecc54eaa48140c7fd836c6aa48140c7fd536c6aa48140a7fecc60eaa44140e3fd8360aaa44140a7fecc60aaa44140e7ed8254aaa44140a7fecc54aaa44140a7fdc84caaa44140a7fdc54caaa44140e7ed824caaa44140a7fecc4caaa44140f7e920549814c140c7fdba2e95348140b6fdc62e95348140f7d9302e95348140a7fcca6c55348140f7d93054d814814097fccb54d8244140f3dd8354d8244140b7edc254d8244140f76d5254d8244140a7fdca60d5244140f7e92060d5244140c7fdba6153244140efb5416953120940efd9306953120940c7fdba6553120940e7dda36553120940e7f5a16553120940cfbdba5513120940ef9da35513120940efb5a15513120940ff99305513120940aff9ca5453020940eff1a15453020940ef3d5469d5320540c7fdba65d5320540e77da565d5320540e7dda365d5320540ef5da55cd5320540ff1d545cd5320540ef3d5454da220540a7fdca54d9220540e5fda754d9220540e77da554d9220540e7dda354d9220540c7fdba64d5220540e5fda764d5220540e7eda264d52205408ffdcb68c5220540cefdb668c5220540cfddb368c5220540c7fdba65d3220540e7dda365d3220540e7eda265d3220540c7fdba6553220540e5fda76553220540e7dda36553220540e7eda26553220540cfbdba5513220540edbda75513220540ef9da35513220540efada25513220540efcda25cd3220540cdfda7aed3220540aff9ca5c93020540edf9a75c93020540efd9a35c93020540aff9ca5493020540edf9a75493020540ef79a55493020540efd9a35493020540efe9a25493020540c7fdba64d8214540) else (if i<3 then 0x84804002244300590e1002c8708016438402200a21c320200190e1800819080164c8400b264200593211010028990c0164c84404002264301ab00124158048d0ec0246856012342b0091a06d1d8048d0368cc00468400a0282005014100280a08014050400a01e20010141002c8d08016468400b234260200111a1802a8d094841a440b524205c305a92102e182d0908158c16a4840ac600b21c200590e1002c8708044014438640400321c398e06914c70348a6381a4431c0d2298e069158048d0170ec024680b8760123405c3b0091a02b198008d0158c2a4335219a90cd4841b58645352c042005014100280a08014050400a01e20010141687034890481a45a1c0d22d0e06916870348b4381a44a1c0d220059321002c99080164c8400b26422020011321d8048d0ac0246856012342b0091a118008d0a0b2825606c80de01a8025fec7f3dfbe7e85f787d3df3e7c85f047bcdeca7ab5e9079cde627915e1c77fddd676e5d9c762dd6e7545d34745dd067375cc0728dc8671a5c4c70bdc126fa5bcc6e8db866da5b4c6cbdb066ba5acc6aeda9e6a05a5868bd9fa67759c0668d9926605964651d92a64058e4631d8b6626587c617d84260958085fdd7ce5ec57945e0d7665d2572c5c3d6fe5b856d05a9d68a598565058cd61657e55e8578d5ae561552c549d51654454b852cd48a5215474515d44650d54184fed3de4f353b04e4d3764d653244bbd2d24ad529849ed24648751f4472d1a24645174455d14644a511843ed0de43050b0427d082419504840ad01a3ff4fec3f3cfca3e84f783d6cf3e3c84f043bcced63ae4ea83a2ce6e3944e34385cdfa37a4de4377cdc23694d94363cd8a3614d74355cd3a3474cf4335ccba3274c80315cc3a3074c002f8cbba2e74b8c2decb6a2d64b302c1cade2a74a74292ca1627e49dc26fc99625e495c24fc91623b48d022cc89621e485020cc80a1fb47c41e9c78a1d847381c6c6fe1b846c41a9c68a19b465018cc61617b45d016cc58a1584538143c4f213544b8123c466112442c103c3f20f543ac0e0c35a0cc43080bdc2e60b542c40a9c28a09b425008cc21607e41dc06fc1a20614168052c12e04440f4035c0ba0244074015c03a0074000c7fda86d53148140f7f1815453048140e7eda36095244140c7fda86d53244140c7fdb86953244140b7f9c854d2044140f7798554d2044140f7d98354d2044140efb9a55053020940efb9a15053020940adfdc32d5a720540adfdc32c9a720540e7bdb9551a220540e7bd5468992205408ffecc6e93220540edf9c269d3020540efb9546893020540a7fdc864da2145408ffecc6e982145408ffecc6e93214540e7f9a86493014540abfecc6d5a808540abfdc32d5a808540abfecc6cda808540af7dc32e1a508540e3fdc56a19508540e3fdc36a19508540 else 0x2c01a05c302e00d1030c94b0c0c00416a5158d8800205a2c02098760108ca70085a1c1d0e00d118d3870170cc49c3815c6018100ca8210008038b4382433a1c0d2300100910008038800401c521c100531a118d3870170c0140504634e1c05c300551a1002a990b4002a35a00200500f178d01288014044405a105a02502e180280788c68094400a6642005011100298d0801409041240d2231a41202e198d58008c6ac000b870240d220055221000807880155884e00a340da300551a12c7034896a43a1c0d22d0e06916874908348c0900060646002e8b03200e400c00110060008800400c4e00170e08038008800401c4e00034200700101718008038800401c4e1c1001032138000d08014cc84e006342932005100800088ca4200600268a300802b100400088ca420100022003005100180288010004460c10040011194840100040c060080022004001345198704010004402da6c2745718170004160446e058028402ed3600d180209b88708c8af8018009c02be10000817ea291b01490c0031c00020d48303000f84004054490414860a0ad800920ac00490d6002a19080d68708a1807c41b20ae200106e1016a4110c8ac912089264a448482b2c3220d9121120c834880780b840dd24321c05c441990e02e19410088908c00408931460ae00b2443482080a817080540b841041001015102485208524400202a2005912124105208282b6002b0041512415800920ac004292100500b168704a0b43840d0e2c5069182be870348f4381a4578a0d22d0e069100081109208200201620010071005840040544104224208291a100080d08004054490422420240801a1c11c2282d0e168704000101040164a4400b25220059291101000c948c016468400b234200591a1002c8d08808004468600b234200591a1002c8d080164684c040022343282d001680074003a001500080d6870170f04b4380b87825a1c05c3c8231a41200502b2a096870170f04b4380b8663182400ba1c40010221002c910801648))
def qL30 : PackingT:=(283,5,7,14,qL30F)
def qH0_30F (i : Nat) : Nat:=0xe010059c03e06e06b82202ac09012805802d205a03d00f025051607e2309ce00e4024850023a1000b082881780000b284c02c88ef0600585001013081080
def qH0_30 (h : Nat) : Option (Nat × Nat):=lookupWord 9 34 6 13 5 4 qH0_30F h
def qL31F (i : Nat) : Nat:=(if i<1 then 0xc6fda6aed9308540c77da5aed930854097bdc4aed9308540c7f9a0aed9308540cbf9a8aed3008540cdf9a7aed3008540cef9a6aed3008540cf79a5aed3008540cfd9a3aed3008540c7bdb4606aa4c140c7bdb4546aa4c140c7bdb4486aa4c140a7f9c8482aa4c140e7d953482aa4c140e7e952482aa4c140e7d931482aa4c140e7e921482aa4c140c7f5b1606aa48140c7f9b84c2aa48140e7d9534c2aa48140e7e9524c2aa48140e7d9314c2aa48140a7f9c3442aa48140e7e952442aa48140e7f151442aa48140e7e952482aa44140e7f151482aa44140a7f4cb6a61120940edd9a34c27720540e57da76565520540ed3da75525520540e57da764a5520540ed79a74c25520540ef59a34c25520540e5dda76563320540ed9da75523320540e5dda764a3320540e5eda764a2220540e5eda76562220540edada75522220540e5eda764e2220540ede9a74c22220540efc9a34c22220540efc9a34c22214540e1fd9869e8808540e2fd9869a8808540e37d986968808540e3dd9868e8808540e3f9986828808540e37dc96968808540eb3dc46968808540e1fda76568808540e2fda66568808540e37da56568808540e9bda75528808540eabda65528808540eb3da55528808540e3ddc968e8808540e3dd9568e8808540eb9d5468e8808540ebd9c068e8808540e3f9956828808540ebb9546828808540abf9ca4c28808540e9f9a74c28808540eaf9a64c28808540eb79a54c28808540ebd9a34c28808540e37da86565508540e57da76565508540e67da66565508540eb3da85525508540ed3da75525508540ee3da65525508540e75d9568e5508540ef1d5468e5508540e779956825508540ef39546825508540e37dc96a25508540e37da86625508540e57d9869e5508540e67d9869a5508540e75dc968e5508540e75d9868e5508540ef59c068e5508540e37da864e5508540e57da764e5508540e67da664e5508540e75da364e5508540e779986825508540e779936825508540af79ca4c25508540eb79a84c25508540ed79a74c25508540ee79a64c25508540ef59a34c25508540e3ddc96a23308540e3dda86623308540e5dd9869e3308540e6dd9869a3308540e75dc96963308540e75d986963308540ef1dc46963308540e3dda86563308540e5dda76563308540e6dda66563308540e75da56563308540eb9da85523308540ed9da75523308540ee9da65523308540ef1da55523308540e7d9986823308540e7d9956823308540ef99546823308540f3e9825498180140f3e9824c98180140f3f1826055180140f77152605518014097f8cb6093180140d3f9b86093180140f7c9824c93180140d7f1b56053180140f3f1826053180140f7d132605318014097f9cb615218014097f9cb60d218014097f9cb54d2180140d7f1b84c52180140 else (if i<2 then 0x3a001d0009016800880a4004405200221290015874800ac3a400561d200230e90016800480b4005a001d000e80074002e01a002d000e80074002405a002b00d0015806800ac034005601a002202900110148008c024005c001e000f0007800229223221dc004106e0017000457f8005c001e0008a289b7000c4db800428bc00210ee001697b3c3964c79e23b0fb83cc15e06afcb7d4be1de0aeb370cb65daead53698b3dd9aacb363cadfd5caac3514a5dd12a873428a05cefa75b39c9c5cdea6bb340967c97a3db17c885c26a11306c82dc0fa05b01c7ffbe99e9aef4753b969c02df06efb739b7adac6cdb629adad5c69fb4b9a3ad00659b199802bb45d1ae49702b705afabe9572a9053fa9b94baa4c51da7e93d29d84e3a6d934a9944c1a5c92c295049fa4b9222900471a3491828a4449a2090e2854421a09902a7f83f39f58f8a7b43cb9e18ed27583a39ca8e1a6f03699b08d6269433b9968c7a6203019798b925ac2cd9628af255c29f9488a224f426b92e895248c23d91a88b244821590688123f81ed8ef87423841b38d2865a31017f8b885a22c01578a7850227012f89384622140fb876837a1a00c185982aa14409984881da0d005f828812208002b80e803a00087fecc6e9834414087fecc6e9824414087fecc6e93244140a3fecc6e5a808540a77ecc6e5a508540af3ecc6d1a508540a7decc6e5a308540afdacc6c1a3085408ffacc6e9300854087fdc1aeda848140c7f9c0aeda848140c7f930aeda84814087fdc8aeda34414087fdc5aeda344140c7bdc4aeda34414087fdc2aeda344140c7f9c0aeda344140c7f920aeda344140c5fd95aeda720540cdbd54aeda720540c5fd93aeda720540c5fd92aeda720540cdf930aeda72054087fdcaaed9720540c5fda7aed9520540cdbda7aed5420540c5fda7aed932054097bdc4aed9320540c5fda7aed9220540cdf9a7aed3020540cfd9a3aed3020540cfd930aeda31454097bdc4aed9314540cfd9a3aed3014540c3fd98aeda808540c3fdb9aeda808540c3fd95aeda808540cbbd54aeda808540cbf930aeda808540c3fda8aed9808540c5fda7aed9808540c6fda6aed9808540c77da5aed9808540c7dda3aed9808540c7f9a0aed9808540c77d95aeda508540cf3d54aeda508540c77db9aeda508540cf3db4aeda508540c77d98aeda508540c77d93aeda508540cf7930aeda508540c3fda8aed9508540c5fda7aed9508540c6fda6aed9508540c77da5aed9508540c7dda3aed9508540c7f9a0aed9508540cbbda8aed5408540cdbda7aed5408540cebda6aed5408540cf3da5aed5408540cf9da3aed5408540cfb9a0aed5408540c7dd93aeda308540cfd930aeda308540c7ddb9aeda308540cfd9b0aeda308540c7dd98aeda308540c7dd95aeda308540cf9d54aeda308540 else 0x93d140dc0a806743801c00780b8014019e8a06e055e3001e003a0dc05c00a063f45f3602a01900100cd06e02e00518d02399b81778c00a643002e41241ac11ccdfc6005321801720919041024f18c86005c82298004004200a007c00e0446000b00041140d80a4018090a05600c0483017c0400a001e02e003005003f01700383158002c0018820b804410a2083104170e882100c80d01b81578c007803802800b412a4ca46a48402c015a08cd041922f1891a00b005682300802bf5c01700b800f411c11db7e4dc0b803005802c015a09320019000a87441081c7b57ae005c007a08d20018820d80062082e01104270e882148d023c9b81778c00a343002b412411e46a4dc0bbc60051a18015a09206f23408e05de30028d0c00ad04902a91a047937f180146860056824807c8d023c9b81778c343002b412446811a4dc0afc60051a19a0800531041700882158005c02c00510418820b874410a4ca46bc60051a18015a08f265235e30028d0c00ad04793291af18014686005682389978c00a343002b411a4ca46bc61a18015a08c264235e30028d0cd0400276820b4105a082d0416820b41062082a1d1042b0008089800a20831041700882149178c00a343002b411a48bc60051a18015a08c0200cdd91d7005c01e003d048122f18014686682001348006400320019000c8005043d16d16ca6c1bcdb83b8010021e6dc1de8a05c5f36f450171c0006000300018000c000417fcd800f81b800a01018000c0006000300018000c0006000300015820c80074003601a002d000d874800a4003a001b00d001680074003a001b00d00168006c3a4005200130e9001680074003a001d0009014800b4002e01a002d000e800480b4005601a002b00d0015806800b4003a001700d0011092800880a4004601200221290015874800ac3a400561d200230e9001680074003a001b00d0015806800ac034005a001700d00110148008c024005a001202d001680074003a001d0009092800b4))
def qL31 : PackingT:=(199,5,7,13,qL31F)
def qH0_31F (i : Nat) : Nat:=0x16107780059c61211907e0bd59e016340
def qH0_31 (h : Nat) : Option (Nat × Nat):=lookupWord 3 9 4 13 5 4 qH0_31F h
def qH1_31F (i : Nat) : Nat:=0x81403003302c80403302782910f412da680fd9eda240101c420032c194084020800
def qH1_31 (h : Nat) : Option (Nat × Nat):=lookupWord 6 20 5 12 4 4 qH1_31F h
def qL32F (i : Nat) : Nat:=(if i<1 then 0xc5fdb969d5220540c6fda96d85220540ccfda76d85220540cebdb66905220540c5fdb969d3220540edb9a75513020540ef995468d3020540afd9ca54d3020540edd9a754d3020540ef59a554d3020540ff195454d3020540e5f9a76493020540e7d9a36493020540e7d9a36493014540a3fdc92d5a808540a9fdc72d5a808540aafdc62d5a808540abbdc42d5a808540abddc32d5a808540abf9c02d5a808540a77dc92e1a508540ad7dc72e1a508540ae7dc62e1a508540af3dc42e1a508540af5dc32e1a508540af79c02e1a508540a77dcb661a508540e73d986d1a508540cf3db46cda508540c3fdcb6a19508540c3fdb96a18508540c5fdb969d8508540c6fdb96998508540c77db96958508540c6fda96d88508540ccfda76d885085408efdcb6988508540c6fdb96988508540ccfdb76988508540c7eda96c88508540cbeda86c88508540cdeda76c88508540ceeda66c88508540c7f5a96c48508540cbf5a86c48508540cdf5a76c48508540cef5a66c48508540cf75a56c48508540adbdc7215a408540aebdc6215a408540afadc2215a408540afb5c1215a408540e3bdc96a15408540e3bda86615408540e5bd9869d5408540e6bd986995408540e73d986955408540a7ddc92e1a308540adddc72e1a308540aeddc62e1a308540af5dc52e1a308540af9dc42e1a308540afd9c02e1a308540a7ddcb661a308540a7ddc92d5a308540af9dc42d5a308540afd9c02d5a308540a7ddcb655a308540a7ddc9615a3085408fddcb215a308540a7ddc9215a308540adddc7215a308540aeddc6215a308540af9dc4215a308540afcdc2215a308540afd5c1215a308540e79d98551a308540ef1db5551a308540e7d9986c1a308540cfd9b56c1a308540ef99546c1a308540c77dcb6959308540c3fdb96a15308540c5fdb969d5308540c6fdb96995308540c77db96955308540cf3dba5515308540eb3da85515308540ed3da75515308540ee3da65515308540ef1d5468d5308540a7f9c9615a0085408ff9cb215a008540a7f9c9215a008540adf9c7215a008540aef9c6215a008540afb9c4215a008540afd9c3215a008540afe9c2215a008540aff1c1215a008540e7b998551a008540a7f9c960da008540a7f9c954da008540ef395454da008540e3f9c96a13008540c7f9ba6613008540e3f9a86613008540e5f99869d3008540e6f9986993008540e779986953008540ef39c46953008540ef59c36953008540cfb9ba5513008540ebb9a85513008540edb9a75513008540eeb9a65513008540ef39a55513008540e7d99868d3008540ef995468d3008540afd9ca54d3008540cfd9ba54d3008540ebd9a854d3008540edd9a754d3008540eed9a654d3008540ef59a554d3008540ff195454d3008540f749535493048140f761525452044140 else (if i<2 then 0xc00a502471a006005218c98c64104911c6809401720886be68a66c00c00a5011345336006005281778d08cc9c68c64018014a05de34202ef1a138d60301298c900bbc68405de3423290254051e64012d8d0c0440b8094017208a0d205de3190d904581202502ec86c822aafaa2a9b003002941815154d8018014a090abea6c00c00a503855f5450060052aafaa2a9b003002941b5b21a1a482c68b242d90d0d24163459216c8686920b1a2c90b6434349058d16b20095c6a014868a66c61c00c0040026d1a3a9f0ec06c82001309928d18c9870036410009c0af21b20b468805790d905a34451a321f0ec06c0231930159d4e4364168d140af20b468601a05790da344329401321c86c8229a299b19480300100098d7cd14cd8018008004c64283864161d99190c650e02ef18005a822808815f8c000b41164380bbc60015a08aa1c05de3000b504550e02ef18005a822a8701778c002d411548a0154840b1482a1aa08e0d205c059e3150d5046b1902b9206866822d8c81749034334116c640ba481a19a08b63205d240d0cd04540192292102c920b196866824087017090802d41164380940b2016a1aa08c0d2059e30d0cd04506902bf18686682283481778c343341141a40bbc61a19a08a0d205de30d0cd04506902e02c619f186866823834890f6475c743741190880bc0400c402281805004fd7fd17cdbc63c09a05a01005e014017009ebfe8be6de31e1cb8d1e3068a86260887e1de8616150849e0da8296058805dffa7ee5f9c7dcdf267b05e9879bde3a7845dd0763dd4e7495d08731dc8671a5c286f9dbb26d95b3c6c4dade6a75a6868cd9fe66c599465dd93664658d861fd86261158045f9d7a65d9573c5bed6ba59e563857dd5b655d555854ed4ee534549c51fd46251154104fcd3d64ee539c4d6d31a4b952b04a1d25e48d520c478d1ae45e5144443d0da429506440bcffa3f14f843d0cf263b94ec83aace763964e3c384cdea36a4d68349cce63294c64308cbe22e84b602c7cade2aa4a5c283c9b6260494c23fc8be2254860207c7d21e147381bdc6b619d463417cc5b2156450c132c48a11244080e8c3620c542d40a4c25208441d005dc12a022400087fdc52e93148140e3f9a86053048140a7f8ca5453048140b7d9c54c53048140f7d1814c5304814087fdcb6953244140e7e9a35492044140f769535492044140f7e1c25452044140ef95a35053120940efd1a14c53020940ff91414c53020940a5fdc92d5a720540acfdc62d5a720540adbdc42d5a720540adddc32d5a720540adedc22d5a720540adf9c02d5a720540a5fdc92c9a720540acfdc62c9a720540ad7dc52c9a720540adbdc42c9a720540adddc32c9a720540adf9c02c9a720540ed3da75515320540ef1d5468d5320540e5bda755192205408dfccb69d5220540 else 0x4503601800e00600206b00002a4f8c79b01768758114190864022ca7c63000002c09005ce53e3001b604575ff3600de06f18282f82281b00c0009641801a003d15c3b80bc60ee1de8bc05e30402d02c2031a0900685c890b4300299b7c07fc61a18800b21c243d9007bd0c633271a321306005281778d09c6bc1b008c84c64a05de3420d902ef1a1b8d06cf87057f8300299c6817ccd8ca4c64c38c1801501900afe3430c8057f1a1b8d00619098c9032015fc686e3405de1c60c00a50d96df921920b1a2d4106c890b8d4029403101648460afe34204b05f53650e0052b0e003301310b0c940bbc685634a0d405443432504b05f5365290052e87017490b411048a4380b2014486a08c0580d2d04302e0696821b0c8348173411015fae01a4487a08b21c05de30d04402e0051216822087002890b4110cc9c68c64c38018014c05de34202ef1a138d60360119098c940bbc684e34753e1d80c00a571a34533631930e006005381778d080bbc684e3580d804642632502ef1a138d016f8760300294d14cd8c38018014a05a80a642306dcc8c8632071a2aa2a9b287003002955154d9438018014a090a6ca1c00c00a503854550e0060052aa2a9b28700300295871819809885864a05de34202ef1a129938d28ca87003002980bbc684c38c04c42c32402ef1a101778d080bbc684438c0cc42c32402ef1a101778d080bbc68405de342d1ac06c02c21c192e8d603601610e0c9746b00b0870649a3580d84383245292055211c94902c908d4a48154846a5240aa423129201521181218c8030029009720824bc68804b904125e344025c82092f1a238d60104918c91c68097018014868a66c65200))
def qL32 : PackingT:=(156,5,7,14,qL32F)
def qH0_32F (i : Nat) : Nat:=0x205201880e016b05805bc08c05a0a684d80580ec00580402ce1200b302002c510020
def qH0_32 (h : Nat) : Option (Nat × Nat):=lookupWord 5 19 5 13 5 4 qH0_32F h
def qH1_32F (i : Nat) : Nat:=0xc00c00c360f21346b4500c3a1bb0604e0372300c00c40200c00c00c00c00c00c00c00cb0600c00c00c00cd7400c00c080000
def qH1_32 (h : Nat) : Option (Nat × Nat):=lookupWord 4 32 6 12 4 4 qH1_32F h
def qH2_32F (i : Nat) : Nat:=0x9901d18506b03205808904f00f07009a021687000
def qH2_32 (h : Nat) : Option (Nat × Nat):=lookupWord 4 13 4 12 4 4 qH2_32F h
def qL33F (i : Nat) : Nat:=(if i<1 then 0xa57d1ce86f3fb9dfcde26632df9574a224992108ea468e2cf13687d42ce0ef0518103fbdf92fa37c43d5de36ed475739f5c82e1b6f536e5afad4168db37d946c7262bb0f1816bda5c9ad31636aea55ca9f54569ef4d9a6612ce92047222a10ee83b4051f38f2474b38d1b4cd5a6713259868bbc5a22ad947c99a49121f8f887203491868b444fe2380f886a82f213207b02900ba000effb74c0a60a077fda260530503bfea930298281dff6e95348140eff974a9a40a077fdb154d20503bfea9b4290281dff68d8148140effaa6c0a40a077fdba60d10503bfec1b4488281dff6e98244140effb6ac1220a077fda560910503bfed9b0488281dff68d8244140effaa6c1220a077fdba54910503bfed9aa488281dff68d5244140effb06a9220a077fdba4c910503bfedaa6488281dff6953244140effb0a99220a06ffda3544825037fed2a6241281dff6553120940ff7aa898904a07ff9514c0825037fed2ae640a81dff6557320540ff7aa8b9902a05ffebb5cc815037fed3aa640a81dff65d5320540ffbae6a9902a06ffdb5688815037febab4440a81bff6cda220540dffae6d1102a06ffd5368881503bfea9b2440a81bff68d7220540fbfae6b9102a06ffda354881503bfec9aa440a81bff6895220540dffb4629102a06ffdba4c881502ffedba6440a81bff69d3220540effb2e99102a06ffda54c881503bfecaa6440a81fef5513220540ffbae699102a06ffda24c881502fff5da6440a81ffe5c93020540fff2a498102a06ffdb268c515037fedc34428a81bff6cda214540dffb74c10a2a06ffda360851503bfec9b0428a81bff6898214540bffd76c10a2a05ffdb3208515037fed190428a81bff6e93214540bffb70990a2a06ffda84c851503bfecc26428a81bff6893214540ffdb04990a2a05ffebb4c851503ffcc126028a81ffe2093014540dffb6ad4042a06ffdb36a021503bfedcb0a10a81bff6a18508540effb30c2842a077fd9561421502fff5db0a10a81fef6155408540dffb70d1842a06ffdb568c215037fec2b4610a81bff215a308540effb0ac9842a06ffdba60c215037fed430610a81dff6618308540dffb4ac1842a077fd9560c21503fdeaa30610a817ffaed8308540bffb70a9842a06ffda854c21503bfecc2a610a81dff6555308540fefb0aa9842a07fbd5454c21503feec1aa610a817ffaed5308540fff30a98042a077fd83aa920503bfea9d5490281bff6961120940effb2b08904a07fbd54844825037fed1c2241281ffe4c21120940dffb472a902a06ffda2954815037fed2c4440a81dff6562220540ff7aa911102a06ffda3888815037fed444428a81dff6622214540dffb47110a2a077fd9388851503ffc9844428a81dff6568808540ff7aa944042a06ffda3a20215037fed44aa10a81bff68e5508540 else 0x222e6dc600680528270214db8c1020c6014e5611142268b4db0c19a2b180260508001a0b00a0c060080260ac809c04005a6cc628100d39768ec57c37d3601b008e8119b318180c00201068119b09020070c2d1480b4008041a0400e18460900080463040cc1be020d0203001402c881017f4561c0b0059812004a8ac608300a05672b081202545220402e240801c09345211200201064490240418924334689081f2a190e20540f900501543281a43164330082a8648a188d42124207ca32416a1aa34314aca19380526480a411451b2864f2098011a1b2484a3380291ac04326109b8d0d90ae30dc80a41129242564c6a7010d92b2084ac680380978a41125258d4190e4502a01c048c44b1a83302464949308963506439069286e8044848702e282443205a8d0c9298619205b01221282443205a8d5c50e4600a48901482b8a864ca0841009a35714039063815a0c48417100a807224300a46b010c98425124148e2f1a192522480a4121929254340b839219200522480a412192c826010550c90c360219252410954108201244803906309200a02f014212a82a1d0847439e2c210d2402a04687069231a00e0246054038091807e342048059870692005244865014822a821040268d00720c600a02f010c02912c0488482180a92161c1a4a05403912180523580a10910ca1a0e2054801489202904864aa084100922401ca63b01421189200a02f014212805a1d084c70692805a1d08434903271a1064e342d041901521922821041938d1002c820c84a439219300523480a4102a432600a468390712282a0106416118d011a1c1a48c6808825a1c1a4a24890b1a8321c8c750e3b1a8244868702e2805244a0a01419280fe3425042083271a20054052083221921c605c6a78d2190e4500a4c9014824325904c008d21920e200a0530142128052341ca10901a9df0de1c834942d06f0e4484171402a029040a90c90e318e0e508434918011a4320b34102e31a90e408460d4028140e5084b43a108691801011002031004400027018159402d02a3407e8c148100a00a81a41486300d90521980219289200a84a8151aa30638f21987005a30638a0910d121a35460c702e38a911286504d29a35460c3204302d43541a8d1a9432700a02d014821b2864d2098011a432364a2181201631c1a4a2187521943541a8d1df380501680a43482432610c0900b18e61c1a4c0140581440521a411a410164421a48014992029041ad0c9a41300234864369449212a3577cc730e0d270e54a4ef82ee35460c24909121a35460c730e05c8e83f2d78ddc3de1c704b7c3b8fd9eec5f5e3ad6d52e9ff4b3a28d016747315938c83e3b3177895c37e0cf0057c6bcadd66e0f6b5b3cd8cac195c5ac4d562a394f6)
def qL33 : PackingT:=(132,4,7,13,qL33F)
def qH0_33F (i : Nat) : Nat:=0x101778a9c0237c080008db015740d50079008de812802360024c01a78080016a011b008df0098c03d009c602fd1afb008e011b008dbba640236c09b008df000f51760c4e008dc8088815600459038d011240b5a0bc7058d019802368015008d981b60027807250069baf84967007ea016601d580bd40b7d024902ec023680194056f028e4054a032e0598046cc0ac809420508046dc0a8e00100270046c81310008aa59e02bb4050c0b0601cb0226c17a011b008d8046c0236c09a304fd8237012c011b90498046cc0c920594042981b00236a083f01fa828802374073a0158046fc06c011b008d881889565c00a704648085406320a5008da0174c0a7804c008d8046e002ea0606035c8160c0aec04b10033800000e8606350488046c80f16c4fc00f901ba00b7c07b9027a0212c4ea011b4012c00f241100030115f602571173e050f043c811bc0d3801bc045e92ca405ac27f704cf01f300a2011b100a680580104011b10484008d00662005404b902c8800820b9d007982e280efe035e033c92d80237200e008d8bace405ec002008dd22c9403b6086008db8106c14142b460148046f813a4065105f0046c0237003b008d9010f4018011b800d3023fc11dc0a73139eaafb015940b4a00960061097c011b008dc01da80748271c004e01f64175e068008da82068020e00b30530001c02366040008da81378071608a7054f01840237e02710242807101490037c03f9010a80a520b6008db82a00237606f102e0046dc07d80709049302bf413c011b008da9ad00236011b008dc31400236203d003d0046e402340aa000101c04008000003010040e010383800000005c300200010180301808041501800140200000141f000182e010108c0002040140804018000e0600000000a00808120002040080a000340218008180002
def qH0_33 (h : Nat) : Option (Nat × Nat):=lookupWord 72 276 9 17 9 4 qH0_33F h
def qL34F (i : Nat) : Nat:=(if i<2 then (if i<1 then 0x954815037bed3caa40a81ddf65e5520540defb472a902a06f7da295481503bbec94aa40a81fde4c25520540dfbb4f19902a077dd978cc815037eed2c6640a81df76563320540ff3aa919902a06fdda28cc81503beec946640a819ff6a62220540dbfb4f11102a06fbda4888815037f6d144440a81dfb64a2220540dfdb4f11102a077ed97888815037f6d2c4440a81dfb6562220540ff5aa911102a06feda388881503bf6c9c4440a81ffa4c22220540dfbb45198a2a077dd928cc515033fed4c4428a81bef6922214540dfdb45110a2a077ed92888515037f6d444428a81dfb6622214540dfdb47110a2a077ed9388851503ff49844428a819ff6a68808540d7fb5144042a073fd98a20215036fed3d1010a81bbf69a8808540defb4b44042a06fbda4a20215037eed1d1010a81bfe6828808540d7fb4b44042a073fd95a2021503ddeaa51010a81aff68e8808540f7f26144042a067fda9954215035fed44aa10a81b7f69e5508540ddfb4d2a842a06f7da595421503bbecacaa10a81bef6925508540fe7aa92a842a06fdda3954215037fcd04aa10a81bdf6a25508540eefb312a842a06f7da395421503bbec9caa10a81fde4c25508540dfbb5119842a077dd988cc215037eed2c6610a81df76563308540ff3aa919842a077f9b360a00503bfcd8b0500281dfe6e13280140eff36a99400a077f9b14ca00503bfcdab0300281dfe6cd8180140eff364c0c00a077f95260600503bfc9930300281dfe6cd5180140eff364a8c00a077f98254600503bfc992a300281dfe6e13180140eff36a98c00a077f9b24c600503bfcc126300281dfe5493180140eff37090c00a077f9b548600503bfcc2a4300281dfe6cd2180140eff30690c00a077f953486005023ff5db50902811ffaeda3441408ffd76d1220a04dfebb69c815025ff5db5010a813dfaeda5085409fbd76d1842a067f920aa9305023fedc554902811ff6ceaa481408ffb6355240a067f930aa9205033fc88554902819fe482aa44140cfeb5308904a065fda99dc815036ded24ee40a819df6a65520540dafb4f2a902a06f3da4954815036eed3c6640a819fb6a62220540dbdb4f11102a06fada4888815033f6d4c4428a81beb6922214540c7fb5344042a069fda7a202150357ed351010a81adf6968808540d77b4944042a06bdda3a20215035fcd051010a819df6a65508540d6fb512a842a06d7da79542150373ed34aa10a81bcf6925508540debb472a842a06f79a0954215035eed446610a81b7769e3308540ddbb4d19842a06f5da58cc215037ecd046610a815fe6e13280140efd30499400a073f98260600503bf8c0aa3002815fe6e13180140aff36a98c00a077d9324c600503bf8c0a63002815fe6e12180140aff36a90c00a057f9b348600503bf898a43002811ef6d2aa4c140 else 0x1057fa2945e6c4db8c11820d8013d179b502205c61836003b5f2bfc628710ee6d800fd14a2929e3046087736c0082bfcd89b71823043ba2e00415fe8a5179b136253c608c6004f45e3042487736a0d800e043aff45e6dca783702c0088e951ada31145ba8abb13aa24c443b884110161d4435685f30a72114c20383210476044c06e7fcafd9df7fbe6b7ca0f7cdecb3d187976f179df5bbc576d0ec2dd3bba517338e529c3fb8016f48dd75b3e359069e2d27d9efb32a64bec6a98c2315e6270c31584fb07960a6c0b5803afe15f76be557b7af3e5e1abb9d75b2e905cbeb8b96c7ad325a18b399623ac2157f6af295d22b7e56b0acc95862adb556aaa3d534aa43543aa625496289850e4a13141327f54f9e9ea53c1a75d4e6e9c45375a6c54c3696a12c1255c4a6c944126fa4b949268ffd1c0a35045d089d5101216341f681f502ba0263fea7f10fc99ee93d1878bcee91d6a3a72723ce2f1c0137326dccda11b1135c06abcd449a5834646804ce819b5331e65d0ca71933321a639cc60989030d4613cc14980e2fe65f34bd917972f0e5d58b98170a2dde5b50b5c969e2c2a55d8a7c1485280e4e2499092f024e447fc8c6112f21a442008068fc61efe3cb47578e5d1bea36e46a30d0a1986321c6200bcd169e2b445450a221348254846a08610fc61e4439486b60c9c17982bf0516093010c01ef038c06740b7413a822303a205d008b80af00ba0002bff5db42982815ffaeda848140cffd76d4240a057febb68d20502bff5db46882819ffaeda3441409ffd76d0904a057febb64482502fdf5da82412817feaed30209409ffd76d3902a06dfebb69c81502bff5db2e40a813ffaeda520540affd76ca902a05fbebb55081502bff5db2640a813ffaeda220540affd76c9102a05ffabb4c0815027ff5db4628a815ffaed93145409ffd76d10a2a057febb64851502ffd5da6028a813ffaeda808540d7fd76d4042a057febb660215027ff5db4a10a81bdfaeda508540affd76ca842a05fbebb550215027ff5db4610a81bf7aeda308540affd76c9842a05ffabb4c0215033fec0d54982819ff546aa4c140cffa4355260a067fda8aa9205033fed1d5490281dfe4c2aa48140cffb0755240a067fd53aa9205033fec0d54902819ff4c6aa48140cffb0755220a067fd82aa9105033fea9554882819ff4caaa44140dfbb4319904a077dd918cc82503fcea0c66412819ff6a61120940dfeb4308904a077f59184482503fdaa0c2241281bfd6961120940efeb2b08904a07fb554844825037fad1c2241281ffc4c21120940dbfb4b3b902a075fd959dc81503edeaa4ee40a81b7f68e7720540ebfb273b902a06dfda29dc81503afec94ee40a81f7e4c27720540cffb532a902a06dfda7954815037bed2caa40a81ddf6565520540df7b492a902a07f3d54) else (if i<3 then 0x1708dd645a9bbf639432820d3c6940b5642b80db77ec72865041a78d2ae2db6bbf6a58d28610c8194120200b40110a197092590ae2efda950ca0834f1a4804590ae2d4869bbf63833286504c697c690cd001a029be86680126fb0043340088650930ea0049bec391090025dfb8b6a6db21ce314614308650420800d00442865e3da94dc5b6d6384302ee3481914a6efdb6b1c2181771a40b8a5377ee2d8e10c0bb8d2094ddfb8b6d90cd8e10c0bb8d25010a94334008072efdc5b536d98d28610c8194120200b40110a1978a9600866801049529bbf716db08605dc6914a6efdc5b6d63815a86504c6928678d5001a0295286680110ca1261d400880a54a19a004952c39109002219e35400680a47219a004e34866800d0148e433400923980219a00461d8004cd9816001912c00268a44b000d8160017366538007cd9876001f3660d8006561a2d36c0042254db000d87600134560d80060b7000889600135f66d8006ca70009836001600095868a41b001084b36c00368a427000c84e001109c002213800442700083782e02d57fa2f36e53c6387606e0580180900cc040cd08baff45e6dca78c50ee0d80b003806409ebfd179b729e31c3a83602c00b09737e5c71ae1dc1b8c7009042094182644b8e35c3a43406e31c0241082582d9912e38d70e90d01b8c7009042096046644b890dc6b8c70090420920181120000040de0330335fe8bcdb94f18e1dc0b002c06606ebfd179b729e30c3b816005008c0dd7fa2f36e53c6387302c00ae8a0200760640dc610000047450188100471860480000239b00400dc630120000076349151b229e3081b80221b05401487103700442a0a80198d70640088541500321ce3081b80221505400e92694adf571c6b87706e31c01415005a1c635c1900221505400e926872df571c6b8c700505401287380221505400a126832df571c6b87718e00a0a80298d200442a0a80150e31a43283941500331a400885415002a1c40dc0110a82a00659157d5c71ae1ca1b8c70050540148deafac8e35c3943206e31c01415005d5f590ae38d70e50c81b8c7005054016c6903200442a0a801aafac8571c6943718e00a0a8026afac8570c6902218e1ca1903282200b439c6103700442a0a801e94ac8571c6b8728640dc6380282a00b5914a55c71ae1ca1b8c70050540148de94ac8e35c3943206e31c01415005a1c63481900221505400f4a5642b8e34a1b8c70050540134a5642b8635c638728640ca08802a872c8570a1b8d718e00a0a80256450e570a1b8d718e00a0a80251bd0e590a1b8d718e00a0a8026872c8570a1b8d718e00a0a80250e50e590ae18d204430a1903282200be8a5179b136253c608c102c00922457f9b718a1dd17001fa2b0620d40881736c00705a57fa2d29253cdb001fa2945253c608c73620d8 else (if i<4 then 0xf8c516c2384302ee34826415f5c11a05448405805003a0940c80ce8218220afae01771803219802801d04a9be32e5c0a911223803c820d3c69407b6f852d700b80601902c02c03805003a09b0848008088df18a2d80f8250482180b482a41c6981c76aeb8245c608d00f01601400e8258df1972e25488911c01e4171a481e0e214b5c6a90180640b00b00e01400e826c2120029902a47b08e90d20834f1a44c87523d9c74869041a78d203391a0c9b235c02e243a1802801d04b03237c628b611c2181771a402d7bef15db38e10c0bb8d20996c8d7046815121d0c01400e825032033a08637c628b615209641092e3487bef15db3a904b2084971a40220cdb235c02ee300640a00fd0c01400e82682284240061802ff4568b11594c2960d08a03302005cdb07600801005bcda117454000ba001c04b5f8beca611429821c620c30600dcd981002e8b83b00400905f68acd994b1861c02003805003001603813b1801001c0280180080100af8c000026014c03c040010c4d7c2ff4588aca614f1861c03b9b60601ac0a01600801401e020008316be1be2ff3686cca414f1861c03ba2e0601ac0a0160080150101802fb4588bcd994c296310618740e01b001c0200881601dcd806c0038620bfd15a2c456530a78c00ee6cc1a02406c0480b0040088610bfd1594c29e30c620c30e81d01003736c05802004017b5f8bfcd99b436053c618c41861d03a02006e8b80b0040090126bf17f9b33686cca61480ee8b01003718c0580200410ca09a00343281a800d80219a00303c07e8c20eb1c81843002432015486404d001a1940d4006c010cd001a194354006865035001b004334006865095001b0e44240068690cd001a0298a866801262b0043340088650d5001a0298a86680110ca09a0034053150cd0024c561c88480106fdc54396da8c206b536194108200340110a1970cba5237edb58eb0c0bb8d210d219a003404866800c0e0dfb8b6d98d5a9b0dc194120200b40110a19730043340069278d5001a0249286680110ca1aa003432826800d01219a00361c884800d24f1aa0034049250cd00221a43340068090cd001b00433400686504d001a02433400637ee2db643961ad480650420800d00442865ab7d5c0d9b1d61941069e3481bf716db586b52c6a8328240401680221432d432026800d01219a003093c6a800d0104943340088690cd001a024334006c010cd001a1902b40068090cd001b0e442400686504d001a02433400777ee2a1cb6cc6854a0eb0d6380328210400680219791abbf716db586152a0802d00442a432026800d01219a00343286a800d01219a0034320558750022194054006c39109001dc5b6c872efda950c2194108200340110a196864432b215c5a93bf639432820d3c6968086fa19a004590ae2d4ddfb1ca1941069e349 else 0x4908810f1800805383502c0004400aeaff45e6c0af94f18027c383380700a18400b404745e6c0af94f18027c383380700a18400b413823e314380800700a04800a41202301501008003022005009011f1800802b8301000604400aa6fcc817807c47089e347039b201e87124203400e864019304284240040640f84916c23843057e348096325db38e70c15f8d1f6feb805c484a4805003a0900640)))
def qL34 : PackingT:=(230,4,7,15,qL34F)
def qH0_34F (i : Nat) : Nat:=0x381c02ecfc00320027059f60dc8069db33901b480de70000046ec19f40c15465e0009000780e35065b035e459c80c63464f0364c1c3e0015a62d1307c98d00e2406438010919b00c2766bc0357c18f60d2008d8046d018a00d030670046ec988011b6068b833481b6e0c3206fc836241ba40089064d001d018100bf50028046c419840c4806b6a3840236011bd06531b0c023740d4b26103241000522000091a1c78100080011e28080
def qH0_34 (h : Nat) : Option (Nat × Nat):=lookupWord 21 71 7 17 9 4 qH0_34F h
def qH1_34F (i : Nat) : Nat:=0x4b37b014c837703200def3140063806380638063e85ac004303c0063eb3e400c701b705b485d38ba380b0063f81c784e50523024600180638063d88358448063e84a0063f0178063b029806380638807082b00638063e812d05ed8817840203f302be02e4055c3abab13f042284a8059f04fa83d982fa05da03ce84ea01a808592ded018904b92366022800030364845782d504600638063a813684880638063e8278063806380639b3f103fb002c854080d006380638063b25e083000638063e01b8063f00d9851c05080639825704b2024f02a00638063a0468063a80b806380638001105308258063f80e501db0050063800f2005903af25de55d8063d00ce31288397810184c2013c81cc03b381e6800e831f857584f5820ab39d040a080ca347803903d1819785cb845d233e02c6007f030e0160063c8218815a33af808b05e7806b82ea02838353057d85a701e80638063833fe039806380639b1500550063a05b806380638063904d006380638834b80480638063e036f032f0064d5e2010b82ae8097043803a700a2054a811d828d8b8b83e0b14d015403ec814680ee01f584718510063c856a037c027483310380063f8261338d859381d188428429018482f4035905650430817102228020063c816d01a0063b85c0853b0584829480f8833f04c8063f019d8032026904790412008006380638063b84188237933500a8063b2368063b82c8852803bc81fb02148238063802dc049f8bb484df050781208490063b8204831205890389b4a00485809e0342044081102c1800040283e01080bc0002030280a000200006050380402010181c06010201016010082008000280800000082c32110000c02020301006040200c34090001018060280002000300000010680c020d05848160a
def qH1_34 (h : Nat) : Option (Nat × Nat):=lookupWord 75 285 9 16 8 4 qH1_34F h
def qL35F (i : Nat) : Nat:=(if i<3 then (if i<1 then 0x148815033fed48a440a817bf6d85220540df7b4829102a04ffdba4c881502bfedca6440a81b7f69d3220540dfbb4699102a06feda24c8815037fcdd26040a81bfe69d3020540dff34a98102a07fb9544c081503feca9a6040a81bfe6893020540eff32498102a067fdb968c515033fedcb4428a819ff64da214540cffb50c90a2a067fda3648515033fed132428a813ff6e98214540affb72c10a2a067fda9608515037ded230428a81bfb68982145409ffb74410a2a057fdb9208515033fed490428a81bef69082145409ffb74990a2a057fdb94c8515037eed1a6428a81bfe6e93014540dff344980a2a077f9924c0515033fedcb5010a81aff6d5a808540d7f96ad4042a06bfdb36a0215033fed433010a819ff6e5a508540cffb30d2842a06fbdb4694215037bedc34a10a81bdf2e1a508540defb66d2842a067fda8654215033fed2b2a10a813ff6e98508540affb72c2842a067fda9614215035fed430a10a81b7f69d8508540ddfb4cc2842a06f7da5614215027fedd10a10a819ff6a48508540bdfb6c42842a06efda621421502ff6d910a10a817fd6c48508540df7b0ad2042a06fbc85690215037ded42a810a81def6615408540df7b4aaa042a067fdb968c215033fecc34610a819ff655a308540df7aa8d1842a06ff9b068c215037eedc34610a81bf72e1a308540dfbb6ad1842a06fdcb568c215037eec2b4610a81bf7215a308540cffb4ac9842a04ffdba60c215035fed430610a81b7f69d8308540ddfb4cc1842a06f7da560c215037eed1b0610a813ff6e95308540affb72a9842a06bfda854c215036fed3aa610a81bbf6995308540defb4aa9842a07f3d5454c215037eed1aa610a81bfe615a008540dff10ad0042a06ff983680215037fca9b4010a81bfe6e93008540dff35098042a077f9984c0215037fcd2a6010a81fee5513008540ffb2a698042a047fcba54d205023fe5d262902819fe6a13048140efb2a698240a077e9524c120503bec98a60902811ff6e983441408ffb74c1220a047fdba4c9105033fcd1a4088281dfa5492044140efe2a290220a065fda7654815036ded3aa840a8197f69d9320540cbfb4ec9102a06df9a74c0815037ecd1a6040a81bf668d3014540c7fb72d4042a063fda8660215032fecc34e10a819bf661a608540cefb72d2842a0677d986942150379eda34a10a818ff6a19508540cbfb4eca842a066fda6654215033bed2b2a10a81aef6a15408540db7b4eaa042a06ebda65502150379ed2aa810a819f76e5a308540cfbb30d1842a067dd9568c215037ceaa34610a81bf66c1a308540cdfb4cc9842a0677da564c215033fccc34010a819fe655a008540df72a8d0042a067f993680215027fcdd26010a81afe6a13008540dbf34e98042a06ef9a64c0215037bcd2a6010a81bf668d3008540 else (if i<2 then 0x5612ab0953829a5524ea329436a8104f7c9ddd39826de4d0298652e9258b4a8893f5250242247068c6d16a228d443486c90aaa119418e81d50119fdc3f2a7d38f6d9e683c00768cea31cde39027090dde1b5435ee6a10d1399ca32f06498c6a18612ff25e9cba516e22d2058ccaeb156e29ca51c89fa137625f04a149039194225842b88128fb21e943ad87168dd01aba342c64c0c25177a2d5457c0a85146627004a688da10fa20543d687450de61a2c30c05a50a9013ac23c040507240c50150822e03a205d008b80ba00ba00033fed4342982819ff695a14c140cffb44d0a60a057fdba605305033fed8b50902819ff6a1a348140cffb4ad1a40a057fdba54d205033fed4342902819ff68da148140cffb74c0a40a057fdba605205039fed4302902815ff6e93148140affb6a98a40a077f9b04c520503bfcdc26090281dfe6a13048140eff36a98240a077f9a54c120503bfcd8a6090281dfe6853048140eff30298240a077f9514c1205033fed4346882819ff6e1a344140cffb6ad1a20a067fdb268d10502bfedd306882819ff6a1a244140cffb4ad1220a067fda3689105033fedc344882819ff6cda244140cffb74c1220a057fdba609105033fed2b04882819ff68d8244140cffb74a9220a057fdba549105033fed1aa488281dfb6095244140affb7499220a057fdb54c9105033fed2a6488281dfe6e12044140eff35090220a077f9b548110503bfcd2a4088281dfe6152044140eff36690220a077f9a348110503bfcc1a4088281dfe54d2044140cffb72d0904a067fda5644825033fed1b22412819ff68591209409ffb74a8904a057fdb9544825033fed4aa241281bfd6855120940bf7b6aa0904a06fbda5504825037ded1a8241281bef68541209409ffb7498904a06fdda34c4825037fad0a6241281fed5053120940dff37498104a06ff9a14c082503fdca0a6041281ff64c53020940dbfb6ad3902a06dfcb569c815036fed9b4e40a81b7f6c9a720540dbf964d3902a067fdb9694815033fecbb4a40a81bef6d1a520540cffb4eca902a067fda565481502bfedcaea40a819ff6a57520540df7aead2102a06fbda755081503bdecbaa840a81bef6955420540cffb2ed1902a067fd9568c815037deaa34640a819ff69d93205409ffb74b9902a057fdb95cc815036fed3ae640a81d7f65d73205409ffb74a9902a06dfda754c815037bed2aa640a81fcf5515320540dfbb46a9902a067fdb9688815033fecbb4440a819ff655a220540df7aa8d1102a067fd93688815033fed3b2440a819ff6959220540ef7aa8c9102a067fda3648815033fed132440a815ff6e57220540cffb52b9102a06fbda45c8815027fedd2a440a815ff6e55220540cffb52a9102a06dfda7548815037bed2aa440a81bef6915220540dfdb44a9102a04ffdba else 0xd701a41082ee31a1b41201b86ee8bcda94f18a1c033002424837011d7fa2f36e53c6287606a0580180b800b5fe8bcdb94f18a1d81b8128188080280afaff45e6cca78c606e04b05e0ae11013ebfd179b329e3143b812c0880801a017aff45e6dca78c606604b00357fa2f36e53c6287706c0580141bc00d5fe8bcdb94f18e1d41b016005801ebfd179b729e3143a83602c00a003d7fa2f36e53c6187506c04905e0ac05c04ebfd179b329e31c3b012c1682b0140300275fe8bcd994f18e1d41994c82586b00ab7d5c7201b2a0a8d2a9906da32b7d5c5201b2a0a8d242484ba521ee830575beae0175200cca0a8d346584ba5343864adf5700b80b586505469815e8d2df5700ba9006950480ae1a28d2dff8aae0177180d2a0954696aab8553c6034a823b290de192644b805dc8243482634aa521bc322c85700bb902865054694ca6643df9700bb90486904c692ca65c3df9900bb90486904c692d7c35cc8971c8243482634805a1c8173df9912e390486904c6941b6644b864121a4131a3d320c0015642b8b53c8143282a34aa6557d640055716a79028650546954caafab800ab22d4f2050ca0a8d2aaf86b590ae39028650546914ca8cac85716a69028650546934c9645195716a69028650546934c95c5195916a69028650546921b5642b8a40a194151a3b5f65218e644b805d21a4131a4811652095efcc89700ba43482634a022cc9af8259912e1d4c86904c694cc812cc8970ea64348263486341a6644b805dc6243482455fa52ae0332c805d48143282a34a05b57c17066590ae2902865054694ca40e3df9912e015f18e4121a41289935f002072644b8753c6390486904b264c640e11a9912e1d4b2090d2094d7d9481c0cd3225c02b64121a412a8d069590ae015d2050ca0901a68d2c85700ba90286504859146834ab805d4814328242b8a341a56402ea40a1941201751a0d2b215c52050ca09146834ac85700bb8c2865048d669aa834fb698ed263a24b3f9e78bce479aef32f65f6cb75954b27ae4c4c8cf8fd31c66319c563897f0f0e19ac1e1824f01b5fd9bef97c26f5bde44bbe57682ea1dce6b84d6f26dab5af9b48966eecaf589eaf915ddab81d6a6ac93572eabcd506a92750569d6d33aa5bb4a02911d1c6a32b450e878d0aaa0b140467dfcf6d9e4d3b7e74c4e3b9be936326b34d09996f316a609cbab96b32ca256b4a4d93f726d24b6c93c91d522e642e47e98f2f1d16379c6968c8917ca2cac53889e3127e22c43f087270a72109c1ab82870342039c00b7f46fcedf69be6b7c06f641ea4bd027960f14de00bbba76a4ec2dd4c3a1a7364e4fdc7138907092e009bd837696e44db6db39b6216b72d411a48b429676ccd3996db268642cc7118beb1206170c199804af965e88bbf573fae0c5b5eb57568b2cb95876af4d5c62b5b)) else (if i<4 then 0xced7da2b36052c3844c82e0001d2064110096bf37f8c41801e238039069ab2e24140000b00320796aab8a1c02d4100200a1c54046af829242438292b800a059357ea2d36112aa4c328240004c03a80c8645aaaa447007570a0b8d2432052d700a48c90e02c01c02e82521c5aa0195c2a9442a0800d00432a5aaae154a8200b401109c0386c5aaae154a82e3470327205b871113c68c77ce46b8052484c3005d0484397215c2a9442a0800a19b0c9b90ae154a8200a886c31c0c8df570b5403a82a41c69006438852d700a78c00f00e017412807ad5570aa405a82e347048aa78c286504004c0400081a5bf48047718026b555c282590e00214b5c21902daa78c013d04af8bedb8c06c90d20b8006440649912e1c7486905c68f3225c48605cea78d18324c87532e243482641c690b16a2ab6a6c86036006504800321df5b5f68acd816f2090d20b8002a482d2520643948605c6635c381702c24c8970e3a434820e5c68f3225c48605c0b78d1a5c4c890d20990072e3470320c8325322beb23e2ab8f6c0aad4f180cdc814328200bc024a0816932430a3a87006004800151a95819590ae0472865041cb8d20326c8d700a89080600ba090071642b850ca098d2210e280c8b215c58e50ca0b8d1d642b8b1ca194171a32c857163943282e346590ae2c72865041cb8d1d640b71040645482e05bc690871642b850ca0800a214336a522dcefec805da0b8d185bac850c0bad4f1a31df591ae017682e3463bfb215c02e505c68d3225c48690546a1087183289912e28d48680d20a01005842ea60cac0cd19a641b1647c5571ed8165a9a40a194151a71290d9b235c02e23481490e824a82035c381702c352604824a43482e0003cc064088646521ca644b890c09690280c8116be0aa644b890c0969025804120593225c48604a481009434f18904248b3225c3a990d20834f1a3cc897009490482125c68ef7e644b890d20834f1a3cc897009641092e3461253225c486905c68d3225c48605cea78d180c822abe4a5642b8e300514302e50190c8b20390a9570a1941520e34a0c8051645a9570a1941520e349590052d4ab850ca0a9071a40145916a55c2865054838d20168145901c95c2865054838d25642b80e56a5432820d3c6900655c2c850ca0a90072e3480cdb235c02a03203c03005d0491ec1bc0a2b8590a1941520e34902977d5c2c850ca0a9071a40b71708dc0a5df590a1941520e34a570865642865054803971a402c243ae364686240c6b4122efac8570a1941069e3478393225c38e90d20a8d1e644b805721a413a9a347002012643a96400525c4869054694f7e5c41c6400526448690546920909102be30a19410013a19a3143802ac8570a0834a0326c8d708669002ee300174125642b84334838c28605c7433b235c31905c4834368246c8 else (if i<5 then 0xe8bcd98750620cca78c6025b5f68acd815f18c04004ed7da2b3600841815f1801580800a804001009d1594b0ee6d41b8c6025008002011aff3661dd1683329e31809617da2b36652c3844c86e0000d20640e2c85e94394300601400438aa94ac85e8018050014d04850a188e089a1c608032000068032b217a0720582380ff1a405fd900f41512100202b43200f04444207c8b217a0720da07d4371a3900d900f41612101ba18eb217a28601b468389890ac85e8a1806d1a0d075be6e38700d018224c065640a95e94800ff1a380f590bd00f80d50dc68eb200faf450d4838d1890ec807a48006e863027057c614300500260200040d2a9590bd29001f46c8de848c9000dd0c620001410ec8de807f8c00dd0c90ae3278d0e5c0d91962bce282e753c69137e5c0d9904c8064f1a3cdf970e383d8d99043278d20644b838a15dc371a305f68acd98730605b20b8002a482d0bf2e00cb0e2b20b8ec6b8702e058406417e9b50e1b215de29c16932353c614750e50d419410024000a9817f5c02a24252402e823872504c6910a19baa60e520a8d4217ab064dc386c85778a4253ae090959234817411e8d70e05c0b080442fc8e092ca65c30604a80320442fc8e68a3665c06b60c0954c000d48e1b32e0368253822092ae38c07b0aef14eb7d5c0d950548064f1a385fd700b80c80f29201741216fab81b2a0a900c9e347d7086690159292c6b411c0c8c5570219415200e5c69032d5c0d9b0ca0a90072e34857086439282a41c68c0b35c6df2424818d682380f1b2ae039282e3460bed159b32911320b8001300e90bfc61874b82b2014a48cb40190640266fc86292d146ccc5153c620c06661d238039069701ae4140000b60640666f8d998a56454c8e9701b64131a60190121ed94f1897120802866481e0be3255c7180ae014293c5481e55217c64d455700668700b05ca01815f5c02e23501490e8240110be326a2d29242ae002816485fa8b4da9488950480009807485f093ae01711902c01c02e824adf570870392820028850cdc84adf5701c98d28200a886e4219481918a5655c08e00ea083971a485f28a14b5c02a03205803805d04a039716db0824421c8cae0392df5043678d18acab80e402d6fa82e34740046ae2db61048843921940071b25655c072505c68e7205b81905c2278d196fdc857087141001442866c3245b9c830c0bb4171a32dfb90ae18d28240401510d86432a032b7c648c55701c8548075054838d2c2f852d700b80c80f00e017412465ab80e56a46480b5bea0a9071a500f192ae03900b5bea0b8d2003adf5701c941520e3470480af8c286504004cb7d5c520e3015de299548575708669071805c7a1c15f5c02e243a08c15f5c02105c1a741190cd18a1cae141069310e0a5ae10c81605dc6009e824824a41c600a482e0003 else 0x5022bed16a2b36a6cca69480f60d41881718002ea04d7eafb45a8acda9b12960d41881718002da04d7eafb45a8acda9b329a5203c83102e3180000bca293625288b8c00fe0d40800a7a2f36e53c63870076040051438afb45a8acda9b329a52c628c10e00e01400ba8735fabed16a2b36a6c4a58c51821c01c02801775fe8bcda94f18a1c01c028014b4566cca58c30e01801e810014b5f68acd994b1801801e810014f45e6dca78c70ec0d80001a0a29362524608700c00f40800a40400ba040340294af94526c4a48c00c00f40800a40415fe6cca78c745a1c03500440a0160144044d159b606057c600280144066bfd179b10e057c6009805002ac0cd7da2b3640cca78c005002980cd7da2b3621cca78c01300a0054d7da2b3604581815f18604005203015f18026c0a000013810010015aff4565381b8c736a1cc097cda87606e31d14171a8715f68b5159b5366534a58c51821cc1a83003002f6bfd179b729e31c1801801475fe8bcd994f18e0c00c00a3aff45e6dca78c30600600505149b129230419020030028a0cd159b329630c3806106006005541816b1861c030830013d066bed159b32963003083003002a68acd994b1861c030009dafb4566cca58c00c0027e8bcdb94f1802780b00007414526c4a48c10e40800c00a00080705b57fa2f18a301990750ea0c01b9b329c05802004430f45453cdb01718c00199097cac745e6c0ab8c013c0580003a8af94526c4608720400600500040382405e97eaff36a6d4a414b0ee8b80b8c506c0100c201c17b5f4bfd1707529c05c6300736615f28a4d89491840800c00a0038010b4010afe5fa1d03ba2e02004ca78c600001cda83440080705a0492fd5fe6d4d994929a1c03ba2d0600dc6301600801368acd98702be31808009da2b3661c4180202be3002b01001535f68acd987329e3180800a016b0e20cca78c00ac04005002000804)))
def qL35 : PackingT:=(278,4,7,15,qL35F)
def qH0_35F (i : Nat) : Nat:=0x140b800b3cb8c0933c02364098c003701194086011b008d8046c0236011b70850046d4010011b008da0ab8d62bc0da30828046f41e0eaccb032d01a1c03c011b008de2220c0cf0095f0105b142c13960942048c82080236011b504528354817cc0a7008de01580236011b901c181ba405d20a640802806e013a203a0016302d002360022008db020e4048608f008d881814099400560288046c0236011b100c402958066a085008df00c181f080e280878046e815d6097008dc818b00ff2104106978220023680ada03b0046c298d80d63021703d40237a115900d400dc415840eea02cb8306014720418259302a00236804ba1566dadb00b116c0b009981dd016d60f340584a21e41cca0a4300af09d202268064b443401f6403e001dd03330281407c2306c467580e7c064004ed0204840d81b6c08e4002482304176200ef0146805d41eda2523050f03a70004ec7fe015f008401cae02a201b281bf00da00702765c00d28172ee99606ef012ac1f9202f4089501edc09ba0b190061843b413c60f7b042509d9007b405f30308046c0236011b4035180640236011b604d8046c0236011b0157f04300236011be049c81c901ff811a008df82180236c107c040981500237a109008dc834f801e011b008da00480236011b0a59954540236011bd00a0046f41af20af008dd842dd901000b20318046c0237e078e00e0046c023740fd008de037299da011b9073f00f1400380b5001ab83c80237c0031024380ff4a2feeb7008df83d1c1650027c004fcae280d82029c07d403a1c1f3010de06a2016f408a02b0c02e882430092e07ca03ca001c023620ed5023e80c7d5c6ecc2008dc017ac01b608d20050046c0236011b800b783448022011bc04d0046f41fcc1086035e81a781f6011ba0284845d89c1808b108c803ab8124610226278046c0236c106c0220046c023662aaf155c00b580208312a0404008d0223a0994154982ad40e720896062604075564a0538054800948221a0aa008db03b002372116008d8046dc1df809f00788046dc4afd2b59027e00ec0237c075008df0364410ec026a07268288c000011b00758046f44ef80715870e01680237c1148156d04600a020001004000300c36150100004001401c000b0a8080805000102205000040e0103800020a1580402000101000000281020010a00000210080000080d02c1610078101e00028240c11000280c00058103e0b1300460030281804180280c0200000040808020880000000000005
def qH0_35 (h : Nat) : Option (Nat × Nat):=lookupWord 98 376 9 17 9 4 qH0_35F h
def qH1_35F (i : Nat) : Nat:=0x9068220b366aa0477b0c302ca032a09c00c75080a065104430198037c038d09e109fc073307ca09060104809404d2060d0ac00c7306b006ad012207f1a0dea05b0204039f088660750aa6033806c8089401f80b26a0b715400c7604a80c190b090988069f09a90a3f00e6a08d80250247079e048103cd04500c7a091e0921081a03df46fb066d06300c4e07ee62700c7101a60a14061d0131014947100722058901610be3096e0432083601ba0b3707ab07b002e807010c320b570285099e0498021480320515085c08b008caa09005a680190502403a04bb071c08d002f4030d08240bf10a5109bc08af0c0006260ae9017d018962a8022c02320a22056e059c034c0a8905c109530a9704e9046776c00c7909360a720c570bbb0403a02501cd0848094004190369805a04c50156052d806e09de0a4f2676097d05e7604708f705b1800e03e60c280b100542026e206501d901eb601b0558035e08eb00f704f505da01110579067405fd62980ad7b0760a0d03fb0779025403a803b375700c7407860b4802be087302db0426053f03150c6e20a001740070f1704076b2a06090e0e4d131602053c007309120012004e2f050b00050207070d550d0317005003030017001414010003110200041030000102050000
def qH1_35 (h : Nat) : Option (Nat × Nat):=lookupWord 65 202 8 16 8 4 qH1_35F h
def qH2_35F (i : Nat) : Nat:=0x8085203eb14f1017604c8011962a005e9087d62c8040202421214092a15320016000c01d4294106c8495b055c1391074b07ed08ed498105f009c6019e01a1045508480685006402ae093f02e009c4037502b7300009cf08f9070d15b009c962e7010e03dd04f40238003e02f800fd11f009c303fa09a36989004c07850435156762be0165056b060c0822099f399c0791054d0089033806af994009cf02c604d009c7094603a009c009c009c009c8152a020009c908d607b009c009c009ca04a009c009c009c009c9069009c7039009c3005c05b009c009c009c606681227046009cd072f01be0485494b0624044800a815ad047b07ce08a4499009c009c009ca096906f009c009cd076009c009c305c009c1058c097a897009c7075009c009c009c90157034801e20251032404e009cd022b07d009ce065f798009c009c4083200980497138c0120064009c609bc05a009c009c009cd013009c80533028407a009cf293306ed01cf091d041009c009ce038469b407f009cf05d300e700cc0511697808ba07334932080b050e11e8018702670357036d296009c6172b007009c0095600b304ba042009c3081a0307014506d009cb0294196d03b21365071008c30909067c62dc03c8057e088a19a6052009c161a9619b0023098377b439630594021d0636077000d808910279086d01f4031102de061606b03010400040b0c0e06051009051d02130f0900030010001f0000000105030a0a000f1f100501041304020201110b0000000b0c040b023a130004081b020601000001
def qH2_35 (h : Nat) : Option (Nat × Nat):=lookupWord 66 252 8 16 8 4 qH2_35F h
def qL37F (i : Nat) : Nat:=0x16fd90dc03ec730543634837dd5ae18e6182ea0b1a45bee4570d4b1cc30d341634977dc8ae2a963986a0b1a45915c352393bec750c34d058d28a94a5dfb22b8638860ba82c69403019afe8b9b6538c61d81400a43821b22f4b7f1ac6300a190055917a5bf436358c600c1200931545ae2dfc6b18c0282401254a535c5bf8d6318050480250eae021b7f1ac6300a0900490c835716fe358c60141200943ad5ae021aa71ac6300a0900510c835ab5c5538d631805048028df57ec8ae286c6b18c0282401454a5364571436358c60141200a43ac8ae021a1b1ac6300a09005045076bfa2e6d94e318360500280881b5fd1736ca718c3b02801402405afe8b9b6538c61d83400aca529c395fd1736c6106c0a005224afe53a2e6d8c21c83605002b294a70e57f45c6306cd902801416abf8766c94e318368a81400ad7d5fca745cd90ec1b1840a005212afe538c61d9b20da2a05002a91a7c664a4f63521ae009e65ce9b6d9f18756f95553b120d068ec4d20b7c9d88346904ec3481a4003ffe1120940fff95481503ffe2220540fff88851503ffe8808540fff954215037feaa48140ff78cc82503ff61120940f7f9dc81503f7e5520540ff78cc81503fee2220540ff78cc51503fee2214540effa2021503f7e5508540ff78cc215027feaa4c1409ffaa9205027feaa44140dfe60a005037f93280140dfe606005037f95180140dfe4c6005037f92180140
def qL37 : PackingT:=(27,3,7,12,qL37F)
def qH0_37F (i : Nat) : Nat:=0x180504028804900540211581a4032804002100210401d400c021002100213803e004c02138059c0460024400ac0138000c03b0004c019002e8037d059c01700200044080044000
def qH0_37 (h : Nat) : Option (Nat × Nat):=lookupWord 9 32 6 16 8 4 qH0_37F h
def qH1_37F (i : Nat) : Nat:=(if i<1 then 0x8538073505a80730073505900730073007370490073125e28160073007300730073700d00730073007320132004103bf006681520570073007368df807300730073007300730073007300732831807300730073180c0073007300730073400b807300730073484af03e80730073007308d9900e7051f83d007368e0a02ac02b007338112004e8036834605e3803c0190073007300737807807338bf00735856007300730073385b00730073007300730030182e807300730073688200730073604460100073505468260005882fd32c807300730073007300730073084db05cf84580730073007300730073007300730073403d80730073284b7a5c6806f0d90073007300730033202800730073007328328073480180735054983f5360007358853016b89d7014f83598844055e84d1839007300730073585d0073105d807300734824500ef25dc83880730073007340448073007300734010f80880730073007338200073004680731850807300730073007358818073007300734a1800733013807300730073004180730073007300733018e03f8073007300731116007300730073280d8073381f0073400c8073007300730805007300730073780b00734029d82380735002504ca859802c007300730b192a168073481180730073007300730073007300733836807300730073007360477857807378510073007360159b3b0073280fa020c827a02680736029601780730073688580730073082e00736843d8210073007368a3984f2047b852f030e04a0073007300730073007300735837903ac884807300730073783c80730073604b8073680980731825c01f807300730073007300730073007300736032485f1024f89968129834807368464217007300737840007350a0781d58a8d8228073301dd04e1018101e8073007300730073007300730073007378410073007350a280730073680000733008007308498073525e807300730073602d0073007300730073509d807368255800b0028073007300730073007318bf8073304ee84200731017007300730073404c0073007340010073007300730073482cd02f1838007300730073007300732014282a0073402b8073007300730073007300730073305000730073007300730073007340220073007348428073007300730073785e80733052085c007300735843102d8073007300730073704570310073080f2bc0c058f03738120836007300731033d83b00730073480a90d8805a007300732053084858218073301e1823785b80730073415b1056e39900734028807300000060080000000000000000200408020001008010000c00000080000000080000000080810010000000000000800000000000030102000010000406030080404000201c0001000000002000000000000000000 else 0x38075855515a0073103e00733840d05fa860807300730073683a0073007328580073004f9039807370a080736827706000737835183c30090073180a6048f)
def qH1_37 (h : Nat) : Option (Nat × Nat):=lookupWord 75 501 9 16 8 4 qH1_37F h
def qL38F (i : Nat) : Nat:=(if i<1 then 0x9041634b1252906559b7dc5ae02ec81c8a091a6032430e4169bfe2970d4e4041634b065324186b016dff16b86a720a091a6032990da8cdbfe2d70d4a4141234b0646837fc52e12020b1a42522b832830f76ff8b5c05c900cd41234d064cb2a5c8224dff14b8c818620b1a62522b832870a56ff8b5c05c0b30d41234d15c2146adff16b80b9201a68250326f90c121aa5c152901058d281957d2241871b56b8aa520a091a58326f9126a97054e40c31058d295f0650e1c6d5ae2a905986a091a58429100a8d5ab5c552905049064a93d9df320b8c808620b1a52520cbbf6457017641435048d28df06472320b86a72021882c694992be0c80b64570d4e41435048d2c194c919b22b86a520a1a8246940c9be54924641709010c41634a57d2906466b22b80b920a1a82469610a3434d915c05c9050d41255fd1736ca718c3a06c0a004845afe8b9b6538c21d036049d7f45cdb29c610ec1a028012066bfa2e6d94e318720d01400a03004d7f45cdb29c630e41a025052011907a0424323470700637fc52e0212091a40926f971901058d18dff14b808482468c0e00c6a97054842412348354b82a4212091a3038641701090c412347320b8c808620b1a31905c640431058d18b83232021882c68c641719010c416346320b8084862091a31905c10c4163450711a320b8c63202188247583a17ccae21efbb747b44d7cea434779facd2e56b20b8a6c1edf02e876c6b29d782aef4faa39d002707310949c85a33314e872c1f203afc87aabb61ccade86bab481932c1c5caacb1586a504f3a5d122a8ac4219f68ece6fe34a9888b86564282929887a3d41c48cd05e62b212e88703a21900a7843819a08c02a8003ffd5120940fff4c482503ffd7520540fff5cc81503ffd5320540fff5c881503ffd5220540fff14881503ffd3220540fff60851503ffc8214540fff4c851503ffd8508540fff21421503ffd8308540fff54c215037fda14c140dff605305037fda848140dff68d205037fd5348140dff685205037fd8148140dff4c5205037fda344140dff60d105037fda244140dff609105037fd5244140dff4c910502ffda320940bff684825037fd9120940fef50482503ff93020940bff69c815037fd9720540bff694815037fd9520540fef55081502ffda320540dff64c81502ffda220540dff64881503ff93020540bff68c515037fd9314540bff688515037fd9214540ffe4c051502ffda808540dff66021502ffda508540dff65421503fbd5408540bff68c215037fd9308540ffe4c0215027fda848140dfe4c1205027fda3441409ff689105037f920441409ff6a4825027fda920540b7f69c81502fbda4205409ff6a451502fbda4145409ff6a421502bfda808540b7f69c21502efda608540bdf69421502fbda408540bf768c21502ff9a008540 else 0xb22f41c86d6381fa1b1a4043643537a2400fd0d8d22b81c85775682c68c6488f6fd7039352e2842c30a4905058d35c5ae021619201ca82c6916fd70390f6e45058d1dc536559ae18e02c72a0b1a4dbee45701730d416347716b81c9a90840bb7d20a0b1a50d96ab1c05d7154d058d21c8ae07161a82c68cefd7010daa05a41416348b2072ae18ea1a82c68eefd915c50c17353416348052c86a421ae28648282c6920a3bf5c0e410d914324141634a1980108b5fd1736ca71883b0640a006044bb444afe8b9b6538c41d8320500302e0580157f45cdb29c630e81b02801817003afe8b9b6538c21d03605002c310235fd17364a71843a06c0a005819afe8b9b6538c61d032050028760340c57f45cdb29c630e8190280180882c06819afe8b9b6538c21d032050034010135fd1736ca71843b0680a005808b1408afe8b9b6538c21d8340500300c0135fd1736ca718c390680a0058c202408afe8b9b6538c61c8340500300456204d7f45cd929c630e41a02801802225026bfa2e6d94e308720d01400c06468320f448086c68e0c9520f912641e99010cc1634a0652902ac8bd071c82866091a503206d917a0e29050cc12349084694891ab22f44828640926c9926fb8a5c3ab903)
def qL38 : PackingT:=(77,3,7,13,qL38F)
def qH0_38F (i : Nat) : Nat:=0x9b0128005641b802100213001c4074021002120174021181640212808802100211010781c80210021002100210021201ec0212418000ed0444021002114170021002100212c1340210e9d402100210021200a201b40210021280bc021185199de6012ec14541fc021002100212c188021002100210021081f002100213e858014802118084021002108185c150021002118014c138411002100211c0700213c20801a31c5781e50065adb6c41c021204ea1df5c130eddc021344e44061420d815cc081445002136577407d814f40b485a7c0422dc7416c021100de40ac40f002100210c1c4021000b802100210400001f640e40210021180cf19b7011c02118094021002100210021002100213019d805cc068021002134031808e8013013f0190c0180212c9d981b26dd440f5c0d8aa080211c0a640c4854d19b3403a41db810a1122816b8047015944140213de0881f802100211c1d700b0021002100211c17b01bc02100211019441ced144c1d0400909b365cc0211414380c84117019980050200021002104120c07a4156018dc9c1800e40fc0210021002100211c1acc09c0211403691f081dd44a2c0d1817c0210d1600212ddfa042540900210021200d4c4de402cc028021200e9c0ab00c341a54118021002100211d15ec50002104160021002100210803d006ec1c1c9e5010d84400212c1a8021002114a08021002100210021169e4021002100212590705a0021002135a08859cc204021200e280f802100210021201e2810289c50124021381e80005008000200000400a000201c0803008000201000000011008000000000000601008200401038040600008001601020000400000003e06020040800000000606
def qH0_38 (h : Nat) : Option (Nat × Nat):=lookupWord 58 282 9 16 8 4 qH0_38F h
def qH1_38F (i : Nat) : Nat:=0x2c0cb430680e0c03561290288039b0b0388240398039803999ae101ea00ce4066826b01a7d2fce0168294039a0194005002080398a830039b418fc190039b427f016801b8c3854213c5f10188c09d6944039b2013180a432b60f64204039803980398039a83238235c2dc832cc22401b582d9112886aaed424367c19821084352c36b5eeb8081c0dc82e6420ec17880a9593b42b48057405d005a42d3d81805e142e080a29e071965834a828d6c2d83900399426741cf4380808f2103039681fb825081c00398d81dc15e41bc41f00398833720ebe106c241c34c82f0019f10f5e91b8281422d021d02bac5f4033c826d01c560fc43240398039be0ef42fa8480004ec2bfc1ae423981dd41dba8284092c06f8184c3390063c23dc1a2d00c8921429e8176831a038a46af416c06b143110230c261e10d433101d0039a41d542762d24039a4157420200968084c38d8375c0a40398039ba12c4379c098039910f89927030dc31c039940b00398039b407646c00398039ae9490215007042f485df41f580d980d082188047c04945d445d8817de822a8ef803beaedc03e200b80e755358b058d1e824fc1b180882d3fc079c2c54316dedd590ae1120222a90640ac590384ad8484039803985916036c039981ec039800d640400398039840b460f0039ac0680398039803980398039ac1ffc27bc07e422842a783448292e007830b190cc35a8254c2ea881e828641abe01c8165c29942cf018002a08159c272693280b8c17202d586a5816201c8825d02c2024946a34372091b82c89ad14356c37d0259814c43428244035c85e4c1520360020e008240600000142c0a0e0287c01028080000000040408118200202000c0021001000000d0000000000980c0a020008c040200018061b080a41c0e00880340d00028000b008081601080880407028700e5a088040600008242e04130083804
def qH1_38 (h : Nat) : Option (Nat × Nat):=lookupWord 86 296 9 16 8 4 qH1_38F h
def qH2_38F (i : Nat) : Nat:=(if i<1 then 0xa2983031483ad0125a0098755502d5a1dad2c0f1665142de9e32ceb902b601f9c0b72084f14ca82cc81f0407374702b22140ff80854675080abc17c0828402ae040d00d1c4289014b8367011f20ce303a1cafcc1d8ac0b406e688bbc19640c350265097f420dc2878081193c9004104f1863d0301a81e1804af01af13f8c5a6c07b5188c01e6c8576061f0882007fc1b4628830188039ec5b1603d700598262405de0b08080b0455c044004e116f293e080340041202040422c09680bb10734b02845d3808d105e4b3a5414900a710794a3fb84bb6002c02f109e5c1e8e10790019a43181e640759015f0b5840a5a0041071281c0404300af5b7518090c1ec262ec06f902bb8165606e4027b8a5dd623c013e47fb89df81fc404520332030a0169409e7625900e445a42c29d05ec803581c0e0062040c0285d144c0ad0a70d8251c0d88c43ea7fd835501dd60371087d00f88051805f0009381230076c0d6e02258416408f604930779042ec153800ea782b83a500ae44ec802e1005041884910008b3bc1e009ba064a13d00458006c20b6b07fa8060021580c6e041783d7c12ba4e7507ba02c741c2009d86832824e80cfa08a303560095c0d22017008b00458c02c8ae4403b3006e011001162044b01b4c1ca4280f374b80cc022c0116002ce00410065882a8080480e8022c0007ab76603c7415040511032d5bb7c0c78077008b7809bc1d56900047300458022d207c60162816184ed8627008b18b38022d80190383a834581aecd081089c02384456e053c0051802051d0e099037688968d06080ed30720000551464f0ec07e000c2c59a825e112e103170498a07d701fbd0c000d6282f80657828289d5c111d087293a540b4a11234840045ba9e10507f01e682a8022c02dd505f923d0412d20a3a02a68b5541a1801d704b88295c01eae95405ce836081a68042404dd0348c1bbc01c9066e80e04118e4ff7082703220047e0e3c05bf0378003dc0f99270803a26dd3eee11377a8302010fa0d4f2726bbfd01b7c0460017983f480df00fa5008c5bce1df26a2b705c1821a920860c1c04fb08ec0218a0c9003d58242022801169181b88b0ade1202d4276e0245c17529022878481e0821aa080c04e200035dc1c1093045c828a015942eda04d302af09cb0015400614b8119da627b414340330018f2260f0536801780e3e5123041f8142c19fe043207dcd3cc04000983826001a0181801001102e01190044e00168004a07000442c32000a40244000149201069cc00070812c0002008044a030e80402430607400153781c0e001381c1204048587c0a0c0002a06008e408bc000009e22000140a14008440000080184015001041e03368002e0c0597c00514983c30cf0638c2c020000c26ba00004062b00024045d128603a0101860260d2d0cc0830 else 0x3270581cbc0c04027201a31bfbc0ba)
def qH2_38 (h : Nat) : Option (Nat × Nat):=lookupWord 134 418 9 17 9 4 qH2_38F h
def qL40F (i : Nat) : Nat:=0x4a61d06a2cda3102002005fe80140
def qL40 : PackingT:=(1,2,7,7,qL40F)
def qH1_40F (i : Nat) : Nat:=0x401402808100601ba001008037a0400dc88504801b911806c03601b00c20
def qH1_40 (h : Nat) : Option (Nat × Nat):=lookupWord 4 17 5 13 5 4 qH1_40F h
def qL41F (i : Nat) : Nat:=0x321e92043468adfe2ae240828d19aab854c81051a332171204320a3461157e8b3694c601d068100155fa2cda53188701a04004812bf459b4a6310e8300800ae2e2a9f145a97c01ffc82503ff902a07ff14540ffe10a817fd30502ffa40a05ff44140
def qL41 : PackingT:=(7,2,7,9,qL41F)
def qH1_41F (i : Nat) : Nat:=0x40f303806f084219fb2204682c01b00d806d01c01bd1d704e46401bf06683403601bc09006da8a01b31b806f01601b00d806c03601b00d806d80c01b00da40c0376a380a006e18801b5161c02010e4300d806e90001b00d806c03601b00d806c03600af60a82783150100da05403634380b806e835a1000d8906180010000000060c006
def qH1_41 (h : Nat) : Option (Nat × Nat):=lookupWord 13 74 7 13 5 4 qH1_41F h
def qH2_41F (i : Nat) : Nat:=0x26901dd0480135414004d102c0134026e026009b2028026b0038122013781e004d71380135002004da09128380268809015a0134026804d009a0134026804d205601340268932009ae01cc25682700594097006d04c4074c0ab98f004d009b0085608600e0062e03c026804d009a0137421804d40600134026a02291780134026804d009a0135c0df81e009a0134c16d019556d80cc8010811546b4ef198828069183843842200ac9177e277865c81f009a01340269936009a74c5c88004df016e11540ad80550006043025804d009a84bc898804d009a0137855804d009a0135c042829009a010b819004d009a0134026804dbb6320e080a383f706b4006809804d009a0137417681c34720136658101af361c24141be03e009a01340269836009a0134c06004d70248844026804d009a20ee8249820b21fee4180c7134d08c8100026d823905e611e81a2039402f8e44026903d009ac104026804d009a0134026933c009a0134026804da6220134026804d0c000000000200000303000003040d0303000c010401000004010003060a0001060101000900
def qH2_41 (h : Nat) : Option (Nat × Nat):=lookupWord 38 198 8 15 7 4 qH2_41F h
def qL44F (i : Nat) : Nat:=0x5f453629180e0602004807fd40
def qL44 : PackingT:=(1,1,7,7,qL44F)
def qH1_44F (i : Nat) : Nat:=0x1a000fa0032c0080402010080403b400d90020100e4000
def qH1_44 (h : Nat) : Option (Nat × Nat):=lookupWord 2 19 5 9 1 4 qH1_44F h
def qH2_44F (i : Nat) : Nat:=0x1c0380700e2e403807e0001c0380700f8e003c9172401c0380700e01c038c875001c03c8100e01c03ea900e80b5171800fc200380700e01c0380700e01c03807132e240380700e01c0080001
def qH2_44 (h : Nat) : Option (Nat × Nat):=lookupWord 5 53 6 11 3 4 qH2_44F h
def qSeedH2F (i : Nat) : Nat:=0x1c1bc190531601c0380700e01c46d0400
def qSeedH2 (h : Nat) : Option (Nat × Nat):=lookupWord 2 11 4 11 3 4 qSeedH2F h
def qLevels : Nat → PackingT
  | 24 => qL24
  | 27 => qL27
  | 28 => qL28
  | 29 => qL29
  | 30 => qL30
  | 31 => qL31
  | 32 => qL32
  | 33 => qL33
  | 34 => qL34
  | 35 => qL35
  | 37 => qL37
  | 38 => qL38
  | 40 => qL40
  | 41 => qL41
  | 44 => qL44
  | _ => emptyPackingT
def qIdx0 : Nat → Nat → Option (Nat × Nat)
  | 27 => qH0_27
  | 30 => qH0_30
  | 31 => qH0_31
  | 32 => qH0_32
  | 33 => qH0_33
  | 34 => qH0_34
  | 35 => qH0_35
  | 37 => qH0_37
  | 38 => qH0_38
  | _ => fun _ => none
def qIdx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => qH1_31
  | 32 => qH1_32
  | 34 => qH1_34
  | 35 => qH1_35
  | 37 => qH1_37
  | 38 => qH1_38
  | 40 => qH1_40
  | 41 => qH1_41
  | 44 => qH1_44
  | _ => fun _ => none
def qIdx2 : Nat → Nat → Option (Nat × Nat)
  | 32 => qH2_32
  | 35 => qH2_35
  | 38 => qH2_38
  | 41 => qH2_41
  | 44 => qH2_44
  | _ => fun _ => none
abbrev bkT:=blockT qLevels qIdx0 qIdx1 qIdx2
abbrev bmT (k tm s a b : Nat):=@blockT_merge qLevels qIdx0 qIdx1 qIdx2 k tm s a b
set_option maxHeartbeats 0 in
theorem c24_0 : bkT 8 0 0 2=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a24 : bkT 8 0 0 2=true:=c24_0
set_option maxHeartbeats 0 in
theorem c27_0 : bkT 9 0 0 22=true:=cellsBlockT (ar:=10) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
theorem a27 : bkT 9 0 0 22=true:=c27_0
set_option maxHeartbeats 0 in
theorem c28_0 : bkT 9 1 0 12=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a28 : bkT 9 1 0 12=true:=c28_0
set_option maxHeartbeats 0 in
theorem c29_0 : bkT 9 2 0 9=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a29 : bkT 9 2 0 9=true:=c29_0
set_option maxHeartbeats 0 in
theorem c30_0 : bkT 10 0 0 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_48 : bkT 10 0 48 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_96 : bkT 10 0 96 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_144 : bkT 10 0 144 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_192 : bkT 10 0 192 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_240 : bkT 10 0 240 43=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a30 : bkT 10 0 0 283=true:=(bmT 10 0 0 144 139 (bmT 10 0 0 48 96 c30_0 (bmT 10 0 48 48 48 c30_48 c30_96)) (bmT 10 0 144 48 91 c30_144 (bmT 10 0 192 48 43 c30_192 c30_240)))
set_option maxHeartbeats 0 in
theorem c31_0 : bkT 10 1 0 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_48 : bkT 10 1 48 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_96 : bkT 10 1 96 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_144 : bkT 10 1 144 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_192 : bkT 10 1 192 7=true:=chunkBlockT (ar:=10) (by decide +kernel)
theorem a31 : bkT 10 1 0 199=true:=(bmT 10 1 0 96 103 (bmT 10 1 0 48 48 c31_0 c31_48) (bmT 10 1 96 48 55 c31_96 (bmT 10 1 144 48 7 c31_144 c31_192)))
set_option maxHeartbeats 0 in
theorem c32_0 : bkT 10 2 0 2=true:=chunkBlockT (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c32_2 : bkT 10 2 2 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c32_50 : bkT 10 2 50 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c32_98 : bkT 10 2 98 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c32_146 : bkT 10 2 146 10=true:=chunkBlockT (ar:=10) (by decide +kernel)
theorem a32 : bkT 10 2 0 156=true:=(bmT 10 2 0 50 106 (bmT 10 2 0 2 48 c32_0 c32_2) (bmT 10 2 50 48 58 c32_50 (bmT 10 2 98 48 10 c32_98 c32_146)))
set_option maxHeartbeats 0 in
theorem c33_0 : bkT 11 0 0 48=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_48 : bkT 11 0 48 48=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_96 : bkT 11 0 96 36=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a33 : bkT 11 0 0 132=true:=(bmT 11 0 0 48 84 c33_0 (bmT 11 0 48 48 36 c33_48 c33_96))
set_option maxHeartbeats 0 in
theorem c34_0 : bkT 11 1 0 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c34_1 : bkT 11 1 1 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_49 : bkT 11 1 49 9=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c34_58 : bkT 11 1 58 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_106 : bkT 11 1 106 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_154 : bkT 11 1 154 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_202 : bkT 11 1 202 28=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a34 : bkT 11 1 0 230=true:=(bmT 11 1 0 58 172 (bmT 11 1 0 1 57 c34_0 (bmT 11 1 1 48 9 c34_1 c34_49)) (bmT 11 1 58 96 76 (bmT 11 1 58 48 48 c34_58 c34_106) (bmT 11 1 154 48 28 c34_154 c34_202)))
set_option maxHeartbeats 0 in
theorem c35_0 : bkT 11 2 0 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c35_48 : bkT 11 2 48 3=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c35_51 : bkT 11 2 51 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c35_99 : bkT 11 2 99 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c35_147 : bkT 11 2 147 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c35_195 : bkT 11 2 195 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c35_243 : bkT 11 2 243 35=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a35 : bkT 11 2 0 278=true:=(bmT 11 2 0 99 179 (bmT 11 2 0 48 51 c35_0 (bmT 11 2 48 3 48 c35_48 c35_51)) (bmT 11 2 99 96 83 (bmT 11 2 99 48 48 c35_99 c35_147) (bmT 11 2 195 48 35 c35_195 c35_243)))
set_option maxHeartbeats 0 in
theorem c37_0 : bkT 12 1 0 9=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c37_9 : bkT 12 1 9 12=true:=chunkBlockT (ar:=11) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c37_21 : bkT 12 1 21 6=true:=chunkBlockT (ar:=12) (by decide +kernel)
theorem a37 : bkT 12 1 0 27=true:=(bmT 12 1 0 9 18 c37_0 (bmT 12 1 9 12 6 c37_9 c37_21))
set_option maxHeartbeats 0 in
theorem c38_0 : bkT 12 2 0 19=true:=cellsBlockT (ar:=10) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c38_19 : bkT 12 2 19 42=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c38_61 : bkT 12 2 61 16=true:=cellsBlockT (ar:=12) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
theorem a38 : bkT 12 2 0 77=true:=(bmT 12 2 0 19 58 c38_0 (bmT 12 2 19 42 16 c38_19 c38_61))
set_option maxHeartbeats 0 in
theorem c40_0 : bkT 13 1 0 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a40 : bkT 13 1 0 1=true:=c40_0
set_option maxHeartbeats 0 in
theorem c41_0 : bkT 13 2 0 3=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c41_3 : bkT 13 2 3 4=true:=chunkBlockT (ar:=11) (by decide +kernel)
theorem a41 : bkT 13 2 0 7=true:=(bmT 13 2 0 3 4 c41_0 c41_3)
set_option maxHeartbeats 0 in
theorem c44_0 : bkT 14 2 0 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a44 : bkT 14 2 0 1=true:=c44_0
theorem tables2149 : ∀ k ≤ 14,∀ tmax ≤ 2,blockT qLevels qIdx0 qIdx1 qIdx2 k tmax 0 (qLevels (3*k+tmax)).1=true:=by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 0 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 0 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 0 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 1 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 1 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 1 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 2 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 2 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 2 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 3 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 3 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 3 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 4 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 4 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 4 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 5 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 5 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 5 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 6 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 6 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 6 2 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 7 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 7 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 7 2 0 0=true)
  · exact a24
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 8 1 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 8 2 0 0=true)
  · exact a27
  · exact a28
  · exact a29
  · exact a30
  · exact a31
  · exact a32
  · exact a33
  · exact a34
  · exact a35
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 12 0 0 0=true)
  · exact a37
  · exact a38
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 13 0 0 0=true)
  · exact a40
  · exact a41
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 14 0 0 0=true)
  · exact (rfl : blockT qLevels qIdx0 qIdx1 qIdx2 14 1 0 0=true)
  · exact a44
def roots:=inputs ++ [seed]
private lemma andRep {w a b}  (ha : represented w a) (hb : represented w b) :
    represented w (bin false a b)∨(∃ x y,x ∈ w∧y ∈ w∧proper x∧proper y∧x≠y∧bin false a b=bin false x y):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; simp_all
  · rw [bin_comm]; simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · simp_all
  · simp_all
  by_cases he : a=b
  · subst b; simp_all
  exact Or.inr ⟨a,b,ham,hbm,hap,hbp,he,rfl⟩
theorem andGate (g : Gate) (op : g.op=.and) (hl : g.inputs.length ≤ 2) :
    represented roots (gv roots g)∨∃ a b,a ∈ roots∧b ∈ roots∧proper a∧proper b∧a≠b∧gv roots g=bin false a b:=by
  obtain ⟨o,l⟩:=g
  change o=.and at op
  subst o
  cases l with
  | nil => exact Or.inl (Or.inr (fun hp => hp.2 rfl))
  | cons i l =>
    cases l with
    | nil =>
      simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using
        (Or.inl (get_rep roots i) : represented roots (roots.getD i zero)∨_)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil => simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using andRep (get_rep roots i) (get_rep roots j)
theorem oldImpossibleT : ImpossibleT graph 14 2 inputs.toFinset:=by
  have hall:=forestT_all qLevels qIdx0 qIdx1 qIdx2 14 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tables2149 14 (by decide) 2 (by decide) 0 (by decide)
  have hsame : sameWords (stateSetT qLevels 44 0) inputs=true:=by decide +kernel
  have htgt : targetOf dead=graph:=by decide +kernel
  rw [←sameWords_sound hsame,←htgt]
  exact hall
theorem looseT {k t S} (run : Live graph k t S) (hk : k ≤ 13) (ht : t ≤ 2) (sub : ∀ a ∈ S,a ∈ roots) : False:=by
  have wit : witness inputs seed:=by
    right
    exact ⟨true,inputs.getD 0 zero,inputs.getD 4 zero,by decide +kernel,by decide +kernel,
      by unfold proper; decide +kernel,by unfold proper; decide +kernel,by decide +kernel,rfl⟩
  have witT : represented inputs seed∨(if false then ∃ a,a ∈ inputs∧proper a∧seed=neg a
      else ∃ d a b,a ∈ inputs∧b ∈ inputs∧proper a∧proper b∧a≠b∧seed=bin d a b):=by
    have hne : inputs.all (fun a => seed != neg a)=true:=by decide +kernel
    simp only [List.all_eq_true,bne_iff_ne] at hne
    right; exact wit.resolve_left (by rintro ⟨a,ha,hp,he⟩; exact hne a ha he)
  obtain ⟨l,u,V,hl,hu,hr,hs⟩:=pull_gateT false run witT sub
  have hs' : ∀ a ∈ V,a ∈ inputs ++ [seed]:=fun a ha => List.mem_append_left _ (hs a ha)
  rcases all_roots hr hs' with e | e
  · exact oldImpossibleT l u (by omega) (by simpa using hu.trans ht) (e ▸ hr)
  · have hm : seed ∈ V:=e.symm ▸ List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
    exact (show seed ∉ inputs by decide +kernel) (hs _ hm)
def seedBank : List Decor:=decodeBank 1 0x140 deadWires
def rootDecor : List Decor:=seedBank
def seedRules : List BoundPool :=
  ([(0,0),(24,0),(32,0),(54,1),(69,1),(2,0),(26,0)] : List (Nat×Nat)).filterMap
    (fun (a,b) => buildRule dead 0x140 1 seedBank a b)
def seedLinks2 : LinkFn:=fun tag => ((qSeedH2 tag).bind (linkedSetT qLevels 41)).toList
def seedCtx : NodeContextT :=
  (14,2,rootDecor.length,rootDecor,preCov rootDecor,seedRules,
   seedRules.map (summarizePool rootDecor),fun _ => [],fun _ => [],seedLinks2)
theorem decRootT : rootDecor.map Prod.fst=roots:=by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checkedPairsT : rootDecor.all (fun a => rootDecor.all (fun b => a.1==b.1||testPairT seedCtx a b false))=true:=by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem childrenT {a b : Sig} (am : a ∈ roots) (bm : b ∈ roots) (hab : a≠b)
    (ka kb : Bool) (fr : bin false a b ∉ roots) (pr : proper (bin false a b)) :
    ImpossibleT graph 13 2 (childTwo roots a b false ka kb).toFinset:=by
  rw [← decRootT] at am bm fr ⊢
  obtain ⟨a,aa,rfl⟩:=List.mem_map.mp am
  obtain ⟨b,bb,rfl⟩:=List.mem_map.mp bm
  have nd : (rootDecor.map Prod.fst).Nodup:=by rw [decRootT]; decide +kernel
  rw [← binary_front nd aa bb hab]
  have check:=List.all_eq_true.mp (List.all_eq_true.mp checkedPairsT a aa) b bb
  simp only [Bool.or_eq_true,beq_iff_eq] at check
  have test:=check.resolve_left hab
  have geo:=geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have pairs:=chart_pairs geo.1.1.1 geo.1.1.2
  have cols:=fun ci hc => col_sound ci (boundsBefore known383) (before_sound known383 valid383) (geo.1.2 ci hc)
  have hev:=evalMoveT_sound (raw:=vars dead.mask) (T:=targetOf dead) (op:=0) (ka:=ka) (kb:=kb)
    (pools:=seedRules) (l0:=fun _ => []) (l1:=fun _ => []) (l2:=seedLinks2) (cap:=14) (tmax:=2)
    pairs (fun v hv => decode_faithful _ _ _ _ _ (wires_faithful dead) v hv) nd aa bb
    (fun _ e => hab (congrArg Prod.fst e)) (by decide) (by decide)
    (fun p hp => by obtain ⟨⟨i,j⟩,_,h⟩:=List.mem_filterMap.mp hp; exact buildRule_sound dead cols h)
    (fun _ _ hx => by simp at hx)
    (fun _ _ hx => by simp at hx)
    (fun tag xs hx => by
      change xs ∈ ((qSeedH2 tag).bind (linkedSetT qLevels 41)).toList at hx
      have e : (qSeedH2 tag).bind (linkedSetT qLevels 41)=some xs:=by simpa using hx
      obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
      exact linkedSetT_sound qLevels 13 2 geo.2
        (forestT_all qLevels qIdx0 qIdx1 qIdx2 14 _ (before_sound known383 valid383) geomdead tables2149 13 (by decide) 2 (by decide)) h)
    pr fr (testPairT_at test ka kb)
  have hlen : (moveFront rootDecor 0 a b ka kb).length < 14:=by
    have hcard : (moveFront rootDecor 0 a b ka kb).length ≤ rootDecor.length+1:=by
      unfold moveFront
      have sub:=keep_sub rootDecor a b false ka kb
      have hl:=sub.length_le
      simp; omega
    have hrlen : rootDecor.length=10:=by decide +kernel
    omega
  have hct : childT 2 14 (moveFront rootDecor 0 a b ka kb).length 0=2:=by
    unfold childT
    have hne : ((moveFront rootDecor 0 a b ka kb).length==14)=false:=beq_eq_false_iff_ne.mpr (by omega)
    simp [hne]
  have htgt : targetOf dead=graph:=by decide +kernel
  change ImpossibleT (targetOf dead) (14-1) (childT 2 14 (moveFront rootDecor 0 a b ka kb).length 0) _ at hev
  rw [hct,htgt] at hev
  exact hev
theorem startAndT {k t U a b} (hk : k ≤ 13) (ht : t ≤ 2) (ha : proper a) (hb : proper b) (hab : a≠b)
    (hf : bin false a b ∉ insert a (insert b U)) (tail : Live graph k t (insert (bin false a b) U))
    (sub : ∀ v ∈ insert a (insert b U),v ∈ roots) : False:=by
  classical
  have full:=Live.binary ha hb hab hf tail
  rcases all_roots full sub with he | he
  · exact oldImpossibleT _ _ (by omega) ht (he ▸ full)
  have he : roots.toFinset=insert a (insert b U):=he.symm
  have hn : roots.Nodup:=by decide +kernel
  have am : a ∈ roots:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bm : b ∈ roots:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have fresh : bin false a b ∉ roots:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
  have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
  let ka:=decide (a ∈ U)
  let kb:=decide (b ∈ U)
  let rest:=(roots.erase a).erase b
  have er : rest.toFinset=(roots.toFinset.erase a).erase b:=by
    rw [show rest=(roots.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
  have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
    rw [kept_fin,kept_fin,er,he]
    ext j
    by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
      by_cases jb : j=b <;> simp [ka,kb,aa,bb,ja,jb,hab,Ne.symm hab]
  have rn : rest.Nodup:=(hn.erase _).erase _
  have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
  have br : b ∉ rest:=(hn.erase a).not_mem_erase
  have nk:=kept_nd kb b rest rn br
  have ax : a ∉ kept kb b rest:=by cases kb <;> simp [kept,ar,hab]
  have eq : (childTwo roots a b false ka kb).toFinset=insert (bin false a b) U:=by
    change (bin false a b :: kept ka a (kept kb b rest)).toFinset=_
    simp [ke]
  exact childrenT am bm hab ka kb fresh hz k t hk ht (eq.symm ▸ tail)
theorem killT {k t S z} (hk : k ≤ 13) (ht : t ≤ 2) (h : Live graph k t S)
    (hz : represented roots z∨∃ a b,a ∈ roots∧b ∈ roots∧proper a∧proper b∧a≠b∧z=bin false a b)
    (sub : ∀ a ∈ S,a ∈ roots ++ [z]) : False:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ roots
    · apply looseT h hk ht
      intro a ha
      rcases (by simpa using sub a ha : a ∈ roots∨a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | ⟨a,b,ha,hb,pa,pb,hab,rfl⟩
      · exact (hr.resolve_left hw) hp
      · let U:=S.erase (bin false a b)
        have tail : Live graph k t (insert (bin false a b) U):=by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ roots:=fun v hv => by
          obtain ⟨hne,hm'⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hm'
        have hf : bin false a b ∉ insert a (insert b U):=fun hh => by
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact startAndT hk ht pa pb hab hf tail (by simpa using And.intro ha (And.intro hb hu))
  · apply looseT h hk ht
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem edge_eq_petersen (x : Fin 9→Bool) : edge x=Binary.petersenF x:=by
  simp [edge,Binary.petersenF,Binary.PetersenNine.edgeFun,Binary.PetersenNine.edges,Bool.or_assoc]
theorem finishT (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9→Bool,(C.wires (List.ofFn y)).getD 9 false=(y 0||y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C=edge) (small : C.size ≤ 15)
    (second : Option.map Gate.op C.gates[1]?=some GateOp.and) : False:=by
  have headEq : (execute C.gates inputs).getD 9 zero=seed:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out:=get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn:=out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g=seed:=by
      rw [hgs] at headEq
      change (execute gs (inputs ++ [gv inputs g])).getD 9 zero=seed at headEq
      obtain ⟨l,hl⟩:=exec_extends gs (inputs ++ [gv inputs g])
      rw [hl] at headEq
      exact headEq
    have hg_not : g.op≠GateOp.not:=by
      intro hnot
      have h0:=congrArg (bit ⟨0,by decide⟩) eq0
      have hseed0 : bit ⟨0,by decide⟩ seed=false:=by decide +kernel
      rw [hseed0] at h0
      have hgv0 : bit ⟨0,by decide⟩ (gv inputs g)=true:=by
        simp only [gv,hnot]
        cases hi : g.inputs with
        | nil => decide +kernel
        | cons a t =>
          simp only [List.map_cons,List.headD_cons,bit_neg]
          have hin0 : bit ⟨0,by decide⟩ (inputs.getD a zero)=false:=by
            by_cases ha : a < 9
            · interval_cases a <;> decide +kernel
            · have hge : inputs.length ≤ a:=by rw [←input_list,List.length_ofFn]; exact Nat.le_of_not_lt ha
              rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none hge]; exact (by decide +kernel : bit ⟨0,by decide⟩ zero=false)
          rw [hin0]; rfl
      rw [hgv0] at h0; cases h0
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs ++ [gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs,gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧gate.inputs.length ≤ 2:=by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    cases gs with
    | nil => simp [hgs] at second
    | cons g2 rest =>
      have op : g2.op=.and:=by simpa [hgs] using second
      have len : rest.length ≤ 13:=by simp [Circuit.size,hgs] at small; omega
      have hlow:=Binary.petersen_binary_lower C legal (fun x => (congrFun computes x).trans (edge_eq_petersen x))
      have hnn : Binary.CircuitProof.nonNotCount C.gates=2+Binary.CircuitProof.nonNotCount rest:=by
        rw [hgs]
        simp only [Binary.CircuitProof.nonNotCount,List.countP_cons,op]
        have hg1 : Binary.CircuitProof.isNotGate g.op=false:=by
          cases hgo : g.op <;> first | exact False.elim (hg_not hgo) | rfl
        have hg2 : Binary.CircuitProof.isNotGate GateOp.and=false:=rfl
        rw [hg1,hg2]; simp; omega
      rw [hnn] at hlow
      have hbound:=Binary.nonNotCount_add_notCount rest
      change Binary.CircuitProof.nonNotCount rest+(rest.filter fun q => Binary.CircuitProof.isNotGate q.op).length=rest.length at hbound
      have hfeq : (fun q : Gate => isNotT q.op)=(fun q : Gate => Binary.CircuitProof.isNotGate q.op):=by
        funext q; cases q.op <;> rfl
      have hcntEq : rest.countP (fun q => isNotT q.op)=(rest.filter fun q => Binary.CircuitProof.isNotGate q.op).length:=by
        rw [List.countP_eq_length_filter,hfeq]
      have ht2 : rest.countP (fun q => isNotT q.op) ≤ 2:=by omega
      obtain ⟨k,t,S,hk,ht,run,hs⟩:=extractT rest (roots ++ [gv roots g2]) (fun x hx => tailLegal x (by simp [hx])) graph_proper targetIn
      exact killT (hk.trans len) (ht.trans ht2) run (andGate g2 op (tailLegal g2 (by simp)).2) hs
end PEqualNP.Outside.L_meta_2149
theorem PEqualNP.Outside.L_meta_2149 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (16 : ℕ) ≤ x1.size := by
  intro C hf hw he hs
  by_contra h
  exact PEqualNP.Outside.L_meta_2149.finishT C hf hw he (by omega) hs
