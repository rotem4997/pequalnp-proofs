import Mathlib
import PEqualNP.Defs
-- The base certificate is by odinfree, PR 6586, commit 91a84e0e2892154c472c668594ba47bec3d0534b.
namespace PEqualNP.Outside.L_meta_4759
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
  Finset.univ.filter (fun v => G.Adj u v /\ v ∉ removed)
lemma b31 {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u:=by
  intro v membership
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at membership ⊢
  exact ⟨membership.1,fun vIn => membership.2 (h vIn)⟩
lemma b85 {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w:=by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B):=by
    ext z
    simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hz => ⟨⟨hz.1,fun zIn => hz.2 (h zIn)⟩,hz.2⟩,fun hz => ⟨hz.1.1,hz.2⟩⟩
  rw [e u,e w,same]
def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group,∀ w ∈ group,(neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty -> neighborsAfter G removed u = neighborsAfter G removed w
def b106 (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)
def b24 (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed /\ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed /\ neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅
def closeIsolates (removed : Finset V) : Finset V:=removed ∪ b106 G removed
def b20 (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ b24 G removed root)
lemma b29 (removed : Finset V) (root : V) : removed ⊆ b20 G removed root:=by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
lemma b56 {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ b20 G removed root:=by
  have hn : ¬ (neighborsAfter G (removed ∪ b24 G removed root) u).Nonempty:=by
    intro existsNeighbor
    exact h (existsNeighbor.mono (b31 G Finset.subset_union_left u))
  have hu : u ∈ b106 G (removed ∪ b24 G removed root):=by
    simp [b106,Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu
theorem b175 [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V,A ∪ Q ⊆ b20 G B root:=by
  classical
  by_cases someActive : ∃ root ∈ Q,root ∉ B /\ (neighborsAfter G B root).Nonempty
  · obtain ⟨root,rootQ,rootOut,rootLive⟩:=someActive
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact b29 G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact b29 G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU:=live.mono (b31 G smaller u)
      have oldRoot:=rootLive.mono (b31 G smaller root)
      have same:=b85 G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ b24 G B root:=by simp [b24,rootOut,rootLive,uIn,same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact b56 G root u live
  · let root : V:=Classical.choice inferInstance
    refine ⟨root,?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact b29 G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact b29 G B root uIn
    exact b56 G root u (fun live => someActive ⟨u,hu,uIn,live⟩)
lemma b67 {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty:=by
  have uOut : u ∉ removed:=fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty:=by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [b106,Finset.not_nonempty_iff_eq_empty.mp empty]
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
    have none : neighborsAfter G removed v = ∅:=by simpa [b106] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness
lemma b51 (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed:=by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live:=b67 G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅:=by
      simpa [b106] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left
def b60 : Finset V -> List (Finset V) -> Prop
  | _,[] => True
  | removed,group :: rest => TwinGroup G removed group /\ b60 (removed ∪ group) rest
def b13 : Finset V -> List (Finset V) -> Finset V
  | removed,[] => removed
  | removed,group :: rest => b13 (removed ∪ group) rest
def b102 : ℕ -> Finset V -> Finset V -> Prop
  | 0,start,finish => finish = start
  | k + 1,start,finish => ∃ root : V,b102 k (b20 G start root) finish
theorem b169 [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : b60 G A groups) :
    ∃ finish : Finset V,b102 G groups.length B finish /\ b13 A groups ⊆ finish:=by
  induction groups generalizing A B with
  | nil => exact ⟨B,rfl,smaller⟩
  | cons group rest ih =>
    obtain ⟨twins,next⟩:=steps
    obtain ⟨root,subset⟩:=b175 G smaller twins
    obtain ⟨finish,walk,covered⟩:=ih subset next
    exact ⟨finish,⟨root,walk⟩,covered⟩
def b19 (removed : Finset V) : Prop :=
  ∀ u v,u ∉ removed -> v ∉ removed -> ¬ G.Adj u v
omit [Fintype V] [DecidableRel G.Adj] in
lemma b178 {A B : Finset V} (subset : A ⊆ B) (noEdges : b19 G A) :
    b19 G B:=by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))
lemma b134 {D : Finset V} (noEdges : b19 G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ:=by
  ext u
  simp only [Finset.mem_univ,iff_true]
  by_contra out
  obtain ⟨v,hv⟩:=b67 G out
  simp only [neighborsAfter,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  exact noEdges u v out hv.2 hv.1
lemma b99 {k : ℕ} {start finish : Finset V} (walk : b102 G k start finish)
    (closed : ∃ D : Finset V,start = closeIsolates G D) : ∃ D : Finset V,finish = closeIsolates G D:=by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root,after⟩:=walk
    exact ih after ⟨_,rfl⟩
theorem b58 [Nonempty V] (groups : List (Finset V))
    (twins : b60 G ∅ groups) (finished : b19 G (b13 ∅ groups)) :
    b102 G groups.length (closeIsolates G ∅) Finset.univ:=by
  obtain ⟨D,steps,subset⟩:=b169 G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges:=b178 G subset finished
  obtain ⟨A,hD⟩:=b99 G steps ⟨∅,rfl⟩
  rw [hD] at noEdges
  rwa [hD,b134 G noEdges] at steps
end FiniteGraph
end BranchGraph
namespace BranchGroupsLean
open BranchGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}
def bucket (label : V -> Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v = r)
def below (label : V -> Fin m) (r : Fin m) : Finset V:=Finset.univ.filter (fun v => label v < r)
def b23 (label : V -> Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)
omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V -> Fin m) : b23 label [] = ∅:=by
  ext v
  simp [b23]
lemma b36 (label : V -> Fin m) (done : List (Fin m)) (r : Fin m) :
    b23 label (done ++ [r]) = b23 label done ∪ bucket label r:=by
  ext v
  simp [b23,bucket,List.mem_append]
omit [DecidableEq V] in
lemma b98 (label : V -> Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V,label v = out \/ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : b23 label done = below label r:=by
  have facts:=List.pairwise_append.mp sorted
  ext v
  simp only [b23,below,Finset.mem_filter,Finset.mem_univ,true_and]
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
theorem b110 (label : V -> Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V,label v = out \/ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots,r < out)
    (twinAt : ∀ r ∈ roots,TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    b60 G (b23 label done) (pending.map (bucket label)):=by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots:=complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev:=b98 label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next:=ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_,?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [b36] at next
lemma b96 (label : V -> Fin m) (done pending : List (Fin m)) :
    b13 (b23 label done) (pending.map (bucket label)) = b23 label (done ++ pending):=by
  induction pending generalizing done with
  | nil => simp [b13]
  | cons r tail ih =>
    change b13 (b23 label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← b36,ih]
    simp [List.append_assoc]
omit [DecidableRel G.Adj] in
lemma b105 (label : V -> Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V,label v = out \/ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    b19 G (b13 ∅ (roots.map (bucket label))):=by
  rw [← coveredBy_nil label,b96,List.nil_append]
  intro u v uNot vNot
  have hu : label u = out:=(allRoots u).resolve_right (by simpa [b23] using uNot)
  have hv : label v = out:=(allRoots v).resolve_right (by simpa [b23] using vNot)
  exact outputIndependent u (by simp [bucket,hu]) v (by simp [bucket,hv])
theorem roots_required (label : V -> Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V,label v = out \/ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches,r < out)
    (twinAt : ∀ r ∈ branches,TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V),b60 G ∅ groups →
      b19 G (b13 ∅ groups) -> k ≤ groups.length) : k ≤ branches.card:=by
  let roots:=branches.sort
  have sorted : roots.Pairwise (· < ·):=List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out \/ label v ∈ roots:=by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out:=beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : b60 G ∅ (roots.map (bucket label)):=by
    simpa using b110 G label out roots sorted covers early twins [] roots rfl
  have last:=b105 G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last
end Graph
end BranchGroupsLean
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def b1 (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem b42 (gs gs' : List Gate) (w : List Bool) :
    b1 (gs ++ gs') w = b1 gs' (b1 gs w):=by
  simp [b1,List.foldl_append]
theorem b61 (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool,b1 gs w = w ++ t /\ t.length = gs.length:=by
  induction gs with
  | nil => intro w; exact ⟨[],by simp [b1],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
    have : b1 (g :: gs) w
        = b1 gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
    rw [this,ht]; simp
theorem b28 (gs : List Gate) (w : List Bool) :
    (b1 gs w).length = w.length + gs.length:=by
  obtain ⟨t,ht,hl⟩:=b61 gs w
  rw [ht]; simp [hl]
theorem b41 (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (b1 gs w).getD i false = w.getD i false:=by
  obtain ⟨t,ht,_⟩:=b61 gs w
  rw [ht,List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length ≤ 2
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
theorem b33 {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j≠L.length) :
    (L ++ [S]).getD j d = L.getD j d:=by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem b50 {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S:=by
  simp
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def NOk (g : Gate) : Prop:=Ok g /\ (g.op = GateOp.not -> g.inputs.length ≤ 1)
abbrev Stat:=Sum Bool ℕ
def Stat.val (w : List Bool) : Stat -> Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def Stat.Valid (m : ℕ) : Stat -> Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m
def b162 (m : ℕ) : List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl true)
  | Sum.inl c :: _ => (none,Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def b145 (m : ℕ) : List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl true)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def simpOr (m : ℕ) : List Stat -> Option Gate × Stat
  | [] => (none,Sum.inl false)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def b12 (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => b145 m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => b162 m ins
  | _ => (none,Sum.inl false)
theorem b172 (op : GateOp) (hop : op = GateOp.and \/ op = GateOp.or \/ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins,s.Valid w.length) :
    ((b12 op w.length ins).2).Valid (w.length + (b12 op w.length ins).1.toList.length) ∧
    ((b12 op w.length ins).2).val (b1 (b12 op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)):=by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [b12,b145,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [b12,b145,Stat.Valid,Stat.val,GateOp.eval,b1]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [b12,b145,Stat.Valid,Stat.val,GateOp.eval,b1]
    · simp at hlen
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    · simp [b12,simpOr,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [b12,simpOr,Stat.Valid,Stat.val,GateOp.eval,b1]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [b12,simpOr,Stat.Valid,Stat.val,GateOp.eval,b1]
    · simp at hlen
  · rcases ins with _ | ⟨a,l⟩
    · simp [b12,b162,Stat.Valid,Stat.val,GateOp.eval]
    · cases a <;> simp_all [b12,b162,Stat.Valid,Stat.val,GateOp.eval,b1]
def b43 (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(b12 g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (b12 g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (b43 n) acc
theorem b140 {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S:=by
  subst h; simp
theorem b156 {α : Type} (o : Option α) : o.toList.length ≤ 1:=by
  cases o <;> simp
theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length:=by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1:=ih (b43 n acc g)
    have h2 : (b43 n acc g).2.length ≤ acc.2.length + 1:=by
      simp only [b43,List.length_append]
      have:=b156 (b12 g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (b43 n acc g):=rfl
    rw [h3,List.length_cons]; omega
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat,s.Valid m -> s.Valid m'
  | Sum.inl _,_ => trivial
  | Sum.inr _,hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat,s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _,_ => rfl
  | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length /\ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (b1 acc.2 y) = w.getD i false
theorem b139 (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) -> Inv n y w acc →
      Inv n y (b1 gs w) (elim n gs acc):=by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (b43 n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl,hi⟩:=h
    set w':=b1 acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length:=by rw [hw',b28,hy]
    set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok:=hok g List.mem_cons_self
    have hs:=b172 g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r:=b12 g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false:=by
      rw [hins,List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : b1 (acc.2 ++ r.1.toList) y = b1 r.1.toList w':=by
      rw [b42]
    obtain ⟨t,ht,htl⟩:=b61 r.1.toList w'
    refine ⟨by simp [b43,hl],?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (b1 (acc.2 ++ r.1.toList) y) = _
    rw [hnew,List.length_append,← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [b50,hl,b50]
      exact ⟨hs.1,by rw [hs.2,hvals]⟩
    · rw [b33 _ _ _ _ hil,b33 _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1,?_⟩
      rw [ht,Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
def b47 (test : GateOp -> Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)
lemma b157 (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (b12 op m ins).1,g.op = op:=by
  intro g hg
  cases op <;> simp only [b12] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [b145] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
      simp [b162] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg
lemma b174 (test : GateOp -> Bool) (gs hs : List Gate) :
    b47 test (gs ++ hs) = b47 test gs + b47 test hs:=by
  simp [b47]
lemma b151 (test : GateOp -> Bool) (g : Gate) (gs : List Gate) :
    b47 test (g :: gs) = b47 test gs + (if test g.op then 1 else 0):=by
  by_cases h : test g.op <;> simp [b47,h]
lemma b133 (test : GateOp -> Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    b47 test (b12 op m ins).1.toList ≤ (if test op then 1 else 0):=by
  cases h : (b12 op m ins).1 with
  | none => simp [b47]
  | some g =>
    have hg : g ∈ (b12 op m ins).1:=by simp [h]
    have he:=b157 op m ins g hg
    simp [h,b151,b47,he]
lemma b167 (test : GateOp -> Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      b47 test (elim n gs acc).2 ≤ b47 test acc.2 + b47 test gs:=by
  induction gs with
  | nil => intro acc; simp [elim,b47]
  | cons g gs ih =>
    intro acc
    change b47 test (elim n gs (b43 n acc g)).2 ≤ _
    apply (ih (b43 n acc g)).trans
    simp only [b43,b174,b151]
    have hb:=b133 test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    omega
def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))
lemma b65 (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  b167 (fun op => !(isNotGate op)) n gs acc
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def b101 (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not /\ ∃ j,j < m /\ g.inputs = [j]) ∨
  ((g.op = GateOp.and \/ g.op = GateOp.or) /\ ∃ j k,j < m /\ k < m /\ g.inputs = [j,k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate),gs[p]? = some g -> b101 (m + p) g
theorem b101.nok {m : ℕ} {g : Gate} (h : b101 m g) : NOk g:=by
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
theorem b101.lt {m : ℕ} {g : Gate} (h : b101 m g) : ∀ a ∈ g.inputs,a < m:=by
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
theorem b188 (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs,NOk g:=by
  intro g hg
  obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
theorem b173 (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins,s.Valid m) :
    ∀ g ∈ (b12 op m ins).1,b101 m g:=by
  intro g hg
  cases op <;> simp only [b12] at hg
  · rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [b145] at hg
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
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [b162] at hg
    subst hg
    refine Or.inl ⟨rfl,_,?_,rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
theorem b171? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 /\ a ∈ o:=by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
theorem b150 (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),(∀ g ∈ gs,Ok g) -> Inv n y w acc →
      CleanL n acc.2 -> CleanL n (elim n gs acc).2:=by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (b1 [g] w) (b43 n acc g) :=
      b139 n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (b43 n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (b12 g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g':=hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0,hmem⟩:=b171? _ _ _ hp'
      have hpl : p = acc.2.length:=by omega
      rw [hpl]
      exact b173 _ _ _ (fun s hs => by
        obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def b9 (n : ℕ) : List Stat:=List.ofFn (fun i : Fin n => Sum.inr i)
theorem inv_id (n : ℕ) (y : Fin n -> Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (b9 n,[]):=by
  refine ⟨by simp [b9],?_⟩
  intro i
  by_cases hlt : i < n
  · simp [b9,hlt,Stat.Valid,Stat.val,b1]
  · rw [List.getD_eq_default _ _ (by simp [b9]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩
theorem b165 {α : Type} (m : ℕ) (F : Fin m -> α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j:=by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α),l[p]? = some g →
    ∃ pre post,l = pre ++ g :: post /\ pre.length = p:=by
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
theorem b190 (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs,k ∉ g.inputs) -> w.length = w'.length →
    (∀ j,j≠k -> w.getD j false = w'.getD j false) →
    ∀ j,j≠k -> (b1 gs w).getD j false = (b1 gs w').getD j false:=by
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
    · rw [hjl,b50,hl,b50,e]
    · rw [b33 _ _ _ _ hjl,b33 _ _ _ _ (by omega)]
      exact h j hj
end CircuitProof
namespace CircuitProof
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k -> Bool) (j : ℕ) : Bool :=
  (b1 gs (List.ofFn u)).getD j false
theorem b69 {k : ℕ} (gs : List Gate) (u : Fin k -> Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j,h⟩:=by
  unfold vl
  rw [b41 gs _ j (by simpa using h)]
  exact b165 k u false ⟨j,h⟩
theorem b104 {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k -> Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)):=by
  have hlt:=(hcl p g hp).lt
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp
  have hwl : (b1 pre (List.ofFn u)).length = k + pre.length:=by
    rw [b28]; simp
  have e : b1 (pre ++ g :: post) (List.ofFn u)
      = b1 post (b1 pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (b1 pre (List.ofFn u)).getD i false)]):=by
    rw [b42]; rfl
  have full : ∀ j,j < k + pre.length →
      (b1 (pre ++ g :: post) (List.ofFn u)).getD j false
        = (b1 pre (List.ofFn u)).getD j false:=by
    intro j hj
    rw [e,b41 _ _ j (by simp [hwl]; omega),b33 _ _ _ _ (by omega)]
  have top : (b1 (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (b1 pre (List.ofFn u)).getD i false):=by
    rw [e,b41 _ _ _ (by simp [hwl]),b140 _ _ _ _ hwl]
  show (b1 (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (b1 (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k -> Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs,vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p):=by
  rw [b104 gs hcl u p g hp,b104 gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k -> Bool,S.Valid (k + (elim k pre (b9 k,[])).2.length) ∧
      S.val (b1 (elim k pre (b9 k,[])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k -> Bool,vl (pre ++ g :: post) y o≠vl (pre ++ g :: post) y' o) :
    ∃ gs' o',CleanL k gs' /\ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k -> Bool,vl gs' y o' = vl (pre ++ g :: post) y o:=by
  have hok : ∀ g' ∈ pre ++ g :: post,Ok g':=fun g' hg' => (b188 _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre,Ok g':=fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post,Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k -> Bool,Inv k (List.ofFn y) (b1 pre (List.ofFn y))
      (elim k pre (b9 k,[])) :=
    fun y => b139 k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k -> Bool,(b1 pre (List.ofFn y)).length = k + pre.length:=by
    intro y; rw [b28]; simp
  have hfull : ∀ y : Fin k -> Bool,b1 (pre ++ g :: post) (List.ofFn y)
      = b1 post (b1 pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false)]):=by
    intro y; rw [b42]; rfl
  have hgv : ∀ y : Fin k -> Bool,vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false):=by
    intro y
    show (b1 (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull,b41 _ _ _ (by simp [hwl y]),b140 _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k -> Bool,Inv k (List.ofFn y)
      (b1 pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (b1 pre (List.ofFn y)).getD a false)])
      ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2):=by
    intro y
    obtain ⟨hl,hi⟩:=inv1 y
    refine ⟨by simp [hl],?_⟩
    intro a
    show (((elim k pre (b9 k,[])).1 ++ [S]).getD a (Sum.inl false)).Valid
        (k + (elim k pre (b9 k,[])).2.length) ∧
      (((elim k pre (b9 k,[])).1 ++ [S]).getD a (Sum.inl false)).val
        (b1 (elim k pre (b9 k,[])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (b9 k,[])).1.length
    · rw [hal,b50,hl,b50]
      exact ⟨(hS y).1,by rw [(hS y).2,hgv]⟩
    · rw [b33 _ _ _ _ hal,b33 _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k -> Bool,Inv k (List.ofFn y)
      (b1 (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2)):=by
    intro y
    rw [hfull]
    exact b139 k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (b9 k,[])).2 :=
    b150 k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (b9 k,[])).1 ++ [S],(elim k pre (b9 k,[])).2)).2 :=
    b150 k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
      (elim k pre (b9 k,[])).2)).2.length + 1 ≤ (pre ++ g :: post).length:=by
    have h1 : (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
        (elim k pre (b9 k,[])).2)).2.length
        ≤ (elim k pre (b9 k,[])).2.length + post.length:=elim_len k post _
    have h2 : (elim k pre (b9 k,[])).2.length ≤ 0 + pre.length :=
      elim_len k pre (b9 k,[])
    simp only [List.length_append,List.length_cons]
    omega
  have hval : ∀ y : Fin k -> Bool,
      ((elim k post ((elim k pre (b9 k,[])).1 ++ [S],
        (elim k pre (b9 k,[])).2)).1.getD o (Sum.inl false)).val
        (b1 (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
          (elim k pre (b9 k,[])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o:=fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (b9 k,[])).1 ++ [S],
      (elim k pre (b9 k,[])).2)).1.getD o (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y,y',hne⟩:=hnc
    apply hne
    rw [← hval y,← hval y',hst]
    rfl
  | inr j =>
    refine ⟨_,j,hc3,hlen,?_,?_⟩
    · exact (b65 k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using b65 k pre (b9 k,[])) _)
    · intro y
      have h:=hval y
      rw [hst] at h
      exact h
theorem b177 (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k -> Bool,vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k -> Bool,vl gs y o≠vl gs y' o) :
    ∃ gs' o',CleanL k gs' /\ gs'.length + 1 ≤ gs.length /\ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k -> Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]? = some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl,Nat.sub_self,List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post:=by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (b9 k,[])).1.getD j (Sum.inl false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre,Ok g' :=
    fun g' h => (b188 _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1:=b139 k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1,?_⟩
  rw [(inv1.2 j).2,heq y]
  show (b1 pre (List.ofFn y)).getD j false
    = (b1 (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [b42,b41 (g :: post) (b1 pre (List.ofFn y)) j
    (by rw [b28]; simp; omega)]
end CircuitProof
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
def avoid {W : Type} (edge : W -> W -> Prop) (cut : W) (a b : W) : Prop :=
  edge a b /\ a≠cut /\ b≠cut
theorem b147 {W : Type} (rank : W -> Nat) (input : W -> Prop)
    (edge : W -> W -> Prop) (cut : W) (x y : W -> Bool)
    (order : ∀ a b,edge a b -> rank a < rank b)
    (localStep : ∀ b,¬ input b -> x b≠y b -> ∃ a,edge a b /\ x a≠y a)
    (sameCut : x cut = y cut) {out : W} (different : x out≠y out) :
    ∃ a,input a /\ x a≠y a /\ Relation.ReflTransGen (avoid edge cut) a out:=by
  classical
  have track : ∀ k b,rank b = k -> x b≠y b →
      ∃ a,input a /\ x a≠y a /\ Relation.ReflTransGen (avoid edge cut) a b:=by
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
theorem b180 {W : Type} (rank : W -> Nat) (input : W -> Prop)
    (edge : W -> W -> Prop) (cut out : W) (x y : W -> Bool)
    (order : ∀ a b,edge a b -> rank a < rank b)
    (localStep : ∀ b,¬ input b -> x b≠y b -> ∃ a,edge a b /\ x a≠y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a,input a -> x a≠y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out:=by
  by_contra different
  obtain ⟨a,ha,da,reaches⟩:=b147 rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches
theorem b184 {A : Type} (w f : A -> Bool)
    (h : ∀ x y,w x = w y -> f x = f y) :
    ∃ outer : Bool -> Bool,∀ x,outer (w x) = f x:=by
  classical
  let outer (b : Bool):=if hb : ∃ a,w a = b then f (Classical.choose hb) else false
  refine ⟨outer,fun x => ?_⟩
  have hx : ∃ a,w a = w x:=⟨x,rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)
def b8 {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)
def b5 {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate),gs[p]? = some g /\ b.val = n + p /\ a.val ∈ g.inputs
theorem b15 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : b5 gs a b) : a.val < b.val:=by
  obtain ⟨p,g,hpg,hb,ha⟩:=edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha
private theorem b166 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n -> Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val≠vl gs y b.val) :
    ∃ a : Fin (n + gs.length),b5 gs a b /\ vl gs x a.val≠vl gs y a.val:=by
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
theorem b59 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n -> Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n,x i≠y i →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs i) out) :
    vl gs x out.val = vl gs y out.val:=by
  apply b180 Fin.val (fun v => v.val < n) (b5 gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => b15 hcl e
  · exact b166 hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n:=⟨a.val,ha⟩
    have sameWire : b8 gs i = a:=Fin.ext rfl
    have di : x i≠y i:=by
      rw [b69 gs x a.val ha,b69 gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di
theorem b135 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n -> Prop) (base : Fin n -> Bool)
    (blocked : ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs i) out) :
    ∃ outer : Bool -> Bool,∀ x : Fin n -> Bool,(∀ i,¬ group i -> x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val:=by
  let Fiber:={x : Fin n -> Bool // ∀ i,¬ group i -> x i = base i}
  obtain ⟨outer,ho⟩:=b184
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply b59 hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer,fun x agrees => ho ⟨x,agrees⟩⟩
end PetersenCutTrace
namespace CircuitProof.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
def Dep {m : ℕ} (f : (Fin m -> Bool) -> Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m -> Bool,f (Function.update x p (!x p))≠f x
def Least (m : ℕ) (f : (Fin m -> Bool) -> Bool) (gs : List Gate) (o : ℕ) : Prop :=
  CleanL m gs /\ (∀ x : Fin m -> Bool,vl gs x o = f x) ∧
    ∀ (gs' : List Gate) (o' : ℕ),CleanL m gs' -> (∀ x : Fin m -> Bool,vl gs' x o' = f x) →
    nonNotCount gs' ≤ nonNotCount gs -> gs.length ≤ gs'.length
def Least.hcl {m f gs o} (h : Least m f gs o):=h.1
def Least.hev {m f gs o} (h : Least m f gs o):=h.2.1
def Least.hmin {m f gs o} (h : Least m f gs o):=h.2.2
def Reads (gs : List Gate) (p w : ℕ) : Prop:=∃ g,gs[p]? = some g /\ w ∈ g.inputs
theorem dep_nc {m : ℕ} {f : (Fin m -> Bool) -> Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m -> Bool,f x≠f y:=by
  obtain ⟨x,hx⟩:=h
  exact ⟨_,_,hx⟩
theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q:=by
  obtain ⟨g,hg,hw⟩:=h
  exact (hcl q g hg).lt w hw
theorem b136 {k : ℕ} (gs : List Gate) (u : Fin k -> Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false:=by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [b28]; simp; omega)
theorem b149 {n : ℕ} {f : (Fin n -> Bool) -> Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n -> Bool,C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y,f x≠f y) :
    ∃ gs o,CleanL n gs /\ nonNotCount gs ≤ nonNotCount C.gates /\ ∀ x,vl gs x o = f x:=by
  have hok : ∀ g ∈ C.gates,Ok g:=hfan
  set acc:=elim n C.gates (b9 n,[]) with hacc
  have hinv : ∀ y : Fin n -> Bool,
      Inv n (List.ofFn y) (b1 C.gates (List.ofFn y)) acc :=
    fun y => b139 n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n -> Bool,
      (acc.1.getD C.output (Sum.inl false)).val (b1 acc.2 (List.ofFn y)) = f y:=by
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
    · exact b150 n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount,hacc] using b65 n C.gates (b9 n,[])
    · intro y
      simpa only [hst,Stat.val,vl] using hval y
theorem b146 {n : ℕ} {f : (Fin n -> Bool) -> Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n -> Bool,C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y,f x≠f y) :
    ∃ gs o,Least n f gs o /\ nonNotCount gs ≤ nonNotCount C.gates:=by
  classical
  let admissible (t : ℕ):=∃ gs o,CleanL n gs /\ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x,vl gs x o = f x) /\ gs.length = t
  obtain ⟨gs,o,clean,count,he⟩:=b149 C hfan hev hnc
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
    (hnc : ∃ y y' : Fin k -> Bool,vl gs y o≠vl gs y' o) :
    ∃ gs' o',CleanL k gs' /\ gs'.length + 1 ≤ gs.length /\ nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k -> Bool,vl gs' y o' = vl gs y o:=by
  obtain ⟨g,hg⟩ : ∃ g,gs[p]? = some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p:=by
    rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩ <;> omega
  let g0 : Gate:=⟨GateOp.and,[0,0]⟩
  let gs':=gs.set p g0
  have hlen : gs'.length = gs.length:=by simp [gs']
  have hget_p : gs'[p]? = some g0:=by simp [gs',hp]
  have hget_ne : ∀ r,r≠p -> gs'[r]? = gs[r]?:=by
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
  have hagree : ∀ y : Fin k -> Bool,∀ w,w≠k + p -> vl gs' y w = vl gs y w:=by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [b69 gs' y w hwk,b69 gs y w hwk]
      · obtain ⟨r,rfl⟩ : ∃ r,w = k + r:=⟨w - k,by omega⟩
        have hrp : r≠p:=fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr
          rw [b136 gs' y _ (by omega),b136 gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g':=by rw [hget_ne r hrp]; exact hr
          rw [b104 gs' hcl' y r g' hr',b104 gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt:=(hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g',hr,e ▸ ha⟩)
  have halias : ∀ y : Fin k -> Bool,vl gs' y (k + p) = vl gs' y 0:=by
    intro y
    rw [b104 gs' hcl' y p g0 hget_p]
    simp [g0,GateOp.eval]
  have hnc' : ∃ y y' : Fin k -> Bool,vl gs' y o≠vl gs' y' o:=by
    obtain ⟨y,y',h⟩:=hnc
    exact ⟨y,y',by rw [hagree y o ho,hagree y' o ho]; exact h⟩
  obtain ⟨gs'',o'',hc'',hl'',hcost,he''⟩ :=
    b177 k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs:=by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'',o'',hc'',by omega,hcost.trans hkeep,fun y => by rw [he'' y,hagree y o ho]⟩
section LocalSection1
variable {m : ℕ} {f : (Fin m -> Bool) -> Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) :
    ∃ y y' : Fin m -> Bool,vl gs y o≠vl gs y' o:=by
  obtain ⟨x,y,h⟩:=hnc
  exact ⟨x,y,by rw [L.hev,L.hev]; exact h⟩
theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m -> Bool,vl gs u (m + p) = vl gs u j:=by
  intro hall
  obtain ⟨gs',o',hc',hl',hcost,he'⟩:=b177 m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have:=L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega
theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) (p : ℕ)
    (hp : p < gs.length) (ho : o≠m + p) : ∃ q,p < q /\ Reads gs q (m + p):=by
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
    (hnc : ∀ b : Bool,∃ x y : Fin m -> Bool,
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
    rw [← L.hev,← L.hev,e,b69 gs _ i i.isLt,b69 gs _ i i.isLt]
    simp
  obtain ⟨x,hx⟩:=hd
  apply hx
  rw [← L.hev,← L.hev]
  refine b190 i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j,hjm⟩ from b165 m _ false ⟨j,hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j,hjm⟩ from b165 m x false ⟨j,hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
end LocalSection1
end CircuitProof.Readers
namespace CircuitProof.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof
open CircuitProof.Readers
theorem pq2f_nodup {m : ℕ} {f : (Fin m -> Bool) -> Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m -> Bool,f x≠f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and \/ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a,b]) : a≠b:=by
  rintro rfl
  have hcl:=L.hcl p g hg
  have hlt : a < m + p:=by
    rcases hcl with ⟨h1,j,_,h2⟩ | ⟨h1,j,k,hj,hk,h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [b104 gs L.hcl u p g hg,hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
end CircuitProof.RunAsm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm
theorem b164 {n out : Nat} {f : (Fin n -> Bool) -> Bool} {gs : List Gate}
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
theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n -> Bool) -> Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y,f x≠f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup:=by
  obtain ⟨slot,atSlot⟩:=List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [args]
  · have distinct:=pq2f_nodup least nonconstant atSlot ops args
    simp [args,distinct]
theorem b79 {n out : Nat} {gs : List Gate}
    {f : (Fin n -> Bool) -> Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val≠out) :
    ∃ (p : Nat) (g : Gate),gs[p]? = some g /\ w.val ∈ g.inputs /\ n + p < n + gs.length:=by
  obtain ⟨p,g,hit,reads⟩:=b164 least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound:=(List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p,g,hit,reads,by omega⟩
namespace PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers
def b10 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
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
theorem b45 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (b10 clean b).map Fin.val =
      (gs[b.val - n]'(by have:=b.isLt; omega)).inputs:=by
  simp [b10,internal,List.map_map,Function.comp_def]
theorem b111 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : b10 clean b = []:=by
  simp [b10,show ¬ n ≤ b.val by omega]
theorem b116 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (b10 clean b).map Fin.val = g.inputs:=by
  have isGate : n ≤ b.val:=by omega
  have which : b.val - n = p:=by omega
  have located:=(List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which,located] using b45 clean b isGate
theorem b158 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ b10 clean b↔b5 gs a b:=by
  by_cases internal : n ≤ b.val
  · let slot:=b.val - n
    have hs : slot < gs.length:=by have:=b.isLt; dsimp [slot]; omega
    let g:=gs[slot]'hs
    have wire : b.val = n + slot:=by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g:=List.getElem?_eq_getElem hs
    have valList : (b10 clean b).map Fin.val = g.inputs :=
      b45 clean b internal
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
  · have empty : b10 clean b = []:=by simp [b10,internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot,g,_,wire,_⟩
      omega
theorem b137 {n out : Nat} {gs : List Gate} {f : (Fin n -> Bool) -> Bool}
    (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y) (b : Fin (n + gs.length)) :
    (b10 least.hcl b).Nodup:=by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [b45 least.hcl b internal]
    exact PEqualNP.Outside.L_meta_4759.Binary.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have:=b.isLt; omega))
  · simp [b10,internal]
end PetersenCutTrace
namespace PetersenScratch
open PEqualNP.MetaComplexity
def b0 {n : ℕ} (i : Fin n) : DMFormula n -> ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => b0 i p + b0 i q
  | .or p q => b0 i p + b0 i q
def b21 {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < b0 i p \/ 0 < b0 j p
def b11 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k
def b4 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool) (p : DMFormula n) :
    Bool -> Bool -> Bool :=
  fun a b => p.eval (b11 i j base a b)
def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a&&b else a||b
noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool -> Bool -> Bool) : Bool -> Bool -> Bool:=by
  classical
  exact if b21 i j p then
    if b21 i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q
noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n -> Bool -> Bool -> Bool
  | .lit k sign => fun a b =>
    let bit:=if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)
private theorem b176 {n : ℕ} (p : DMFormula n) {x y : Fin n -> Bool}
    (h : ∀ k,0 < b0 k p -> x k = y k) : p.eval x = p.eval y:=by
  induction p with
  | lit k s =>
    have e:=h k (by simp [b0])
    simp [DMFormula.eval,e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [b0]; omega)),
      ihq (fun k hk => h k (by simp only [b0]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [b0]; omega)),
      ihq (fun k hk => h k (by simp only [b0]; omega))]
private theorem b107 {n : ℕ} {i j : Fin n} {base : Fin n -> Bool} {p : DMFormula n}
    (h : b0 i p = 0) (a a' b : Bool) :
    b4 i j base p a b = b4 i j base p a' b:=by
  apply b176
  intro k hk
  have ne : k≠i:=by rintro rfl; omega
  simp [b11,ne]
private theorem b125 {n : ℕ} {i j : Fin n} {base : Fin n -> Bool} {p : DMFormula n}
    (h : b0 j p = 0) (a b b' : Bool) :
    b4 i j base p a b = b4 i j base p a b':=by
  apply b176
  intro k hk
  have ne : k≠j:=by rintro rfl; omega
  simp [b11,ne]
def b39 (f : Bool -> Bool -> Bool) : Prop :=
  ∃ b,f false b≠f true b
private theorem b154 {op : Bool -> Bool -> Bool} {P Q : Bool -> Bool -> Bool}
    (h : b39 fun a b => op (P a b) (Q a b))
    (hQ : ∀ b,Q false b = Q true b) : b39 P:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp,hQ])⟩
private theorem b144 {op : Bool -> Bool -> Bool} {P Q : Bool -> Bool -> Bool}
    (h : b39 fun a b => op (P a b) (Q a b))
    (hP : ∀ b,P false b = P true b) : b39 Q:=by
  obtain ⟨b,hb⟩:=h
  exact ⟨b,fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq,hP])⟩
private theorem b73 {n : ℕ} {i j : Fin n} {base : Fin n -> Bool} {p : DMFormula n}
    (h : ¬ b21 i j p) (a b : Bool) :
    b4 i j base p a b = b4 i j base p false false:=by
  have hi : b0 i p = 0:=by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : b0 j p = 0:=by
    by_contra e
    exact h (Or.inr (by omega))
  exact (b107 hi a false b).trans (b125 hj false b false)
private theorem b138 (conj c : Bool) (P : Bool -> Bool -> Bool)
    (h : ∃ a b a' b',binOp conj (P a b) c≠binOp conj (P a' b') c) :
    ∀ a b,binOp conj (P a b) c = P a b:=by
  cases conj <;> cases c <;> simp [binOp] at h ⊢
private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a:=by
  cases conj <;> cases a <;> cases b <;> rfl
private theorem b132 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : b0 i p + b0 i q ≤ 1)
    (hj : b0 j p + b0 j q ≤ 1)
    (present : b21 i j p \/ b21 i j q)
    (dep_i : 0 < b0 i p + b0 i q →
      b39 fun a b => binOp conj (b4 i j base p a b) (b4 i j base q a b))
    (dep_j : 0 < b0 j p + b0 j q →
      b39 fun b a => binOp conj (b4 i j base p a b) (b4 i j base q a b))
    (ihp : b0 i p ≤ 1 -> b0 j p ≤ 1 -> b21 i j p →
      (0 < b0 i p -> b39 (b4 i j base p)) →
      (0 < b0 j p -> b39 fun b a => b4 i j base p a b) →
      ∀ a b,b4 i j base p a b = pairKernel i j p a b)
    (ihq : b0 i q ≤ 1 -> b0 j q ≤ 1 -> b21 i j q →
      (0 < b0 i q -> b39 (b4 i j base q)) →
      (0 < b0 j q -> b39 fun b a => b4 i j base q a b) →
      ∀ a b,b4 i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (b4 i j base p a b) (b4 i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b:=by
  classical
  have pl : b21 i j p -> ∀ a b,b4 i j base p a b = pairKernel i j p a b:=by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact b154 (dep_i (by omega)) (fun b => b107 (by omega) false true b)
    · intro h
      exact b154 (dep_j (by omega)) (fun a => b125 (by omega) a false true)
  have ql : b21 i j q -> ∀ a b,b4 i j base q a b = pairKernel i j q a b:=by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact b144 (dep_i (by omega)) (fun b => b107 (by omega) false true b)
    · intro h
      exact b144 (dep_j (by omega)) (fun a => b125 (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (b4 i j base p a b) (b4 i j base q a b) ≠
        binOp conj (b4 i j base p a' b') (b4 i j base q a' b'):=by
    unfold b21 at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
    · obtain ⟨b,h⟩:=dep_i (by omega)
      exact ⟨false,b,true,b,h⟩
    · obtain ⟨a,h⟩:=dep_j (by omega)
      exact ⟨a,false,a,true,h⟩
  by_cases hp : b21 i j p
  · by_cases hq : b21 i j q
    · simp [combine,hp,hq,pl hp,ql hq]
    · rw [b73 hq a b]
      have hn:=nonconst
      simp_rw [b73 hq] at hn
      rw [b138 conj _ _ hn a b,pl hp]
      simp [combine,hp,hq]
  · have hq:=present.resolve_left hp
    rw [b73 hp a b,bin_comm]
    have hn:=nonconst
    simp_rw [b73 hp,bin_comm conj (b4 i j base p false false)] at hn
    rw [b138 conj _ _ hn a b,ql hq]
    simp [combine,hp]
private theorem b161 {n : ℕ} (i j : Fin n) (base : Fin n -> Bool) (p : DMFormula n)
    (hi : b0 i p ≤ 1) (hj : b0 j p ≤ 1) (present : b21 i j p)
    (dep_i : 0 < b0 i p -> b39 (b4 i j base p))
    (dep_j : 0 < b0 j p -> b39 fun b a => b4 i j base p a b) :
    ∀ a b,b4 i j base p a b = pairKernel i j p a b:=by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [b4,pairKernel,DMFormula.eval,b11,hki]
    · have hkj : k = j:=by
        by_contra h
        simp [b21,b0,hki,h] at present
      simp [b4,pairKernel,DMFormula.eval,b11,hkj]
  | and p q ihp ihq =>
    have present' : b21 i j p \/ b21 i j q:=by
      unfold b21 at *
      simp only [b0] at present
      omega
    exact b132 i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : b21 i j p \/ b21 i j q:=by
      unfold b21 at *
      simp only [b0] at present
      omega
    exact b132 i j base false p q hi hj present' dep_i dep_j ihp ihq
theorem b129 {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : b0 i p ≤ 1) (hj : b0 j p ≤ 1)
    (baseA baseO : Fin n -> Bool) (outerA outerO : Bool -> Bool)
    (hA : ∀ a b,outerA (b4 i j baseA p a b) = (a&&b))
    (hO : ∀ a b,outerO (b4 i j baseO p a b) = (a||b)) : False:=by
  have depAi : b39 (b4 i j baseA p):=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depAj : b39 fun b a => b4 i j baseA p a b:=by
    refine ⟨true,fun h => ?_⟩
    have e:=congrArg outerA h
    rw [hA,hA] at e
    cases e
  have depOi : b39 (b4 i j baseO p):=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have depOj : b39 fun b a => b4 i j baseO p a b:=by
    refine ⟨false,fun h => ?_⟩
    have e:=congrArg outerO h
    rw [hO,hO] at e
    cases e
  have present : b21 i j p:=by
    left
    by_contra! h
    obtain ⟨b,hb⟩:=depAi
    exact hb (b107 (by omega) false true b)
  have stableA:=b161 i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO:=b161 i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
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
noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n -> Bool) : Bool:=by
  classical
  exact decide (∃ u v,G.Adj u v /\ x u = true /\ x v = true)
private theorem b57 {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n -> Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true:=by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u,v,h,hu,hv⟩
private theorem b22 {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n -> Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w,x w = true -> w = u \/ w = v) :
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
private theorem b179 {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (b11 i j (fun _ => false) a b) = (a&&b):=by
  cases a <;> cases b
  · apply b22 (u:=i) (v:=i) G.irrefl
    intro k hk
    simp [b11] at hk
  · apply b22 (u:=j) (v:=j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [b11,hki,hkj] at hk ⊢
  · apply b22 (u:=i) (v:=i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [b11,hki,hkj] at hk ⊢
    assumption
  · exact b57 h (by simp [b11]) (by simp [b11,h.ne.symm])
private theorem b186 {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i≠j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (b11 i j (fun k => decide (k = u \/ k = v)) a b) = (a||b):=by
  have hu : b11 i j (fun k => decide (k = u \/ k = v)) a b u = true:=by
    simp [b11,hiu.ne.symm,huj]
  have hv : b11 i j (fun k => decide (k = u \/ k = v)) a b v = true:=by
    simp [b11,hvi,hjv.ne.symm]
  cases a <;> cases b
  · apply b22 huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [b11,hki,hkj] at hk
    exact hk
  · exact b57 hjv (by simp [b11,hij.symm]) hv
  · exact b57 hiu (by simp [b11]) hu
  · exact b57 hiu (by simp [b11]) hu
theorem b113 {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : b0 i p ≤ 1) (hj : b0 j p ≤ 1)
    (factors : ∀ base : Fin n -> Bool,∃ outer : Bool -> Bool,∀ a b,
      outer (b4 i j base p a b) = edgeValue G (b11 i j base a b)) : False:=by
  obtain ⟨outerA,ha⟩:=factors (fun _ => false)
  obtain ⟨outerO,ho⟩:=factors (fun k => decide (k = u \/ k = v))
  exact b129 i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (b179 hij a b))
    (fun a b => (ho a b).trans (b186 hij.ne hiu hjv huj hvi huv a b))
end PetersenScratch
namespace PetersenCutFormula
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch
def b18 {n : Nat} : DMFormula n -> DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (b18 a) (b18 b)
  | .or a b => .and (b18 a) (b18 b)
theorem b163 {n : Nat} (p : DMFormula n) (x : Fin n -> Bool) :
    (b18 p).eval x = !(p.eval x):=by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [b18,DMFormula.eval,e]
  | and a b iha ihb =>
    simp only [b18,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [b18,DMFormula.eval,iha,ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
theorem b112 {n : Nat} (i : Fin n) (p : DMFormula n) :
    b0 i (b18 p) = b0 i p:=by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [b18,b0,iha,ihb]
  | or a b iha ihb => simp [b18,b0,iha,ihb]
def b2 {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w,hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op,g.inputs with
      | .not,[a] =>
        if _ha : a < w then b18 (b2 fallback gs a) else .lit fallback true
      | .and,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .and (b2 fallback gs a) (b2 fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or,[a,b] =>
        if _ha : a < w then
          if _hb : b < w then .or (b2 fallback gs a) (b2 fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _,_ => .lit fallback true
termination_by w
decreasing_by all_goals assumption
theorem b94 {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    b2 fallback gs i.val = .lit i true:=by
  rw [b2]
  simp [i.isLt]
private theorem b114 {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    b2 fallback gs (n + p) = b18 (b2 fallback gs a):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [b2]
  simp [hn,hp,hg,op,inputs,ha]
private theorem b115 {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a,b]) (ha : a < n + p) (hb : b < n + p) :
    b2 fallback gs (n + p) = .and (b2 fallback gs a) (b2 fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [b2]
  simp [hn,hp,hg,op,inputs,ha,hb]
private theorem b131 {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a,b]) (ha : a < n + p) (hb : b < n + p) :
    b2 fallback gs (n + p) = .or (b2 fallback gs a) (b2 fallback gs b):=by
  have hn : ¬ n + p < n:=by omega
  have hp : n + p - n = p:=by omega
  conv_lhs => rw [b2]
  simp [hn,hp,hg,op,inputs,ha,hb]
theorem b155 {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n -> Bool) (w : Nat) (hw : w < n + gs.length) :
    (b2 fallback gs w).eval x = vl gs x w:=by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [b94 fallback gs ⟨w,hi⟩,b69 gs x w hi]
      rfl
    · obtain ⟨p,rfl⟩ : ∃ p,w = n + p:=⟨w - n,by omega⟩
      have hp : p < gs.length:=by omega
      let g:=gs[p]
      have hg : gs[p]? = some g:=List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
      · rw [b114 fallback hg op inputs ha,b163,ih a ha (by omega),
          b104 gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [b115 fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),b104 gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
      · rw [b131 fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega),ih b hb (by omega),b104 gs hcl x p g hg]
        simp [op,inputs,GateOp.eval]
theorem b103 {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    b0 chosen (b2 fallback gs i.val) = if i = chosen then 1 else 0:=by
  rw [b94]
  rfl
theorem b109 {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    b0 chosen (b2 fallback gs (n + p)) =
      (g.inputs.map fun a => b0 chosen (b2 fallback gs a)).sum:=by
  rcases hcl p g hg with ⟨op,a,ha,inputs⟩ | ⟨op | op,a,b,ha,hb,inputs⟩
  · simp [b114 fallback hg op inputs ha,inputs,b112]
  · simp [b115 fallback hg op inputs ha hb,inputs,b0]
  · simp [b131 fallback hg op inputs ha hb,inputs,b0]
theorem b84 {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    b0 chosen (b2 fallback gs b.val) =
      (parents.map fun a => b0 chosen (b2 fallback gs a.val)).sum:=by
  rw [hb,b109 fallback hcl chosen hg,← parentsVal,List.map_map]
  rfl
end PetersenCutFormula
namespace PetersenCutIndependent
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch
theorem b30 {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    b0 chosen (b2 fallback gs a.val) =
      if a = b8 gs chosen then 1 else 0:=by
  let i : Fin n:=⟨a.val,ha⟩
  have e : i = chosen↔a = b8 gs chosen:=by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change b0 chosen (b2 fallback gs i.val) = _
  simp only [b103,e]
theorem b196 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n -> Prop) (base : Fin n -> Bool)
    (controlled : cut = out \/ ∀ i : Fin n,group i →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs i) out) :
    ∃ outer : Bool -> Bool,∀ x : Fin n -> Bool,(∀ i,¬ group i -> x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val:=by
  rcases controlled with rfl | blocked
  · exact ⟨id,fun _ _ => rfl⟩
  · exact b135 hcl cut out group base blocked
theorem b124 {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x,vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u≠j) (hvi : v≠i) (huv : ¬ G.Adj u v)
    (hi : b0 i (b2 i gs cut.val) ≤ 1)
    (hj : b0 j (b2 i gs cut.val) ≤ 1)
    (controlled : cut = out \/ ∀ k : Fin n,(k = i \/ k = j) →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs k) out) : False:=by
  refine b113 G i j u v hij hiu hjv huj hvi huv
    (b2 i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f,hf⟩:=b196 hcl cut out (fun k => k = i \/ k = j) base controlled
  refine ⟨f,fun a b => ?_⟩
  have agree : ∀ k,¬ (k = i \/ k = j) -> b11 i j base a b k = base k:=by
    intro k hk
    simp [b11,show k≠i from fun e => hk (Or.inl e),
      show k≠j from fun e => hk (Or.inr e)]
  unfold b4
  rw [b155 i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)
end PetersenCutIndependent
namespace FirstBranchRoute
open Relation
variable {m : Nat} (reads : Fin m -> Fin m -> Prop) (output : Fin m)
def Branches (v : Fin m) : Prop:=∃ a b,reads v a /\ reads v b /\ a≠b
def Terminal (v : Fin m) : Prop:=v = output \/ Branches reads v
def Follow (v w : Fin m) : Prop:=reads v w /\ ¬ Terminal reads output v
lemma b72 {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b:=by
  by_contra separate
  exact first.2 (Or.inr ⟨a,b,first.1,next.1,separate⟩)
variable (forward : ∀ {v w : Fin m},reads v w -> v < w)
variable (live : ∀ v : Fin m,v≠output -> ∃ w,reads v w)
include forward live in
theorem b81 (v : Fin m) :
    ∃ root : Fin m,Terminal reads output root /\ ReflTransGen (Follow reads output) v root:=by
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
theorem b121 {v a b : Fin m} (terminalA : Terminal reads output a)
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
      have equal:=b72 reads output edge edgeB
      subst nextB
      have increase:=forward edge.1
      have closer : distance next < distance v:=by
        dsimp [distance]
        have bounds:=next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB
noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (b81 reads output forward live v)
theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (b81 reads output forward live v)).1
theorem b127 (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (b81 reads output forward live v)).2
theorem b35 {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  b121 reads output forward (first_stops reads output forward live v) stopped
    (b127 reads output forward live v) ReflTransGen.refl
theorem b108 {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  b121 reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (b127 reads output forward live v)
    ((b127 reads output forward live w).head step)
include forward in
theorem b119 {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w:=by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))
lemma b38 {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem b141 (v : Fin m) : v ≤ first reads output forward live v :=
  b119 reads forward (b38 reads output (b127 reads output forward live v))
theorem b75 {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w /\ first reads output forward live w = first reads output forward live v:=by
  induction route with
  | refl => exact ⟨ReflTransGen.refl,rfl⟩
  | tail _ edge ih =>
    have predecessorBefore:=lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked,label⟩:=ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _:=⟨edge,fun stopped => by
      have self:=b35 reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step,(b108 reads output forward live step).symm.trans label⟩
theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w:=by
  by_contra tooLate
  have earlier:=lt_of_not_ge tooLate
  have same:=(b75 reads output forward live route (le_of_lt earlier)).2
  rw [b35 reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
theorem b168 {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b:=by
  have earlier:=lt_of_lt_of_le (forward edge) bound
  have same:=(b75 reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge,fun stopped => ?_⟩
  rw [b35 reads output forward live stopped] at same
  exact (ne_of_lt earlier) same
def Avoid (cut v w : Fin m) : Prop:=reads v w /\ v≠cut
lemma b123 (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w:=by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1
theorem b122 {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v:=by
  induction route with
  | refl => exact b141 reads output forward live v
  | tail prior edge ih =>
    have label:=(b75 reads output forward live (b123 reads _ prior) ih).2
    have earlier:=lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _:=⟨edge.1,fun terminal => by
      rw [b35 reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same:=(b108 reads output forward live following).symm.trans label
    rw [← same]
    exact b141 reads output forward live _
theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (b122 reads output forward live route)) after
include forward in
theorem b90 {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b:=by
  let distance (w : Fin m):=m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA,stepA,laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next,stepB,later⟩
      · exact bHere
      have equal : next = goal:=b72 reads output stepB edgeA
      subst next
      have increasing:=b119 reads forward (b38 reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB,stepB,laterB⟩
      · subst b
        have equal : nextA = goal:=b72 reads output stepA edgeB
        subst nextA
        have increasing:=b119 reads forward (b38 reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal:=b72 reads output stepA stepB
      subst nextB
      have increase:=forward stepA.1
      have closer : distance nextA < distance source:=by
        dsimp [distance]
        have bounds:=nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB
theorem b89 {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b:=by
  have aBound:=le_trans (le_of_lt (forward edgeA)) bound
  have bBound:=le_trans (le_of_lt (forward edgeB)) bound
  exact b90 reads output forward
    (b75 reads output forward live routeA aBound).1
    (b168 reads output forward live routeA edgeA bound)
    (b75 reads output forward live routeB bBound).1
    (b168 reads output forward live routeB edgeB bound)
lemma b54 {α : Type*} (weight : α -> Nat) (xs : List α)
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
lemma b62 {α : Type*} (weight : α -> Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs,weight a ≤ 1)
    (unique : ∀ a ∈ xs,∀ b ∈ xs,0 < weight a -> 0 < weight b -> a = b) :
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
      obtain ⟨b,hb,hbPos⟩:=b54 weight rest (by omega)
      have equal:=unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero,Nat.add_zero]
    exact small a (by simp)
section Count
variable (parents : Fin m -> List (Fin m))
variable (reads_parent : ∀ a b : Fin m,reads a b↔a ∈ parents b)
variable (weight : Fin m -> Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m,v≠source -> weight v = ((parents v).map weight).sum)
include forward reads_parent other_weight in
theorem b66 {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v:=by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a,member,hp⟩:=b54 weight (parents v) positive
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
    apply b62 weight (parents v) (distinct v)
    · intro a member
      have earlier:=forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact b89 reads output forward live bound
        (b66 reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (b66 reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)
end Count
end FirstBranchRoute
namespace PetersenFirstGroup
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch
noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut
theorem b48 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut↔firstInputBoundary clean out live i = cut:=by
  simp [firstInputGroup]
theorem b130 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (w : Fin (n + gs.length)) : w ≤ out:=by
  let last : Fin (n + gs.length):=⟨n + gs.length - 1,by have:=out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last:=by
    change v.val ≤ n + gs.length - 1
    have:=v.isLt
    omega
  have lastOut : last = out:=by
    by_contra notOutput
    obtain ⟨v,e⟩:=live last notOutput
    exact (not_lt_of_ge (top v)) (b15 clean e)
  exact lastOut ▸ top w
theorem b17 {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (distinct : ∀ w,(b10 clean w).Nodup)
    (fallback chosen : Fin n) :
    b0 chosen (b2 fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1:=by
  let weight (a : Fin (n + gs.length)):=b0 chosen (b2 fallback gs a.val)
  have sourcePrimary : (b8 gs chosen).val < n:=chosen.isLt
  have atSource : weight (b8 gs chosen) = 1:=by
    dsimp [weight]
    rw [b30 fallback chosen _ sourcePrimary,ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length),w≠b8 gs chosen →
      weight w = ((b10 clean w).map weight).sum:=by
    intro w other
    by_cases primary : w.val < n
    · simp [weight,b30 fallback chosen w primary,other,
        b111 clean w primary]
    · let p:=w.val - n
      have hp : p < gs.length:=by have:=w.isLt; dsimp [p]; omega
      have hw : w.val = n + p:=by dsimp [p]; omega
      let g:=gs[p]
      have atSlot : gs[p]? = some g:=List.getElem?_eq_getElem hp
      exact b84 fallback chosen clean atSlot hw _
        (b116 clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (b5 gs) out (b15 clean) live
    (b10 clean) (fun a b => (b158 clean a b).symm) weight
    (b8 gs chosen) otherWeight atSource distinct le_rfl
theorem b86 {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out \/ ∀ k : Fin n,k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (b5 gs) cut) (b8 gs k) out:=by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out:=lt_of_le_of_ne (b130 clean out live cut) terminal
  have firstHere:=(b48 clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out:=by rwa [firstHere]
  have blocked:=FirstBranchRoute.no_avoiding_after (b5 gs) out
    (b15 clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (b5 gs)
    (firstInputBoundary clean out live k)) (b8 gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1,e.2.1⟩) _ _ path
theorem b80 {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length),w≠out -> ∃ v,b5 gs w v)
    (distinct : ∀ w,(b10 clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x,vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j,G.Adj i j -> ∃ u v,
      G.Adj i u /\ G.Adj j v /\ u≠j /\ v≠i /\ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut):=by
  intro i iIn j jIn adjacent
  obtain ⟨u,v,hiu,hjv,huj,hvi,huv⟩:=witnesses i j adjacent
  have iFirst:=(b48 clean out live cut i).mp iIn
  have jFirst:=(b48 clean out live cut j).mp jIn
  have iCount:=b17 clean out live distinct i i
  have jCount:=b17 clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine b124 clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases b86 clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))
end PetersenFirstGroup
namespace PetersenNine
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Vertex:=Fin 9
abbrev Edges:=List (Vertex × Vertex)
def edges : Edges:=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def edgeFun (es : Edges) (x : Vertex -> Bool) : Bool :=
  es.any (fun edge => x edge.1&&x edge.2)
lemma noLoops : ∀ e ∈ edges,e.1≠e.2:=by decide
lemma edgeFun_true (es : Edges) (x : Vertex -> Bool) :
    edgeFun es x = true↔∃ a b,(a,b) ∈ es /\ x a = true /\ x b = true:=by
  simp only [edgeFun,List.any_eq_true,Bool.and_eq_true,Prod.exists]
def graph (es : Edges) (noSelf : ∀ e ∈ es,e.1≠e.2) : SimpleGraph Vertex where
  Adj a b:=(a,b) ∈ es \/ (b,a) ∈ es
  symm:=⟨fun _ _ => Or.symm⟩
  loopless:=⟨fun v h => h.elim (fun he => noSelf (v,v) he rfl) (fun he => noSelf (v,v) he rfl)⟩
end PetersenNine
namespace PetersenGroupBFS
def b7:=Nat × (Nat -> Nat)
def b7.width (g : b7):=g.1
def b7.adjacency (g : b7):=g.2
def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex
def b71 (g : b7) : Nat :=
  bit g.width - 1
def b3 (g : b7) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (b71 g) deleted)
def closeIsolates (g : b7) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if b3 g deleted v = 0 then Nat.lor mask (bit v) else mask)
    deleted
def b74 (g : b7) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (b3 g deleted v==b3 g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0
theorem bit_at (v w : Nat) : (bit v).testBit w = decide (v = w):=by
  simp [bit,Nat.shiftLeft_eq,Nat.testBit_two_pow]
theorem b194 (g : b7) (w : Nat) :
    (b71 g).testBit w = decide (w < g.width):=by
  simp [b71,bit,Nat.shiftLeft_eq]
theorem b191 (g : b7) (deleted v w : Nat) (hw : w < g.width) :
    (b3 g deleted v).testBit w =
      ((g.adjacency v).testBit w&&!(deleted.testBit w)):=by
  simp [b3,Nat.testBit_xor,b194,hw]
private theorem b152 (vertices : List Nat) (p : Nat -> Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w||(vertices.any fun v => decide (p v)&&(v==w))):=by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons,List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h,bit_at,Bool.or_assoc,Bool.beq_eq_decide_eq]
private theorem b170 (p : Nat -> Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v)&&(v==w)) =
      (decide (w < n)&&decide (p w)):=by
  rw [Bool.eq_iff_iff,List.any_eq_true,Bool.and_eq_true]
  simp only [List.mem_range,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · rintro ⟨v,hv,hp,rfl⟩
    exact ⟨hv,hp⟩
  · rintro ⟨hw,hp⟩
    exact ⟨w,hw,hp,rfl⟩
theorem close_at (g : b7) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w||(decide (w < g.width)&&decide (b3 g deleted w = 0))):=by
  unfold closeIsolates
  rw [b152,b170]
theorem class_at (g : b7) (deleted v w : Nat) :
    (b74 g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w)&&(b3 g deleted w==b3 g deleted v))):=by
  unfold b74
  rw [b152,b170]
  simp [Bool.beq_eq_decide_eq]
theorem b52 (width : Nat) : bit width = 2 ^ width:=by
  simp [bit,Nat.shiftLeft_eq]
theorem b192 {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width:=by
  rw [b52] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb
theorem b126 {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false:=by
  rw [b52] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))
theorem mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width,a.testBit w = b.testBit w) : a = b:=by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [b126 ha (Nat.le_of_not_gt hw),b126 hb (Nat.le_of_not_gt hw)]
theorem b64 (g : b7) (deleted v : Nat) (hd : deleted < bit g.width) :
    b3 g deleted v < bit g.width:=by
  rw [b52]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [b3,b194,Nat.not_lt_of_ge hw,b126 hd hw]
theorem b142 (g : b7) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width:=by
  rw [b52]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at,Nat.not_lt_of_ge hw,b126 hd hw]
theorem b181 (g : b7) (deleted v : Nat) :
    b74 g deleted v < bit g.width:=by
  rw [b52]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at,Nat.not_lt_of_ge hw]
def step (g : b7) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v)&&(b3 g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (b74 g deleted v)))
    else none
def b34 (g : b7) : Nat -> List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((b34 g depth).flatMap (step g)).eraseDups
theorem advance {g : b7} {depth deleted next : Nat}
    (hd : deleted ∈ b34 g depth) (hs : next ∈ step g deleted) :
    next ∈ b34 g (depth + 1):=by
  rw [b34,List.mem_eraseDups,List.mem_flatMap]
  exact ⟨deleted,hd,hs⟩
theorem stay {g : b7} {depth deleted : Nat} (hd : deleted ∈ b34 g depth) :
    deleted ∈ b34 g (depth + 1) :=
  advance hd (by simp [step])
theorem b183 {g : b7} {depth deleted vertex : Nat}
    (hd : deleted ∈ b34 g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : b3 g deleted vertex≠0) :
    closeIsolates g (Nat.lor deleted (b74 g deleted vertex)) ∈ b34 g (depth + 1):=by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex,List.mem_range.mpr hv,?_⟩
  simp [hlive,hne]
def petersenNine : b7 :=
  ⟨9,fun v => (#[50,69,138,276,9,385,258,36,104] : Array Nat)[v]?.getD 0⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b117 : b71 petersenNine ∉ b34 petersenNine 4:=by
  decide +kernel
end PetersenGroupBFS
namespace PetersenMaskBridge
open PetersenGroupBFS
open BranchGraph
def decode (g : b7) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)
@[simp] lemma mem_decode (g : b7) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask↔mask.testBit v.val = true:=by
  simp [decode]
@[simp] lemma decode_zero (g : b7) : decode g 0 = ∅:=by
  ext v
  simp
@[simp] lemma decode_full (g : b7) : decode g (b71 g) = Finset.univ:=by
  ext v
  simp [b194,v.isLt]
lemma decode_or (g : b7) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b:=by
  ext v
  simp [Bool.or_eq_true]
lemma b148 (g : b7) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b:=by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w,hw⟩ : Fin g.width) ∈ decode g a↔(⟨w,hw⟩ : Fin g.width) ∈ decode g b:=by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm
lemma b182 (n : Nat) : 0 < bit n:=by
  rw [b52]
  exact Nat.two_pow_pos n
lemma b185 (g : b7) : b71 g < bit g.width:=by
  unfold b71
  have:=b182 g.width
  omega
section Graph
variable (g : b7) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width,G.Adj u v↔(g.adjacency u.val).testBit v.val = true)
include adj in
lemma b44 (deleted : Nat) (u : Fin g.width) :
    decode g (b3 g deleted u.val) = neighborsAfter G (decode g deleted) u:=by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode,neighborsAfter,b191 g deleted u.val v.val v.isLt,adj,h]
include adj in
lemma b95 (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    b3 g deleted u.val = 0↔neighborsAfter G (decode g deleted) u = ∅:=by
  constructor
  · intro h
    rw [← b44 g G adj,h,decode_zero]
  · intro h
    apply b148 g (b64 g deleted u.val bound) (b182 g.width)
    rw [b44 g G adj,h,decode_zero]
include adj in
lemma b153 (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted):=by
  ext v
  simp [close_at,v.isLt,BranchGraph.closeIsolates,b106,Bool.or_eq_true,
    b95 g G adj deleted bound]
include adj in
lemma b187 (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (b74 g deleted root.val) = b24 G (decode g deleted) root:=by
  have same (u : Fin g.width) : b3 g deleted u.val = b3 g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root:=by
    rw [← b44 g G adj deleted u,← b44 g G adj deleted root]
    exact ⟨congrArg (decode g),b148 g (b64 g deleted u.val bound)
      (b64 g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at,v.isLt,b24,outside,live,h,same,Bool.beq_eq_decide_eq]
def b83 (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m,m ∈ b34 g depth /\ m < bit g.width /\ decode g m = removed
include adj in
lemma b193 : b83 g 0 (BranchGraph.closeIsolates G ∅):=by
  refine ⟨PetersenGroupBFS.closeIsolates g 0,?_,
    b142 g 0 (b182 g.width),?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [b153 g G adj _ (b182 g.width),decode_zero]
include adj in
lemma b197 {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : b83 g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    b83 g (depth + 1) (b20 G removed root):=by
  obtain ⟨m,hm,bounded,same⟩:=rep
  subst removed
  by_cases active : root ∉ decode g m /\ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false:=by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : b3 g m root.val≠0:=by
      intro h
      have none:=(b95 g G adj m bounded root).mp h
      simpa [none] using active.2
    have united:=b192 bounded (b181 g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (b74 g m root.val)),
      b183 hm root.isLt live someNeighbor,b142 g _ united,?_⟩
    rw [b153 g G adj _ united,decode_or,b187 g G adj m bounded root active.1 active.2,
      b20]
  · have sameRemoval : b20 G (decode g m) root = decode g m:=by
      have emptyClass : b24 G (decode g m) root = ∅:=ite_eq_right active
      simp only [b20,emptyClass,Finset.union_empty,closed]
    exact ⟨m,stay hm,bounded,sameRemoval.symm⟩
include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : b102 G count start finish) (initial : b83 g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : b83 g (depth + count) finish:=by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk,Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root,next⟩:=walk
    have nextClosed : BranchGraph.closeIsolates G (b20 G start root) = b20 G start root :=
      b51 G _
    have rest:=ih next (b197 g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rest
lemma b195 {m k r : Nat} (reached : m ∈ b34 g k) (budget : k ≤ r) : m ∈ b34 g r:=by
  induction r with
  | zero =>
    have : k = 0:=by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))
include adj in
theorem b128 [Nonempty (Fin g.width)] (k : Nat) (noFinish : b71 g ∉ b34 g k)
    (groups : List (Finset (Fin g.width))) (twins : b60 G ∅ groups)
    (finished : b19 G (b13 ∅ groups)) : k < groups.length:=by
  by_contra! budget
  have walk:=b58 G groups twins finished
  obtain ⟨m,reached,bound,allGone⟩ :=
    simulate g G adj walk (b193 g G adj) (b51 G ∅)
  have equal : m = b71 g:=b148 g bound (b185 g) (by simpa using allGone)
  rw [equal,Nat.zero_add] at reached
  exact noFinish (b195 g reached budget)
end Graph
theorem petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9,G.Adj u v↔(petersenNine.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 9))) (twins : b60 G ∅ groups)
    (finished : b19 G (b13 ∅ groups)) : 5 ≤ groups.length :=
  @b128 petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 b117 groups twins finished
end PetersenMaskBridge
open PetersenNine
def b6 : SimpleGraph Vertex:=graph edges noLoops
def b37 : DecidableRel b6.Adj:=fun a b =>
  inferInstanceAs (Decidable ((a,b) ∈ edges \/ (b,a) ∈ edges))
theorem b77 (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge b6 S:=by
  constructor
  · intro h
    obtain ⟨a,b,edge,ha,hb⟩:=(edgeFun_true edges _).mp h
    exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,Or.inl edge⟩
  · rintro ⟨a,ha,b,hb,adjacent⟩
    change (a,b) ∈ edges \/ (b,a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a,b,edge,decide_eq_true ha,decide_eq_true hb⟩
    · exact ⟨b,a,edge,decide_eq_true hb,decide_eq_true ha⟩
theorem b76 :
    ∀ a b : Vertex,b6.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val = true:=by
  letI : DecidableRel b6.Adj:=b37
  decide
theorem b53 :
    ∀ i j : Vertex,b6.Adj i j →
      ∃ u v,b6.Adj i u /\ b6.Adj j v ∧
        u≠j /\ v≠i /\ ¬ b6.Adj u v:=by
  letI : DecidableRel b6.Adj:=b37
  decide
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators
def b14 (gs : List Gate) : List Nat:=gs.flatMap Gate.inputs
def b49 (gs : List Gate) : Nat:=(gs.filter fun g => isNotGate g.op).length
theorem b46 {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ b14 gs:=by
  obtain ⟨g,gAt,before⟩:=read
  exact List.mem_flatMap.mpr ⟨g,List.mem_iff_getElem?.mpr ⟨slot,gAt⟩,before⟩
theorem b91 {gs : List Gate} {wire p q : Nat}
    (neq : p≠q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (b14 gs).count wire:=by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g,atGate,_⟩
    simp at atGate
  | cons a rest ih =>
    simp only [b14,List.flatMap_cons,List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using first
        have later : Reads rest q wire:=by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (b14 rest).count wire:=List.count_pos_iff.mpr (b46 later)
        simp only [b14] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs:=by simpa [Reads] using second
        have later : Reads rest p wire:=by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire:=List.count_pos_iff.mpr atA
        have restPos : 0 < (b14 rest).count wire:=List.count_pos_iff.mpr (b46 later)
        simp only [b14] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire:=by simpa [Reads] using first
        have late : Reads rest q wire:=by simpa [Reads] using second
        have different : p≠q:=fun eq => neq (congrArg Nat.succ eq)
        have count:=ih different early late
        simp only [b14] at count
        omega
theorem b120 (gs : List Gate)
    (arity : ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (b14 gs).length + b49 gs = 2 * gs.length:=by
  induction gs with
  | nil => simp [b14,b49]
  | cons g gs ih =>
    have gArity:=arity g (by simp)
    have rest:=ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [b14,b49,h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [b14,b49,h] at rest ⊢
      omega
theorem b159 {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs,g.inputs.length + (if isNotGate g.op then 1 else 0) = 2:=by
  intro g gMem
  obtain ⟨p,atGate⟩:=List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op,a,_,args⟩ | ⟨ops,a,b,_,_,args⟩
  · simp [op,args,isNotGate]
  · rcases ops with op | op <;> simp [op,args,isNotGate]
theorem b40 (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches,2 ≤ (b14 gs).count w) :
    branches.card + (b14 gs).toFinset.card ≤ (b14 gs).length:=by
  classical
  let W:=(b14 gs).toFinset
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
  have total : (∑ w ∈ W,(b14 gs).count w) = (b14 gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W,((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W,(b14 gs).count w:=by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (b14 gs).count w:=List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib,aux,total] at bound
  simpa [W] using bound
theorem b160 {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length,w≠out -> ∃ p,Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches,∃ p q,p≠q /\ Reads gs p w /\ Reads gs q w) :
    branches.card + (n + gs.length - 1) + b49 gs ≤ 2 * gs.length:=by
  let W:=(b14 gs).toFinset
  let required:=(Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W:=by
    intro w inSet
    have spec:=Finset.mem_erase.mp inSet
    obtain ⟨p,read⟩:=everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (b46 read)
  have numRequired : required.card = n + gs.length - 1:=by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid),Finset.card_range]
  have twice : ∀ w ∈ branches,2 ≤ (b14 gs).count w:=by
    intro w mem
    obtain ⟨p,q,different,pReads,qReads⟩:=twoReaders w mem
    exact b91 different pReads qReads
  have up:=b40 gs branches twice
  have used:=Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total:=b120 gs (b159 clean)
  change n + gs.length - 1 ≤ (b14 gs).toFinset.card at used
  omega
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace
theorem b68 {n out : Nat} {gs : List Gate}
    {f : (Fin n -> Bool) -> Bool} (least : Least n f gs out) (nonnull : ∃ x y,f x≠f y)
    (dependent : ∀ v : Fin n,Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool),∃ x y,
      f (Function.update x v b)≠f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length),w≠(⟨out,outValid⟩ : Fin (n + gs.length)) -> ∃ v,b5 gs w v:=by
  intro w notOutput
  have notSame : w.val≠out:=fun eq => notOutput (Fin.ext eq)
  obtain ⟨p,g,atSlot,reads,bound⟩ :=
    b79 least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p,bound⟩,p,g,atSlot,rfl,reads⟩
theorem b88 {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (b5 gs) w) :
    ∃ p q,p≠q /\ Reads gs p w.val /\ Reads gs q w.val:=by
  obtain ⟨first,next,pRead,qRead,separate⟩:=fork
  obtain ⟨p,g,atP,src,ap⟩:=pRead
  obtain ⟨q,h,atQ,dst,aq⟩:=qRead
  refine ⟨p,q,?_,⟨g,atP,ap⟩,⟨h,atQ,aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))
noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)):=by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (b5 gs) w
theorem b25 {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs↔FirstBranchRoute.Branches (b5 gs) w:=by
  classical
  simp [circuitBranchWires]
def b93 {V W : Type} [Fintype V] (label : V -> W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut
def b26 {V W : Type} [Fintype V] (label : V -> W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut
theorem b189 {V W : Type} [Fintype V] (label : V -> W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ b93 label cut↔label v = cut:=by
  simp [b93]
theorem b143 {V W : Type} [Fintype V] (label : V -> W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ b26 label cut↔label v < cut:=by
  simp [b26]
theorem b82 {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V -> W) (cut : W)
    (independent : BranchGraph.Independent G (b93 label cut))
    (code : Finset V -> Bool) (decode : Bool -> Finset V -> Prop)
    (factors : ∀ I O : Finset V,(∀ i ∈ I,label i = cut) →
      (∀ i ∈ O,cut < label i) -> (BranchGraph.containsEdge G (I ∪ O)↔decode (code I) O)) :
    BranchGraph.TwinGroup G (b26 label cut) (b93 label cut):=by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ b93 label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ b26 label cut) : cut < label y:=by
    have ne : label y≠cut:=fun equal =>
      independent x xGroup y ((b189 label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut:=fun h => notEarlier ((b143 label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ b93 label cut) (yLater : cut < label y) :
      (G.Adj x y↔decode (code {x}) {y}):=by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut:=by
      have eq : i = x:=Finset.mem_singleton.mp mem
      subst i
      exact (b189 label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i:=by
      have eq : i = y:=Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ b93 label cut)
      (active : (BranchGraph.neighborsAfter G (b26 label cut) x).Nonempty) :
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
theorem b100 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n -> Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i,ReflTransGen (b5 gs) (b8 gs i) w -> x i = y i) :
    vl gs x w.val = vl gs y w.val:=by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n:=⟨w.val,input⟩
      have name : b8 gs i = w:=Fin.ext rfl
      have atInput : ReflTransGen (b5 gs) (b8 gs i) w:=by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (b5 gs) w w)
      have a:=agree i atInput
      simpa only [b69 gs x w.val input,b69 gs y w.val input] using a
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
      have read : b5 gs wire w:=⟨p,g,atGate,gateWire,inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)
end PetersenCutTrace
open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation
def b55 {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool:=decide (i ∈ S)
theorem b97 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out -> ∃ w,b5 gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (b5 gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
    ∃ code : Finset (Fin n) -> Bool,∃ decode : Bool -> Finset (Fin n) -> Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I,label i = cut) -> (∀ i ∈ O,cut < label i) →
        (vl gs (b55 (I ∪ O)) out.val = true↔decode (code I) O):=by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
  let code (I : Finset (Fin n)):=vl gs (b55 I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n),(∀ j ∈ J,label j = cut) /\ code J = b ∧
      vl gs (b55 (J ∪ O)) out.val = true
  refine ⟨code,decode,?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I,label i = cut) at groupI
  change (∀ i ∈ O,cut < label i) at afterO
  change (_↔decode (code I) O)
  constructor
  · exact fun yes => ⟨I,groupI,rfl,yes⟩
  · rintro ⟨J,groupJ,sameCode,yes⟩
    have stable (K : Finset (Fin n)) : vl gs (b55 (K ∪ O)) cut.val = code K:=by
      apply b100 clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (b5 gs) out (b15 clean) live ancestral terminal
      have absent : i ∉ O:=fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [b55,absent]
    have sameCut : vl gs (b55 (I ∪ O)) cut.val = vl gs (b55 (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out:=lt_of_le_of_ne prior atOutput
    have eq:=b59 clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut:=by
        by_contra offGroup
        have notI : i ∉ I:=fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J:=fun mem => offGroup (groupJ i mem)
        exact diff (by simp [b55,notI,notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (b5 gs) out (b15 clean) live
          (b8 gs i) = cut:=isGroup
      have forbid:=FirstBranchRoute.no_avoiding_after (b5 gs) out (b15 clean) live
        (v:=b8 gs i) (w:=out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b,avoid (b5 gs) cut a b -> FirstBranchRoute.Avoid (b5 gs) cut a b :=
        fun _ _ h => ⟨h.1,h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (b5 gs) cut) (b8 gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]
open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace
theorem b87 {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length),v≠out -> ∃ w,b5 gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n),vl gs (b55 S) out.val = true↔BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (b5 gs) out cut)
    (independent : BranchGraph.Independent G
      (b93 (fun i => FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)) cut)) :
    let label (i : Fin n):=FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
    BranchGraph.TwinGroup G (b26 label cut) (b93 label cut):=by
  let label (i : Fin n):=FirstBranchRoute.first (b5 gs) out (b15 clean) live (b8 gs i)
  obtain ⟨code,decode,factors⟩:=b97 clean out live cut prior terminal
  change BranchGraph.TwinGroup G (b26 label cut) (b93 label cut)
  exact b82 G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup
abbrev petersenF:=edgeFun edges
private theorem b78 : ∀ v : Vertex,∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w))))≠petersenF (fun i => decide (i = w)):=by
  decide +kernel
theorem b63 (v : Vertex) : Dep petersenF v:=by
  obtain ⟨w,hw⟩:=b78 v
  exact ⟨fun i => decide (i = w),hw⟩
theorem b16 : ∃ x y : Vertex -> Bool,petersenF x≠petersenF y :=
  dep_nc (b63 0)
private theorem b92 : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true:=by
  decide +kernel
theorem b27 (v : Vertex) (b : Bool) :
    ∃ x y,petersenF (Function.update x v b)≠petersenF (Function.update y v b):=by
  obtain ⟨no,yes⟩:=b92 v b
  exact ⟨fun _ => false,fun _ => true,by rw [no,yes]; decide⟩
lemma b118 (x : Fin 9 -> Bool) : petersenF x = true ↔
    ∃ u v : Fin 9,b6.Adj u v /\ x u = true /\ x v = true:=by
  change PetersenNine.edgeFun PetersenNine.edges x = true↔_
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    exact ⟨a,b,Or.inl edge,ha,hb⟩
  · rintro ⟨a,b,adjacent,ha,hb⟩
    change (a,b) ∈ PetersenNine.edges \/ (b,a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a,b,edge,ha,hb⟩
    · exact ⟨b,a,edge,hb,ha⟩
lemma b32 {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length:=by
  by_contra! after
  obtain ⟨x,y,different⟩:=least.ncv b16
  exact different ((b136 gs x out after).trans (b136 gs y out after).symm)
theorem b70 (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n:=9) gs).card:=by
  classical
  letI : DecidableRel b6.Adj:=b37
  have outValid:=b32 least
  let outWire : Fin (9 + gs.length):=⟨out,outValid⟩
  have live:=b68 least b16 b63 b27 outValid
  let label : Fin 9 -> Fin (9 + gs.length):=firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)):=circuitBranchWires gs
  have computes (x : Fin 9 -> Bool) : vl gs x outWire.val = PetersenScratch.edgeValue b6 x:=by
    change vl gs x out = _
    rw [least.hev,Bool.eq_iff_iff,b118]
    simp only [PetersenScratch.edgeValue,decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (b55 S) outWire.val = true ↔
      BranchGraph.containsEdge b6 S:=by
    change vl gs (b55 S) out = true↔_
    rw [least.hev]
    exact b77 S
  have independent (r) : BranchGraph.Independent b6 (BranchGroupsLean.bucket label r) :=
    b80 least.hcl outWire live (b137 least b16)
      b6 computes b53 r
  have labels (v : Fin 9) : label v = outWire \/ label v ∈ branches:=by
    have stopped:=FirstBranchRoute.first_stops (b5 gs) outWire (b15 least.hcl) live (b8 gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (b25.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire:=by
    obtain ⟨a,_,path,_,_⟩:=b25.mp member
    exact lt_of_lt_of_le (b15 least.hcl path) (b130 least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup b6
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    b87 least.hcl outWire live b6 marked r
      (le_of_lt (before r member)) (Or.inr (b25.mp member)) (independent r)
  exact BranchGroupsLean.roots_required b6 label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five b6 b76)
lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length:=by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount,List.countP_cons,List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega
theorem petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex -> Bool,C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates:=by
  obtain ⟨gs,o,least,budget⟩:=b146 C hfan he b16
  have valid:=b32 least
  have live:=b68 least b16 b63
    b27 valid
  let branches:=circuitBranchWires (n:=9) gs
  have branchLower : 5 ≤ branches.card:=b70 gs o least
  have branchBudget:=b160 least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length):=⟨w,hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩:=live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      exact b88 (b25.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal:=nonNotCount_add_notCount gs
  change nonNotCount gs + b49 gs = gs.length at countTotal
  omega
end Binary
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero /\ a≠one
private theorem m24 (d : Bool) (a b : Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (target : Sig) : Nat -> Nat -> Finset Sig -> Prop:=fun k t S =>
  ∀ (M : (Nat -> Nat -> Finset Sig -> Prop)),(proper target -> M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a -> neg a ∉ insert a U -> M k t (insert (neg a) U) -> M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a -> proper b -> a≠b -> bin d a b ∉ insert a (insert b U) -> M k t (insert (bin d a b) U) -> M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target}:=fun M stop unary binary => @stop  h0
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
theorem Live.induct {target : Sig} {M : (Nat -> Nat -> Finset Sig -> Prop)} {k t S} (h : Live target k t S)
  (stop : proper target -> M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a -> neg a ∉ insert a U -> Live target k t (insert (neg a) U) -> M k t (insert (neg a) U) -> M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a -> proper b -> a≠b -> bin d a b ∉ insert a (insert b U) -> Live target k t (insert (bin d a b) U) -> M k t (insert (bin d a b) U) -> M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S /\ M k t S)
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
  have hh:=h (fun k _ W => k=0 -> W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
private lemma m22 {k t S} (h : Live target k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
private lemma m26 {k t S} (h : Live target k t S) : t ≤ k /\ S.card+t ≤ k+1:=by
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
def represented (w : List Sig) (v : Sig) : Prop:=v ∈ w \/ ¬proper v
private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
private lemma m16 (a : Sig) :
    bin false a one=a /\ bin true a zero=a ∧
    bin false a zero=zero /\ bin true a one=one ∧
    bin false a a=a /\ bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
private lemma m70 : neg zero=one /\ neg one=zero:=by simp [neg,zero,one]
private lemma m13 {w : List Sig} {a : Sig} (h : represented w a) :
    a=zero \/ a=one \/ a ∈ w /\ proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w,proper a /\ z=neg a) ∨
  (∃ d a b,a ∈ w /\ b ∈ w /\ proper a /\ proper b /\ a≠b /\ z=bin d a b)
private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) \/ witness w (bin d a b):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=m16 a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=m16 b
  rcases m13 ha with rfl | rfl | ⟨ham,hap⟩
  · rw [m24]; cases d <;> simp_all
  · rw [m24]; cases d <;> simp_all
  rcases m13 hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z \/ witness w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1 /\ Live target k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w \/ a=z:=by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=m22 h z hm
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
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
private lemma m15 (i) : bit i zero=false:=by simp [bit,zero]
private lemma bit_one (i) : bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (m15 _).symm
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
    | nil => exact m15 _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,m15]
    | cons a l => exact bit_neg _ _
private lemma m47 (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Wire (R : Type):=R -> Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat:=(xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool \/ Constant v
def supply {R} (pool xs : List (Wire R)):=∀ a ∈ xs,Available pool a
def Reach {R} (roots : List (Wire R)) : Nat -> List (Wire R) -> Prop:=fun p bank =>
  ∀ (M : (Nat -> List (Wire R) -> Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank -> Available bank a -> M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank -> Available bank a -> Available bank b -> M (p+1) (combine op a b :: bank)) →
  M p bank
theorem Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots:=fun M start one two => @start
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank):=fun M start one two => @one p bank a (h0 M start one two) h1
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank):=fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
theorem Reach.induct {R} {roots : List (Wire R)} {M : (Nat -> List (Wire R) -> Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},Reach roots p bank -> M p bank -> Available bank a -> M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),Reach roots p bank -> M p bank -> Available bank a -> Available bank b -> M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank /\ M p bank)
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
def Run {R} (goal : Wire R) : Nat -> List (Wire R) -> Prop:=fun s ws =>
  ∀ (M : (Nat -> List (Wire R) -> Prop)),(M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs -> M s xs -> M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),M s (inv a :: kept save a rest) -> M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),M s (combine op a b :: kept ka a (kept kb b rest)) -> M (s+1) (a::b::rest)) →
  M s ws
theorem Run.stop {R} {goal : Wire R}   : Run goal 0 [goal]:=fun M stop perm one two => @stop
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
theorem Run.induct {R} {goal : Wire R} {M : (Nat -> List (Wire R) -> Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs -> Run goal s xs -> M s xs -> M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),Run goal s (inv a :: kept save a rest) -> M s (inv a :: kept save a rest) -> M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),Run goal s (combine op a b :: kept ka a (kept kb b rest)) -> M s (combine op a b :: kept ka a (kept kb b rest)) -> M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws /\ M s ws)
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
theorem m30 {R} (a : Wire R) (xs) : mass (a::xs)=cost a+mass xs:=by
  simp [mass]
theorem m86 {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs):=by
  cases k <;> simp [kept,m30]
theorem m75 {R} {a : Wire R} (h : Constant a) : Constant (inv a):=by
  obtain ⟨v,rfl⟩:=h
  exact ⟨!v,rfl⟩
theorem m117 {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b):=by
  obtain ⟨v,rfl⟩:=h
  obtain ⟨w,rfl⟩:=g
  cases op <;> exact ⟨_,rfl⟩
theorem m115 {R} (op) {a b : Wire R} {bank}
    (h : Constant a \/ Constant b) (ha : Available bank a) (hb : Available bank b) :
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
theorem m36 {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next,Reach roots q next /\ Available next (inv a) ∧
        (∀ v,Available bank v -> Available next v) /\ q+cost a ≤ p+1+cost (inv a):=by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (m75 c),fun _ h => h,by simp [cost,c,m75 c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => m36 _ h,by simp [cost,c]⟩
theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next,Reach roots q next /\ Available next (combine op a b) ∧
        (∀ v,Available bank v -> Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b):=by
  classical
  by_cases c : Constant a \/ Constant b
  · refine ⟨p,bank,hp,m115 op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,m117 op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a:=fun h => c (Or.inl h)
    have cb : ¬Constant b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => m36 _ h,
      by simp [cost,ca,cb]⟩
theorem m112 {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a \/ x∈xs:=by cases k <;> simp_all [kept]
theorem m150 {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next,Reach roots q next /\ Available next goal /\ q+mass ws ≤ p+s:=by
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
      · exact inc v (hs v (List.mem_cons.mpr (m112 hh)))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=m86 a rest save
    rw [m30] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩:=extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases m112 hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (m112 hh))
    obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
    have hlen:=m86 a (kept kb b rest) ka
    have hlen':=m86 b rest kb
    rw [m30] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [m30,m30]
    omega
def restrictRows {R S : Type} (rows : S -> R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
theorem m68 {R S : Type} (rows : S -> R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)):=by
  cases k <;> simp [kept]
theorem m121 {R S : Type} (rows : S -> R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)):=by
  induction h using Run.recurse with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,m68] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,m68] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih
theorem m29 {R S : Type} (rows : S -> R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs,Reach roots q bs -> Available bs (restrictRows rows goal) -> L ≤ q) :
    L+mass (ws.map (restrictRows rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩:=m150 nc (m121 rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem m52 (f : Wire Row) (r : Row) : bit r (table f)=f r:=by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem m18 (v : Sig) : table (observe v)=v:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact m52 (observe v) ⟨j,hj⟩
theorem m41 (f : Wire Row) : observe (table f)=f:=by
  funext r
  exact m52 f r
theorem obs_neg (a : Sig) : observe (neg a)=inv (observe a):=by
  funext r
  exact bit_neg _ _
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b)=combine d (observe a) (observe b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
theorem m113 {α β : Type} (f : α -> β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f=kept d (f a) (l.map f):=by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup:=by cases k <;> simp [kept,hn,ha]
theorem m28 (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [kept]
theorem m114 {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
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
      rw [show tail=kept save a rest by rfl,m28,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=kept_nd save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,m113,obs_neg] at progress
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
      rw [m28,m28,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,m113,m113,obs_bin] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)
theorem table_inv (f : Wire Row) : table (inv f)=neg (table f):=by
  rw [←m18 (neg (table f)),obs_neg,m41]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g)=bin d (table f) (table g):=by
  rw [←m18 (bin d (table f) (table g)),obs_bin,m41,m41]
theorem m21 {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (m52 _ ⟨j,hj⟩).trans (m15 ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (m52 _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) \/ witness w (neg a):=by
  rcases m13 ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 m70.1)
  · exact Or.inl (Or.inr fun h => h.1 m70.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
theorem m124 {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z \/ witness w z) (hs : ∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1 /\ Live T k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm
theorem m100 {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S,a ∈ bank.map table) :
    ∃ l v U,l ≤ p+k /\ Live T l v U /\ ∀ a ∈ U,a ∈ roots.map table:=by
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=m124 run (inv_rep (m21 ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩:=m124 run (bin_rep d (m21 ha) (m21 hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩:=ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
theorem m74 {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S,k ≤ p /\ Live T k t S /\ ∀ a ∈ S,a ∈ roots:=by
  have hm:=m21 hit
  rw [m18] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩:=m100 h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,m18] using hs
theorem m31 {T k t S} (h : Live T k t S) {r s : Row}
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
theorem m32 {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S,v ∈ roots) (r s : Row) (diff : bit r T≠bit s T)
    (isolated : ∀ v ∈ roots,v≠a -> bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩:=m31 h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def oldSeed : Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def seed : Sig:=inputs.getD 0 zero ||| inputs.getD 4 zero
def sample (r : Row) (j : Fin 9):=bit r (inputs.getD j.val zero)
def edge (x : Fin 9 -> Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
theorem edge_table : ∀ r : Row,bit r graph=edge (sample r):=by decide +kernel
theorem seed_table : ∀ r : Row,bit r seed=(sample r 0||sample r 4):=by decide +kernel
theorem m76 : proper graph:=by unfold proper; decide +kernel
theorem seed_nonzero : seed≠zero:=by decide +kernel
theorem m38 : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero)=inputs:=rfl
theorem sampled (r : Row) : List.ofFn (sample r)=inputs.map (bit r):=by
  rw [←m38]
  rw [List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false:=by
  rw [←b_read,m47 _ _ _ (fun g hg => (h g hg).1),←sampled]
  rfl
theorem m129 (gs : List Gate) (ws : List Sig) : ∃ l,execute gs ws=ws ++ l:=by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩:=ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def neighbor (i : Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
def rename (f : Row -> Row) (a : Sig):=table fun r => bit (f r) a
theorem m7 (f : Row -> Row) (a : Sig) (r : Row) :
    bit r (rename f a)=bit (f r) a:=m52 _ _
theorem m14 (f : Row -> Row) (a : Sig) :
    observe (rename f a)=restrictRows f (observe a):=by funext r; exact m7 f a r
theorem rename_neg (f : Row -> Row) (a : Sig) : rename f (neg a)=neg (rename f a):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a))=bit ⟨j,hj⟩ (neg (rename f a))
  rw [m7,bit_neg,bit_neg,m7]
theorem rename_bin (f : Row -> Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b)=bin d (rename f a) (rename f b):=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b))=bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [m7,bit_bin,bit_bin,m7,m7]
theorem rename_inj (f : Row -> Row) (onto : Function.Surjective f) :
    Function.Injective (rename f):=by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [m7,m7,hr] at he
  exact he
theorem m79 (f : Row -> Row) : rename f zero=zero /\ rename f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (m7 f zero ⟨j,hj⟩).trans ((m15 _).trans (m15 ⟨j,hj⟩).symm)
  · exact (m7 f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem m90 {T k t S} (h : Live T k t S) (f : Row -> Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)):=by
  have inj:=rename_inj f onto
  obtain ⟨fz,fo⟩:=m79 f
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
theorem m63 {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T=true) (negRow : bit s T=false) :
    ∃ a ∈ S,bit r a=true /\ bit s a=false:=by
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
  ∀ p bank,Reach (roots.map observe) p bank -> Available bank (observe T) -> L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap -> ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row,bit r T≠bit s T /\ ∀ v ∈ roots,v≠a -> bit r v=bit s v
theorem m43 {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots,Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1):=by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩:=m74 hp h ha
  have he : roots.toFinset=S:=by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩:=essential _ hm
    exact m32 run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
theorem m59 {v : Sig} (hv : proper v) : ¬Constant (observe v):=by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v:=by
    have avail : Available ([] : List (Wire Row)) (observe v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,m18] using m21 avail
  exact (hr.resolve_left (by simp)) hv
theorem m137 {R} (a b : List (Wire R)) : mass (a++b)=mass a+mass b:=by
  simp [mass]
theorem m101 {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs,Constant x) :
    mass xs=xs.length:=by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [m30,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega
theorem m88 {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row -> Row) (eq : rename r T=G)
    (covered : ∀ a ∈ roots,Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles,Essential T roots a)
    (constant : ∀ a ∈ singles,Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L+singles.card):=by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩:=m74 pT hh ha
  have subS : singles ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩:=necessary a hs
    exact m32 run roots a sub i j hd hiso
  let front:=singles.toList ++ (S \ singles).toList
  have nd : front.Nodup:=by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run':=m114 run front nd fe
  have gc : restrictRows r (observe T)=observe G:=(m14 _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
    rw [←m14]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=m29 r run' (gc ▸ m59 pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)):=by
    simp only [front,List.map_append,m137]
    let xs:=(singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs,Constant v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
      rw [←m14]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=m101 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs+_
    rw [sz]
    omega
  omega
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem m39 {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws,∀ keep,neg a ∉ ws -> proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b -> bin d a b ∉ ws →
      proper (bin d a b) -> (childTwo ws a b d ka kb).length ≤ cap →
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
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=m39 hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [m28,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      have nk:=kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(m26 tail).2
    have len : (childOne ws a keep).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,m39 (hn.erase _) b,
        m39 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [m28,m28,er,he]
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
    have sc:=(m26 tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width -> Row)
    (asig : Sig -> BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true /\ bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig -> BitVec n × BitVec n) : List Sig -> BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
theorem m140 {n : Nat} {oriented : Bool} {sig : Sig -> BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem m96 {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width -> Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true -> t=0) :
    covered oriented sig ws=BitVec.allOnes width:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (m140 (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩:=m31 h (show bit (r i) T≠bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩:=m63 h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem m103 {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n -> Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n:=by
  apply m96 h rfl correct
  intro hh
  have eq:=of_decide_eq_true hh
  have bound:=(m26 h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row -> Row) (roots : List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank,Reach (roots.map observe) p bank -> Available bank (restrictRows f (observe T)) -> L ≤ p
def masked (d a : Sig):=a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m:=masked d a
  m==zero||m==d||(pool.map (masked d)).any (fun v => v==m)
theorem masked_eq {f : Row -> Row} {d a b : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=masked d b) :
    restrictRows f (observe a)=restrictRows f (observe b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
theorem m87 {f : Row -> Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=zero) : restrictRows f (observe a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [m15] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
theorem m106 {f : Row -> Row} {d a : Sig} (dom : ∀ r,bit (f r) d=true)
    (eq : masked d a=d) : restrictRows f (observe a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def poolSupply (f : Row -> Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool,Available bank (restrictRows f (observe a))
theorem m6 {f : Row -> Row} {d a : Sig} {bank pool}
    (dom : ∀ r,bit (f r) d=true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a=true) : Available bank (restrictRows f (observe a)):=by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,m87 dom hz⟩
  · exact Or.inr ⟨true,m106 dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv
abbrev Choice:=Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1&&(c.1==2||availableB d pool c.2.2)
theorem m104 {f : Row -> Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r,bit (f r) d=true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c=true) :
    ∃ next,Reach roots (q+1) next /\ poolSupply f next (choiceVal c :: pool):=by
  have ok : availableB d pool c.2.1=true /\ (c.1==2||availableB d pool c.2.2)=true:=by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha:=m6 dom hs ok.1
  let z:=restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank):=by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz':=Reach.two (c.1==1) hp ha (m6 dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w)=combine b (restrictRows f v) (restrictRows f w):=by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact m36 _ (hs _ hm)
def makePool (d : Sig) (pool : List Sig) : List Choice -> Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
theorem m61 {d : Sig} {f : Row -> Row} (dom : ∀ r,bit (f r) d=true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs=some result) :
    ∃ next,Reach roots (q+cs.length) next /\ poolSupply f next result:=by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩:=m104 dom hp hs c h
      obtain ⟨out,hr',sh'⟩:=ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def isMaskedConstant (d a : Sig):=masked d a==zero||masked d a==d
theorem m49 {d : Sig} {f : Row -> Row} (dom : ∀ r,bit (f r) d=true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)):=by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,m30]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)):=by
        have hh : masked d a=zero \/ masked d a=d:=by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,m87 dom hz⟩
        · exact ⟨true,m106 dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d))&&ws.all (availableB d pool)
theorem m111 {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs=some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws=true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
  obtain ⟨bank,hr,hs⟩:=m61 dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩:=cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
    exact m6 dom hs (List.all_eq_true.mp all a ha)
  have b:=m29 f (m114 h ws nd rfl) nc hr coveredS lo
  have massLo:=m49 dom ws
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
theorem m40 (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a)=bit (movedRow ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem m20 (ms : List Move) (a : Sig) : movedWord ms a=rename (movedRow ms) a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (m40 ms a ⟨j,hj⟩).trans (m7 _ _ ⟨j,hj⟩).symm
def freeWord (roots : List Sig) (w : Sig):=w==zero||w==one||roots.contains w
theorem m138 {roots w} (ok : freeWord roots w=true) :
    Available (roots.map observe) (observe w):=by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext m15⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T==G&&raw.all (fun a => freeWord base (movedWord ms a))
theorem m64 {ms raw T base G} (ok : checkMap ms raw T base G=true) :
    rename (movedRow ms) T=G ∧
    ∀ a ∈ raw,Available (base.map observe) (observe (rename (movedRow ms) a)):=by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,m20] at ok
  exact ⟨ok.1,fun a ha => m138 (ok.2 a ha)⟩
theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G=true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L:=by
  obtain ⟨eq,supp⟩:=m64 ok
  simpa using m88 pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL
theorem m110 {ms raw T base G L d} (ok : checkMap ms raw T base G=true)
    (all : movedWord ms d=one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L:=by
  obtain ⟨eq,supp⟩:=m64 ok
  have obs : restrictRows (movedRow ms) (observe T)=observe G :=
    (m14 _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←m40,all,bit_one]
  · intro a ha
    rw [←m14]
    exact supp a ha
  · rw [obs]
    exact m59 properG
  · rw [obs]
    exact hL
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
theorem m98 {T roots a rs} (ok : witnessB T roots a rs=true) : Essential T roots a:=by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem m35 {T raw xs} (ok : checkEssential T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  exact m98 (List.all_eq_true.mp ok _ hm)
theorem m89 {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs=true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩:=m74 properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩:=m35 ok a ha
    exact m32 run raw a sub r s hd iso
  have bound:=(m26 run).2
  omega
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G&&checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1==zero||movedWord ms a.1==one)
theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs=true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩:=m64 ok.1.1
  apply m88 properT properG _ eq supp _ (m35 ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,m20] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext m15⟩
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
def cube0 : Nat -> Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat -> Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat -> Nat
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
theorem m19 (T : Sig) (h : properB T=true) : proper T:=by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs:=graphPairs m hints
  properB (graphGoal m)&&checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L=true) :
    Lower (vars m) (graphGoal m) L:=by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (m89 (m19 _ h.1.1) _ h.1.2 p bank hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat -> Nat) : Bool :=
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
theorem m50 {m : Nat} (c : ColumnInfo) (prior : Nat -> Nat)
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
  apply m110 ok.1.1.2 ok.1.2 (m19 _ ok.1.1.1)
  intro p bank hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (m89 (m19 _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (m19 _ ok.1.1.1) (m19 _ hh.1.1) (valid q) p bank hr ha)
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old)&&properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps=true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L:=by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (m19 _ ok.1.1) (m19 _ ok.1.2) h
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
theorem m4 (entries : List (Nat × Nat))
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
  ∃ (f : Row -> Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r,bit (f r) c.domain=true) /\ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws,Reach (roots.map observe) q ws -> Available ws (restrictRows f (observe T)) -> c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank /\ poolSupply f bank c.wires /\ True
theorem m152 {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs=some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩:=by
  obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
  obtain ⟨bank,hr,hs⟩:=m61 dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩
theorem m109 {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
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
    have b:=m29 f (m114 run ws nd rfl) nc reach covered lo
    have cm:=m49 dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact m6 dom hs buy
    · exact m6 dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩:=m104 dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=m6 dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact m6 dom point ha
      · exact Or.inr con
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z:=choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires))&&(!extra||choiceOK c.domain c.wires op)
theorem m9 {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op=true) :
    Impossible T k (choiceVal op::rest).toFinset:=by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply m109 valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem m37 {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L=some c) : ValidPool raw T c:=by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h
    change some _=some c at h
    injection h with h
    subst c
    exact m152 slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n : Nat} (r : Fin n -> Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem m8 {n : Nat} (r : Fin n -> Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val=bit (r i) v:=by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 -> Row) (a : Sig) : Signals:=(ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 -> Row) :=
  ∀ i,bit (r i) T=true /\ bit (s i) T=false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s):=by
  exact ⟨h,fun a i => ⟨m8 _ _ _,m8 _ _ _⟩⟩
def faithful (r s : Fin 768 -> Row) (x : Decor):=x.2=pairSig r s x.1
def dneg (x : Decor) : Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
theorem ofRows_neg (r : Fin 768 -> Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=m8 r (neg a) ⟨j,hj⟩
  rw [bit_neg,←m8 r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 -> Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b)=if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h:=m8 r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←m8 r a ⟨j,hj⟩,←m8 r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem m46 {r s x} (h : faithful r s x) : faithful r s (dneg x):=by
  change x.2=_ at h
  simp only [faithful,dneg,pairSig,ofRows_neg,h]
theorem m34 {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y):=by
  change x.2=_ at hx
  change y.2=_ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]
def codeDecor (op : Nat) (x y : Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor:=(zero,0,0)
theorem m80 (r s) : faithful r s defaultDecor:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j=(ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from m8 _ _ ⟨j,hj⟩,m15]
    simp
  · change (0 : Bits).getLsbD j=(ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from m8 _ _ ⟨j,hj⟩,m15]
    simp
theorem m27 {r s ws} (all : ∀ v ∈ ws,faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact m80 _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem m48 (n bits) (ws) (r s) (base : ∀ v ∈ ws,faithful r s v) :
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
      · exact m46 (m27 base _)
      · exact m34 _ (m27 base _) (m27 base _)
def asRow (cols : Nat -> Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem m149 : ∀ r : Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
theorem m148 : ∀ r : Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
theorem m147 : ∀ r : Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
theorem m146 : ∀ r : Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
theorem m145 : ∀ r : Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
theorem m144 : ∀ r : Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
theorem m143 : ∀ r : Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
theorem m142 : ∀ r : Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
theorem m141 : ∀ r : Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
theorem m45 : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
  intro j r
  fin_cases j
  · exact m149 r
  · exact m148 r
  · exact m147 r
  · exact m146 r
  · exact m145 r
  · exact m144 r
  · exact m143 r
  · exact m142 r
  · exact m141 r
theorem m53 (cols : Nat -> Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [m45]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat -> Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem m99 {m j a} (h : (j,a) ∈ selected m) :
    j<9 /\ a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem m122 (m) (p q : Nat -> Bits) :
    ∀ a ∈ rawDecor m p q,faithful (asRow p) (asRow q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
  obtain ⟨hj,rfl⟩:=m99 hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (m53 p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (m8 _ _ ⟨i,hi⟩).symm
  · exact (m53 q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (m8 _ _ ⟨i,hi⟩).symm
def liftGoal (m : Nat) (v : Nat -> Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat -> Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [vertex,hh] using m53 v i j
  · simp [vertex,hh,m15]
theorem m77 (m : Nat) (v : Nat -> Bits) (i : Fin 768) :
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
theorem m65 {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
theorem m97 {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)):=by
  cases keep
  · change (coverage d (ws.erase a)).1=takeOne (coverage d ws) _
    rw [cov_perm d (m65 a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem m139 {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (m65 a ha).trans (List.Perm.cons _ (m65 b hm))
theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)):=by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1=takeTwo (coverage d ws) _ _
    rw [cov_perm d (m139 a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact m97 d a ha false
  · exact m97 d b hb false
  · rfl
def sameWords (a b : List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
theorem m11 {xs ys} (h : sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def keyWord (v : Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat -> List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws:=choiceVal op::rest
  (links (keySet ws)).any (sameWords ws)||pools.any (fun p => scalarPoolCut p k rest op)
theorem m81 {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag -> Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op=true) :
    Impossible T k (choiceVal op :: rest).toFinset:=by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [m11 ok]
    exact lValid _ _ hx
  · exact m9 (pValid _ hp) nd ok
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
theorem m69 {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false -> a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb:=by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact m97 d a ha ka
theorem m55 (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem m71 (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (m55 _ _ _).trans (m55 _ _ _)
  · exact m55 _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false -> a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]
def movedDecor (op : Nat) (a b : Decor):=codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice:=(op,a.1,b.1)
theorem m54 (op) (a b : Decor) :
    (movedDecor op a b).1=choiceVal (movedChoice op a b):=by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem m60 {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b):=by
  unfold movedDecor codeDecor
  split
  · exact m46 ha
  · exact m34 _ ha hb
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat -> List (List Sig))
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
theorem m62 {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false -> a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag -> Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb=true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=m71 _ _ _ _ _ _
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
  have hsz:=(m26 h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep:=m103 h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap:=by omega
  rw [ce] at sep
  let d:=child.length==cap
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=m69 ha hb (op==2) ka kb d ne
  have hf:=m60 (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap)=(child.length==cap):=by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length=cap)) (pairSig r s) child=BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst)=_ at sep
  change z.2=pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768)=false:=by simp [sep]
  change (if (_ != _) then true else if !properB z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  have val:=m54 op a b
  change z.1=_ at val
  change Live T k t child.toFinset at h
  have nd':=ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact m81 pv lv nd' test k t hk h
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false&&evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false&&testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor -> Bool
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
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true \/ testPair ctx b a d=true:=by
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
theorem m135 {ctx a b d} (h : testPair ctx a b d=true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem m23 {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v↔(w=a /\ k=true) \/ w∈v:=by cases k <;> simp [kept]
theorem m105 {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k↔w∈v /\ (w≠a \/ k=true):=by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]
theorem m44 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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
theorem m107 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst /\ (v≠a.1 \/ ka=true) /\ (un=true \/ v≠b.1 \/ kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (m55 ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    m105 wn,m105 dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (m44 nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (m44 nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (m44 nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem m83 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset=(childOne (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    m107 nd ha ha,m23,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
theorem m78 {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    m107 nd ha hb,m23,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
theorem m73 (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset=(childTwo v b a d kb ka).toFinset:=by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    m23,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,m24 d b a]
  tauto
theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv : ∀ tag xs,xs ∈ links tag -> Impossible T (cap-1) (List.toFinset xs))
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
    have hf:=m83 nd ha keep
    rw [←hf]
    exact m62 pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d=true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      rw [←m78 nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      exact m62 pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (m135 test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [m73 _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (m24 d a.1 b.1 ▸ pro)
        (m24 d a.1 b.1 ▸ fresh) hh
theorem m134 (r s : Row) (h : ∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← m38]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (m45 i r).symm.trans ((h _ hm).trans (m45 i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def composedOK (p q : List Move):=inputs.all (fun a => movedWord p (movedWord q a)==a)
theorem m42 {p q} (h : composedOK p q=true) (r : Row) :
    movedRow q (movedRow p r)=r:=by
  apply m134
  intro a ha
  rw [←m40,←m40]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T==T)&&composedOK p p.reverse&&composedOK p.reverse p
theorem m85 {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,m42 ok.2 r⟩
  intro k t hk h
  have run:=m90 h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(m20 p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [m7,m40,m42 ok.1.2]
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
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat -> Nat)
def emptyPacking : Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat -> Nat) (pos len : Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat -> Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def m2 (α : Type):=List α
def m2.leaf {α} (xs : List α) : m2 α:=xs
def m2.fork {α} (_ : Nat) (a b : m2 α) : m2 α:=List.append a b
def m2.read {α} (tree : m2 α) (i : Nat):=(show List α from tree)[i]?
def m2.values {α} (tree : m2 α) : List α:=tree
theorem m2.read_mem {α} (tree : m2 α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
def Forest:=(Nat) × (Nat) × (Nat -> Bits × Bits) × (m2 ColumnInfo) × (Array (List Nat)) × (Nat -> Packing) × (Nat -> Nat -> Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat:=c.1
def Forest.cap (c : Forest) : Nat:=c.2.1
def Forest.samples (c : Forest) : Nat -> Bits × Bits:=c.2.2.1
def Forest.cols (c : Forest) : m2 ColumnInfo:=c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat):=c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat -> Packing:=c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat -> Nat -> Option (Nat × Nat):=c.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem m57 (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a:=by
  have base:=m122 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩:=List.mem_map.mp ha
    exact m34 false (base w hw) (m46 (m34 false
      (m27 base 0) (m27 base 1)))
  · exact base _ ha
def targetOf (g : Forest):=chartGoal g.mask
def chartSamples (m : Nat) (v : Nat -> Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat -> Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m)=(chartSamples m v).getLsbD i.val:=by
  by_cases e : m=1023
  · have u:=m53 v i (0 : Fin 9)
    have w:=m53 v i (1 : Fin 9)
    have h:=m77 m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val=(v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val=(v 1).getLsbD i.val at w
    have seedEq : oldSeed=inputs.getD 0 zero &&& inputs.getD 1 zero:=by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using m77 m v i
theorem m66 {m : Nat} {p q : Nat -> Bits}
    (hp : chartSamples m p=BitVec.allOnes 768) (hq : chartSamples m q=0) :
    properPairs (chartGoal m) (asRow p) (asRow q):=by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α -> List α
  | [] => []
  | w::ws => if bits &&& 1==1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem m58 {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws:=by
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
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat -> List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem m51 (g : Forest)
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid=some c) :
    ValidPool (vars g.mask) (targetOf g) c:=by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply m37 _ h
    exact cols ci (g.cols.read_mem e)
def getPairs (data : Nat -> Nat) (w v : Nat) : Nat -> Nat -> List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem m91 (g : Forest) (k : Nat)
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
      exact m85 (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
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
theorem m33 (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values,Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList,autoOK (targetOf g) (x.map swapRows)=true)
    (prior : k>0 -> ∀ j < (g.levels (k-1)).1,Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
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
    apply m48 _ _ _ _ _ (m57 g) v
    exact (m58 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact m51 g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact m91 g _ names (prior (by omega)) h
def block (g : Forest) (k start : Nat) : Nat -> Bool
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
theorem m5 {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true:=by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1=true
def graphValid (g : Forest) (prior : Nat -> Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2)==0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat -> Nat)
    (lower : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : checkedTables g top) :
    ∀ k ≤ top,∀ i < (g.levels k).1,Impossible (targetOf g) k (stateSet g k i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply m33 g 0 i (m66 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => m50 _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply m33 g _ i (m66 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => m50 _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1)&&sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws=true) : Impossible (targetOf g) k ws.toFinset:=by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←m11 idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1
theorem m17 {g prior i hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask)=true) (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply m43 (m19 _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply m35 ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
theorem m10 {g prior ci hints} (low : ∀ q,Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior=true)
    (hp : properB (targetOf g)=true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst=vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1):=by
  apply m43 (m19 _ hp) _ (m111 (m50 ci prior low ok) [] rfl nd cut)
  intro a ha
  apply m35 ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
def Known (entries : List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem m0 {old L m relabels} (previous : Known old)
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
def combineLanes {α : Type} (f : α -> Bits) : List α -> Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat -> Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem m95 (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v=lanePlace (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (m95 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v=lanePlace (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (m95 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v=lanePlace (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (m95 _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem m93 {α} (f g : α -> Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs=combineLanes (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem m82 {α} (f g : α -> Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs=combineLanes (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem m92 {α} (f g : α -> Bits) (xs) :
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
theorem mark_at {α} (f : α -> Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
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
def packedSig {α} (s : α -> Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α -> Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem xor_meet (a b : Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
theorem m12 {α} (s : α -> Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs)=combineLanes (fun x => column d (s x)) xs:=by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,m93,m92,xor_meet]
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
theorem m125 {α} (a b : α -> Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,m92,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,m82,m93,movedDecor,codeDecor,dbin]
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
theorem m67 {α} (c : α -> Cov) (a b : α -> Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,m93,m82,m92,xor_meet,restCov,takeOne,takeTwo,
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
def onMarks {α : Type} (f : α -> Bool) (mask : Nat) : List α -> Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1==0)||f x)&&onMarks f (mask >>> 769) xs
theorem m126 {α} (f : α -> Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
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
theorem m94 (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i=packedSig (fun c => (contextWire c i).2) xs:=by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero||m==p.domain||(p.wires.map (masked p.domain)).any (fun v => v==m)
theorem m25 (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x=availableMasked p (masked p.domain x):=rfl
def constantLoss (p : Decor -> Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem m127 (p : Decor -> Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p+constantLoss p a keep:=by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]
theorem keptCount (p : Decor -> Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un||kb) ≤
    (opKeep un ka kb a b ws).countP p:=by
  have h1:=m127 p ws a ka
  have h2:=m127 p (delOne ws a ka) b kb
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
theorem m72 {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
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
    have ready : free=true -> availableB p.domain p.wires z=true:=by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [m25,za,←m25]
        exact hav _ ha
      · rw [m25,zb,←m25]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat:=by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((m71 ws a b (op==2) ka kb).subset hw)
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
theorem m123 {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true:=by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1:=by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
  have closed:=m72 (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length /\ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem m102 {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true:=by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact m123 yes.1 yes.2 h
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
theorem m133 (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
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
    have ca : a=_:=m94 k n xs hi
    have cb : b=_:=m94 k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,m125,m12,m12,m12,chosen,m67,m82] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · apply m102
      apply m126 _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f:=batchMove b xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false&&batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0&&batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat -> Bool
  | [] => true
  | i::js => batchRow b xs i js&&batchRows b xs js
theorem m132 (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@m133 k n xs
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
theorem m136 {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true:=by
  have all:=m132 k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
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
theorem m128 (g : Forest) (k i : Nat) :
    nodeVerified g k i=(prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)):=rfl
theorem makeBlock {g k start n} (h : ∀ (i : Nat),start ≤ i -> i < start+n -> nodeVerified g k i=true) :
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
theorem m84 {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true:=by
  have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem m120 {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true:=by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt:=List.mem_range.mp hj
  by_cases first : j<a
  · exact m84 h (lo+j) (by omega) (by omega)
  · exact m84 t (lo+j) (by omega) (by omega)
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
      have ok:=m84 h lo (by omega) (by omega)
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
  rw [m128,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ m136 hq hb ha hn (cutsRun h)
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat -> Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d /\ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true:=by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v:=m120 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g : Forest) (k start n ar rows : Nat) : Nat -> Prop
  | 0 => header g k start n ar=true /\ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d /\ cells g k (start+n/2) (n-n/2) ar rows d
theorem m1 {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true:=by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v:=m5 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def listPieces {α} (f : α -> Bool) (xs : List α) : Nat -> Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d /\ listPieces f (xs.drop (xs.length/2)) d
theorem m3 {α f xs d} (h : @listPieces α f xs d) : xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat:=0xf
def g15l3 : Packing:=(1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : m2 ColumnInfo:=(.leaf [])
def g15autos : Array (List Nat):=Array.mk [[],[33,48]]
def g15levels : Nat -> Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat -> Nat -> Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest:=⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat:=0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat:=0x84001e90fd02fd01fa00
def g31l5 : Packing:=(3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat:=0x11a20bf
def g31l6 : Packing:=(1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : m2 ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat -> Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat -> Nat -> Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest:=⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits):=Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : m2 ColumnInfo:=(.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat):=Array.mk [[],[83,32]]
def g47levels : Nat -> Packing
  | _ => emptyPacking
def g47index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest:=⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits):=Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : m2 ColumnInfo:=(.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat):=Array.mk [[],[84]]
def g55levels : Nat -> Packing
  | _ => emptyPacking
def g55index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest:=⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits):=Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : m2 ColumnInfo:=(.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat):=Array.mk [[],[50,65]]
def g63levels : Nat -> Packing
  | _ => emptyPacking
def g63index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest:=⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat:=0x120ff
def g111l6 : Packing:=(1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits):=Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : m2 ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat):=Array.mk [[],[83,32]]
def g111levels : Nat -> Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest:=⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits):=Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : m2 ColumnInfo:=(.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat):=Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat -> Packing
  | _ => emptyPacking
def g119index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest:=⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat:=0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat:=0x82000f487f40bfa03fa00
def g189l6 : Packing:=(3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat:=0x1f5859bf
def g189l7 : Packing:=(1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits):=Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : m2 ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat -> Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest:=⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits):=Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : m2 ColumnInfo:=(.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat):=Array.mk [[],[101,66,16]]
def g127levels : Nat -> Packing
  | _ => emptyPacking
def g127index : Nat -> Nat -> Option (Nat × Nat)
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
def g191columns : m2 ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat -> Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest:=⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits):=Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : m2 ColumnInfo:=(.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat):=Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat -> Packing
  | _ => emptyPacking
def g251index : Nat -> Nat -> Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest:=⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits):=Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : m2 ColumnInfo:=(.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat -> Packing
  | _ => emptyPacking
def g255index : Nat -> Nat -> Option (Nat × Nat)
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
def g383columns : m2 ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat -> Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat -> Nat -> Option (Nat × Nat)
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
theorem valid3 : Known known3:=m0 baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2:=size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat):=[]
def known7:=extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7:=m0 valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=0) ?_⟩,m3 (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true:=by
  apply m1 (ar:=4) (rows:=0) (d:=0)
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
  m17 (g:=g15) (i:=0) (hints:=8449) (m4 known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15:=extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15:=m0 valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3:=size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat):=[]
def known45:=extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45:=m0 valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3:=size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat):=[]
def known51:=extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51:=m0 valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=1) ?_⟩,m3 (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true:=by
  apply m1 (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3=true:=(@m5 g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true:=by
  apply m1 (ar:=5) (rows:=0) (d:=0)
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
  m17 (g:=g31) (i:=0) (hints:=8449) (m4 known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31:=extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31:=m0 valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  m10 (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (m4 known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47:=extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47:=m0 valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  m10 (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (m4 known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55:=extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55:=m0 valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  m10 (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (m4 known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63:=extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63:=m0 valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=0) ?_⟩,m3 (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
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
  m17 (g:=g111) (i:=0) (hints:=16785665) (m4 known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111:=extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111:=m0 valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  m10 (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (m4 known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119:=extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119:=m0 valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=1) ?_⟩,m3 (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3=true:=(@m5 g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true:=by
  apply m1 (ar:=6) (rows:=0) (d:=0)
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
  m17 (g:=g189) (i:=0) (hints:=536879876) (m4 known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189:=extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189:=m0 valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5:=size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat):=[]
def known250:=extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250:=m0 valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  m10 (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (m4 known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127:=extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127:=m0 valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=4) ?_⟩,m3 (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1=true:=s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28=true:=(@m5 g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100=true:=(@m5 g191 8 0 68 32 (@m5 g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12=true:=(@m5 g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true:=by
  apply m1 (ar:=7) (rows:=0) (d:=0)
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
  m17 (g:=g191) (i:=0) (hints:=536879361) (m4 known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191:=extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191:=m0 valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  m10 (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (m4 known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251:=extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251:=m0 valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  m10 (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (m4 known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255:=extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255:=m0 valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=4) ?_⟩,m3 (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25=true:=(@m5 g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true:=by
  apply m1 (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91=true:=(@m5 g383 9 0 84 7 (@m5 g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true:=by
  apply m1 (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41=true:=(@m5 g383 10 0 21 20 (@m5 g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true:=by
  apply m1 (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true:=by
  apply m1 (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6=true:=(@m5 g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true:=by
  apply m1 (ar:=8) (rows:=1) (d:=0)
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
  m17 (g:=g383) (i:=0) (hints:=12901687553) (m4 known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383:=m0 valid255 low383 (by decide +kernel)
def deadsamples : Array (Bits × Bits):=Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : m2 ColumnInfo:=(.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest:=⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383)=true:=by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,m3 (d:=5) ?_⟩,m3 (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
def isNotT (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
private lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w /\ proper a /\ gv w g=neg a
       else ∃ d a b,a∈w /\ b∈w /\ proper a /\ proper b /\ a≠b /\ gv w g=bin d a b):=by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) \/ ∃ x,x∈w /\ proper x /\ neg a=neg x:=by
    rcases m13 ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 m70.1)
    · exact Or.inl (Or.inr fun h => h.1 m70.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b) \/ ∃ d' x y,x∈w /\ y∈w /\ proper x /\ proper y /\ x≠y /\ bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero /\ bin true v zero=v:=fun v => ⟨(m16 v).2.2.1,(m16 v).2.1⟩
    have bone : ∀ v,bin false v one=v /\ bin true v one=one:=fun v => ⟨(m16 v).1,(m16 v).2.2.2.1⟩
    rcases m13 ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [m24]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [m24]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases m13 hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a=b
        · subst b
          cases d
          · rw [(m16 a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(m16 a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩:=hg
  rcases ho with ho | ho | ho
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(m16 _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho,isNotT,ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,m70.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)
private lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a,a∈w /\ proper a /\ z=neg a
       else ∃ d a b,a∈w /\ b∈w /\ proper a /\ proper b /\ a≠b /\ z=bin d a b))
    (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1 /\ t' ≤ t+isN.toNat /\ Live target k' t' S' /\ ∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w \/ a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=m22 h z hm
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
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length /\ t ≤ gs.countP (fun g => isNotT g.op) /\ Live target k t S /\ ∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩:=pull_gateT (isNotT g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega
def I1 (T : Sig) (cap tm : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap -> t ≤ tm -> ¬Live T k t S
theorem i2i1 {T cap tm S} (h : Impossible T cap S) : I1 T cap tm S :=
  fun k t hk _ => h k t hk
theorem re1 {T n tm} {ws : List Sig} (hi : I1 T n tm ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : I1 T n tm (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p):=fun r => ⟨movedRow p.reverse r,m42 ok.2 r⟩
  intro k t hk ht h
  have run:=m90 h (movedRow p) onto
  have goal : rename (movedRow p) T=T:=(m20 p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [m7,m40,m42 ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p))=ws.toFinset:=by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run
def child1 (tm cap len op : Nat) : Nat :=
  if len==cap||op==2||tm==0 then 0 else 1
theorem es1 {T : Sig} {cap tm : Nat} {ws : List Sig} (htm1 : tm ≤ 1) (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tm > 0 -> ∀ a ∈ ws,∀ keep,neg a ∉ ws -> proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      I1 T (cap-1) (child1 tm cap (childOne ws a keep).length 2) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a≠b -> bin d a b ∉ ws →
      proper (bin d a b) -> (childTwo ws a b d ka kb).length ≤ cap →
      I1 T (cap-1) (child1 tm cap (childTwo ws a b d ka kb).length 0)
        (childTwo ws a b d ka kb).toFinset) :
    I1 T cap tm ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=m39 hn a
    have rest : (kept keep a (ws.erase a)).toFinset=U:=by
      rw [m28,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset=insert (neg a) U:=by simp [childOne,rest]
    have sc:=(m26 tail).2
    have len : (childOne ws a keep).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have htm_pos : tm > 0:=by omega
    have ht' : t ≤ child1 tm cap (childOne ws a keep).length 2:=by
      unfold child1; simp; omega
    exact oneStep htm_pos a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=m22 tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,m39 (hn.erase _) b,m39 hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset=U:=by
      rw [m28,m28,er,he]
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
    have sc:=(m26 tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap:=by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : t ≤ child1 tm cap (childTwo ws a b d ka kb).length 0:=by
      unfold child1
      by_cases hlen : (childTwo ws a b d ka kb).length=cap
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; simp [hlen]; omega
      · by_cases htm0 : tm=0
        · simp [htm0]; omega
        · have hne : ((childTwo ws a b d ka kb).length==cap||0==2||tm==0)=false:=by
            simp [beq_eq_false_iff_ne.mpr hlen,beq_eq_false_iff_ne.mpr htm0]
          rw [hne]; simp; omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
def sameWordsF (a b : List Sig) : Bool := a.length==b.length&&a.all (fun x => b.contains x)
lemma sameWordsF_eq {xs ys : List Sig} (hnd : xs.Nodup) (h : sameWordsF xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWordsF,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  have hsub : xs.toFinset ⊆ ys.toFinset:=fun x hx => List.mem_toFinset.mpr (h.2 x (List.mem_toFinset.mp hx))
  have hle : ys.toFinset.card ≤ xs.toFinset.card:=by
    rw [List.toFinset_card_of_nodup hnd,h.1]; exact List.toFinset_card_le ys
  exact Finset.eq_of_subset_of_card_le hsub hle
def closeChild1 (pools : List BoundPool) (links : Nat -> List (List Sig)) (k : Nat) (rest : List Sig) (op : Choice) (z : Sig) : Bool :=
  let ws:=z::rest
  (links (keySet ws)).any (sameWordsF ws)||pools.any (fun p => scalarPoolCut p k rest op)
theorem cc1s {raw T pools links k tm rest op}
    (pValid : ∀ p ∈ pools,ValidPool raw T p)
    (lValid : ∀ tag xs,xs ∈ links tag -> I1 T k tm (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild1 pools links k rest op (choiceVal op)=true) :
    I1 T k tm (choiceVal op :: rest).toFinset:=by
  simp only [closeChild1,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWordsF_eq nd ok]; exact lValid _ _ hx
  · exact i2i1 (m9 (pValid _ hp) nd ok)
abbrev LinkFn:=Nat -> List (List Sig)
abbrev QuickPool2:=BoundPool × Nat × Bool × List Sig
def sumPool2 (ws : List Decor) (p : BoundPool) : QuickPool2 :=
  let mw:=p.wires.map (masked p.domain)
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1),mw)
def sumPool2_fast (ws : List Decor) (p : BoundPool) : QuickPool2 :=
  let mw:=p.wires.map (masked p.domain)
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => let m:=masked p.domain w.1; m==zero||m==p.domain||mw.any (fun v => v==m)),mw)
lemma sumPool2_eq (ws : List Decor) (p : BoundPool) : sumPool2_fast ws p=sumPool2 ws p:=rfl
def fastCost2 (s : QuickPool2) (k : Nat) (a b : Decor) (z : Sig) (un ka kb : Bool) : Bool :=
  if !s.2.2.1 then false else
  let p:=s.1
  let zm:=masked p.domain z
  let zc:=zm==zero||zm==p.domain
  let la:=if ka then 0 else (isMaskedConstant p.domain a.1).toNat
  let lb:=if un||kb then 0 else (isMaskedConstant p.domain b.1).toNat
  let cm:=s.2.1 - la - lb + zc.toNat
  let free:=zc||s.2.2.2.any (fun v => v==zm)
  decide (k+p.paid+(!free).toNat < p.bound+cm)
lemma m72_2 {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost2 (sumPool2_fast ws p) k a b (choiceVal (movedChoice op a b)) (op==2) ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true:=by
  rw [sumPool2_eq] at h
  let z:=choiceVal (movedChoice op a b)
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let rest:=opKeep (op==2) ka kb a b ws
  have ck:=keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav:=List.all_eq_true.mp all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact hav w ((m71 ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true:=by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost2,sumPool2,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const+if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost2,sumPool2,all] at h
abbrev NC1 :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool2 × LinkFn × LinkFn
def cw1 (c : NC1) (i : Nat) : Decor:=c.2.2.2.1.getD i defaultDecor
def em1 (c : NC1) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,cov,pools,qpools,l0,l1):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let ct:=child1 tm cap len op
    let d:=ct==0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
    if qpools.any (fun qp => fastCost2 qp (cap-1) a b z.1 un ka kb) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      let links:=if d then l0 else l1
      closeChild1 pools links (cap-1) rest (movedChoice op a b) z.1
theorem e1s {raw T r s ws pools l0 l1 cap tm a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false -> a≠b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag -> I1 T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag -> I1 T (cap-1) 1 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : em1 (cap,tm,ws.length,ws,preCov ws,pools,pools.map (sumPool2_fast ws),l0,l1)
      op a b (movedDecor op a b) ka kb=true) :
    I1 T (cap-1) (child1 tm cap (moveFront ws op a b ka kb).length op)
      (moveFront ws op a b ka kb).toFinset:=by
  let z:=movedDecor op a b
  let rest:=opKeep (op==2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=m71 _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=m54 op a b
  have fr : ws.any (fun v => v.1==z.1)=false:=by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1=true:=by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))=child.length:=by
    change _=(z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz:=(m26 h).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold em1 at test
  change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  let ct:=child1 tm cap child.length op
  have ht0 : (ct==0)=true -> t=0:=fun hct => by have:=beq_iff_eq.mp hct; change t ≤ ct at ht; omega
  have sep:=m96 h rfl (pair_sep pairs) (ct==0) ht0
  let d:=ct==0
  have g : (coverage d rest).1=covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz:=m69 ha hb (op==2) ka kb d ne
  have hf:=m60 (faith _ ha) (faith _ hb) op
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
  by_cases hq : (pools.map (sumPool2_fast ws)).any (fun qp => fastCost2 qp (cap-1) a b z.1 (op==2) ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩:=List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hqp
    exact m9 (pv p hp) nd' (m72_2 ha hb (val ▸ hfc)) k t hk h'
  · have hqf : (pools.map (sumPool2_fast ws)).any (fun qp => fastCost2 qp (cap-1) a b z.1 (op==2) ka kb)=false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (sumPool2_fast ws)).any fun qp => fastCost2 qp (cap-1) a b z.1 (op==2) ka kb)=true then true else _)=true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true,ite_false] at test
    by_cases hd : d=true
    · dsimp only [d,ct] at hd; rw [hd] at test; simp only [ite_true] at test
      exact cc1s pv lv0 nd' (val ▸ test) k t hk (by have:=ht0 hd; omega) h'
    · have hdf : d=false:=Bool.eq_false_iff.mpr hd
      dsimp only [d,ct] at hdf; rw [hdf] at test; simp only [Bool.false_eq_true,ite_false] at test
      have hct1 : ct ≤ 1:=by dsimp only [ct,child1]; split_ifs <;> omega
      exact cc1s pv lv1 nd' (val ▸ test) k t hk (by change t ≤ ct at ht; omega) h'
def tp1 (ctx : NC1) (a b : Decor) (d : Bool) : Bool :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  em1 ctx op a b z false false&&em1 ctx op a b z true false &&
    em1 ctx op a b z false true&&em1 ctx op a b z true true
def tr1 (ctx : NC1) (a : Decor) (bs : List Decor) : Bool :=
  let unOk:=if ctx.2.1==0 then true else
    let n:=movedDecor 2 a a
    em1 ctx 2 a a n false false&&em1 ctx 2 a a n true true
  unOk&&bs.all (fun b => tp1 ctx a b false&&tp1 ctx a b true)
def ta1 (ctx : NC1) : List Decor -> Bool
  | [] => true
  | a :: ws => tr1 ctx a ws&&ta1 ctx ws
theorem au1 {ctx} {ws : List Decor} (h : ta1 ctx ws=true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    em1 ctx 2 a a (movedDecor 2 a a) keep keep=true:=by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [ta1,Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · have hr:=h.1
      simp only [tr1,Bool.and_eq_true] at hr
      have hne : (ctx.2.1==0)=false:=beq_eq_false_iff_ne.mpr (by omega)
      have hu:=hr.1
      rw [hne] at hu; simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true] at hu
      cases keep <;> [exact hu.1; exact hu.2]
    · exact ih h.2 hm
theorem ab1 {ctx} {ws : List Decor} (h : ta1 ctx ws=true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (d : Bool) :
    tp1 ctx a b d=true \/ tp1 ctx b a d=true:=by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [ta1,Bool.and_eq_true,tr1,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact False.elim (ne rfl)
    · left; cases d <;> [exact (h.1.2 b hb').1; exact (h.1.2 b hb').2]
    · right; cases d <;> [exact (h.1.2 a ha').1; exact (h.1.2 a ha').2]
    · exact ih h.2 ha' hb'
theorem tp1_at {ctx a b d} (h : tp1 ctx a b d=true) (ka kb : Bool) :
    em1 ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb=true:=by
  simp only [tp1,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> simp [h]
theorem n1s {raw T r s ws pools l0 l1 cap tm}
    (htm1 : tm ≤ 1) (pairs : properPairs T r s) (faith : ∀ w ∈ ws,faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools,ValidPool raw T p)
    (lv0 : ∀ tag xs,xs ∈ l0 tag -> I1 T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs,xs ∈ l1 tag -> I1 T (cap-1) 1 (List.toFinset xs))
    (checks : cap=0 \/ ta1 (cap,tm,ws.length,ws,preCov ws,pools,pools.map (sumPool2_fast ws),l0,l1) ws=true) :
    I1 T cap tm (ws.map Prod.fst).toFinset:=by
  rcases checks with rfl | checks
  · intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 -> S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  by_cases hc : cap=0
  · subst hc
    intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 -> S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply es1 htm1 nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hv
    have hf:=m83 nd ha keep
    have hev:=e1s (op:=2) pairs faith nd ha ha (by simp) hc' pv lv0 lv1 pro fresh (au1 checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length=(childOne (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup:=by
        unfold moveFront
        have sub:=m71 ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_,kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [m23] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
    rw [hf,hlenEq] at hev
    exact hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
    have ab : a≠b:=fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : tp1 (cap,tm,ws.length,ws,preCov ws,pools,pools.map (sumPool2_fast ws),l0,l1) a b d=true) :
        I1 T (cap-1) (child1 tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length 0)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      have hf:=m78 nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      have hop0 : child1 tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length (if d then 1 else 0)=child1 tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length 0:=by cases d <;> rfl
      have hev:=e1s (op:=if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv0 lv1
        (eq ▸ pr) (eq ▸ fr) (tp1_at test ka kb)
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup:=by
          unfold moveFront
          have sub:=m71 ws a b ((if d then 1 else 0)==2) ka kb
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
          rw [m23] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [m23] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1,←List.toFinset_card_of_nodup nd2,hf]
      rw [hf,hlenEq,hop0] at hev
      exact hev
    rcases ab1 checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw:=m73 (ws.map Prod.fst) nd a.1 b.1 d ka kb
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
          rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
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
          rw [m24 d b.1 a.1] at hm
          rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [m23] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA,←List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (m24 d a.1 b.1 ▸ pro) (m24 d a.1 b.1 ▸ fresh) hh
abbrev PT:=Nat × Nat × Nat × Nat × (Nat -> Nat)
def ePT : PT:=(0,0,0,0,fun _ => 0)
def dW : List Decor:=wiresOf dead
def dS : List Sig:=dW.map Prod.fst
def dcS (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) zero
    let b:=ws.getD ((bits >>> 4) &&& 15) zero
    let op:=(bits >>> 8) &&& 3
    dcS k (bits >>> 10) (ws ++ [if op=2 then neg a else bin (op==1) a b])
theorem m116 (n bits : Nat) (ws : List Decor) :
    dcS n bits (ws.map Prod.fst)=(decodeBank n bits ws).map Prod.fst:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [dcS,decodeBank]
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
theorem sLm {α β : Type} (f : α -> β) (bits : Nat) (ws : List α) :
    selectLive bits (ws.map f)=(selectLive bits ws).map f:=by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,selectLive]
    split <;> simp [ih]
def rN (levels : Nat -> PT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw:=dW
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def sS (levels : Nat -> PT) (slot i : Nat) : List Sig :=
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+dS.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (dcS depth ops dS)
theorem m119 (levels : Nat -> PT) (slot i : Nat) :
    sS levels slot i=(rN levels slot i).2.2.map Prod.fst:=by
  unfold sS rN
  rcases levels slot with ⟨num,depth,cw,offw,data⟩
  dsimp only
  have hlen : dS.length=dW.length:=by simp [dS]
  rw [hlen]
  dsimp only [dS]
  rw [m116,sLm]
def emptyPT : PT:=(0,0,0,0,fun _ => 0)
def lw0 (nb slots sw vw iw pw : Nat) (data : Nat -> Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a * sw) sw
  let row:=(h / nb + sh) % slots
  let word:=packedAt data (nb * sw + row * vw) vw
  some (word &&& ((1 <<< iw) - 1),(word >>> iw) &&& ((1 <<< pw) - 1))
def inS0 : Sig:=inputs.getD 0 zero
def inS1 : Sig:=inputs.getD 1 zero
def inS2 : Sig:=inputs.getD 2 zero
def inS3 : Sig:=inputs.getD 3 zero
def inS4 : Sig:=inputs.getD 4 zero
def inS5 : Sig:=inputs.getD 5 zero
def inS6 : Sig:=inputs.getD 6 zero
def inS7 : Sig:=inputs.getD 7 zero
def inS8 : Sig:=inputs.getD 8 zero
def rotS0 : List Sig:=[inS0,inS1,inS2,inS3,inS4,inS5,inS6,inS7,inS8]
def rotS1 : List Sig:=[inS0,inS5,inS8,inS3,inS4,inS1,inS7,inS6,inS2]
def rotS2 : List Sig:=[inS1,inS0,inS5,inS8,inS6,inS2,inS4,inS7,inS3]
def rotS3 : List Sig:=[inS1,inS2,inS3,inS8,inS6,inS0,inS7,inS4,inS5]
def rotS4 : List Sig:=[inS2,inS1,inS0,inS5,inS7,inS3,inS6,inS4,inS8]
def rotS5 : List Sig:=[inS2,inS3,inS8,inS5,inS7,inS1,inS4,inS6,inS0]
def rotS6 : List Sig:=[inS3,inS2,inS1,inS0,inS4,inS8,inS7,inS6,inS5]
def rotS7 : List Sig:=[inS3,inS8,inS5,inS0,inS4,inS2,inS6,inS7,inS1]
def rotS8 : List Sig:=[inS5,inS0,inS1,inS2,inS7,inS8,inS4,inS6,inS3]
def rotS9 : List Sig:=[inS5,inS8,inS3,inS2,inS7,inS0,inS6,inS4,inS1]
def rotS10 : List Sig:=[inS8,inS3,inS2,inS1,inS6,inS5,inS4,inS7,inS0]
def rotS11 : List Sig:=[inS8,inS5,inS0,inS1,inS6,inS3,inS7,inS4,inS2]
def rotDS : Nat -> Option (List Sig)
  | 0 => some rotS0
  | 1 => some rotS1
  | 2 => some rotS2
  | 3 => some rotS3
  | 4 => some rotS4
  | 5 => some rotS5
  | 6 => some rotS6
  | 7 => some rotS7
  | 8 => some rotS8
  | 9 => some rotS9
  | 10 => some rotS10
  | 11 => some rotS11
  | _ => none
lemma rotDS_eq : (List.range 12).all (fun p =>
    match rotDS p, dead.autos[p]? with
    | some xs, some perm => xs == dS.map (movedWord (perm.map swapRows).reverse)
    | _, _ => false)=true:=by decide +kernel
lemma rotDS_at (p : Nat) : rotDS p = (dead.autos[p]?).map (fun perm => dS.map (movedWord (perm.map swapRows).reverse)):=by
  by_cases hp : p < 12
  · have h:=List.all_eq_true.mp rotDS_eq p (List.mem_range.mpr hp)
    cases h1 : rotDS p <;> cases h2 : dead.autos[p]? <;> simp [h1,h2] at h ⊢
    exact h
  · have h1 : rotDS p=none:=by
      unfold rotDS
      match p with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
      | _ + 12 => rfl
    have h2 : dead.autos[p]?=none:=Array.getElem?_eq_none (by change deadautos.size ≤ p; have : deadautos.size=12:=rfl; omega)
    rw [h1,h2]; rfl
lemma dcS_movedWord (ms : List Move) (n bits : Nat) (ws : List Sig) :
    dcS n bits (ws.map (movedWord ms))=(dcS n bits ws).map (movedWord ms):=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [dcS]
    have hget (i : Nat) : (ws.map (movedWord ms)).getD i zero=movedWord ms (ws.getD i zero):=by
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? with
      | none => exact ((m20 ms zero).trans (m79 (movedRow ms)).1).symm
      | some x => rfl
    rw [hget,hget]
    have hop : (if ((bits >>> 8) &&& 3)=2 then neg (movedWord ms (ws.getD (bits &&& 15) zero))
        else bin (((bits >>> 8) &&& 3)==1) (movedWord ms (ws.getD (bits &&& 15) zero)) (movedWord ms (ws.getD ((bits >>> 4) &&& 15) zero))) =
        movedWord ms (if ((bits >>> 8) &&& 3)=2 then neg (ws.getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3)==1) (ws.getD (bits &&& 15) zero) (ws.getD ((bits >>> 4) &&& 15) zero)):=by
      simp only [m20]; split
      · exact (rename_neg _ _).symm
      · exact (rename_bin _ _ _ _).symm
    rw [hop,← List.map_singleton,← List.map_append]
    exact ih (bits >>> 10) _
def sS_base (levels : Nat -> PT) (slot i : Nat) (base : List Sig) : List Sig :=
  let (_,depth,_,_,data):=levels slot
  let len:=10 * depth
  let width:=len+dS.length+depth
  let recp:=packedAt data (i * width) width
  let ops:=recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (dcS depth ops base)
lemma sS_base_eq (levels : Nat -> PT) (slot i : Nat) (ms : List Move) :
    sS_base levels slot i (dS.map (movedWord ms))=(sS levels slot i).map (movedWord ms):=by
  unfold sS_base sS
  rcases levels slot with ⟨num,depth,cw,offw,data⟩
  dsimp only
  rw [dcS_movedWord,sLm]
def lS (levels : Nat -> PT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (rotDS pair.2).map (sS_base levels slot pair.1)
theorem ls1s (levels : Nat -> PT) (k tm : Nat)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (earlier : ∀ i < (levels (3*k+tm)).1,I1 (targetOf dead) k tm (sS levels (3*k+tm) i).toFinset)
    {pair out} (h : lS levels (3*k+tm) pair=some out) :
    I1 (targetOf dead) k tm out.toFinset:=by
  unfold lS at h
  split at h
  · cases h
  next valid =>
    rw [rotDS_at] at h
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      rw [← h,sS_base_eq]
      exact re1 (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def ctx1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm i : Nat) : NC1 :=
  let slot:=3 * k+tm
  let raw:=dW
  let (num,depth,cw,offw,data):=levels slot
  let (ops,bank,ws):=rN levels slot i
  let start:=num * (10 * depth+raw.length+depth)
  let c0:=packedAt data (start+i * offw) offw
  let c1:=packedAt data (start+(i+1) * offw) offw
  let nr:=c1 - c0
  let st:=start+(num+1) * offw+c0 * (cw+depth)
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule dead ops depth bank a b)
  let ls0:=fun tag => ((idx0 slot tag).bind (lS levels (3*(k-1)))).toList
  let ls1:=fun tag => ((idx1 slot tag).bind (lS levels (3*(k-1)+1))).toList
  (k,tm,ws.length,ws,preCov ws,rules,rules.map (sumPool2_fast ws),ls0,ls1)
def pre1 (T : Sig) (c : NC1) : Bool :=
  let ws:=c.2.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
def nv1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm i : Nat) : Bool :=
  let c:=ctx1 levels idx0 idx1 k tm i
  pre1 (targetOf dead) c&&(if k=0 then true else ta1 c c.2.2.2.1)
theorem nv1s (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm i : Nat)
    (htm1 : tm ≤ 1) (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList,autoOK (targetOf dead) (x.map swapRows)=true)
    (prior0 : k > 0 -> ∀ j < (levels (3*(k-1))).1,I1 (targetOf dead) (k-1) 0 (sS levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 -> ∀ j < (levels (3*(k-1)+1)).1,I1 (targetOf dead) (k-1) 1 (sS levels (3*(k-1)+1) j).toFinset)
    (checked : nv1 levels idx0 idx1 k tm i=true) :
    I1 (targetOf dead) k tm (sS levels (3*k+tm) i).toFinset:=by
  rw [m119]
  simp only [nv1,pre1,ctx1,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at checked
  have hN:=checked.1.1
  have hT : targetOf dead ∉ (rN levels (3*k+tm) i).2.2.map Prod.fst:=checked.1.2
  by_cases h0 : k=0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k'=0:=by omega
    subst k'
    generalize he : ((rN levels (3*0+tm) i).2.2.map Prod.fst).toFinset=S at h
    have eqS : S={_}:=h (fun k _ S => k=0 -> S={_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply n1s (raw:=vars dead.mask) htm1 samples _ hN hT _ _ _ (Or.inr (by simpa only [h0,ite_false] using checked.2))
  · intro v hv
    apply m48 _ _ _ _ _ (m57 dead) v
    exact (m58 _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
    exact m51 dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tm) tag).bind (lS levels (3*(k-1))))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1)=3*(k-1)+0:=by omega
    rw [h0'] at h
    exact ls1s levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tm) tag).bind (lS levels (3*(k-1)+1)))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
    exact ls1s levels (k-1) 1 names (prior1 (by omega)) h
def bk1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start : Nat) : Nat -> Bool
  | 0 => true
  | n+1 => nv1 levels idx0 idx1 k tm start&&bk1 levels idx0 idx1 k tm (start+1) n
theorem bk1_at {levels idx0 idx1 k tm start n} (h : bk1 levels idx0 idx1 k tm start n=true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+n) : nv1 levels idx0 idx1 k tm i=true:=by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [bk1,Bool.and_eq_true] at h
    by_cases eq : i=start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)
theorem m130 {levels idx0 idx1 k tm start a b}
    (ha : bk1 levels idx0 idx1 k tm start a=true)
    (hb : bk1 levels idx0 idx1 k tm (start+a) b=true) :
    bk1 levels idx0 idx1 k tm start (a+b)=true:=by
  induction a generalizing start with
  | zero => simpa [bk1] using hb
  | succ a ih =>
    simp only [bk1,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
theorem mkB1 {levels idx0 idx1 k tm start n}
    (h : ∀ i,start ≤ i -> i < start+n -> nv1 levels idx0 idx1 k tm i=true) :
    bk1 levels idx0 idx1 k tm start n=true:=by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [bk1,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
def chk1 (c : NC1) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a:=cw1 c i
  let b:=cw1 c j
  em1 c op a b (movedDecor op a b) ka kb
def cf1 (c : NC1) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a:=cw1 c i
  let b:=cw1 c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def fb1 (c : NC1) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,_,pools,qpools,l0,l1):=c
  let a:=ws.getD i defaultDecor
  let b:=ws.getD j defaultDecor
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  let ct:=child1 tm cap len op
  let z1:=choiceVal (movedChoice op a b)
  if !properB z1||ws.any (fun v => v.1==z1) then true else
  if qpools.any (fun qp => fastCost2 qp (cap-1) a b z1 un ka kb) then true else
    let rest:=(opKeep un ka kb a b ws).map Prod.fst
    let links:=if ct==0 then l0 else l1
    closeChild1 pools links (cap-1) rest (movedChoice op a b) z1
theorem fb1s {c i j op ka kb}
    (hlen : ¬(1+(c.2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > c.1))
    (h : fb1 c i j op ka kb=true) :
    chk1 c i j op ka kb=true:=by
  rcases c with ⟨cap,tm,n,ws,cov,pools,qpools,l0,l1⟩
  dsimp only [chk1,em1,cw1]
  dsimp only at hlen
  rw [if_neg hlen]
  dsimp only [fb1] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    m54 op _ _
  set len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  set ct:=child1 tm cap len op
  set d:=ct==0
  by_cases hcomb : ((restCov (getCov cov d) (column d (ws.getD i defaultDecor).2) (column d (ws.getD j defaultDecor).2) (op==2) ka kb ||| column d (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).2) != BitVec.allOnes 768)=true
  · simp only [hcomb,ite_true]
  · simp only [hcomb,ite_false,hz1]
    exact h
def mkBt1 (k n : Nat) (xs : List NC1) : Batch :=
  (k,n,units xs.length,
    (List.range n).map (fun i => packedSig (fun c => (cw1 c i).2) xs),
    packedCov (fun c => c.2.2.2.2.1.1) xs,
    packedCov (fun c => c.2.2.2.2.1.2) xs)
theorem lw1_at (k n : Nat) (xs : List NC1) {i : Nat} (h : i < n) :
    laneWire (mkBt1 k n xs) i=packedSig (fun c => (cw1 c i).2) xs:=by
  simp [laneWire,mkBt1,List.getD_eq_getElem?_getD,h]
def bmv1 (b : Batch) (tm : Nat) (xs : List NC1) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > k then true else
    let d:=child1 tm k len op==0
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r * (BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fb1 c i j op ka kb) mask xs
theorem bmv1a (k tm n : Nat) (xs : List NC1) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1=k) (ht : xs[q].2.1=tm) (arity : xs[q].2.2.1=n)
    (pass : bmv1 (mkBt1 k n xs) tm xs i j op ka kb=true) :
    chk1 xs[q] i j op ka kb=true:=by
  let len:=1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  let d:=child1 tm k len op==0
  have eval : chk1 xs[q] i j op ka kb =
      if len > k then true else if cf1 xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else fb1 xs[q] i j op ka kb:=by
    rcases hxq : xs[q] with ⟨cap,tmm,nn,ws,cov,pools,qpools,l0,l1⟩
    rw [hxq] at budget ht arity
    dsimp only at budget ht arity
    subst budget ht arity
    unfold chk1 em1 cf1 fb1 cw1
    dsimp only [len,d]
    have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
        choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)):=m54 op _ _
    rw [hz1]
  by_cases small : len > k
  · simp [eval,small]
  · let r:=units xs.length
    let a:=laneWire (mkBt1 k n xs) i
    let b:=laneWire (mkBt1 k n xs) j
    let cov:=if d then packedCov (fun c : NC1 => c.2.2.2.2.1.2) xs
               else packedCov (fun c : NC1 => c.2.2.2.2.1.1) xs
    change (if len > k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r * (BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg small] at pass
    have chosen : cov=packedCov (fun c => getCov c.2.2.2.2.1 d) xs:=by
      dsimp only [cov]; cases d <;> rfl
    have ca : a=_:=lw1_at k n xs hi
    have cb : b=_:=lw1_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,m125,m12,m12,m12,chosen,m67,m82] at pass
    by_cases hit : cf1 xs[q] d (op==2) ka kb op i j=BitVec.allOnes 768
    · have hlenq : ¬(1+(xs[q].2.2.1 - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > xs[q].1):=by
        rw [budget,arity]; exact small
      apply fb1s hlenq
      apply m126 _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def bp1 (b : Batch) (tm : Nat) (xs : List NC1) (i j op : Nat) : Bool :=
  let f:=bmv1 b tm xs i j op
  f false false&&f true false&&f false true&&f true true
def br1 (b : Batch) (tm : Nat) (xs : List NC1) (i : Nat) (js : List Nat) : Bool :=
  let unOk:=if tm==0 then true else
    bmv1 b tm xs i i 2 false false&&bmv1 b tm xs i i 2 true true
  unOk&&js.all (fun j => bp1 b tm xs i j 0&&bp1 b tm xs i j 1)
def brs1 (b : Batch) (tm : Nat) (xs : List NC1) : List Nat -> Bool
  | [] => true
  | i :: js => br1 b tm xs i js&&brs1 b tm xs js
theorem brs1a (k tm n : Nat) (xs : List NC1) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1=k) (ht : xs[q].2.1=tm) (arity : xs[q].2.2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js,j < n) (allRows : brs1 (mkBt1 k n xs) tm xs js=true) :
    ta1 xs[q] (js.map (cw1 xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [brs1,Bool.and_eq_true,br1,List.all_eq_true] at allRows
    simp only [List.map_cons,ta1,tr1,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=bounds i List.mem_cons_self
    have check:=@bmv1a k tm n xs
    have hun : (if xs[q].2.1==0 then true else
        em1 xs[q] 2 (cw1 xs[q] i) (cw1 xs[q] i) (movedDecor 2 (cw1 xs[q] i) (cw1 xs[q] i)) false false &&
        em1 xs[q] 2 (cw1 xs[q] i) (cw1 xs[q] i) (movedDecor 2 (cw1 xs[q] i) (cw1 xs[q] i)) true true)=true:=by
      rw [ht]
      cases htm : (tm==0)
      · simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true]
        have h1:=allRows.1.1
        simp only [htm,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h1
        exact ⟨check hi hi hq budget ht arity h1.1,check hi hi hq budget ht arity h1.2⟩
      · simp
    refine ⟨⟨hun,?_⟩,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj':=bounds j (List.mem_cons_of_mem _ hj)
    have both:=allRows.1.2 j hj
    have opCheck (d : Bool) (pass : bp1 (mkBt1 k n xs) tm xs i j (if d then 1 else 0)=true) :
        tp1 xs[q] (cw1 xs[q] i) (cw1 xs[q] j) d=true:=by
      simp only [bp1,Bool.and_eq_true] at pass
      simp only [tp1,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1,check hi hj' hq budget ht arity pass.1.1.2⟩,
        check hi hj' hq budget ht arity pass.1.2⟩,check hi hj' hq budget ht arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩
def rb1 (k tm n : Nat) (xs : List NC1) : Bool :=
  brs1 (mkBt1 k n xs) tm xs (List.range n)
theorem rb1a {k tm n} {xs : List NC1} {q} (hq : q < xs.length)
    (hb : xs[q].1=k) (ht : xs[q].2.1=tm) (ha : xs[q].2.2.1=n) (hn : xs[q].2.2.2.1.length=n)
    (pass : rb1 k tm n xs=true) : ta1 xs[q] xs[q].2.2.2.1=true:=by
  have all:=brs1a k tm n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (cw1 xs[q])=xs[q].2.2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [cw1,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def ctxs1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start n : Nat) : List NC1 :=
  ((List.range n).map (start+·)).map (ctx1 levels idx0 idx1 k tm)
def cc1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start n ar : Nat) : Bool :=
  let xs:=ctxs1 levels idx0 idx1 k tm start n
  xs.all (fun c => c.2.2.1==ar&&pre1 (targetOf dead) c) &&
  let b:=mkBt1 k ar xs
  (List.range ar).all (fun i => br1 b tm xs i (List.range' (i+1) (ar - (i+1))))
theorem cb1 {levels idx0 idx1 k tm start n ar}
    (h : cc1 levels idx0 idx1 k tm start n ar=true) :
    bk1 levels idx0 idx1 k tm start n=true:=by
  unfold cc1 at h
  rw [Bool.and_eq_true] at h
  let xs:=ctxs1 levels idx0 idx1 k tm start n
  have hrun : rb1 k tm ar xs=true:=by
    have go (lo num : Nat) (eq : lo+num=ar) :
        brs1 (mkBt1 k ar xs) tm xs (List.range' lo num)=true:=by
      induction num generalizing lo with
      | zero => rfl
      | succ num ih =>
        simp only [List.range'_succ,brs1,Bool.and_eq_true]
        refine ⟨?_,ih (lo+1) (by omega)⟩
        have ok:=List.all_eq_true.mp h.2 lo (List.mem_range.mpr (by omega))
        simpa only [show ar - (lo+1)=num by omega] using ok
    unfold rb1; rw [List.range_eq_range']; exact go 0 ar (by omega)
  apply mkB1
  intro i lo hi
  have hm : ctx1 levels idx0 idx1 k tm i ∈ xs:=by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
  have one:=List.all_eq_true.mp h.1 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e]; rfl
  have ht : xs[q].2.1=tm:=by rw [e]; rfl
  have ha : xs[q].2.2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.2.1.length=ar:=by rw [e]; exact one.1
  simp only [nv1,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ rb1a hq hb ht ha hn hrun
def cs1 (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (k tm start n ar : Nat) : Nat -> Prop
  | 0 => cc1 levels idx0 idx1 k tm start n ar=true
  | d+1 => cs1 levels idx0 idx1 k tm start (n / 2) ar d /\ cs1 levels idx0 idx1 k tm (start+n / 2) (n - n / 2) ar d
theorem k1 {levels idx0 idx1 k tm start n ar}
    (h : cc1 levels idx0 idx1 k tm start n ar=true) :
    cs1 levels idx0 idx1 k tm start n ar 0:=h
theorem csb1 {levels idx0 idx1 k tm start n ar d}
    (h : cs1 levels idx0 idx1 k tm start n ar d) :
    bk1 levels idx0 idx1 k tm start n=true:=by
  induction d generalizing start n with
  | zero => exact cb1 h
  | succ d ih =>
    have v:=m130 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
theorem f1_all (levels : Nat -> PT) (idx0 idx1 : Nat -> Nat -> Option (Nat × Nat)) (top : Nat)
    (prior : Nat -> Nat)
    (lo : ∀ m,Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior=true)
    (tabs : ∀ k ≤ top,∀ tm ≤ 1,bk1 levels idx0 idx1 k tm 0 (levels (3*k+tm)).1=true) :
    ∀ k ≤ top,∀ tm ≤ 1,∀ i < (levels (3*k+tm)).1,I1 (targetOf dead) k tm (sS levels (3*k+tm) i).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs:=m66 valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values,Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => m50 ci prior lo (valid.1.2 ci hc)
  have names:=valid.2
  intro k
  induction k with
  | zero =>
    intro hk tm htm i hi
    have hb:=tabs 0 hk tm htm
    exact nv1s levels idx0 idx1 0 tm i htm pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (bk1_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tm htm i hi
    have hb:=tabs (k+1) hk tm htm
    exact nv1s levels idx0 idx1 (k+1) tm i htm pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (bk1_at hb i (Nat.zero_le i) (by simpa using hi))
def pL24F (i : Nat) : Nat := 0x3b649c6549302e95348244
def pL24 : PT := (1,7,7,1,pL24F)
def pL27F (i : Nat) : Nat := 0x2e00b0035b6cd826c13619b04db600b0035ea600d01fcca568b0835ac5a9294a50729084108420800000000059afb74a92d9814c24483fe6e350daa6290489a7f0ca605514c1209130f7b7166152b8a6122696f61ecc2a5714c244d2debb59854ae298489a7b521b30a95c5309130f7b7166152b0a612261ef6decc2a5614c244c3ded959854ac298489a6bd62b30a9585309134f6b0366152b0a61227df04c520549814c244c37edd38c5d2a690489b6d9c64c0ba54d20913ee92a498174a9a41227dd25493054d8148244cbb665aa4a9b0488489f749534818354910913eec2a290306a92212271ed6d181546aa4c244c3dee2b6890d549848927badd325b3680219120f7dbae595240a612241efb75cb2a4214c244c2dedbd98549029848986bdb6b30a9085309130e7b6b6615210a612261ee6c2cc2a4214c244
def pL27 : PT := (29,6,7,5,pL27F)
def pH0_27F (i : Nat) : Nat := 0x0
def pH0_27 (h : Nat) : Option (Nat × Nat) := lw0 1 1 1 5 1 4 pH0_27F h
def pL28F (i : Nat) : Nat := 0x2202e4173c02e0102e4006005002803c00201706c801400a005002f803c01e00f007800197e007007800193c002087003801c00e00001400200f000806d832c19007b0640060010008028014001e006385f75b6db6d95d54d13cd2c91c50c0fbcebae36cb0baebacaaaa2692282079c69859449038c288184102082082082000078f46a1814c53048244ad5aec182db144a8c895eb1d0305b6289519123d69b6e3144c0aa3225ec9754b26098154644bd92ec144a9302a8c897b24da6095260551913f4496cc12a4c0aa322678d32d655897154644a35e6cb745b3029848907bddb325a7205309128e79b2e536a10a612251e7365ca6cc8548244c3da5c982d33469048986bcb9718a568d209133e1aa665ae6a92412260ef325b868ca148244c2de64b6ed19429048986bcc96d9a3285209130e7992dab4650a41226aad6a1c62858148244d59ad438a50b0290489ab95a870ca160520912fe43a060aa4a8a412252ed36da86055148244f592d42a4c0aa290489ada5c7694a1485209137f03a0e194290a41226b69329875c52148244b752eb19498a4290489afa0ca70131485209127b51b8b9a42b8241225fe074ca14857048244bf84e994aa926090489f708b954d524c120913fa118ea9aa498241227ae46a1814c53048244bed0eb94290a60904897f81d3285214c120913df01b498a4298241227de02e5314853048244c35e6496cd9b5088489479cd9729b3215109130f59726136ed1a212241ef770b9215a344244c2de5cb8e42b468848986bcb97188568d109130f3972e190ad1a212261eb2e5c2215a344244c3da5cb8242b468848987b8b97008568d109130d799263374c1a212241ef76cc968c5244244c35e64b6cd18a4884897f21d02c952545109130f719664b4690221225fc8744b55492044244df90e938a58a4088489bf21c5548b148110912bd63ac65aa2902212267e832dc25452044244ef9065aa4a8a4088489fd20d75495148110912bf41b6a8a42902212257e836d314852044244
def pL28 : PT := (65,6,7,6,pL28F)
def pL30F (i : Nat) : Nat := 0x2e01600d02e00d06192961805a94503f02d001c0230ec02329c0203f753e0023702c014b0200d04402407181904600700c00100c00100317500102515fd4503f05c00107032900304602b00800800132900500300500330632900400100404630e01903707c01f03707c01f01905607901f210ddd057010044017210057210044071dd5db801701007b04401700503d06302402b02400101700a052b29b06f45f36410f45410044f45f36017b7403debcb86dd5a33e5c78b0e0c172d58ab4e8cd9b32649931e3448501fbd76e9cb76ad182d529d1a13e6cb95264478d1014100c7fda86d53148244f7f1815453048244e7eda36095244244c7fda86d53244244c7fdb86953244244b7f9c854d2044244f7798554d2044244f7d98354d2044244f7e920549814c244c7fdba2e95348244b6fdc62e95348244f7d9302e95348244a7fcca6c55348244f7d93054d8148244c7fd85aeda344244c7fd52aeda344244c7fd83aeda244244c7fd53aeda24424497fccb54d8244244f3dd8354d8244244b7edc254d8244244f76d5254d8244244a7fdca60d5244244f7e92060d5244244c7fdba6153244244e7f581546aa4c244a7fdc5486aa4c244c7fdb560eaa48244a7fdc854eaa48244e7dd8354eaa48244c7fd836c6aa48244c7fd536c6aa48244e3fd8360aaa44244e7ed8254aaa44244a7fdc84caaa44244a7fdc54caaa44244e7ed824caaa4424487fecc6e9834424487fecc6e9824424487fecc6e93244244a7becc2a5764c244a7becc2a4814c244a7becc2a5714c244a7becc2a5614c244a7becc2a4514c244a7becc2a4214c24487fdc1aeda84824487fdc8aeda34424487fdc5aeda344244c7bdc4aeda34424487fdc2aeda344244c7bdb4606aa4c244c7bdb4546aa4c244c7bdb4486aa4c244c7f5b1606aa48244
def pL30 : PT := (55,5,7,7,pL30F)
def pH0_30F (i : Nat) : Nat := 0x20680032c04703022010000068100786de8e90385d841a09b5c12000509c00c70034c1cc1690a06ed4040482c1848055d003003dc16140583801850431800000c1000000001006
def pH0_30 (h : Nat) : Option (Nat × Nat) := lw0 22 49 6 9 5 4 pH0_30F h
def pL31F (i : Nat) : Nat := (if i<3 then (if i<1 then 0xcfb5a36c45244244cfb9a86c05244244cfb9a36c05244244c7bcc96e932442448fbdcb69532442448fbdcb68d8144244a7bcc968d8144244a7bcc968d71442448fbdcb68d5144244a7bcc968d5144244bdb5c72e15144244cfb4cb6a15144244eeb4c66a15144244ef34c56a15144244ef35a85955144244ef35a75955144244fe35865955144244fe35765955144244b7b4c968d5144244beb5c62c95144244bfb1c02c95144244afb5ca2095144244bf35c52095144244bfb1c02095144244fe35655895144244ef35a85495144244fd34c75495144244bf35c65495144244ff24b25495144244ff25825495144244ff257254951442448fbdcb6a121442448fbdcb69521442448fbdcb68d2144244a7bcc968d2144244bfb1c11496044244efb1a85456044244feb1c65456044244feb1655456044244feb1635456044244ff31525456044244beb9c62d52044244bfb1c12d520442449fb9cb2152044244afb9ca2152044244bdb9c72152044244beb9c62152044244bf99c32152044244bfa9c22152044244bfb1c12152044244b7b8c96cd2044244b7b8c968d2044244cfb8cb68d2044244e7b8c968d2044244efa8c268d2044244fda8c75492044244ff28b55492044244ff29755492044244efa9a35492044244ff29535492044244bfb1c52c52044244dfb1b52c52044244dfb1b32c52044244ffa1522c520442449fb8cb5452044244ff29525452044244dfb0cb5452044244dfb1b65452044244ff31b55452044244ff31655452044244ffa1c25452044244ffa1525452044244ff315254520442449fb8cb4c52044244efa9a74852044244bfa9c54852044244efa9a34852044244ffa1714852044244ffa1514852044244ffa1314852044244f749535493048244f761525452044244acbdc62c9a720644ad3dc52c9a720644ad9dc32c9a720644adb9c02c9a7206448dbccb69d5220644ccbda76d85220644fb25825498154644fc35765957154644fd25725497154644fca5765897148644ad3dc72e1a508644ae3dc62e1a508644af1dc32e1a508644af39c02e1a5086448ebdcb6988508644ccbdb76988508644cbb5a86c48508644cdb5a76c48508644ceb5a66c48508644cf35a56c485086448fb9cb215a008644adb9c7215a008644aeb9c6215a008644af99c3215a008644afa9c2215a008644afb1c1215a008644a7b8c96cda00864487bdcb2a4814c244c5bca96dc814c24487bdcb2a4214c244c6bca96d8214c244c73ca96d4214c244c7b8a96c0214c2448ebdc62e953482448ebdc62e951482448ebdc62e93148244bda5c72852148244bf85c32852148244afa4ca5c52148244fd29755497048244fda1714857048244ff09535493048244ff81314853048244fe31655456044244bf31c52c52044244ff21525452044244 else (if i<2 then 0xbdb9c72153048244beb9c62153048244bf99c32153048244bfa9c22153048244bfb1c12153048244f798b954d3048244f7a8b95493048244fda8c75493048244ff28a55493048244ff29755493048244ff89535493048244d7b8b96c530482449fb9cb2853048244bbb9c82853048244bdb9c72853048244beb9c62853048244bf39c52853048244bf99c32853048244efb1a12853048244ebb9a860530482449fb9cb2053048244afb9ca2053048244bdb9c72053048244bf99c32053048244bfa9c22053048244afb8ca5453048244ff295254530482449fb9cb1453048244bf99c31453048244bfa9c21453048244ef98ca4c53048244f798b94c53048244bf99c54c53048244ff91814c53048244f7a8b94853048244dfa9b74853048244bfa9c54853048244ff89534853048244ffa0a14853048244ffa1714853048244ff89314853048244af3cc56dda844244cebdb72d9a844244cebcb66d5a844244cf3db52d5a844244a7bcc96cda844244cebcb66cda844244cebcb66c9a844244cfadb22c9a844244a7bcc96cda544244cfadb22c9a544244cf9dca6cc8544244cfadca6c88544244dfa9c06c88544244c7bcb96a1a344244c7bcb969da344244c7bcb9695a344244c7bcb96e1a344244c7bcb92e1a344244cbbdb82e1a344244c7bcb96dda344244afacc26dda3442448fbccb61da344244c7bcb961da344244c7bcb96d9a344244c7bcb9619a344244c7bcb95d9a344244c7bcb96d5a344244c7bcb92d5a344244cf3db52d5a344244c7bcb9615a3442448fbdcb215a344244c7bcb9215a344244adbdc7215a344244aebdc6215a344244af9dc3215a344244afadc2215a344244afb5c1215a344244afb9c0215a344244c7bcb95d5a344244c7bcb9595a344244c7bcb96c9a344244c7bcb92c9a344244cfadb22c9a344244c7bcc96e98344244cebcc66e983442448fbccb6a163442448fbccb69d63442448fbccb6956344244c7bcc96e953442448fbccb6a1a244244a7bcc968da244244cbbdb82e1a2442448fbccb61da244244cf3db52d5a2442448fbdcb215a244244adbdc7215a244244aebdc6215a244244af9dc3215a244244afadc2215a244244afb5c1215a244244afb9c0215a244244a7bcc96cda2442448fbccb58da244244cebcc66e982442448fbccb69d82442448fbccb69582442448fbccb68d8244244a7bcc968d82442448fbdcb69482442448fbdcb68c8244244a7bcc968c8244244cfb9a56c08244244cfb9a36c08244244a7bcc968d7244244a7bcc968d6244244cdbcc76e952442448fbdcb6a15244244cdbdba2dd5244244a7bcc968d52442448fbdcb6a05244244cbbdb86a05244244cebda86d852442448fbdcb68c5244244a7bcc968c5244244cebdb668c5244244cf9db368c5244244cfb5a86c45244244 else 0xaebdc6295a148244a7bcc968da1482448fbdca6e0a148244cdbda86dca148244cbbdb869ca148244cebda86d8a148244cebda76d8a148244cf3da86d4a148244cf3da76d4a148244df2dc26d4a148244cbbdb8694a148244cdbdb7694a148244cebdb6694a148244cf9da86cca148244cf9da76cca148244cf9da56cca148244df99c06cca148244a7bcc968ca148244cbbdb868ca148244cdbdb768ca148244cebdb668ca148244cf3db568ca148244dbadb8548a148244ddadb7548a148244deadb6548a148244df2db5548a148244df8db3548a148244efa552684a1482448fbdc52e981482448fbdc32e98148244cbbccb6a18148244ebb4c16a18148244cebdba2d98148244eabda82d98148244ebada85498148244cfb5ba2858148244ebb5a82858148244beb5c62858148244bf35c52858148244bf95c328581482449fadcb5488148244cfadba5488148244ddadb75488148244df2db55488148244dfa9526c081482448fbdc82e971482448fbdc52e971482448fbdc32e97148244cdbcba61d7148244ebb5a86056148244aebdc62e951482448fbdc82e951482448fbdc32e951482448fbccb6a151482448fbccb69d51482448fbccb6995148244cfacba6c95148244cfacba5495148244ef2cba5495148244fd2cc75495148244df2db75495148244ef2da75495148244ff24c15495148244cfb4ba6055148244ebb5a86055148244ff25526055148244ff25525c551482448fbdcb6a05148244cfada86c85148244cfb9a86c05148244adbdc72e93148244aebdc62e931482448fbdc52e931482448fbccb6993148244cfb4ba6053148244ebb5a86053148244cfb8ba6c13148244ddacc76d52148244df2db52d52148244beadc629521482449fadcb2152148244afadca2152148244bdadc72152148244beadc62152148244bf8dc32152148244bfa5c12152148244bfa9c02152148244b7acc968d21482449faccb5cd2148244bfa5c72852148244efa5a52852148244bfa5c32852148244efa5a32852148244fda5a75c52148244fda5875c52148244efa5a65c52148244fda5765c52148244dfa5b55c521482449fadcb5452148244afacca5452148244afacca4c52148244efa4ca4c52148244efa5a64c52148244ffa1c04c52148244bfb0c16997048244b7b8c968d7048244ff29535497048244bfa9c22c57048244bbb9c82857048244beb9c62857048244bf39c52857048244bf99c32857048244bfa9c22057048244ff29525457048244bfa8cb4857048244bfa9c54857048244fda9754857048244fda9734857048244ffa0a14857048244fda9714857048244ffa1314857048244e7b8b96a13048244d7b8b96dd3048244bfb0c16993048244beb9c62953048244bf99c329530482449fb9cb2153048244afb9ca2153048244)) else (if i<5 then (if i<4 then 0x8fbccb69d82582449ebccb5958258244cdbdba2dd5258244fab58260561582448fbccb69d5158244fe35655c55158244c7bdb86c4a94c244c7bdb66c4a94c244c7bdb26c4a94c244c7bcb92c9a64c244c7bdba2a5764c244c7bdcb2a5764c244a7bcc96e9814c244c7bdba2a5814c244c7bdcb2a5814c244a7bcc969d814c244cebdba2d9814c244e6bca92d9814c244c7bcc96e8814c24497bdcb2a4814c244c7bdba2a4814c244c7bdcb2a4814c244c7bca96dc814c244d5bca96dc814c244a7bcc969c814c244c7bca96c8814c244d7b8a96c0814c244c7bdba2a5714c244c7bdcb2a5714c244c7bca96e1714c244e5bca961d714c244a7bcc9699714c244e5bca95d9714c244c7bdba2a5614c244c7bdcb2a5614c244c7bca96e1614c244c7bca96dd614c244a7bcc969d614c244e6bca9589614c244e7b4a9605614c244a7bcc96e9514c244c7bdba2a5514c244c7bdcb2a5514c244c7bca96d9514c2448fbccb699514c244a7bcc9699514c244cf9cba6cd514c244e7b4a9605514c244e7b4a95c5514c244c7bcc96e8514c244c7bdba2a4514c244c7bdcb2a4514c244d79ca96cc514c244c7bca96c8514c244a7bcc96e9214c244c7bdba2a5214c244c7bdcb2a5214c244c7bca96d9214c244a7bcc9699214c244c7bca96d5214c244e7b4a95c5214c244c7bcc96e8214c24497bdcb2a4214c244c7bdba2a4214c244c7bdcb2a4214c244d6bca96d8214c244c7bca96d4214c244cf3dca6d4214c244d73ca96d4214c244df1dc36d4214c244d7b8a96c0214c244afb4c16d9a848244a7bcc96cda848244adbdc72c5a848244cfb5b12c5a848244cbbda86c4a8482448fbdc52e987482448fbdc32e987482448fbdc12e98748244cfb5a82c5a648244cfb5a72c5a6482448fbccb61da648244cfb4b52c5a648244afb4c1699a548244cebda86d8a548244afb4c1698a548244cf3da56c4a5482448fbdc32e985482448fbdc12e98548244cf9dca6cc8548244df99c06cc8548244cfb5ca6c48548244dfa5c26c48548244dfb1c06c485482448fbdc82e965482448fbdc32e965482448fbdc12e96548244beb4c16996548244c7bcb96a1a348244c7bcb92a1a348244c7bcb969da348244c7bcb9699a348244afb4c1699a348244c7bcb9695a348244c7bcb9295a348244aebdc6295a3482448fbdc82e973482448fbdc52e973482448fbdc12e97348244cdbcba61d73482448fbdc82e963482448fbdc52e963482448fbdc12e963482448fbccb6a163482448fbccb69d6348244beb4c169963482448fbdc12e95348244ddadb82dd5248244bfa4c16995248244bf2dc32955248244bf2dc12955248244fd2d875d55248244b7acc968d52482449faccb5cd5248244fd2cb754d5248244ef2da754d5248244ddacb76c55248244bfa9c02c55248244 else 0xf0f43c0ec3a0e4380dc350d0330c8310bc2d0b02b0a82909c26094240882107c1e0741c06418058140400b01c050100087fdc52e93148244e3f9a86053048244a7f8ca5453048244b7d9c54c53048244f7d1814c5304824487fdcb6953244244e7e9a35492044244f769535492044244f7e1c254520442448fbccb695a260644cebca66d4a260644cebca66cca260644efa531688a260644cebca66c0a2606448fbdc02e95260644cebdba2995260644adbdc32c9a720644adbdc02c9a720644cdbcc76e95220644adbdca2dd5220644cdbdba2dd5220644edacb768952206448fbdcb149a020644aebdc6149a020644afb9c0149a0206448fbdc82e9655c6448fbdc32e9655c6448fbdc02e9655c6448fbdc52e9625c6448fbdc02e9625c644cebcba595625c6448fbdc82e9525c6448fbdc32e9525c6448fbdc02e9525c644cdbdba2dd5258644bbb5c814981586448fbccb6a1a2546448fbdcb2a0a254644afadc22a0a254644cebda86d8a254644deb4c16d8a254644cebdb668ca254644ef2d50688a254644cfada26c0a2546448fbdc02e982546448fbdc82e962546448fbdc32e962546448fbdc02e962546448fbcca6e16254644cebcba6996254644bbb5c22a18154644bbb5c02a18154644afb4ca61d8154644deb5b72d98154644bf35c22d58154644bf35c02d58154644deb4b66cd8154644ebb4a868d8154644deb4b62c98154644bf35c52c98154644dfa5b22c98154644bbb5c82898154644beb5c62898154644afb4ca6098154644bbb4ca6098154644fab4b66098154644fba4b260981546449fb4cb5898154644bbb5c85898154644fe34b65498154644ff24a25498154644fb35825498154644ff25725498154644deb4b66c18154644df34b56c18154644adbcca61d7154644fd2d725497154644bdb4ca61d7154644fd35655c971546449fb4cb5897154644fe35655897154644bf35c65497154644ff25825497154644aebdc6289a054644ef2d52289a054644a7bcc96c1a3146448fbdcb209a014644afb9c0209a0146448fbccb6a1a548644cbbdb82e1a548644cdbdb82dda548644cdbcb82dda548644cdbcb76d9a548644cdbcb76cda548644cdbcb76c1a5486448fbdca6e0a548644cebcc66e985486448fbdc02e985486448fbdc82e965486448fbdc32e965486448fbdc02e96548644fea56558971486448fbdcb6a15148644beadc62c95148644af3dc32e1a508644af3dc02e1a508644cf3db86cda5086448fbdcb215a008644adbdc7215a008644aebdc6215a008644afadc2215a008644afb5c1215a008644afb9c0215a008644cfb9b86d5a008644afb9cb615a008644ebb9b8615a008644afb9cb215a008644afb9c3215a008644e7b8c96cda008644cfb9b86cda0086449ebccb61d6558244fa3d876156558244) else (if i<6 then 0xd888f6d800c00c88c00f86830b80030b8003dc2a780380380088f86986807b8038018020702e42a780380380380380210431780088c00f0003dc10700300300007807820b00021b00320b00320b00320b00320b00120b00321800720800700000700300021b0030002e42030012002082e70000782e700306b0030002e432f06821b00032c070073cd80c40bfc6002108e9201e40a00bc023dd3c600b55200fc07f37f37c36737c36720ab7c32da083dc367c607742e4364720364378360f7cf7c3603d96a6a08a09a183d8a08ea7208ea72083d83db2083d805f20805d84005d84260984084260bc603dc3dc3246e007810786832c078364078224a183640d4088078367c60088078227c603dc107068078210367c62e3b82deb6ed9b5ed3b46cfb36ccb2ecab2ac9b22c6b16c4b0ec2b06c0afebeaf6bcaeebaae6b8adeb6ad6b4aceb2ac6b0abeadaaeaaaaaaaaa6a8a9ea6a96a5a92a3a8ea2a8aa2a829fa769ca729aa6699a6295a5693a4690a428fa3a8ca328ba2a89a2287a1a85a1283a0e82a06809fe7f9f67c9ee7a9e6789da759d2739ca719be6f9ba6d9b26b9aa699a26799a6498e629866097e5e9765c96e5a962579565494e529465093e4e9364b9264791a469164390a419023f8f63c8ee398de368d6348ce328c6318c6308be2e8b62c8ae2a8a6288a2278962488e228862087e1e8761d8721b86a1985e168561484e128461083e0e8360c82e0b82a098220781a0581202805ff7fdfe7f5fc7edfa7e5f77d9f57d1f37c9f17c1ef7b9ec7a9e97a1e7799e5791e3789e1781df779dd771dc771db769d8759d474dd2745d073dce735cc72dca725c8719c4709c1701be6f5ba6e5b86ddb66d5b46cdb26c5b16c1af6b9ad6b1ab6a9a96a1a7699a5691a3689a16819f6799d6719b669996619765995655956559464d926499063d8e6358c62d8a6258861d866118360d82609816017f5f97d5f17b5e9795dd755cd725c56f5b96d5b16b5a96959d66591625855f5795c56d5a5655855d565555454d525414f5354c52949521475194551143509415013f4f93d4f53c4ed394e1374d9354d1334cd324c5304bd2e4b52c4ad294a12749d264952448d224852047d1e4751b4651846117459154551445113449104390d4310a4250942107419054110340901401003fcfd3f0fb3e8f93e0f73d8f53d0f33c8f23c4f03bcee3b4ec3acea3a8e93a4e839ce6394e438ce2384e037cde374dc36cda360d7354d434cd2344cf338cc328c931cc5310c3308c1300bf2f8bd2e8b82d8b52d0b32c8b02b8ae2b4ab2a8a92a0a7298a428ca22809e2749c2709b2689925c962549424c922449023c8e2348b22487214832047f1f47b1e8791e4781e0771d4741d0741d0741c8711c06e1b06a1a46819c6619464188611805f1584e1344b12448118451083 else 0x381781cb48011019008c0d00b81a5dd007c17c1141001525200a3c601480b40f42f380b8082f1c0171780b009c02809a0980aa0b403400227503809c0032c2f02e432c32c32f80b00b80bc603dc2f38083642e7809c002f38082f380b009c69b56aa700b00b00a2083db2a70083df00a37f00a2082083dc2082e700b00b00aaa6c0300b0083643643642e42e436740003f400227809edb80b80b80b80ac002f0377809c002f3809c0300b008377009c02c83403403403403403208360004005070007008006c83803803803801a0b8038003642e42e407007007005000484000d6d80056d88436d886780000401560800405c15c01432401405c84161800484161a6da60886660800484086660a6d800c0048401138008666a415e6a400400484084005c00c00484086671661800401560800405c0140bb800017868842ed8007801edb54f8038035038038002df7178038002df86b8038038005a3803869a1980380380380380000405c004007802f1400405c86b80380033807b80380380380348380380380386b86b80088c21836786ac802a436786986b80000780380380380380380380386af1780032f802f17803803801f1780007b21801506b80380380380386b86b86b86b86b8038038038038021078016db8006e380380386907386b80280380032c07b803803803803803c638002e78003243678003df8038003678020720738038038002e78003df80386b86b8688cb86b86b86b86986888c21b800324079f1780380380380007b80037b8003678682e42e42192182082e521980371721800436432532007807807807b00036432436700032432407b000327001042a180074800780785a3483483481483483480041043003003002a1800424807807807807807b0005a348348300300306b00021b00300300001700300001700306b00300300300030b80030b803800007803800007803801a09802ed8004004006ed800405c00780380106400506506400405d0640678010678038008cb8008c88c90650640040280078034838038000078000078038038038038008c88c88c800780380380380380086780006780002821a8005a08648678038003778037148642db8010c82f380006780002b8010ca0ca0ca0ca0c80043140678002)))
def pL31 : PT := (634,5,7,10,pL31F)
def pH0_31F (i : Nat) : Nat := 0x28170281818090007004120b01c08130400432100a834301a0880c15201c015cc0300002
def pH0_31 (h : Nat) : Option (Nat × Nat) := lw0 13 25 5 9 5 4 pH0_31F h
def pH1_31F (i : Nat) : Nat := 0x548000280f00b80264e2700780363807c0003e0160284502e062044140bb0200dc1c833038058000c0612095de33a0260041a0360340fc04b400080e8110380581001081e0182e41800505a0c80701d02a0600402a00c0641302f04601c1a82004809c1480d0360ec0902b07a240011664000042c293020809b004008c000c001000040508305800c00000000c18b
def pH1_31 (h : Nat) : Option (Nat × Nat) := lw0 39 81 7 11 7 4 pH1_31F h
def pL33F (i : Nat) : Nat := 0x11100d00bcdb8c06320409f8c03b2b0d169b4224458600a0136a60b0068140560300982703f4081dc762ec1be9c00d48203000a3a0c2d150200705a004328070488700086f0cc02c05204061d14162042b002c1582463003026158a8b0110221c4085400382d00244a0220480d0000400105701a000080260878c0110080901a0670c3d16af83f06819c040610fa0a00902304e0d00882304816f8c01100808c1205b652c1a2c060e8ace21102de8b0882235f6531aba2f360bd0882f8430940a00701e04e0d0000080680360102b01e03037374c9186837b5f6520360100101e0339b06ec91868303366520222a8540d00f40401102c0f614b2960dd1432c41852ca587065691105afb0e8c40bda44416bf0a594865691104378290239230d057ae80a00c86a019d170d6380b61e40ff450c5c63aaf360a80301af456e81cc0605fe8bcdbaab2001817f94f18e8bcdb9000ce53c1b81745e6c043f3dfcbb3a7a79b8f7f6b675f5b4b433b2f271702eededacec6baaa967e6652423219fdedd1c1b1a58151312108f0d8c0a07c604c341803bfedd30298489dff689814c244effaa4c0a612277fdba54d20913bfe5d2a690489dff6c55348244effaa6d0a412277fda360520913bfea9b0290489dff6e98344244effb06d12212277fdba60910913bfedab0488489dff6958244244effb66c12212277fda360910913bfea9b0488489dff6e95244244effb66a92212277fda354910913bfec1aa488489dff6e93244244effb6a992212277fda54c910913bfec2a6488489dff60eaa48244effaa7552412257febb68530912bff5db50904899ffaeda848244affd76d1a412257febb68d109133ff5db46884899ff606aa4c244cffaa3552612267fd21aa9309133fed4554904899ff68eaa48244eff261552412267fd83aa9209133fea9d54904899ff606aa48244cffa63552412267fd83aa9109133fec1554884899ff54aaa44244cffa65552212247febb6a1209123ff5db46884891ffaeda2442448ffb71552412247fdb3aa9209123fed8d54904891ef6d2aa4c244
def pL33 : PT := (54,4,7,8,pL33F)
def pH0_33F (i : Nat) : Nat := 0x14081dd3b8195202b075290a01a464220b403a7c2a0b89367000278291052608c1f46000004000981309460070120012b060272b81701016015ee2502127c071751e254086084377c96000a212002018e05b82c1b95e06c240781546c5c120000200000000a00001027000000000004a140000060300000c012000cf040a00002080061100080060200000000000000000000000000000c0000008380
def pH0_33 (h : Nat) : Option (Nat × Nat) := lw0 72 75 7 10 6 4 pH0_33F h
def pL34F (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0x6142191379ed2b0a10c893ef6e88508644dd7b4c42843225fb5b1214219137dcdc34010c89bee6d5a008644df730ad0043226fb885680219137dcd9b4010c89f8f6156558244af7972d1ac1224fbdba14960912f5edb0a4b0489b6f69d7158244fd6b02b0ac1225ebdb654560913f1eb2aa2b04899ef6d8a94c244cf7b6254a612267bca9699309133de5cb4c984893ef6e9764c244cf7952bb2612267bca9685309133de54b02984893ef6e8814c244cf795240a61225dbdb720530912fdcd8102984899ef2a5714c244cf7952b0a612267bca9545309127dedd0a2984899ef2a4514c244bf3b6628a612267bca9485309127dedd042984899ef2a4214c244bd7b6c10a61225f3db508530912fdcd804298489aef6a0a8482449f7974c3a41225fb4b1699209137da58b4c904893ef6e986482449f7b74bb241225ebdb62952091379ed294a904893ef2e985482449f7b7442a41225dbdb721520912f5edb10a904897e76cc8548244bf5b6442a41225fb5b121520912fdcd810a904893ef2e96548244dd7b4cb2a412257bcb968d209127de5d2e690489b6f69d73482449f7974b1a41226ebda658d209127de5d2a690489f6b2dd5248244df5b4ea9241227f2ca554920913f96baaa490489fcb54d5248244b77b7050a41225dbdb728520912f5edb142904897cf6d4a148244bf3b6650a41226fb5a1285209127de5d30290489aef6a181482449f7b7440a41225dbdb720520912fd6d9102904897ee6c081482449f7974b8a41226dbda75c52091375ed32c2904893ef2e95148244fe5aa4a8a41224fbdba14520912fd6d90a2904897ee6c051482449f797498a41226fada648520912fd6daa4290489fe92852148244ff4ae290a41227fa53148520913edcbaae090489f6e5cd7048244ff52a4b8241227db9715c120913fd490ae090489dee2e53048244df735098241225fb9b74c120913fcca9a6090489fea5493048244ff326298241227fa9214c12091375e5b350884893ef6e987442449f7b74c3221224fbdba5d9109127dedd10a8848976f6dc8544244bd7b6c42a21225f9db321510912fd6d910a884897ed6c48544244bf736042a21224fbdba59510912bde5cb46884899ef2e5a3442449f7b74c1a21224fbdba5cd109127dedd2c6884893ef6e953442449f7b74c1221224fbdba20910912fdcd8104884893ef6e972442449f7b74b1221224fbdba549109127dedd0a4884897af6d85244244bf6b6229221225fb9b0149109127dedd26488489bed6a15144244df6b4ea8a21227f356554510913f9aa92a288489bee6a16044244fd72cab0221227eb96358110913fd8a8ac088489bee69d2044244bf736c90221226fb9a348110913fd4a924088489fec2c52044244ff62a290221227fa921481109123de5cb4c984891ef2e5a344244 else (if i<2 then 0x89fed54d5144244ff6b64a8a21227fb4b254510913fdad12a288489fed6095144244ff6904a8a21227fb57254510913fdab12a288489fed5495144244ff6a64a8a21225fbdb84c5109137ded4262884897ef6dd3144244df7b4e98a21225fbdb54c5109137ded2a6288489bef6893144244ff6b0298a21227fb5514c510912fdedc24288489bef6a12144244bf7b6e90a21226fbda748510912fdedaa4288489bef6952144244bf7b6690a21226fbda348510913fdab8a4288489fed5452144244ff6a6290a21227fb98758110913fdcc2ac088489fee5d56044244ff7306b0221227fb97358110913fdca9ac088489fee6096044244ff72e4b0221227fb95258110913fdc292c088489fee4c96044244ff737090221227fb8b848110913fdcd424088489fee6dd2044244ff734e90221227fb98748110913fdcdb24088489fee6192044244ff72ec90221227fb9b548110913fdc5aa4088489fee6952044244ff730a90221227fb88548110913fdcbaa4088489fee5952044244ff736690221227fb9a348110913fdcc1a4088489fee5cd2044244ff72c690221227fb95348110913fdcc124088489fee5892044244ff72a490221227fb93248110913fdcd8a4088489fee6052044244ff72e290221227fb95148110913fdc98a4088489fee48520442448ff974a9a412247fcba4c5209133fcd426090489df654d3048244efd2a4982412277d9314c1209123fedd306884891ff6e982442448ffb74992212267f9a348110913bf4a924088489dfc5452044244dd7b4e53303226ebca66898191375e53144c0c89beb688a2606449f7974a9303226ebca6681819136ded934e40c89b6f2c9a720644db7b60d3903224fbdba548819136ded3aa440c89beb68952206449f7b7429103225ebdb61488191375e5b350b8c89aef6a0a85c644fb6962c3ae3226dbda85d9719127de5d2cab8c89f2f5d9655c6449f7974b12e3227cbd76589719127de5d2a4b8c893ef6e98758644db7b4ec3ac3226ebda7589619127dedd0a4b0c897af6d85258644fd6ac4c0ac3224fbdba5d951912f5edb144a8c89beb688a2546449f7974c12a3224fbcba5895191375ed32c4a8c89eed2a18154644fd696cc0aa3226fb5a660551913ddac3302a8c89fcd2d58154644f76b04c0aa3227f355260551912fdadc2e2a8c89f6d61d7154644fb6aecb8aa3227f35655c551913edab92e2a8c89fcd54971546449f7b74c10a3226fada2608519127dedd10428c893ef6e97648644db796ed2a43226f3da5295219127dedd30a90c893ef2e985486449f7b74baa43224fbdba595219127de5d2ca90c89f6d61d7148644fb6aecb8a43226fb5a55c521913fd2b12e290c893ef6e95148644de7b70d2843226f3cb86942191379ed9b4a10c89bcf6c1a5086449f7b74c2843226ebda6 else 0x70d1a21226fbdb768d109137dec3b4688489bef6d9a344244df7b0cd1a21226fbd7668d109137dedab4688489bef2d5a344244df7b0ad1a21226fbc8568d109137debab4688489bef595a344244df7b64d1a21226fbcb268d10912fdedd306884897ef6e97344244bf7b70b9a21226fbda85cd10913edec3ae688489bef6997344244bf7b70b1a21226fbda858d10912fdedbac688489bef69d6344244fd7b0cb1a21226fbda558d109137dedd2a6884897ef6e95344244df7b50a9a21225fbdb754d109137ded3aa6884897ef6d95344244df7b4ca9a21227f3d8554d10913fceb9aa688489bef6a1a244244df7b4ed1221226fbda5689109137ded1b4488489bef6e1a244244df7970d1221226fbdb7689109137dec3b4488489bef6d9a244244df7b0cd1221226fbd76689109137dedab4488489bef2d5a244244df7b0ad1221226fbc85689109137debab4488489bef595a244244df7b66d1221226fbd83689109137deb9b4488489bef58da244244df7aa6d1221226fbdba60910912fdedd30488489bef2e98244244df7b50c1221226fbda760910913ddec3b0488489bef6998244244df7b4ac1221226fbda3609109137ded1304884897ef6e88244244bf7b6a41221226fbda520910912fded990488489bef68c8244244bf7b6241221225fbdba5c910912fdedc2e488489bef6a17244244df7b4cb9221226fbda55c9109137ded1ae488489f6f5cd7244244bf7b70b1221226fbda858910912fdedbac488489bef69d6244244fd7aecb1221226fbda558910913f5eb2ac488489bef68d6244244fd7ac6b1221226fbda258910913fd6c12c488489bef6e95244244bf7b74a9221225fbdb8549109137ded42a4884897ef6dd5244244fb796ea9221225fbdb6549109137ded32a488489fcf5d55244244df7b46a9221227f3d53549109137ded12a488489feb6095244244ff5ae4a9221225fbdba14910912fdedc0a488489bef6a05244244bf7b6c29221226fbda614910912fded98a488489bef68c5244244bf7b6229221225fbdba4c910912fdedb26488489bef6993244244bf7b6a99221226fbda54c9109137ded3b0288489bef6958144244df7b46c0a21226fbda260510913ddec1302884897ef6e17144244df7b50b8a21227dbd875c5109137ded2ae288489bef68d7144244df7b44b8a21227dbd725c510912fdedc2a288489bef6a15144244bf7b6ea8a21226fbda7545109137ded1aa288489bef6895144244fe7aa4a8a21227fb58154510913fdab8aa288489fed6e15144244ff6970a8a21227fb5a854510913fdadbaa288489fed69d5144244ff6b0ea8a21227fb5b654510913fdac32a288489fed5d95144244ff6b0aa8a21227fb56554510913fdad9aa288489fed68d5144244ff6b06a8a21227fb57354510913fdab1aa2884)) else (if i<4 then 0x913f9eb2aa290489feb6c95148244ff5aa4a8a41227f3d5254520913fdac0aa290489fed5c55148244bf7b7428a41225fbdb8145209137ded40a2904897ef6cc5148244bf7b6428a41225fbdba4c5209137de5d262904897ef6d93148244df7b4c98a41225fbdb54c520913fdac0a6290489fee6c13148244bf7b7090a41226fbda848520912fdedb24290489bef6992148244bf7b6a90a41227fad8248520913fd6b124290489feb5492148244ff5b7090a41227facb848520913fd6d424290489feb2a12148244ff5b6e90a41227fada748520913fd6c3a4290489feb6d92148244ff5b4c90a41227fad8648520913fd6bb24290489feb6d52148244ff596a90a41227fada548520913fd652a4290489feb6152148244ff590a90a41227fad7548520913fd6b2a4290489feb6cd2148244ff5b4690a41227fad7348520913fd6b1a4290489feb54d2148244ff5b0290a41227fad7148520913fd6a8a4290489feb4c52148244ff7170b8241227fb9a85c120913fdc542e090489fee6997048244ff730cb8241227fb9a55c120913fdcc2ae090489fee5957048244ff7346b8241227fb9635c120913fdca9ae090489fee2c57048244ff7342b8241227fb8a15c120913fdcc0ae090489fee2057048244ff72c2b8241227fb9515c120913fdc98ae090489fee6e13048244ff735098241227fb8a84c120913fdcdba6090489fee69d3048244ff730e98241227fb9b64c120913fdcd326090489fee6193048244ff72ec98241227fb9b54c120913fdcd2a6090489fee2953048244ff730a98241227fb8854c120913fdcbaa6090489fee5953048244ff730498241227fb9624c120913fdca926090489fee6c53048244ff734298241227fb8a14c120913fdcc0a6090489fee2053048244ff72e298241227fb9614c120913fdca8a6090489fee1453048244ff724298241226fbdb76a1109137dedb35088489bef6d5a844244df796ad4221226fbdb36a1109137ded935088489bef2c9a844244df7b50d3a21226fbcb869d10912fdedd30e88489bef2e98744244df7b50c3a21226fbd87699109137ded3b0c884897ef6e17644244df7b50bb221227dbd875d9109137ded434a88489bef69da544244df7b6cd2a21226fbd76695109137ded9b4a88489bef6c9a544244df7964d2a21226fbdba61510912fdedd30a88489bef6a18544244df7b4ec2a21227bbd87615109137ded330a884897ef6e88544244bf7b6642a21225fbdb221510912fded890a884897ef6e97544244bf7b70baa21226fbda85d510913edec3aea88489bef6997544244bf7b70b2a21226fbda859510912fdedbaca88489bef69d6544244fd7b0cb2a21227ebd7659510913f9ec2aca88489def2e5a344244df7b50d1a21226fbda768d109137ded2b4688489bef6e1a344244df79 else (if i<5 then 0xf69da648244ff6962d3241226fbd87699209137de5ab4c904897ef6e98648244df7b4ec3241225fbdba5d920912fdedc2ec90489bef6a17648244fb7b0ebb241226fbda8695209137de5434a90489f6f2dda548244df7b4ed2a41226fbda669520912fdedc14a90489bef6a0a548244bf7b6c52a41226fbda629520912fded994a904897ef6c4a548244df7b74c2a41225fbdba615209137ded3b0a90489eef61d8548244df7b4cc2a41225fbdba21520912fded990a904897ef6c88548244bf7b6242a41225fbdba5d520912fdedc2ea90489f6f61d7548244df7b4cbaa41225fbdba59520912fdedc2ca904897ef6dd6548244df7b4eb2a41227ebda659520913f5ec32ca90489faf5d96548244fe7b0ab2a412277bcb968d209137ded434690489bef2a1a348244df7b4ed1a41226fbda668d209137ded2b4690489bef295a348244bf7b74b9a41227dbda75cd20913edec3ae690489bef6997348244bf7b74b1a41226fbcba58d209137ded42c6904897ef6dd6348244df7b4eb1a41227ebda658d20913f5ec32c6904897ef6e95348244df7b4ea9a41226fbda654d209137ded3304904897ef6e16248244df7b50b1241227ebd6558920913f5eb1ac490489feb6096248244bf7b70a9241225fbdb6549209137ded32a490489feb6095248244ff5ac4a9241227fadb854920913fd65c2a490489feb6a15248244ff5950a9241227fadb754920913fd6d3aa490489feb61d5248244ff5b6ca9241227fada654920913fd6c32a490489feb5d95248244ff5b0aa9241227fad6554920913fd6d9aa490489feb68d5248244ff5ae6a9241227fad6354920913fd6a9aa490489feb6c55248244ff5962a9241226fbda8685209137de5434290489bef69da148244df7b4cd0a41226fbda5685209137de52b4290489bef68da148244ff5aa4d0a41225fbdb8285209137ded4142904897ef6dca148244df7b4e50a41225fbdb5285209137ded2942904897ef6cca148244df7b4650a41227fad52285209137dedd302904897ef6e98148244f77b50c0a41226fbda8605209137ded3b0290489faf2d98148244f77b0cc0a41227bbd8260520913fd6a930290489fed2858148244bf7b7440a41225fbdb7205209137ded3902904897ef6d48148244bf7b6640a41225fbdb220520913fd6a9102904897ef6e97148244bf7b70b8a41226fbda85c520913eded3ae290489f6f61d7148244df7b4cb8a41227dbd765c520913fd6a92e2904897ef6e96148244bf7b70b0a41226fbda858520912fdedbac290489bef69d6148244fd7b4cb0a41227ebd6258520913fd6a92c290489fed6056148244df7b74a8a41225fbdba545209137de5d2a2904897ef6e15148244df7b50a8a41225fbdb7545209137ded3aa2904897ef6d95148244df7b4ca8a41227f3da55452 else 0xa43225fbdb254521913fd6592a290c89fcf5495148644ff6b02a8a43227fb571545219137ded434090c89bef2a1a048644df7b4ed0243226fbda6681219137ded2b4090c89bef295a048644df7b46d0243227fad6268121913fdab8b4090c89bef6e1a508644df7b66d2843226fbdb0694219137dedd30a10c89bef6958508644df7b0ad0043226fbc85680219137de5d30eb0489bef6e98558244f77b0ec2ac1225fbdb85d560913edec3aeab0489faf61d6558244fd7b0ab2ac1227ebcb259560913f5eb2ae6b0489faf2d56358244fd7964b1ac1226fbdba609609137de5d304b0489bef69d8258244f77b0ec12c1227ebd6560960912fdedc2e4b0489faf5957258244fd7ac6b92c1226fbdba54960912fdedc2a4b04897ef6dd5258244fb796ea92c1227f3d7554960913f5eb2aa4b0489faf58d5258244ff5b04a92c1227fad7254960912fdedc0a4b04897ef6cc5258244fd7ac6292c1225fbdb114960913ddec1302b04897ef6e17158244fb7b0eb8ac1227ebd655c560913f5eb1ae2b0489f6f5c97158244fd7b0eb0ac1227ebd8558560913f5ebaac2b0489faf5cd6158244fd7b04b0ac1227ebd7258560913f5ea92c2b0489faf1496158244df7b74a8ac1225fbdb854560912fdedbaa2b0489bef69d5158244fd7b6ca8ac1227ebd6554560913f5eb1aa2b0489fcf5495158244ff6b02a8ac1227fb571545609137dedd242b04897ef6e12158244bf7b6e90ac1226fbda748560912fdedaa42b0489faf5952158244fd7ac690ac1227fb571485609137ded3b4c98489bef2c9a64c244bf7b74bb2612277bca95d9309137ded434298489bef69da14c244df7b4cd0a61226fbda5685309137ded134298489bef6e9814c244bf7b74c0a612277bca9605309137ded3b0298489faf2d9814c244bf7b7440a612277bca920530912fdedb90298489bef69c814c244bf7b6440a61225fbdba5c530913bde54ae2984897ef6e1714c244fb7b0eb8a61226fbda65c530913edebb2e2984897ef6e9614c244ef7952b0a61225fbdb858530912fdedbac298489bef69d614c244fd7ac4b0a61227fb581585309137dedd2a2984897ef6e9514c244df7974a8a612277bca954530912fdedb2a298489bef699514c244ff3b66a8a61227fb58154530913fdab8aa2984897ef6e8514c244ef795228a61225fbdb2145309137dedd242984897ef6e9214c244ef795290a61225fbdb6485309137ded3242984897ef6d5214c244ff6ae290a61225fbdba08530913bde54842984897ef6d4214c244df7b6cd4241226fbdb36a1209137ded8b5090489bef2c5a848244bf7b6e54241225fbdb52a120912fded9950904897ef6c4a848244df7b50d3a41226fbca869d209137de5c34e90489bef2c5a748244bf7b74c3a41226fbcba61d209137ded434c90489be))) else (if i<9 then (if i<7 then 0xfdeda950b8c897ef6cca85c644bf7b60542e3226fbca8695719137de54346b8c89faf595625c644bf7b6ca92e3227dbd87605719137de54340b8c89faf61d6258644fd7aeab12c3226fbdba549619137ded42a4b0c897ef6dd5258644fb796ea92c3227ebd6254961912fdedc0a4b0c89bef6a05258644bf7b66292c3225fbdb014961913fdadbb02b0c89fed6d58158644ff6aeac0ac3227fb5b360561913fdad9302b0c89fed5c98158644ff6aa4c0ac3227fb45260561913fdad8302b0c89bef69da654644df7964d32a3225fbdba5d9519137ded3346a8c89bef6a1a254644fb796ed12a3226fbda7689519137ded3344a8c89bef68da254644bf7b70512a3226fbda8289519137de54144a8c897ef6d8a254644df7b4c512a3225fbdb3289519137ded1944a8c89feb688a254644bf7b60512a3225fbdba60951912fde5d304a8c897ef6e97254644df7b4cb92a3225fbdba58951912fde5d2c4a8c897ef6e16254644bf7b6eb12a3226fbda758951913f5ed32c4a8c89faf5d96254644f77950c0aa3226fbda760551913fda5d302a8c89fed6dd8154644ff6b4ec0aa3227fb58760551913fdadb302a8c89fed6998154644ff6aecc0aa3227fb5b560551913fdad9b02a8c89fed68d8154644ff6b64c0aa3227fb4b260551913fdad1302a8c89fed2898154644ff6b04c0aa3227fb57260551913fdab1302a8c89fed5498154644ff6b60c0aa3225fbdb85c551913edec3ae2a8c89f6f5c97154644fe7aa4b8aa3227fb5815c551913fda5c2e2a8c89fed6a17154644ff6950b8aa3227fb5a65c551913fdac32e2a8c89fed68d7154644ff6b44b8aa3227fb5825c551913fdab12e2a8c89bef699a054644df7b46d02a3226fbda2681519137de51340a8c89fed605a054644ff6ae2d02a3226fbdb268c519137ded834628c89bef6e1a214644df7b66d10a3226fbdb0688519137dedd30428c89bef68d8214644df7b44c10a3225fbdb0208519137dec134028c89bef209a014644df7b50d2a43227dbcb7695219137ded3b4a90c89bef699a548644df7b70d2a43226fbcb8695219137dedbb4a90c89bef6d9a548644df7aecd2a43226fbdb3695219137ded834a90c897ef6e0a548644df7b5052a43225fbdb329521912fded814a90c897ef6e98548644bf7b74baa43226fbda85d5219137ded32ea90c897ef6e96548644bf7b70b2a43226fbda859521912fdedbaca90c89bef69d6548644fd7b0cb2a43227ebd76595219137ded2aca90c89bef6a18148644df7b4ec0a43226fbda560521912fdedc2e290c89bef6a17148644fb7b0eb8a43226fbda55c521913fdac0ae290c89fed6a17148644ff6b0cb8a43227fb5a55c521913fdac2ae290c89fed5957148644bf7b70a8a43226fbda854521912fdedbaa290c89bef69d5148644df7b4aa8 else (if i<8 then 0x1df1de1dd9dd1dc9dc1db1da9d99d89d79d71d69d61d59d49d39d29d19d11d09cf9ce9ce1cd1cc9cb9ca9ca1c91c89c79c71c61c59c51c41c31c29c11c09bf9be1bd9bc9bc1bb9bb1b91b81b71b61b51b41b31b19b09af9ae9ad9ac9ab1aa9a99a89a81a71a61a59a49a41a119d19a99699318f98c18818518297e97997717517397317196f96e96d16b96896696496316195f95f15e95d95c15a95915815615515415315215115014e94b14a94714594494294114013f13e93c93a13913813713593493393192f92e12d12b12a92812692512392292112011f11e91c11891711491290f90c1089069051039018ff8fc0fa8f88f68f58f40f28f18f08ef8ee8ec0ea0e78e60e48e28e08dc8da0d88d68d58d20d08cd0ca8c88c78c40c20c00be0bc0ba0ba0b88b68b48b28b08af0ae8ac8aa0a78a50a28a009d89b09909789609389289108f88d88c08b08a08908708608488388288188107f07d87b07887787607407307206f86e06c86b86a86786686606506286106005e05d05b85a05985905805585405285104f04d04b04984784504284003d83b03883703603483182f82e02b82902702502382201f81d01a81981801501381201181000f00d80c00b80a80980800600580380300180067fda8685309133fed2b42984899ff689a14c244affb74c0a612267fdb16a1209133fed4346904899ff695a348244affb74a9a412267fda8685209133fed1b42904899ff6e98148244affb74c0a412273fda860520912bfedd262904895ff6d53148244eff36098a412277f9b84c120913bfcd426090489dfe6d53048244eff34a982412277f9b14c120913bfcd0a6090489dfe6053048244eff2a2982412267fda868d109133fedc346884899ff6d5a344244cffb64d1a212257fdba60d109133fed4344884899ff695a244244cffb46d12212267fdb8689109133fed9b44884899ff6e98244244affb74c12212267fda5609109133fed1b04884899ff6e95244244affb74a92212267fda354910913bf6c12a4884895ff6e93244244affb6a992212267fda54c910913bfcdc24088489dfe6a12044244eff36a902212277f9a548110913bfcc2a4088489dfe6cd2044244eff346902212277f98348110913bfca9a4088489faf2d9a760644df7b4ed3303227ebda7299819137ded3b44c0c89faf2d9a260644df7b4cd1303227ebca6689819137ded2b44c0c897ef6d4a260644df7b4a51303225fbdb328981912fded8144c0c897ef6e95260644fd794ca9303226fbda768181913f5e5b340c0c89bef699a060644fd794cd0303226fbda5681819137de52b40c0c89bef68da060644df7b44d0303226fbca2681819137dedab4440c89bef6cda220644df7b60d1103226fbdba54881913ede5baa440c89bef6895220644df7aa4d0103226fbc5268081912 else 0x4ac4a449447c46c45444c44443c43442c42441c40c3fc3f43ec3e43bc3b43ac39c38437c37436435434433432c32431c3143042fc2dc2cc2bc2ac29c28c27426c25c24c23c22c2142041f41e41dc1cc1bc1ac1a419418417415c15414c14413c1341241040fc0e40dc0cc0c40ac0a409408c08407c07406c06405404c04403c03402c01400bffbfe3fd3fcbfc3fb3fa3f9bf93f8bf73f5bf4bf43f2bf0bef3ee3edbecbebbeabea3e8be73e63e53e4be3be2be13e03df3debde3ddbdd3dcbdc3db3da3d9bd8bd7bd6bd63d5bd4bd3bd33d1bd13d03cf3ce3ccbcbbcabc93c83c7bc73c6bc53c3bc2bc13bfbbebbdbbcbbabb9bb93b8bb73b5bb4bb3bb33b13b03af3aebae3adbac3aaba9ba93a8ba83a7ba73a6ba53a4ba43a33a2ba23a1ba0ba039fb9f39db9cb9b39ab9a399b98b98397b96b96395b94b94393392391b91390b8fb8f38eb8e38db8c38bb8ab89388387385b85383382381b8137fb7f37eb7db7cb7c37b37a379378377b75b75374b74373372b71b7136f36db6c36b36a369368367366365b64b64363362360b6035f35e35cb5ab59358b57b56b55b54b53b5235134f34e34db4d34c34ab49b48b47b45b4434334234134033fb3f33eb3e33d33c33bb3b33a339338337336b36335334333331b3133032fb2db2d32c32b32ab29b28b27b26b25324b23b22b21b20b1fb1eb1cb1bb1ab18b17b17316b15b14313312b12311b1130fb0e30d30c30b30a309b09307b06b05b04b04303b033023013002ff2fdafd2fc2fbafa2f92f82f72f6af62f52f42f32f2af1af12f02efaeeaed2ebaeaae9ae92e82e6ae5ae52e4ae3ae2ae22e02df2deaddadd2dcadbadb2daada2d9ad92d82d7ad62d5ad52d4ad42d32d2ad1ad12d02cfaceacdacd2ccacbacb2caaca2c9ac92c8ac82c72c6ac5ac4ac42c2ac1ac0ac02bf2be2bd2bcabc2bb2ba2b9ab8ab82b7ab72b62b52b42b3ab32b2ab22b02af2ae2ad2acaabaaaaaa2a92a8aa82a7aa6aa5aa52a42a32a22a12a029ea9e29d29ca9ba9aa99298296a96294a94293a92291a90a9028f28ea8d28c28ba8aa8a289a88a88287a86284283a82a81a80a7fa7ea7e27da7ca7c27aa79a78a77276a75a74a73a72270a6fa6f26e26d26ba6a269268a67a66264a62a6226126025f25e25d25ca5ba5aa59a58256a55a53a52a52251a5024fa4e24d24c24ba4b24a249a48247246245a44a43a42240a4023f23da3ca3ba3aa3a239a38237236a35a35234a33a33232231230a3022fa2f22da2c22b229a28227a26a25a24a23a23221a2021ea1d21ca1c21b21a218a16a15214212a11210a0f20ea0da0ca0c20ba0aa09a08a07a06a05a052042032022009ff9fe1fd1fc1fb1fa9f99f89f81f79f71f69f61f51f41f39f31f21f11f01ee9ed9ec9eb9ea9e99e91e81e79e71e69e59e51e49e39e31e29e21e11e0)) else (if i<11 then (if i<10 then 0x106efda9e30089642b8bbf6a6c7580e30b215c0df1b163ac0718590ae0ef8325703628c0d81ed8607b0d8752e3a640417bee3a640417beea5c7084e313225c3181b03d9efba99901047561a96c3dc208f71a00c87b8d00643dc410d90823df0d0f70823ddefba9704f20083a97e8f20085dfb5360ae4010f8ac607b8f60323651021a421776d4df4b90042efda9b05722db2204348406f8c904636020a100d0104659df1b2104ef841b52882c35f443571508220420106efda9441722dc21a42037c0c8863aa10510210baa104ea841bbf6a6e45b8440869080191d472020a2042172020edfd5272020edf1b072020edfd52720208b7b8a07afa7c5e40107e2f20e303dc410d50423dc548820423dc5b9d503c754648b71d4078470823aa7d01968ed04754fa032d1da08ea9f40640d7411d53e80cb476823aa7d0190f6d1c754fa032d1da08ea9f4064324548c203ca08548f7f8bed8118b711c21b0d0d0a4036464d2003ca0a900f71922dc1a81ee41868ea8a91b3868eae1a3aa0d40f320c346e00f0c93700780f041370078dc01e370324410f603c2e78c082192314ef83508232f471df1b21046f8411be324208861058686f0821b22087b8c916e2a40e01e03c21b0d0e23aa104ea8413aa104648b710c20a9001e1726e30d1b803c32c6481ec34f140f320c347546c81ee30a186cdc51b207b8c0d9112202a9810a40b206c8d906a07a000231b208a9001e80008c44822a4030b900de6802a45b0211b22a78c0d016e37c108d9192340fa0321aba38649f4064757476c83e80c8ea835d907d0190d8d1c754fa0323aba3b641f4064757476c83e80cb8c0d01ea08c20fc5f6c08c648b70322d86c71810c3d00c8d90323607a8c90323d46f7181922dc1a8dde31c601a9c83e807b8c0f73903d0108d91aa0847a8c916e3886ef1816e2d8711c80642f3470f73900c8e4032172720190c918a0647a8c2e3036454e1ac342a46c8411b20730d0f7970210a00f71085007b84110c3645cab819221b8c0861083660d01c1b20780e41a0837747b823f8bae011d3f53cd3ad38535d3453252f52cd2ad2852652452252051d51bd1951751551351150fd0cd0ad08d06d04d02d014ff4fd4fb4f9cf7cf5cf44ef4ec4ea4e84e4ce14dfcdb4d7cd64d44d1cd0ccd4cb4c94c6cc34c2cc24c1cc04bf4be4bdcbb4bacb9cb94b84b74b5cb44b3cb34b2cb0cafcadcabcaacaa4a9ca94a84a74a64a54a4ca3ca34a24a1ca0ca049f49e49dc9cc9bc9ac98c97c97496495493c92c91c91490c9048fc8ec8e48d48c48b48ac8a489c88c86485c85483c82481c8047ec7dc7cc7c47b47b47a479478c78477476474c73c71c70c6fc6e46dc6c46b46a469468c68467c66c66464462c60c5fc5dc5c45b45a459c58c56c55c54c5445345245145044f44ec4dc4d44cc4bc else 0x192213000d5192adb001d516e904420b91843dc420b91b2308fa1dd1ef2e0119df76d480e2d20353481db023c0180011bc519380011bb61e82df000dd16f80011e00c003ab000a9e3035464e001842dda0023c0180011a4104661b000c9109800670c956d802900b74822105c8b61ee2105c8b7a807d05bd4004380011e0056c0d7000c91098006c8353bead8420b916e906903533be618209c8353800c3186640edb0060078a325a9bb61e82df000b71bcf17006001d580054f181aa327000c216ed01900e2c0033864e0016ed001ae0056d80120e0056d800430861927205ba41c01803000dfc0021300086c005a0b461ac00324426001938006f0b748232464600192323003201082e47b8bc1082e45e0c93902f05be008386185c8bc16f8005cc1c6416daa02c5c00717001c5109802e2ab6c0036064884c002bf001c51082e6e28b7482722e2e001b0c80e40a9353800e46001098005e7181782e45ba4110980043718c3408f000841722dd209c51098004960019237e5c0df97037e5c0df971070db61a56d7160e5c5b8b7160e1b6c3410454e1a3aa2a70d600152212413b6353869401d576d8681961a352105e2e1a3aa364eae1ac358680e61a083868d4e1ac3586b0d01c352f170d082c346a40e61ac358682081c3ab868db61a56d480c361aa4186a9052031c070d4e1a36d86b000bcc34720e2e1ac0021b0d60010c720d481c30c0725c0f79712e07bcb89702e65c4b8970f165c0b9a812e243400504078c304190d001411c89050015c041082f164340050521a0d01c30d20a00482e3120a0040017321a0028230c07241400192722000b99050000e40010c1040e1c8800249410f657032ce4282834070448370ddd179b035019d7c24837e539229c520018dd3245200f20d39b031010ca60d079c900d017c22ee811290355050044063388341e724034abe0bfa2e1a0d38e02d86fe318081ad480695d02a06aa9186834e380b6c82a46380f216faf958057c60066386aa0a3af808e1dcd816b298355201e85b752e39c3380a8163ac05d5680380208de1ec0607b0d8b5363ae43401963667a1531b2388208d9193c616f8c5044ae28c2df57036444adf1b2ae00c0ea1bc3ab0c0dee41c6b8c0d91923645b0d91841006f0dd1ee3644301c1bc3dc6c8181bd3206c8231b237c6c8861ee2f07bab81ee2d87b8df0463245e6a9e3424b8c0f7390720648b71521a064041e302180e0de10c3dc7b71ae307d0706a93e837c7b8f63e83d86f8d9105c60548821ee3678c0a91b2aa46c9dd1b232c611dd390366e28d9e300896aab81be2256aab80303a86f0de1b3edb9071a6a632c648b70443778c0df0643787a023192314118f508037844c861b27746c8d99903786ff18970089643df1b0e39c07189912e18c0f61b0f7dc04b8641321efb8e99) else (if i<12 then 0xb7a40a0b5b600192720ef8b7c342df000ba16f86b0d2c5505800e28b7c002e85d0b7c002bf001c8082756e2e1a353800e40b7c002e84960016e2df0d0bc16e3dc5bc411732e05cc82083208208b99712e25c61ac352e30d3c5c342df0d6001ef1045bc411b22e42084116e107000b91ee364d4841c002de208b7882224649c516f1045c8411721046498608208cee8b7446840ef98204660811bc50466e0d4982046618c102356d800db223b6c8407b0c9b6d80070600446843000cb19220864f18113800c3223420324db022c0060b000cb1726e111a1016e08b000b70458005bc413706e30d223c348405b822c342e70d1a9c00d4d11a10113803002234202dc116001122e4e2822c3472111a10c00361db32076d8038c3c50640799001c03c77ee2e00192324d4dc5aa67d0eedb616f208ee8b73058007a0b7c0060b0001e1923745be003ba77ee2e00353717001d53ab714d4bb603d8685bbb616f8699001c03cb17001c5c003a86cac81d46d9410f5c005a30d6001ed8000f0c93aa3545ba82c00714c160016e07b0001e1923086ce0003c2dcfa0b76a63d6a00233bf483001c5a406da903c53534830d023c018000f0c990d480670b750532011982c01483000b71920785be0003d4805bd2038a08f000351b20d54160016ea08fa61ab6c07b0d18ec34078db61a38b868e2e1a16ea0a640a9b8a6a70d1a9c34f170d032c346a70d61ac347546cbc5c346a70d61ac343ab0d0c2c34f170d1a9c343670d035c34f170d086c3477f00182c00609e29b878a6a700182c34609901a9c3407a4361a192b2064e1a064079e2c86c34c824361a10d8695b60036d8030001e3e820864db6c003d8700411726e00f61a904a1adb61a371800658c91043278c01ec005a30d61ac006d80f0c919780064e0003c608648cb1722e4dc0d9c002dc0f60016f1040f0c916f104dc1b8c343d4dc2c5c0071700082c346d80f600c00078648d903d8005b8821738000f0b937186b0d61a03c6a7001a91b38000f60083807b0061a04780143082c0007b000b71042e40f600a40a19001b690586b00082c346e0e2e1a30586820bc59046a70d3b6c342270d182c3586b0d182c35868dc61ac34f170d08978b868c161ac3586b0d0b9c3586b0d182c342e70d61a1ec6e06598203860864cc8b8a07ae2cc8b8b32264320b8b322430d9112326e28c9991069db4c819354e644861b2326642860474800f023590f169052050c08e90520a40a1811bc5a4121a0d520a414829002283421a90022a40089642860474824341a76d482900c9a4148290520800225db3c576cedb000c2c00ed9903b6c002f3001df76d714649a94838015b5c516f1047a0b7c002105c8dd16f500ee9df0826a4eabb61ba2df0032078b803002b6c009055b6001523a86cb5316e90700168c003630d600 else 0x57f8c066a7016f8c355a701a4817180f2d201a71820c57511034e8ace039f45a40dd01a55f6bfcda90355068517afd20eba0d1aad380180a1afb5d6400301a245e6c5d83994ea700f41a50205c0301f95f2a60f41a15f011cda8735503e0fc0a81f66dc6011648068d7faed0e068d7da0648069019ba050069c63ba648068c08060346be09c1764867148287736c900d0055206e816f8c7066e816f9b7186aa1a5837180f216c832410b6c39ba00c0b74181680c0b6dd19000c0b7ca5ba0546bed000605b46dca52085221c8e82d866abe0b68700100e1970d355c7018514e1ae8b8e034f5fe8a904291452c48e82d8240d60bc33638c355203082f6be04f0d638aaa57d2085b2bf438008040b41b71c61aa900b40786b0cb5231c61a2a18e01a30e2900e81a35f61cd171c03405a0d1873290180078c548c70d7da9e38068d7c2080c0b603015d486418e1afb290180071c320a91714eebc5b6ced8e40f676c619db0e0b6ced8d4986c043da410f66400718d6023ba382e2e0276c7768d51a08346adb3b63534696f8f6b6ced8c751ab6ced8c351a5043d865889112b1501618d04a0865bc58390706cad56400718d0c99903246c8cb1736d87b0c91932e05bcb858b8086c5c516f8085b8ded717155c0b71782185bf1816e2f05b932d6dada5c6b61efada5c3c59703d7200f7d6c7745be0236d480efdc576c61b011c8391714c33b6b8a6199060276d20b8c0f71b3c605cab8173c6190482e300718d6023bbc63010b71bc71701186c04208410b91bc364410b9178324c30b81b26185c9df1bf6d96aaa93e8ed96a9df5aab547b1f41b23dcfa4df76d00954ca980477e6fbb6804aa4410f678b2a6011df95220b8c4a98052a6010f71b0b566fbb6552c68db4d5104354e40cb390eda6acc51b2edae28d9aa77146cd53b8b716548d99523642098ea34f14c351a505c60efd00064f141ab1a11222444a0206a80941089113070449dfb8aed8d4e02196755db0de78aedb0160278af15db0dd1b2f15903c56342245e320635808eee021aa3255b60216e378e2db61122e4610f71122e4610b7a807d06c9dd58b6da434b8590379628df9706da642b699121865dc576d321db5c5193322e28d999036664402178ada010a9590755640cb50d208449a990c009432c83beeda8d50038b46820bc535346a8018ea34ed9e28d8640c69012821b10720e600d6cd4c5be001747545be1a3be10419032c3586b0d0))))
def pL34 : PT := (1167,4,7,12,pL34F)
def pH0_34F (i : Nat) : Nat := 0x1e5a0000301589a6100ca52780b0000ea7cb30cc0176421034340c02ebd2b104031274090dad20d5710880f0081307d5eb882b0a40078c0a09c005683200194a58119902f470200828511c138000e1860000402430401800c00c3
def pH0_34 (h : Nat) : Option (Nat × Nat) := lw0 26 57 6 10 6 4 pH0_34F h
def pH1_34F (i : Nat) : Nat := (if i<1 then 0x720083162c828214c90090af1d012ae7a846400f8082068b1bcce23c6e02f0488c6f82d22d204be0120380238b37210a8220271849810c817a01d039e11681e4c85020412a0ba800683fe09e01040490a5c007026c23e81c2242043e05789000b0826a25c31120b50030022834013cbcc413281f803b8034c6b837ae3504e80ca049c0cf89c824d00ae02230f606d01ce0eb00000b20bb60db03660bf0c00109010210e0362117046aef0040811400f8c4702661208470136b3be0c902b4efc096cc350060f32019805c81b604301da0a13bcc037bbbe29f00b40828358c1284ae008800009500001210c8c0ef80000f004b6062000011d0000203302a05a007801184d402500000e3000000000d808b823800280c409f800004d019424d834405d000000003541048338d1189402a0b93a33a034600a8090c43825e0d300a610d88cc0ec83d41330b460c984ec04180000c580d60af826029f84860390a8805bb9f80b581ac0968a9c0f583ee07280000268000092841c100000007b0000230002e01c3c3413803b40190080e7e80b02338440ec104460bb8184f1a00c2e470352c06b41cc9b8230e748a100d2800031a3c72ed283a823083cac6e83a0e4e00dc000014e0f20b88d1882c007eb01403a80e6127813613a8000000024806002cc00002ba105037d33904421130c3220eba2a0000a160fe30c00000000c9a82f00000000108000020280000000000000031c00000000d400000f884d20e181de0bf8320000000003c00002f814e20c18212021830c00004260b3b26800383480e48c560000c020c781f4113845606bba9c000000003c0280400601c1c00500e01c00008012000000020000000400a0460201500700000c0102c0040000280a0080000000301c03c018000020040000a00603c030020000080000504c00c0280f00a1a00f0070020f8001200000180101300a0080180a01201008801004040018030700800080a18a08c0080409a0c8000000000180002e00009c000000260280400200a174010a300c02c16826014070068270280540080800c0000080b02a00002003000008020070120002480000400c1d8e80020080305301a0000300101605c0b000028024060081020640000c00a00400044000034030520061a40400200008c0000100002c0f8030160000c00103a0300782300c09400066030018000010162ac028070180481000b01a0040b0000020080100600400001829000020038030420000400c000000000610140207682002a0941184d10e0040002204a0101a80000a0040781401a0082384f02c0800000300c0040083a03419c0000b00200c1405900000400000000000000030000e02580003a0100181900404c0380d0040300a00003000000017002024060110020080005b0000400000b00002c0480a else (if i<2 then 0x36b3b41248bb40990036617014608600f2c0c800033c01e00f63456f1a800031882c61240394014b42804e030413200e203db0fa08c826e3193430c4780ac329814a13000040000000e808000f21018c11b824c2e500000290b0c0dd308a11d810010580001290262cfe801e01bb940294b1b804f3104c450000000039600038d200f031a13b841829a0000e9581a0d1d0c5002580e800008c808680ec24f82a2c5a3096d150a8611e819ae4884440f3806208708de08d012627cb968efe00840db82ec0e6804c0b60abc06584a6eff08f6012843a53a001008f83e0095810e028b888118841e045823c295018ee6603ba05482802f184960608334e743c182efb2bad35801405701c00d704c623288e8d318c4ecde8056122811800039d606f80000900c580b1033207c39660df811a138833600480000150a021268a8405800b6130b46ce4f00000278210d3ab1662448c1a058819c05e3a0006a838a07a029e08eb4ec2fd022210f03000eb89620d380c6016830a101b0380a733c609c8268243832a0a6bbbc13902aec49028ece301a404739fc73b828600901120ce82aa139a4e40af02e2eaf31f008d80b801a049400339b40a4813000600fa0da04d60cb1ce8d2d813a06c04b80740246c3103a2010bc08231800006e818a00002b80000000c5a825c0f30000048bc000530000cdd83e62f20000000007600000000590904cc081bc0b982ca0a28170000048ef20a4e60b902a009eb3b203501d2137835a259012c0558c5cc8c00000aa3c640f78282112800005201dc00000000e203dc01f337c0b782423168000539048013c007a02303b0f2201ea112039808903100b403080e3835e03f320c11a0c74061810800000cec5c349a0ab00000000000e6fb9702e8000027602f80e109fe28781c405b30d002e804e20f80a013644ead3c831211e00d011f842c0750402000084ad1380000b681e209d88c4103000828708be0dabb4ccf20016c40b16413701f60dc03bceee80260dcb1220e08360082040428608b6067800623a8c8e0b7005cce18176c5b0202cc002fae0b81e6069803a064012e0e7022a9388cae0c0810a094827c0a309ca0e983aa06e3bca0fd024eeab820e133822c09103b812eb0fe1340b44d05811e282baaa0ff0428319ba7e0d581fc0dd837812c31f2c0733b60f1008e0ed81cc00e0a002383b8a033030e0f684aa0f439d8081816a117829605980f403200ca93b04a006a021601b031800c806ae9702e0103812807f8a5a03839940fe83c611f310af0084520ad840ae34017c09d03e493bb4b8050836403481200cc025009c00440a9046612cba58c0783900acbba002600aa02a0cac0a4043410c03ec0fa08dc0a2396a2c501b21180bce05502f604504c402481d60f48c5200a046c0a9832eeed804012d02e812b0 else 0xbfa0ba841a11c883029788fce65bb1631c81c60003100096013ec8c8058076310800000000bc829807b8b9e0500000ee903ea04c84100723a5eeaa017eefb000200009ec00000000000150d16806602f81f2064807e03f822800009f00e904a20003cec0c50454d2e822601403c20fc89f629d890c03004bc0cf0342027015a0830422c83bc86044021e0510294eec002c0fc00b2000042e05602b00178458d2b832200002f4080048c0fd8000))
def pH1_34 (h : Nat) : Option (Nat × Nat) := lw0 311 1025 11 14 10 4 pH1_34F h
def pL36F (i : Nat) : Nat := 0x2be87653244359b0a8060539b60dba68b9c044016bf94e1c0666d244342fe8b876aba4083dab8c0dffaa9209127feaa4c2449ffaa9209127feaa44244
def pL36 : PT := (4,3,7,5,pL36F)
def pH0_36F (i : Nat) : Nat := 0x2805002080008101e01006c98a8048100e22000026870362902403a16070184490e06a3808a1e058013b0000000007800000813180010016a38001
def pH0_36 (h : Nat) : Option (Nat × Nat) := lw0 31 32 5 10 6 4 pH0_36F h
def pL37F (i : Nat) : Nat := (if i<1 then 0x37fda244244dff609109137fd5244244dff4c910913fbda760644fef69981913fbd7660644fef68981913fbca260644fef54981913fbda060644fef54881913fbc5220644fef6a171913fbca85c644fef69971913fbda55c644fef59571913fbda35c644fef68971913fbd625c644fef54971913fbd815c644fef68171913fbd8758644fef5d561913fbd7258644fef54961913fbc5258644fef69951913fbd7654644fef68d51913fbda254644fef28951913fbd8254644fef5c951913fbd6254644fef60551913fbd7154644fef68151913fbd8214644fef20851913fbda648644fef5d921913fbda548644fef29521913fbd8548644fef5d521913fbd6548644fef60521913fbd7148644fef54521913fbda048644fef61421913fbc8508644fef6a160913fbda758244fef61d60913fbda558244fef61560913fbd7558244fef68d60913fbd7358244fef68960913fbd8258244fef5c960913fbd5258244fef14960913fbd8158244fef5c560913fbd5158244fef48560913fbda64c244fef5d930913fbda14c244fef60530913fbc814c244fef5c530913fbd614c244fef54530913fbc514c244fef48530913fbc214c244fef6a120913fbca848244fef69d20913fbd8748244fef69920913fbd8648244fef5d920913fbda548244fef29520913fbd8548244fef21520913fbd7548244fef59520913fbda348244fef5cd20913fbd6348244fef54d20913fbd8248244fef58920913fbd5248244fef68520913fbca148244fef60520913fbc8148244fef5c520913fbd6148244fef54520913fbc5148244fef4c520913fbd2148244fef6a110913fbda744244fef61d10913fbd8644244fef5d910913fbda544244fef61510913fbc8544244fef5d510913fbd6544244fef68d10913fbd8344244fef5cd10913fbd6344244fef54d10913fbda244244fef60910913fbc8244244fef5c910913fbd6244244fef54910913fbc5244244fef4c910913fbd8144244fef5c510913fbd5144244fef4c510913fbd21442449ff6a1209137f930482449ff68d109127fda244244dfe48110913ebca660644bef69c81912fbda220644bef68081912fbda85c644f6f61d71913dbd765c644bef6a161912fbda758644faf58961913fb58158644bef69951913fb58154644fed5c551912fbda314644bef68851912fbda014644bef69921912fbda548644fed5c521912fbda508644bef68021912fbda758244faf59560913ebd6358244faf585609137bca94c244bef69930912fbda848244bef69d20912fbda648244feb54920913fad2148244fee5c120913fb93048244bef6a110912fbda744244bef69910912fbda544244bef68d10912fbda244244fed54510913fb96044244fee48110912dbda720644baf69821912f3da508644bee680219127bca94c244 else (if i<2 then 0xdf32da907b20365b8868c8b7e8eb5441b7ddfc801e755b886adfa39d5106df77ea96a41eb21b84821ab7ea96a41e7d3202e0c8869a9639c8105df6a58e618416a5863d3203661a105537d0417744177e1a639c8104eaa1986c81f47544186918a3a86755f40ca8ea1af4869d577cb72d98e7204177da972041adaa96a4e2b21c810520869df3252061af4754d0105c5869df2dcb66a5207204177c35a1986bd1d510520869df639d5106a96a7207d1c81061aaa68e7d21a722a9a3af4869c877d8e754b9105df715a9bd320365c81061a4628ebd1c80c9dfaa5a924af4720414821a6a58e7221a105df6a58e619c5105df639c88684177da97221a105df639d586841ca70ec09749221a08b36ca774ce2484835fd175543b488e21a0335fca70e8e21a52041d7f29c380cc61488e3c5c80f4c68b8381402a486c831a37cd92e1533571ac60df32c682e3c5c80df105f42d8a921b20c6ab83665337da9a1b2020b1a7d2b8c60d96a720c68de2e0d9500a921bc52e3203d0b7104f6900df2a486c831a2e0d9900dec831a3d718378b8f1720c68f42e0f6900df218b8c8041b54f7500df2a720c69f4b5718edb20c68d53655337c860d71a354b8480dfc831a22718354b8c80d5104df354b8c80413dd40378df315d5c831ab22b8c6320c68d9c60de320df36320c60b832041c80c8104df2a486ae3203dcd9869dfa0841c81d53de1a77e82107c5480f7868803d3c5c8041f17b6040df2a486209dd880f7868a920b207d2c8868df2a482323b6c821a3655337ca920b2086ac83dd40edb207561af17206e21aedb20320d954fb608ac8480b62a4867d3c5c82b8868df2a5c8c82b83661a7d3c5c804137c86c81d5ae21a37ca921bc5482b8868df2a720722b886b2075441868827d3c5c804121b20c61c810720c60823d041c831ac60c82e320c60b832041c801cc60c82e3c5ed82006810a935069bd2fa5147e8c50fa0b3fa7a4ee9cb37269cca98f3125dcb795928e4d49691f22e444818eb1be3646a8cb1762c45089b12a20c3e8710c21542283504e06c047f6fcdf6be67c4f81eebd47a2f21e13b975eeb1d1b9d72ce49c6b886fcde9b83686c8d65aab4c688ce599330650c919031b62cc45833015eebc974ae45b4b55672cc58aaf15b2b1556a8d50298524a3141a7c4e299d2f25549a90d1e23845a8a10f21a42683d031fd3f27d0f61ea3d078ced9d53a0728e31bd3666b0d199f33064cc71893005ecb916d2ce588ae9582a452ca213c26a4b89311f236448841011ee3b8740e11b2348660c517c2ec598ab14a2784d8931182144007d0ea1bc3305e0b41582884d08a0f81d03405a09c1181e0320500780a00a0037fda14c244dff605309137fda848244dff68d209137fd5348244dff685209137fd8148244dff4c5209137fda344244dff60d1091 else 0x15fc6106ca7454e079089761da22d175557e0ed21388682ec3b02ca61a921740a329c0b36dd120920340c408cdb7443a06ce15586b5fca745c61381500c02076ca70e40a1a9217407c1102016d7f29801209213807d06d7f45d550e1304158862ca602c1a00d157448241d7f29c3b450304118404ca70e80a1a5d148905581635fc39298e21a5224144812d7e00ca63848148906df6d8f7755c8c831aae153500f73da18774f7b7db66a720c68f7722b8c6082c61c83dadf716b66a720c68f7365c8ae318b7db66a5863dfc5c82b8468d96a58e61980716dfc62b8208eac60de77db6c831ac62b83648277f18379b6378d977cd5c831ac62b8364cb324c22ddf4b20b8c831835441375df3231aae120364c832cd9c60dea3a80bd253364cb37ed5b2320c68b894ddfc82b8468d9325a963986600f454eb8c61d5ae0b8c60de77cd96a58e6198071718ae1a9c60de619f4c82d510540b7e8ea1a80357182e1dd77d86c6ad5ae12077dc5aa720c69c8ae318aa4a9c6892ae082c61c877ea9c831a722b8c628ea02f4c60d5721df2f0a9c831a3ddc8c60b83d986b2320c68df357182e2df77dc8c831a354b854ddf61b20b56b8469df6398660318b56b820b183a8de500de37718379df715a922720c6ac8ae3186a718378eaa1a82c831a7d1d537b18a3a80bd318321d52dc897d0c2c831ab23182e0f66a489b5720c68dfc60c82e08654cdeb7ddf22720c68d5c60c82e1df6a720b22b8469df6a58e60318b22b820b183d8d86a58e720413dda963986104f72dda961a82c80f436441868dd639c8104f73a8b7a1986a0b2075441868f4b7cb7a3a86a0ab6869d56a5c8104f7338b76a586a0af4364414821a3758e754413dcb7aa5a9a0b2072041868f4b7cb7aa61aa3a82901c8b7dc5ad9a9a0b203d4d97204186adf2de8ea0a4072032104f777cc96a58e618827144177d8e7204177d8e7544177da9609c808e203dcd9869dd6a61a7d1c808ddf6daa96a6c8720223de206e21aaa518b2068106df32620619f475422379c586adfaa620b2041b7ddf8828661822755b886adf8828675441b7ddfaa5a9721b808a2037a1ab7ea9881c8105a907982f17207d21a7d01e77d82757b6c821a54cc907a82609d5c81f4868c86a5f4c82c810540a3a82b561a7d2a9a38f73221a775df7141e60bb6c81d58681a7541e3aa8260b20079f47561a4628ea09d57d032b7e8e322b8869d577c1e608c2c80f7b21b6869df6a582a03b6b2120b7ddf339a907ab86e0d94821a321dfaa5a9079826dac83dd2086adf77c1eae1b80d6c84821aaa5a907a826e3203d0c886aa96a5f46e320868c8502df77c1ea0982ed8a9c821a321df6a41ef17206e21a2181a6e01e77db6aa5a907882c80f7b21b886918a3ad577c41b7d))
def pL37 : PT := (205,3,7,11,pL37F)
def pH0_37F (i : Nat) : Nat := 0x1b4061f40d4b4052650599f082df0b00d0880a0841a0b409b8e8e01433b9c042a0060d02403c080012e0740c0b82b05dca02df024c1f7bc29ad09e0c0102502a44aa7096e9288070c811679db62cab09c1e098157ac28064a361e9c7342306eab0c42f000438532001821a3480026dc680020071606a09802000002000808900ad4070600000
def pH0_37 (h : Nat) : Option (Nat × Nat) := lw0 40 79 7 10 6 4 pH0_37F h
def pH1_37F (i : Nat) : Nat := (if i<2 then (if i<1 then 0x807d082468cc01540f024770882c5c1daa83da00000a340000297000000001790312176200845c4007f04d6c49823e841706cc00000000000090f3164019000006c410f0240011f0000c24c06b018001240675cdb83b606de06644dd386c7326089c0080000007e0000190000007ea00c01db882a613401341018c2d60e4ecc81d68970057a00380a2388202a40f2002282fd0594288c19e80f401ea04e008e01221426c6641518aae042e10a055d08ae0000c580515014ba8d2ceade2c80fb0000108417f0000014602400a6301a03dc106450bb3ef68c80fac10d03070620022995e82f6035e0c98228838800a02703f00100b0010000880002930040050010050a700e00201004500f00400001807b01b03000a01900b00b0140470090d10070030180220040630020310800a80050530040040a908000000400b00502d00400004115601405008805100200800601f01800000b02400a00000007900d0a601300001516f0040a400800303c02303a02901201504600801200e07f00002f02e13f01606a17800501a00f01f08401500002300301901900600102815908003901e00100005e00200e00d02400001900b0020440200681720040210090081660040410000030010320ab03d02d00a00500201504700601f00700100000200000f00500000500001b07405100b00400000000203900200300106d06800c00004d00606000000100600005401d00e03e01401c02c02000400e0000430000bd00600900600403600c00c09706202600e00b00609601e00700004007001a0280c905b00301400701907f05800900000b01801f0d100500e02f00200003c00606a08d01001f0330a501606b02403c03100303b00c01a06304703007807f1a600303a00000500109f01e03d03c06400001800502f00102000300914c05200602018700b01b14606900300400000f00600000c0340190020090fc14a00000f01900d00e0000010100bc02402800000300002404f01800201600102d00800c00403a04602305203200602a02100000200101600100c00000003d09600a06003a00104901300505527701700f15302f00001802a00801d01b0d301a00400800903c05d2a100600301f02002301300605500a0031ea00a05d0aa01402d05102607f00505b02401d07312108f00d02900103705b00804500a04b00603701500402301f05203b00b09200400104f00000000e01a07700400c01101602402300003000201000000203b0a300316612d02b0001f800000005700201d01300400400201d0060170ad09900502800501400000b07708600309a00701100304403500001800800301800100201300400900001f06f00500104c00400307c00300f0000c902301400f01504400a00000001700104100b06c00b00001000104f0000160010cc01a039 else 0x602d80fc850b01d104d42db41d80438680830a00ea9c80107011c4029318301dc04a00f4045c625e0d30119815306700094a300379725571b0186829278902f60227825e01e62c6d9f4331a6188d18dd74044300ae2b3411933ed7430a390053343368060c14199bbea07fe00b408b004904fa0a2824108d2147e0e5003f0003026800a585301df087a11c8080825f155e0c60606820e7844e168107b8d841d00c780368036183c106014c888e027a2c859230874047e2989071831762ba2d5855804300554cdf004101d702e606c804b83a104dc05e80c1028028b23010a35026977c20db020230966388063c0f9008e04a42c941b6802f07c6c95c614800001a02b08195b42b03d40b2c224008d061e0100078800007461138441336a02d4e18d84701a46740e66061e894306aaee1198bb46204e225900fc0840065a000016802e317ec2f8c5e1b250004400018bb033b02ea000014d8350118ae21dcdc823013dee881db4b07b01b004f8019b9bb6218c1f000c887f086ecac040f833f17ae91e4011837067460abd8b208896186ea4818d307a00340cd001601cc03ca094407903e00508e13000003f900a6e5a805f010274f609e41ce546a1166012805582250000033da0002d80234066015f3a5a06fe00000ec0b2f68feceb01708ae0683e0cf009601de17ee08084e381be07ccc208000045e674400000e50000050620dc153828901f800000a6ba8506862d3800039b1770e0f44093823b139420adcaa8a890914100c55f0000675c01cc12581950314000043381fa078e2e70e33381d623412241d130a30262f0edd640444007026f989282550256c83c16110e417b8221c1f98c6215fe0230577821b16880a418e508e711240cc4127043601722b95d92312713b027840918229033eccb023402e41046053c0da02d1029cea200cd027605f0092008438967472251015c00851748000055c83c9080c0e6419f338b67d806f04bd047607e82b919da000d00c408bde39337e034e0ef1e0f82c610cc115983c014701be2478516093b02bc0c745aa31a302e40f64200305cb8cad09c17a02e7490a10b8490027e018eefd863302ab77f42ce0175026f65fe24f05f2033004a610b45d082a6087422f44ed01d207162b701ea038372fed01d91d0035043cced9cf1800001b80290538040500b62a481d5b87c082c0d6c1f0b3bf6312000000000e46064eb3400032a7668806cc0768000074c0925c16000067500c1001f246d64a4f0c059b01ce03b800298b4848462fc0000070881672ee0001cdd000000001160000000066ec000017d03c000000ac806209600440c3b4176813a000005f007f3b2f032425d041638a416cc017c000000001c40db9d96b05700b0088991e0b590852e6c9c0cb97101c6cf75c9a835200002718100336f77f20df) else (if i<3 then 0x74596024101cc03bdcf98b130388517813b80d262f2c58c533035e679ce31c1fd8c2604c00e699cbb36c6812e498588081e757e04401c639b87644eb1c24700600916024dcdb094112dee1ec5300ae37168087409b831328cae195a0109c50730ebed809837801d2f1f81808120641c0b6c47283fa06460919927011764b6085021fb3cc704c01dc0b1839103f20de811e031b040a00c44bcbc8000ba07cc4bf0c02072406b806a8385024c0d941af845f17d2cee84b183fc07e0ce045028061044c0d1980c04200216c64802d036a07582c45cc480b806b8069405630bd76620835c0d318f776c22e8152b9370872071813603d80838082c14080bb00d625600e4b9b548bec60421502d76252c7344be38b5053021b0134012a14dc7189cf1016828d62fbc07e813b77740c9c4063221061c029c16eb17d028a09c9dd110e102b20ed4025807d004c0beddfe00790354c6f00fd844b072c08901ee00ad1630c0518d13190675ec079c7c83b428ba03301a69463055020c9a0f146206840ff4082823500f4f21c1603a3f04c201b00060b7466bc059c04dbb02059a221820780b31868c1c5dd1a47d003cea1c17980bc013222d0026027000000e7c0443117009003e1cc73825060c0179d54839513aa10300f4896e717601a0440818e000009404a8818102f005680658bfa0000e029d078258018a0ca819a89d9010ece3040a039d7848e0ac000036300000e9014102b00310c47d8b7b25e02c0206dd76948015b621618e30442069c00019d8000003d82fa861d32c2607c04340040445039e20a182f80c6629c0965895bb77185ec5ec00003840674c67c00b8274148029b4194000003b2010817cb996045406c40000210156603c1995834100000d24087845302ee0e6c52b02b3090c11ac18a884605a4d0280cb3319028607d410e02420236c541def00d10212000186324891866c5240b803f7774a0324027800008a0277d9618266000010d4103009501b6116c14e001500ea00d02058b2213ba30b123c03b1052cc95020a832462422a459068ba51422011c23f0139616c27a809b0834068a008051681a2035aedec23203c16480109459e837b13cee6b415fb3985914ce7022480f688ccf1545ef03cf64a2caf819c8000127aed219db8c03116a24fc4f401fc126003281168412732210ed853bbf713ac0c2980339f5059c0ee80ad81ba08102dd841a800f00000928075010413e60211cd83ab417b40c7c1e100d366f000a011e80e76764e7ddc6f087c60600ecc175bbe916e20112e31b01d000025340a30be1029409fc5eb0285000029e80270212038400e5959bc520356000044bb864063800e81260125725e07400aa81cd618a05bc14a01c80418e72c0a13c4603ccc281d7781ed60b001ec201337407aa0009c67b161042c08d1a17146 else (if i<4 then 0x1c06a201e18cb0262040e01b8028145a00362060157040913241194034829508aa05d0181823902a2eb1813683aa08a808ac508000005d21101240841307bac2c4408032101d8e35c4a3808108a4cc9824683de04ea06504468ac3000acf7849c880f6792f094020843417c0f169ddb88e40292e2e008180cd03400045ceb818473b60df5dbab18503c4eecc0bf01fd1810e6cc58f00a910ec11318be00d7665e0d68611846c066eccd40b203b2a1d2205422b8375646809740000be70396210c092009464b20d2c5c50371101a10ac2348b3a0548c5ac11b01c0735c04cc1b2545a048011fc1088a67075ec05410fb2ab08e60cb001d835db8d210b01643a3869022ec80ce01bb04b4cc08127b2cc0008306581a382773e4cd381aa0b73b8cc02240350411173ee5c85c303f6739a009ddd3894b722609905d7024d58ba107dccf81110144c0641140a8d0864ce9c5d18b8501622e085d10000036e00005c18a6971b2123015d038e7436c23400003cb1160c6f423014840230c714448032905720614206b8b900c8060c1df00bd17b2014400003e86578041c17bbb3012a60b98615818c7514000009e017f6300304804000000000639c00002d5136c000040933bb789400005dc83c4011ecd3c000327807fc07581810000673c2d8800c03db13bcc92c1d481ef0578c0cd81701660558ca2598fb203182cca34015037c085e25258b38219057671dd9e1baec033c0bc18713aff0700ecdc56f801f031ae4d000003447334c85c0003184750000019b9800002c40f381c83350037205ac0c80b2d7632e25c0ea045900000a201990340037026cc118b38a077006a59b209e500280fbc12b0165041221ac20f01f7133c0024000000003fc000190e809c07e2267c16a03ee00000001e23b06b766a000050681eb05f80f5c16f896c0000112843d8475047c002c1f6823a0312056006d0407071410cc0a0012102c200f41a782e000560c2189202c16244cd801b381c375fac93dd7580c3013010281e802780218e6780f884831098eac40be8bfb709400005ad800002ec06a0e34047a0828c638123810e074e00004c9b09905d8c9fc0f38447046e03e423e0063737ef1144fa819b62ae31f06263097145e000010080f7042a0c318b7018772ae09719c9085501680e819afba83056e51c4171005900ce0b781c6bc4f648a05ec05000e014f0c95806000b514480bbc207021809020efc1503087083607d9d14892565a2c971d2003e906b2638183981e4006e00758c3b2fc741227dde0203227124ea4021230a401900d2806a03256874260815a009f68600da00f183df08ce0e5c0d332df015eeb841e503ae612403fd9cc813508d42b2c200846373d0ed2c172823803160f4c4148066005ceb74048828e04cac5785dd03ea68680f944f63b8a03600a else 0x1548c2e18960a7811733366250cde59d9833662be055850e88a6167ce0d01458244183e0ddc5b90171089a0f181463c53000026e044b02e80562c4d808c8a8271ec0b3ee31046f03820c2d230815003fe06b04b28186071e27718c6b9c72916c0e195d838905b40c000e380c20000e4c01b5827a62ea000007280ba00eceb31cd7b2a8742622e40000466008ce72814980b0156cc0700003a8e6036efd409803e208f002b81f3808b03b602a00418245116e25c5d0b8154176c015000031300414f0f1c6a03d207022711dbd00160000c56d23d800000df11a5c88b24976ce03045c20b61025c099c09683b96310065c1cf022c74540bb800002c9166206fc05f8000732e05e58b88086000029cc0670000000e000195b015d013a07c000000a50786108c00000b2034600001b0807162b411b813e0aed06c083a4213882264b4098c032b1cba8f022800ee839377de06f404f00000026f0e810408a70446ed0c162336e022a010c407011365220dd022e80dd06b00dc81e6815f06a60ad9d0d029106ae0e1c08f3a8d05b8eb101bb00eb053eeba598a0316125230500833bab1084009000031781778000001e007c0252c71c2110373166a00018ae007003c2edf8000147814242610242846d04420c50430816d00ac0e19c3382f17596ced41a38bb706322230166332d65a024e8444034803b4e3744f581f428ee0f1420d33ad17fe04001618b2468400fb008e81416858ed941f202a10612e54821f31a541c20cbc02e3c7817e80bd4462041d1072eec192c0488608c090c0e2812f08620da423a39c661e409500a403111178cfb857382c702b8c48ddb4025b10c4cc6022d010a00e4cab4009398b065ccb158dc8477012c05b993782d305b2eb04102245905440eedd04001c64f421719410287088c05a42080a22055a217c03a32c010600ea1d9500aa1408ee21d648c00016ec6f84ad029a685420d80db027b05fe095c1e60b5a07acc5a00000a250322001808a3174027e0e944a502d6775a0d5810980a101d01099caa094c674ae7981c13a8f17d80ef59988000775c02d81fc0132176a00002310bcf74240a3c0c9828602ae2c5423db9f463142ff85da39c1000003780000c8a77d803641398001056ae368238096b058b51b00d0b11b000006d5d55011208f2e62004d01d3000024b1889085770fa256423089)))
def pH1_37 (h : Nat) : Option (Nat × Nat) := lw0 525 2222 12 15 11 4 pH1_37F h
def pL40F (i : Nat) : Nat := 0x45299b41ae80ea2ce035299b43ae9382406abf2987418701aa2905aac85c48235186ead952867a716411a5c4638b1a6fc60d0b86fb5591208d2e0a6f4e2c8235185c37d0d208d35571189046a30d55c37d53208d32171189046a30c85c2a50c827a716401a20105bea94320845c5db08034df54a0b6d206406952867a716401a20f3d58edd49715f3862b12a02e38380bfe984897fd20912ffa21227ef5da44fdec0c89fbc81913f7ae3227ef58644fdea8c89fbc51913f7a43227ef08644fdeb0489fbd30913f7a41227ef44244
def pL40 : PT := (16,2,7,7,pL40F)
def pH0_40F (i : Nat) : Nat := 0xc0080040000
def pH0_40 (h : Nat) : Option (Nat × Nat) := lw0 4 6 3 6 2 4 pH0_40F h
def pH1_40F (i : Nat) : Nat := 0x1d781c03004a832814c0700bdc358cdc91979c39a91a9c1b1d2c211a786781708c42f81144e031982404c675d800ac5958fc160121874b1009c0019359841840cc1ac0a0261d601bc2241cc43dd98649ca85d418c02c201ee802420c4f5dd4238001cd01644f02dc0544398398a9eb017422c2740d8285d644d000000465c5558701dc5dc69c72c1419701d80001a02e59fc22014800048c30847826c0f81f823c454695db02fc599a585f02c019c52c1c9c99ea86b4091948130465a01324111f3009432c2a5a48b09d3c1ed8dda442e063d8441c464d85006c5502880b06005fc0ec5e0180571849de07301059edd381b407cf020cc305e0984023421c298065a382482a02d40200101785d19d40c9905d34244430b181b82805a41340b9a400d40a812c23032590180cafc278310229ab5cb408c0e58a19cc0899142c82680445c419820af042598790d02f41298f015c48411c61d7188cc18844c074271da9dd00158081001580500345c0195e76701df8425a61975b30049d298d98f81241a42900c18f452189c1f5da40f01382b42e8119e1d0c467c06030dccc2a99a419186eb05e445240c41a829c1d5ee184d8041681e19e0534255a3c0402c400c2146f02b0689a05d0c219a681d1c242940b587c3304444a04cc2cc0081e40fc58dd042d01fc0281e85900318686985d93142ac25001827c41cb042d817c0799d02402f01084944904359c8151d1016dd95ca0085a5428c0a5e2405d82063468431c2058d03202b80e08c813deec0582bc25c2646185e810c039a7c529cb8098671d002ec03c3140680d00dda99a0815424c1446ddce80800f5a4c01c0e81f02c09040cc8004020481218058302255000b4100a0b0405e0816018001c000c05e1f8a8040a092617c18025189400445306006a23b0c08001008184c701780c2812010203411128000432110000e44408f04c030a010060a7b90400002800806140f80400001c00c0051000080a011085c2c0100091781c2a01c3001010100a010d00cba0502002a00d000001004010b0020017c4c1624
def pH1_40 (h : Nat) : Option (Nat × Nat) := lw0 134 404 9 12 8 4 pH1_40F h
def pL43F (i : Nat) : Nat := 0x5f290618022045361ac5b6201a18e507fe44fbe44
def pL43 : PT := (2,1,7,4,pL43F)
def pH1_43F (i : Nat) : Nat := 0x786606701b0b1314630a001d3e2f1073610d03680e010000000015719d09087e0019002e04071a5d3d0c1805694f7d025e600f67791e1100000a0000000810070003c710300000602600041c0000000000000040c004000010000c147
def pH1_43 (h : Nat) : Option (Nat × Nat) := lw0 50 55 6 8 4 4 pH1_43F h
def pL : Nat → PT
  | 24 => pL24
  | 27 => pL27
  | 28 => pL28
  | 30 => pL30
  | 31 => pL31
  | 33 => pL33
  | 34 => pL34
  | 36 => pL36
  | 37 => pL37
  | 40 => pL40
  | 43 => pL43
  | _ => emptyPT
def pI0 : Nat → Nat → Option (Nat × Nat)
  | 27 => pH0_27
  | 30 => pH0_30
  | 31 => pH0_31
  | 33 => pH0_33
  | 34 => pH0_34
  | 36 => pH0_36
  | 37 => pH0_37
  | 40 => pH0_40
  | _ => fun _ => none
def pI1 : Nat → Nat → Option (Nat × Nat)
  | 31 => pH1_31
  | 34 => pH1_34
  | 37 => pH1_37
  | 40 => pH1_40
  | 43 => pH1_43
  | _ => fun _ => none
abbrev bk := bk1 pL pI0 pI1
abbrev bm (k t s a b : Nat) := @m130 pL pI0 pI1 k t s a b
set_option maxHeartbeats 0 in
theorem c24_0 : bk 8 0 0 1=true:=cb1 (ar:=9) (by decide +kernel)
theorem a24 : bk 8 0 0 1=true:=c24_0
set_option maxHeartbeats 0 in
theorem c27_0 : bk 9 0 0 7=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c27_7 : bk 9 0 7 22=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
theorem a27 : bk 9 0 0 29=true:=(bm 9 0 0 7 22 c27_0 c27_7)
set_option maxHeartbeats 0 in
theorem c28_0 : bk 9 1 0 24=true:=csb1 (ar:=9) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c28_24 : bk 9 1 24 24=true:=csb1 (ar:=9) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c28_48 : bk 9 1 48 17=true:=csb1 (ar:=9) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
theorem a28 : bk 9 1 0 65=true:=(bm 9 1 0 24 41 c28_0 (bm 9 1 24 24 17 c28_24 c28_48))
set_option maxHeartbeats 0 in
theorem c30_0 : bk 10 0 0 18=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c30_18 : bk 10 0 18 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c30_42 : bk 10 0 42 13=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
theorem a30 : bk 10 0 0 55=true:=(bm 10 0 0 18 37 c30_0 (bm 10 0 18 24 13 c30_18 c30_42))
set_option maxHeartbeats 0 in
theorem c31_0 : bk 10 1 0 24=true:=csb1 (ar:=9) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_24 : bk 10 1 24 24=true:=csb1 (ar:=9) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_48 : bk 10 1 48 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_72 : bk 10 1 72 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_96 : bk 10 1 96 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_120 : bk 10 1 120 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_144 : bk 10 1 144 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_168 : bk 10 1 168 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_192 : bk 10 1 192 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_216 : bk 10 1 216 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_240 : bk 10 1 240 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_264 : bk 10 1 264 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_288 : bk 10 1 288 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_312 : bk 10 1 312 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_336 : bk 10 1 336 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_360 : bk 10 1 360 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_384 : bk 10 1 384 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_408 : bk 10 1 408 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_432 : bk 10 1 432 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_456 : bk 10 1 456 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_480 : bk 10 1 480 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_504 : bk 10 1 504 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_528 : bk 10 1 528 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_552 : bk 10 1 552 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_576 : bk 10 1 576 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_600 : bk 10 1 600 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c31_624 : bk 10 1 624 10=true:=cb1 (ar:=10) (by decide +kernel)
theorem a31 : bk 10 1 0 634=true:=(bm 10 1 0 312 322 (bm 10 1 0 144 168 (bm 10 1 0 72 72 (bm 10 1 0 24 48 c31_0 (bm 10 1 24 24 24 c31_24 c31_48)) (bm 10 1 72 24 48 c31_72 (bm 10 1 96 24 24 c31_96 c31_120))) (bm 10 1 144 72 96 (bm 10 1 144 24 48 c31_144 (bm 10 1 168 24 24 c31_168 c31_192)) (bm 10 1 216 48 48 (bm 10 1 216 24 24 c31_216 c31_240) (bm 10 1 264 24 24 c31_264 c31_288)))) (bm 10 1 312 168 154 (bm 10 1 312 72 96 (bm 10 1 312 24 48 c31_312 (bm 10 1 336 24 24 c31_336 c31_360)) (bm 10 1 384 48 48 (bm 10 1 384 24 24 c31_384 c31_408) (bm 10 1 432 24 24 c31_432 c31_456))) (bm 10 1 480 72 82 (bm 10 1 480 24 48 c31_480 (bm 10 1 504 24 24 c31_504 c31_528)) (bm 10 1 552 48 34 (bm 10 1 552 24 24 c31_552 c31_576) (bm 10 1 600 24 10 c31_600 c31_624)))))
set_option maxHeartbeats 0 in
theorem c33_0 : bk 11 0 0 1=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c33_1 : bk 11 0 1 6=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c33_7 : bk 11 0 7 20=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c33_27 : bk 11 0 27 24=true:=csb1 (ar:=12) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c33_51 : bk 11 0 51 3=true:=cb1 (ar:=12) (by decide +kernel)
theorem a33 : bk 11 0 0 54=true:=(bm 11 0 0 7 47 (bm 11 0 0 1 6 c33_0 c33_1) (bm 11 0 7 20 27 c33_7 (bm 11 0 27 24 3 c33_27 c33_51)))
set_option maxHeartbeats 0 in
theorem c34_0 : bk 11 1 0 2=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c34_2 : bk 11 1 2 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_26 : bk 11 1 26 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_50 : bk 11 1 50 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_74 : bk 11 1 74 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_98 : bk 11 1 98 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_122 : bk 11 1 122 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_146 : bk 11 1 146 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_170 : bk 11 1 170 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_194 : bk 11 1 194 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_218 : bk 11 1 218 18=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_236 : bk 11 1 236 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_260 : bk 11 1 260 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_284 : bk 11 1 284 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_308 : bk 11 1 308 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_332 : bk 11 1 332 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_356 : bk 11 1 356 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_380 : bk 11 1 380 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_404 : bk 11 1 404 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_428 : bk 11 1 428 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_452 : bk 11 1 452 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_476 : bk 11 1 476 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_500 : bk 11 1 500 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_524 : bk 11 1 524 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_548 : bk 11 1 548 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_572 : bk 11 1 572 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_596 : bk 11 1 596 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_620 : bk 11 1 620 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_644 : bk 11 1 644 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_668 : bk 11 1 668 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_692 : bk 11 1 692 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_716 : bk 11 1 716 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_740 : bk 11 1 740 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_764 : bk 11 1 764 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_788 : bk 11 1 788 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_812 : bk 11 1 812 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_836 : bk 11 1 836 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_860 : bk 11 1 860 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_884 : bk 11 1 884 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_908 : bk 11 1 908 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_932 : bk 11 1 932 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_956 : bk 11 1 956 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_980 : bk 11 1 980 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1004 : bk 11 1 1004 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1028 : bk 11 1 1028 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1052 : bk 11 1 1052 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1076 : bk 11 1 1076 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1100 : bk 11 1 1100 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1124 : bk 11 1 1124 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_1148 : bk 11 1 1148 19=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
theorem a34 : bk 11 1 0 1167=true:=(bm 11 1 0 572 595 (bm 11 1 0 260 312 (bm 11 1 0 122 138 (bm 11 1 0 50 72 (bm 11 1 0 2 48 c34_0 (bm 11 1 2 24 24 c34_2 c34_26)) (bm 11 1 50 24 48 c34_50 (bm 11 1 74 24 24 c34_74 c34_98))) (bm 11 1 122 72 66 (bm 11 1 122 24 48 c34_122 (bm 11 1 146 24 24 c34_146 c34_170)) (bm 11 1 194 24 42 c34_194 (bm 11 1 218 18 24 c34_218 c34_236)))) (bm 11 1 260 144 168 (bm 11 1 260 72 72 (bm 11 1 260 24 48 c34_260 (bm 11 1 284 24 24 c34_284 c34_308)) (bm 11 1 332 24 48 c34_332 (bm 11 1 356 24 24 c34_356 c34_380))) (bm 11 1 404 72 96 (bm 11 1 404 24 48 c34_404 (bm 11 1 428 24 24 c34_428 c34_452)) (bm 11 1 476 48 48 (bm 11 1 476 24 24 c34_476 c34_500) (bm 11 1 524 24 24 c34_524 c34_548))))) (bm 11 1 572 288 307 (bm 11 1 572 144 144 (bm 11 1 572 72 72 (bm 11 1 572 24 48 c34_572 (bm 11 1 596 24 24 c34_596 c34_620)) (bm 11 1 644 24 48 c34_644 (bm 11 1 668 24 24 c34_668 c34_692))) (bm 11 1 716 72 72 (bm 11 1 716 24 48 c34_716 (bm 11 1 740 24 24 c34_740 c34_764)) (bm 11 1 788 24 48 c34_788 (bm 11 1 812 24 24 c34_812 c34_836)))) (bm 11 1 860 144 163 (bm 11 1 860 72 72 (bm 11 1 860 24 48 c34_860 (bm 11 1 884 24 24 c34_884 c34_908)) (bm 11 1 932 24 48 c34_932 (bm 11 1 956 24 24 c34_956 c34_980))) (bm 11 1 1004 72 91 (bm 11 1 1004 24 48 c34_1004 (bm 11 1 1028 24 24 c34_1028 c34_1052)) (bm 11 1 1076 48 43 (bm 11 1 1076 24 24 c34_1076 c34_1100) (bm 11 1 1124 24 19 c34_1124 c34_1148))))))
set_option maxHeartbeats 0 in
theorem c36_0 : bk 12 0 0 3=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c36_3 : bk 12 0 3 1=true:=cb1 (ar:=11) (by decide +kernel)
theorem a36 : bk 12 0 0 4=true:=(bm 12 0 0 3 1 c36_0 c36_3)
set_option maxHeartbeats 0 in
theorem c37_0 : bk 12 1 0 5=true:=cb1 (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c37_5 : bk 12 1 5 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_29 : bk 12 1 29 24=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_53 : bk 12 1 53 1=true:=cb1 (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c37_54 : bk 12 1 54 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_78 : bk 12 1 78 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_102 : bk 12 1 102 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_126 : bk 12 1 126 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_150 : bk 12 1 150 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_174 : bk 12 1 174 24=true:=csb1 (ar:=11) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c37_198 : bk 12 1 198 7=true:=cb1 (ar:=11) (by decide +kernel)
theorem a37 : bk 12 1 0 205=true:=(bm 12 1 0 78 127 (bm 12 1 0 29 49 (bm 12 1 0 5 24 c37_0 c37_5) (bm 12 1 29 24 25 c37_29 (bm 12 1 53 1 24 c37_53 c37_54))) (bm 12 1 78 72 55 (bm 12 1 78 24 48 c37_78 (bm 12 1 102 24 24 c37_102 c37_126)) (bm 12 1 150 24 31 c37_150 (bm 12 1 174 24 7 c37_174 c37_198))))
set_option maxHeartbeats 0 in
theorem c40_0 : bk 13 1 0 16=true:=csb1 (ar:=10) (d:=1) ⟨k1 (by decide +kernel),k1 (by decide +kernel)⟩
theorem a40 : bk 13 1 0 16=true:=c40_0
set_option maxHeartbeats 0 in
theorem c43_0 : bk 14 1 0 2=true:=cb1 (ar:=9) (by decide +kernel)
theorem a43 : bk 14 1 0 2=true:=c43_0
theorem tabs : ∀ k ≤ 14, ∀ t ≤ 1, bk k t 0 (pL (3*k+t)).1=true:=by
 intro k hk t ht;interval_cases k <;> interval_cases t
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact a24
 · rfl
 · exact a27
 · exact a28
 · exact a30
 · exact a31
 · exact a33
 · exact a34
 · exact a36
 · exact a37
 · rfl
 · exact a40
 · rfl
 · exact a43
def seed1666 : Sig:=neg (inputs.getD 4 zero)
def roots1666 : List Sig:=inputs ++ [seed1666]
def negRoots1666 : List Sig:=(inputs.erase (inputs.getD 4 zero)) ++ [seed1666]
theorem m56 (x : Fin 9 → Bool) : edge x=Binary.PetersenNine.edgeFun Binary.PetersenNine.edges x:=by
  unfold edge Binary.PetersenNine.edgeFun Binary.PetersenNine.edges
  simp [List.any_cons,List.any_nil,Bool.or_assoc]
theorem m131 (r : Row) : bit r seed1666 = !(sample r 4):=by
  simp only [seed1666,bit_neg,sample]; rfl
theorem m108 :
    (List.finRange 9).all (fun i =>
      i.val==4 ||
      ((bit (absentRow i) graph != bit (presentRow i) graph) &&
       roots1666.all (fun w => w==inputs.getD i.val zero||bit (absentRow i) w==bit (presentRow i) w)))=true:=by
  decide +kernel
theorem m118a : bit (absentRow ⟨4,by decide⟩) graph ≠ bit (presentRow ⟨4,by decide⟩) graph:=by
  decide +kernel
theorem m118b :
    roots1666.all (fun w => w==inputs.getD 4 zero||w==seed1666 ||
      bit (absentRow ⟨4,by decide⟩) w==bit (presentRow ⟨4,by decide⟩) w)=true:=by
  decide +kernel
theorem same_on_live {T k t S} (h : Live T k t S) (r1 r2 : Row)
    (hs : ∀ v ∈ S,bit r1 v=bit r2 v) : bit r1 T=bit r2 T:=by
  induction h using Live.recurse with
  | stop => exact hs _ (Finset.mem_singleton_self _)
  | unary _ _ _ ih =>
    apply ih; intro v hv; simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · simp only [bit_neg,hs _ (Finset.mem_insert_self _ _)]
    · exact hs _ (Finset.mem_insert_of_mem hv)
  | binary _ _ _ _ _ ih =>
    apply ih; intro v hv; simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · simp only [bit_bin,hs _ (Finset.mem_insert_self _ _),
        hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))]
    · exact hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
def col16 : ColumnInfo:=(16,0,495,0,13)
def pool16 : BoundPool:=⟨subcube 16 0,13,0,vars 511⟩
theorem m151 : ValidPool (vars 511) graph pool16:=by
  have hgd:=geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at hgd
  have hmem : col16 ∈ dead.cols.values:=List.contains_iff_mem.mp (by decide +kernel : dead.cols.values.contains col16=true)
  have hslice:=m50 col16 (boundsBefore known383) (m4 known383 valid383) (hgd.1.2 col16 hmem)
  have htgt : chartGoal dead.mask=graph:=by decide +kernel
  rw [htgt] at hslice
  exact m37 (cs:=[]) hslice rfl
theorem noBoth1666 : Impossible graph 14 (seed1666 :: inputs).toFinset:=by
  have heq : choiceVal (0,seed1666,seed1666)=seed1666:=by
    change bin false seed1666 seed1666=seed1666; unfold bin; exact BitVec.and_self
  have hnd : (choiceVal (0,seed1666,seed1666) :: inputs).Nodup:=by
    rw [heq]; exact of_decide_eq_true (by decide +kernel : decide (seed1666 :: inputs).Nodup=true)
  have hcut : scalarPoolCut pool16 14 inputs (0,seed1666,seed1666)=true:=by decide +kernel
  have h:=m9 m151 hnd hcut
  rwa [heq] at h
theorem noNeg1666 : I1 graph 14 1 negRoots1666.toFinset:=by
  have hall:=f1_all pL pI0 pI1 14 (boundsBefore known383)
    (m4 known383 valid383) geomdead tabs 14 (by decide) 1 (by decide) 0 (by decide)
  have hs : sameWords (sS pL 43 0) negRoots1666=true:=by decide +kernel
  have htgt : targetOf dead=graph:=by decide +kernel
  rw [← m11 hs,← htgt]
  exact hall
theorem noPos1666 : I1 graph 14 1 inputs.toFinset:=by
  have hall:=f1_all pL pI0 pI1 14 (boundsBefore known383)
    (m4 known383 valid383) geomdead tabs 14 (by decide) 1 (by decide) 1 (by decide)
  have hs : sameWords (sS pL 43 1) inputs=true:=by decide +kernel
  have htgt : targetOf dead=graph:=by decide +kernel
  rw [← m11 hs,← htgt]
  exact hall
theorem kill1666 {k t S} (hk : k ≤ 14) (ht : t ≤ 1) (h : Live graph k t S) (sub : ∀ v ∈ S,v ∈ roots1666) : False:=by
  have hother : ∀ i : Fin 9,i.val≠4 → inputs.getD i.val zero ∈ S:=by
    intro i hi
    have hh:=List.all_eq_true.mp m108 i (List.mem_finRange i)
    have hne : (i.val==4)=false:=beq_eq_false_iff_ne.mpr hi
    rw [hne] at hh
    simp only [Bool.false_or,Bool.and_eq_true,bne_iff_ne] at hh
    have h2:=List.all_eq_true.mp hh.2
    exact m32 h _ _ sub (absentRow i) (presentRow i) hh.1 (fun w hw hn => by
      have ha:=h2 w hw; simp only [Bool.or_eq_true,beq_iff_eq] at ha; exact ha.resolve_left hn)
  have hfour : inputs.getD 4 zero ∈ S∨seed1666 ∈ S:=by
    by_contra hneither
    push Not at hneither
    have h2:=List.all_eq_true.mp m118b
    have hsub : ∀ v ∈ S,bit (absentRow ⟨4,by decide⟩) v=bit (presentRow ⟨4,by decide⟩) v:=by
      intro v hv
      have ha:=h2 v (sub v hv)
      have hn1 : (v==inputs.getD 4 zero)=false:=beq_eq_false_iff_ne.mpr (fun e => hneither.1 (e ▸ hv))
      have hn2 : (v==seed1666)=false:=beq_eq_false_iff_ne.mpr (fun e => hneither.2 (e ▸ hv))
      rw [hn1,hn2] at ha
      simp only [Bool.false_or] at ha
      exact beq_iff_eq.mp ha
    exact m118a (same_on_live h (absentRow ⟨4,by decide⟩) (presentRow ⟨4,by decide⟩) hsub)
  by_cases h4 : inputs.getD 4 zero ∈ S
  · have haveIn : inputs.toFinset ⊆ S:=by
      intro v hv
      have hm:=List.mem_toFinset.mp hv
      rw [← m38,List.mem_ofFn] at hm
      obtain ⟨i,rfl⟩:=hm
      by_cases hi : i.val=4
      · rw [hi]; exact h4
      · exact hother i hi
    by_cases hs : seed1666 ∈ S
    · have eqS : S=(seed1666 :: inputs).toFinset:=by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm:=sub v hv
          simp only [roots1666,List.mem_append,List.mem_singleton] at hm
          rcases hm with hm | rfl <;> simp [*]
        · intro v hv
          simp only [List.toFinset_cons,Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact hs
          · exact haveIn hv
      exact noBoth1666 k t hk (eqS ▸ h)
    · have eqS : S=inputs.toFinset:=by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm:=sub v hv
          simp only [roots1666,List.mem_append,List.mem_singleton] at hm
          rcases hm with hm | rfl
          · exact List.mem_toFinset.mpr hm
          · exact False.elim (hs hv)
        · exact haveIn
      exact noPos1666 k t hk ht (eqS ▸ h)
  · have hs : seed1666 ∈ S:=hfour.resolve_left h4
    have eqS : S=negRoots1666.toFinset:=by
      apply Finset.Subset.antisymm
      · intro v hv
        have hm:=sub v hv
        simp only [roots1666,List.mem_append,List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have hne : v≠inputs.getD 4 zero:=fun e => h4 (e ▸ hv)
          exact List.mem_toFinset.mpr (List.mem_append_left _ ((List.mem_erase_of_ne hne).mpr hm))
        · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
      · intro v hv
        have hm:=List.mem_toFinset.mp hv
        simp only [negRoots1666,List.mem_append,List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have hm':=List.mem_of_mem_erase hm
          have hnd : inputs.Nodup:=of_decide_eq_true (by decide +kernel : decide inputs.Nodup=true)
          have hne4 : v≠inputs.getD 4 zero:=fun e => hnd.not_mem_erase (e ▸ hm)
          rw [← m38,List.mem_ofFn] at hm'
          obtain ⟨i,rfl⟩:=hm'
          exact hother i (fun hi => hne4 (by rw [hi]))
        · exact hs
    exact noNeg1666 k t hk ht (eqS ▸ h)
theorem main1666 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool,(C.wires (List.ofFn y)).getD 9 false = !(y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C=edge) : 16 ≤ C.size:=by
  by_contra hlt
  have small : C.size ≤ 15:=by omega
  have headEq : (execute C.gates inputs).getD 9 zero=seed1666:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    change bit r ((execute C.gates inputs).getD 9 zero)=bit r seed1666
    rw [← b_read,m47 _ _ _ (fun g hg => (legal g hg).1),←sampled]
    exact (first (sample r)).trans (m131 r).symm
  have goalEq : (execute C.gates inputs).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row:=⟨j,hj⟩
    change bit r ((execute C.gates inputs).getD C.output zero)=bit r graph
    rw [← b_read,m47 _ _ _ (fun g hg => (legal g hg).1),←sampled]
    exact (congrFun computes (sample r)).trans (edge_table r).symm
  have out:=get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn:=out.resolve_right (fun hn => hn m76)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at targetIn
    exact (show graph ∉ inputs from fun hm => by
      have hnc : inputs.contains graph=false:=by decide +kernel
      rw [List.contains_eq_mem,decide_eq_false_iff_not] at hnc; exact hnc hm) targetIn
  | cons g rest =>
    have eq0 : gv inputs g=seed1666:=by
      rw [hgs] at headEq
      change (execute rest (inputs ++ [gv inputs g])).getD 9 zero=seed1666 at headEq
      obtain ⟨l,hl⟩:=m129 rest (inputs ++ [gv inputs g])
      rw [hl] at headEq
      exact headEq
    have hg_not : g.op=GateOp.not:=by
      have h0:=congrArg (bit ⟨0,by decide⟩) eq0
      have hs0 : bit ⟨0,by decide⟩ seed1666=true:=by decide +kernel
      rw [hs0] at h0
      have hin0 (a : Nat) : bit ⟨0,by decide⟩ (inputs.getD a zero)=false:=by
        by_cases ha : a < 9
        · interval_cases a <;> decide +kernel
        · have hge : inputs.length ≤ a:=by rw [← m38,List.length_ofFn]; exact Nat.le_of_not_lt ha
          rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none hge]
          exact (by decide +kernel : bit ⟨0,by decide⟩ zero=false)
      have h16:=congrArg (bit ⟨16,by decide⟩) eq0
      have hs16 : bit ⟨16,by decide⟩ seed1666=false:=by decide +kernel
      rw [hs16] at h16
      have hleg0:=(legal g (by rw [hgs]; exact List.mem_cons_self)).1
      rcases hleg0 with h1 | h2 | h3
      · exfalso
        cases hi : g.inputs with
        | nil =>
          have hv16 : bit ⟨16,by decide⟩ (gv inputs g)=true:=by
            simp only [gv,h1,hi,List.map_nil,List.foldr_nil]; decide +kernel
          rw [hv16] at h16; cases h16
        | cons a t =>
          have hv0 : bit ⟨0,by decide⟩ (gv inputs g)=false:=by
            simp only [gv,h1,hi,List.map_cons,List.foldr_cons,bit_bin,Bool.false_eq_true,ite_false,hin0,Bool.false_and]
          rw [hv0] at h0; cases h0
      · exfalso
        have hv0 : bit ⟨0,by decide⟩ (gv inputs g)=false:=by
          simp only [gv,h2]
          have hfr : ∀ xs : List Nat, bit ⟨0,by decide⟩ ((xs.map fun i => inputs.getD i zero).foldr (bin true) zero)=false:=by
            intro xs; induction xs with
            | nil => decide +kernel
            | cons a t ih => simp only [List.map_cons,List.foldr_cons,bit_bin,ite_true,hin0,ih,Bool.false_or]
          exact hfr g.inputs
        rw [hv0] at h0; cases h0
      · exact h3
    rw [hgs] at targetIn
    change graph ∈ execute rest (inputs ++ [gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ rest,gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧gate.inputs.length ≤ 2 :=
      fun gate hg => legal gate (by rw [hgs]; exact List.mem_cons_of_mem _ hg)
    have len : rest.length ≤ 14:=by simp [Circuit.size,hgs] at small; omega
    have hlow:=Binary.petersen_binary_lower C legal (fun x => (congrFun computes x).trans (m56 x))
    have hnn : Binary.CircuitProof.nonNotCount C.gates=Binary.CircuitProof.nonNotCount rest:=by
      rw [hgs]
      simp [Binary.CircuitProof.nonNotCount,hg_not,Binary.CircuitProof.isNotGate]
    rw [hnn] at hlow
    have hbound:=Binary.nonNotCount_add_notCount rest
    change Binary.CircuitProof.nonNotCount rest+(rest.filter fun q => Binary.CircuitProof.isNotGate q.op).length=rest.length at hbound
    have hfeq : (fun q : Gate => isNotT q.op)=(fun q : Gate => Binary.CircuitProof.isNotGate q.op):=by
      funext q; cases q.op <;> rfl
    have hcntEq : rest.countP (fun q => isNotT q.op)=(rest.filter fun q => Binary.CircuitProof.isNotGate q.op).length:=by
      rw [List.countP_eq_length_filter,hfeq]
    have ht1 : rest.countP (fun q => isNotT q.op) ≤ 1:=by omega
    obtain ⟨k,t,S,hk,ht,run,hs⟩:=extractT rest roots1666 tailLegal m76 targetIn
    exact kill1666 (hk.trans len) (ht.trans ht1) run hs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def extendWire (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem old_wire (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl extendWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (extendWire w g).length := by
      simp only [extendWire, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (extendWire w g) hlt]
    simp only [extendWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem add_input (bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (4 : Fin (9 : ℕ))]) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C hfan hsize
  by_contra h
  push Not at h
  let head : Gate := ⟨GateOp.not, [4]⟩
  let D : Circuit := ⟨head :: C.gates, C.output⟩
  have fan : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [head]
    · exact hfan g hg
  have start (x : Fin 9 → Bool) :
      extendWire (List.ofFn x) head = List.ofFn x ++ [!x 4] := by rfl
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = !x 4 := by
    change (C.gates.foldl extendWire (extendWire (List.ofFn x) head)).getD 9 false = _
    rw [start, old_wire _ _ _ (by simp)]
    rfl
  apply Nat.not_lt_of_ge (bound D fan first ?_) (by
    change C.gates.length + 1 < 16
    change C.gates.length ≤ 14 at hsize
    omega)
  funext x
  change (C.gates.foldl extendWire (extendWire (List.ofFn x) head)).getD C.output false = _
  rw [start]
  exact h x

end PEqualNP.Outside.L_meta_4759

theorem PEqualNP.Outside.L_meta_4759 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (4 : Fin (9 : ℕ))]) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_4759.add_input PEqualNP.Outside.L_meta_4759.main1666
