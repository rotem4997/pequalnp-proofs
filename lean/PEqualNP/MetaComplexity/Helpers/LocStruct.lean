import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class, graph pieces: closure under subgraphs and the structure lemma

Proofs of `PClosure` and `PStructure` of `LocPlan.lean`. Paper: `routes/lifting/lgp/g97-local-class.md`
sections 1 and 3.

The structure lemma walks from a branch vertex `u` (or, if there is no branch vertex, from an end of
an edge) through vertices with exactly two neighbours. A thread is a path `x ... u` whose vertices
other than `u` have exactly two neighbours; a longest thread has length at least six, since the
other neighbour of its first vertex is `u` (a cycle, length at least 9), a branch vertex (distance at
least 7), a leaf (excluded), or a vertex with two neighbours (on the thread: a third neighbour; off
it: a longer thread).
-/

namespace PEqualNP.MetaComplexity.Loc.Struct

open SimpleGraph
open PEqualNP.MetaComplexity.Loc

variable {n : ℕ}

/-- `w` has exactly two neighbours. -/
def Two (G : SimpleGraph (Fin n)) (w : Fin n) : Prop :=
  ∃ a b, a ≠ b ∧ ∀ x, G.Adj w x ↔ x = a ∨ x = b

theorem classify (G : SimpleGraph (Fin n)) (w : Fin n) :
    Two G w ∨ 3 ≤ (G.neighborSet w).ncard ∨ ∃ a, ∀ x, G.Adj w x → x = a := by
  rcases Nat.lt_or_ge (G.neighborSet w).ncard 3 with h | h
  · obtain h0 | h1 | h2 : (G.neighborSet w).ncard = 0 ∨ (G.neighborSet w).ncard = 1 ∨
        (G.neighborSet w).ncard = 2 := by omega
    · right; right
      refine ⟨w, fun x hx => ?_⟩
      rw [Set.ncard_eq_zero] at h0
      have : x ∈ G.neighborSet w := hx
      rw [h0] at this
      exact absurd this (Set.notMem_empty x)
    · right; right
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
      refine ⟨a, fun x hx => ?_⟩
      have : x ∈ G.neighborSet w := hx
      rw [ha] at this
      exact this
    · left
      obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.1 h2
      refine ⟨a, b, hab, fun x => ?_⟩
      have : x ∈ G.neighborSet w ↔ x ∈ ({a, b} : Set (Fin n)) := by rw [he]
      simpa using this
  · right; left; exact h

theorem two_adj {G : SimpleGraph (Fin n)} {w m1 m2 : Fin n} (hw : Two G w) (h1 : G.Adj w m1)
    (h2 : G.Adj w m2) (hne : m1 ≠ m2) : ∀ x, G.Adj w x ↔ x = m1 ∨ x = m2 := by
  obtain ⟨a, b, hab, h⟩ := hw
  have e1 := (h m1).1 h1
  have e2 := (h m2).1 h2
  intro x
  constructor
  · intro hx
    rcases (h x).1 hx with rfl | rfl <;> rcases e1 with rfl | rfl <;>
      rcases e2 with rfl | rfl <;> simp_all
  · rintro (rfl | rfl) <;> assumption

theorem two_other {G : SimpleGraph (Fin n)} {w m : Fin n} (hw : Two G w) (hm : G.Adj w m) :
    ∃ c, c ≠ m ∧ G.Adj w c ∧ ∀ x, G.Adj w x ↔ x = m ∨ x = c := by
  obtain ⟨a, b, hab, h⟩ := hw
  rcases (h m).1 hm with rfl | rfl
  · exact ⟨b, hab.symm, (h b).2 (Or.inr rfl), h⟩
  · exact ⟨a, hab, (h a).2 (Or.inl rfl), fun x => (h x).trans Or.comm⟩

theorem two_three {G : SimpleGraph (Fin n)} {w p q r : Fin n} (hw : Two G w) (hp : G.Adj w p)
    (hq : G.Adj w q) (hr : G.Adj w r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : False := by
  have := (two_adj hw hp hq hpq r).1 hr
  rcases this with rfl | rfl
  · exact hpr rfl
  · exact hqr rfl

/-- A thread ending at `u`: a path of length at least one whose vertices before `u` have exactly
two neighbours. -/
structure Good (G : SimpleGraph (Fin n)) (u x : Fin n) (q : G.Walk x u) : Prop where
  path : q.IsPath
  pos : 1 ≤ q.length
  two : ∀ i, i < q.length → Two G (q.getVert i)

theorem exists_max (G : SimpleGraph (Fin n)) (u : Fin n)
    (h : ∃ x, ∃ q : G.Walk x u, Good G u x q) :
    ∃ x, ∃ q : G.Walk x u, Good G u x q ∧
      ∀ y (r : G.Walk y u), Good G u y r → r.length ≤ q.length := by
  classical
  let P : ℕ → Prop := fun k => ∃ x, ∃ q : G.Walk x u, Good G u x q ∧ q.length = k
  have hb : ∀ k, P k → k ≤ n := by
    rintro k ⟨x, q, hq, rfl⟩
    have := hq.path.length_lt
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨x, q, hq⟩ := h
  have hP : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec (hb _ ⟨x, q, hq, rfl⟩) ⟨x, q, hq, rfl⟩
  obtain ⟨y, r, hr, hrl⟩ := hP
  refine ⟨y, r, hr, fun z s hs => ?_⟩
  rw [hrl]
  exact Nat.le_findGreatest (hb _ ⟨z, s, hs, rfl⟩) ⟨z, s, hs, rfl⟩

theorem gv_ne {G : SimpleGraph (Fin n)} {x u : Fin n} {q : G.Walk x u} (hq : q.IsPath) {i j : ℕ}
    (hi : i ≤ q.length) (hj : j ≤ q.length) (hij : i ≠ j) : q.getVert i ≠ q.getVert j :=
  fun h => hij (hq.getVert_injOn (Set.mem_setOf.2 hi) (Set.mem_setOf.2 hj) h)

/-- A longest thread has length at least six. -/
theorem thread (G : SimpleGraph (Fin n)) (hL : InL G)
    (h1 : ¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q)
    (u v : Fin n) (hvu : G.Adj v u) (hv : Two G v)
    (hbr : 3 ≤ (G.neighborSet u).ncard ∨ ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard) :
    ∃ x, ∃ q : G.Walk x u, Good G u x q ∧ 6 ≤ q.length := by
  have h0 : Good G u v (Walk.cons hvu Walk.nil) := by
    refine ⟨?_, by simp, fun i hi => ?_⟩
    · rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simpa using hvu.ne⟩
    · simp at hi
      subst hi
      simpa using hv
  obtain ⟨x, q, hq, hmax⟩ := exists_max G u ⟨v, _, h0⟩
  refine ⟨x, q, hq, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hk := hq.pos
  have hxy : G.Adj x (q.getVert 1) := by
    simpa using q.adj_getVert_succ (i := 0) (by omega)
  have hx : Two G x := by simpa using hq.two 0 (by omega)
  obtain ⟨z, hzy, hxz, hxN⟩ := two_other hx hxy
  have hxu : x ≠ u := by
    have := gv_ne hq.path (i := 0) (j := q.length) (by omega) le_rfl (by omega)
    simpa using this
  by_cases hzu : z = u
  · subst hzu
    have hux : G.Adj z x := hxz.symm
    have hne : s(z, x) ∉ q.edges := by
      intro hmem
      have hy1 := hzy
      have hp := hq.path
      clear hmax h0 hxN hlt hk hq
      cases q with
      | nil => exact hxu rfl
      | @cons _ y' _ h q' =>
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rw [Walk.cons_isPath_iff] at hp
        simp only [Walk.getVert_cons_succ, Walk.getVert_zero] at hy1
        rcases hmem with he | he
        · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hxu h1.symm
          · exact hy1 h1
        · exact hp.2 (q'.snd_mem_support_of_mem_edges he)
    have hc : (Walk.cons hux q).IsCycle := (Walk.cons_isCycle_iff q hux).2 ⟨hq.path, hne⟩
    have := hL.1 z _ hc
    simp only [Walk.length_cons] at this
    omega
  · rcases classify G z with hz | hz | ⟨a, ha⟩
    · by_cases hzs : z ∈ q.support
      · obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.1 hzs
        have hi0 : i ≠ 0 := by
          rintro rfl
          simp only [Walk.getVert_zero] at hi
          exact hxz.ne hi
        have hi1 : i ≠ 1 := by
          rintro rfl
          exact hzy hi.symm
        have hik : i ≠ q.length := by
          rintro rfl
          rw [Walk.getVert_length] at hi
          exact hzu hi.symm
        have hA : G.Adj z (q.getVert (i - 1)) := by
          have := q.adj_getVert_succ (i := i - 1) (by omega)
          rw [show i - 1 + 1 = i by omega, hi] at this
          exact this.symm
        have hB : G.Adj z (q.getVert (i + 1)) := by
          have := q.adj_getVert_succ (i := i) (by omega)
          rw [hi] at this
          exact this
        have hC : G.Adj z (q.getVert 0) := by
          rw [Walk.getVert_zero]
          exact hxz.symm
        exact two_three hz hA hB hC (gv_ne hq.path (by omega) (by omega) (by omega))
          (gv_ne hq.path (by omega) (by omega) (by omega))
          (gv_ne hq.path (by omega) (by omega) (by omega))
      · have hg : Good G u z (Walk.cons hxz.symm q) := by
          refine ⟨(Walk.cons_isPath_iff _ _).2 ⟨hq.path, hzs⟩, by simp, fun i hi => ?_⟩
          rcases i with _ | j
          · simpa using hz
          · rw [Walk.getVert_cons_succ]
            simp only [Walk.length_cons] at hi
            exact hq.two j (by omega)
        have := hmax z _ hg
        simp only [Walk.length_cons] at this
        omega
    · rcases hbr with hu | hno
      · have := hL.2 z u hzu hz hu (Walk.cons hxz.symm q)
        simp only [Walk.length_cons] at this
        omega
      · exact hno z hz
    · have hax : x = a := ha x hxz.symm
      exact h1 ⟨z, x, q.getVert 1, hxz.symm, fun w hw => (ha w hw).trans hax.symm,
        fun w hw => ((hxN w).1 hw).symm⟩

/-- Six vertices of a thread of length at least six form a run. -/
theorem run_of_thread {G : SimpleGraph (Fin n)} {x u : Fin n} {q : G.Walk x u}
    (hq : Good G u x q) (h6 : 6 ≤ q.length) : ∃ a' a s t b b', Run G a' a s t b b' := by
  have adj : ∀ j, j < 6 → G.Adj (q.getVert j) (q.getVert (j + 1)) :=
    fun j hj => q.adj_getVert_succ (by omega)
  have ne : ∀ i j, i ≤ 6 → j ≤ 6 → i ≠ j → q.getVert i ≠ q.getVert j :=
    fun i j hi hj hij => gv_ne hq.path (by omega) (by omega) hij
  have two : ∀ j, j ≤ 5 → Two G (q.getVert j) := fun j hj => hq.two j (by omega)
  refine ⟨q.getVert 0, q.getVert 1, q.getVert 2, q.getVert 3, q.getVert 4, q.getVert 5,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    refine ⟨⟨ne 0 1 ?_ ?_ ?_, ne 0 2 ?_ ?_ ?_, ne 0 3 ?_ ?_ ?_, ne 0 4 ?_ ?_ ?_, ne 0 5 ?_ ?_ ?_⟩,
      ⟨ne 1 2 ?_ ?_ ?_, ne 1 3 ?_ ?_ ?_, ne 1 4 ?_ ?_ ?_, ne 1 5 ?_ ?_ ?_⟩,
      ⟨ne 2 3 ?_ ?_ ?_, ne 2 4 ?_ ?_ ?_, ne 2 5 ?_ ?_ ?_⟩,
      ⟨ne 3 4 ?_ ?_ ?_, ne 3 5 ?_ ?_ ?_⟩, ⟨ne 4 5 ?_ ?_ ?_, fun h => h⟩⟩ <;> omega
  · exact two_adj (two 1 (by omega)) (adj 0 (by omega)).symm (adj 1 (by omega))
      (ne 0 2 (by omega) (by omega) (by omega))
  · exact two_adj (two 2 (by omega)) (adj 1 (by omega)).symm (adj 2 (by omega))
      (ne 1 3 (by omega) (by omega) (by omega))
  · exact two_adj (two 3 (by omega)) (adj 2 (by omega)).symm (adj 3 (by omega))
      (ne 2 4 (by omega) (by omega) (by omega))
  · exact two_adj (two 4 (by omega)) (adj 3 (by omega)).symm (adj 4 (by omega))
      (ne 3 5 (by omega) (by omega) (by omega))
  · obtain ⟨c, -, -, hc⟩ := two_other (two 0 (by omega)) (adj 0 (by omega))
    exact ⟨c, fun w hw => (hc w).1 hw⟩
  · obtain ⟨c, -, -, hc⟩ := two_other (two 5 (by omega)) (adj 4 (by omega)).symm
    exact ⟨c, fun w hw => (hc w).1 hw⟩

theorem PClosure_proof : PClosure := by
  intro n G G' hL hle
  refine ⟨fun v p hp => ?_, fun u v huv hu hv p => ?_⟩
  · have := hL.1 v (p.mapLe hle) (hp.mapLe hle)
    rwa [Walk.length_mapLe] at this
  · have hsub : ∀ w, G'.neighborSet w ⊆ G.neighborSet w := fun w y hy => hle hy
    have := hL.2 u v huv (le_trans hu (Set.ncard_le_ncard (hsub u)))
      (le_trans hv (Set.ncard_le_ncard (hsub v))) (p.mapLe hle)
    rwa [Walk.length_mapLe] at this

theorem PStructure_proof : PStructure := by
  intro n G hL ⟨i, j, hij⟩ h1 h2
  by_cases hb : ∃ u, 3 ≤ (G.neighborSet u).ncard
  · obtain ⟨u, hu⟩ := hb
    obtain ⟨m1, m2, -, hm1, hm2, -, hm12, -, -⟩ :=
      (Set.two_lt_ncard_iff (s := G.neighborSet u)).1 (by omega)
    have hm1 : G.Adj u m1 := hm1
    have hm2 : G.Adj u m2 := hm2
    -- a neighbour of `u` is a leaf or has exactly two neighbours
    have cl : ∀ m, G.Adj u m → Two G m ∨ ∀ w, G.Adj m w → w = u := by
      intro m hm
      rcases classify G m with h | h | ⟨a, ha⟩
      · exact Or.inl h
      · have := hL.2 u m hm.ne hu h (Walk.cons hm Walk.nil)
        simp at this
      · have hau : u = a := ha u hm.symm
        exact Or.inr fun w hw => (ha w hw).trans hau.symm
    have hv : ∃ v, G.Adj u v ∧ Two G v := by
      rcases cl m1 hm1 with h | h
      · exact ⟨m1, hm1, h⟩
      rcases cl m2 hm2 with h' | h'
      · exact ⟨m2, hm2, h'⟩
      exact absurd ⟨m1, u, m2, hm1.symm, h, hm2, hm12.symm, h'⟩ h2
    obtain ⟨v, huv, hv⟩ := hv
    obtain ⟨x, q, hq, h6⟩ := thread G hL h1 u v huv.symm hv (Or.inl hu)
    exact run_of_thread hq h6
  · push_neg at hb
    have nb : ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard := fun w h => by have := hb w; omega
    have go : ∀ u v, G.Adj v u → Two G v → ∃ a' a s t b b', Run G a' a s t b b' := by
      intro u v hvu hv
      obtain ⟨x, q, hq, h6⟩ := thread G hL h1 u v hvu hv (Or.inr nb)
      exact run_of_thread hq h6
    rcases classify G j with hj | hj | ⟨a, ha⟩
    · exact go i j hij.symm hj
    · exact absurd hj (nb j)
    rcases classify G i with hi | hi | ⟨b, hb'⟩
    · exact go j i hij hi
    · exact absurd hi (nb i)
    have hai : i = a := ha i hij.symm
    exact absurd ⟨i, j, i, hij, fun w hw => (hb' w hw).trans (hb' j hij).symm,
      fun w hw => Or.inl ((ha w hw).trans hai.symm)⟩ h1

end PEqualNP.MetaComplexity.Loc.Struct
