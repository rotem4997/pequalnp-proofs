import PEqualNP.MetaComplexity.Helpers.ForestBound

/-!
# Local class, graph layer: the class, covers, the potential, deep vertices, runs

Shared definitions of the last-gate line on graphs with long threads (`L-meta-115` and the
full-basis bound on the same graphs). Proofs only use them; no statement of a row does. The
function is `Forest.F G A` of `ForestBound.lean` (some input of `A` is true, or both ends of
some edge are true) and covers are `Forest.Cov`. The arity is fixed: a restriction deletes
edges (`delV`), never vertices.
-/

namespace PEqualNP.MetaComplexity.Loc

open SimpleGraph
open PEqualNP.MetaComplexity.Helpers.Forest

/-- The graph with every edge that has an end in `X` deleted. -/
def delV {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) :=
  G.deleteEdges {e | ∃ v ∈ X, v ∈ e}

theorem delV_adj {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i j : Fin n) :
    (delV G X).Adj i j ↔ G.Adj i j ∧ i ∉ X ∧ j ∉ X := by
  unfold delV
  rw [deleteEdges_adj]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, fun hi => hn ⟨i, hi, Sym2.mem_mk_left _ _⟩, fun hj => hn ⟨j, hj, Sym2.mem_mk_right _ _⟩⟩
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, ?_⟩
    rintro ⟨v, hv, hmem⟩
    rcases Sym2.mem_iff.1 hmem with rfl | rfl
    · exact hi hv
    · exact hj hv

theorem delV_le {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : delV G X ≤ G :=
  deleteEdges_le _

/-- The least size of a vertex cover. -/
noncomputable def tau {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ T : Finset (Fin n), Cov G T ∧ T.card = k}

theorem tau_attained {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n), Cov G T ∧ T.card = tau G :=
  Nat.sInf_mem (s := {k | ∃ T : Finset (Fin n), Cov G T ∧ T.card = k})
    ⟨_, Finset.univ, fun i _ _ => Or.inl (Finset.mem_univ i), rfl⟩

theorem tau_le {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (h : Cov G T) :
    tau G ≤ T.card :=
  Nat.sInf_le ⟨T, h, rfl⟩

/-- The potential plus one: free OR-inputs, plus edges, plus the least cover size. The bound is
`Phi1 G A ≤ size + 1`; no subtraction anywhere. -/
noncomputable def Phi1 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  A.card + G.edgeSet.ncard + tau G

/-- No edge has an end in `A`. -/
def AFree {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∉ A

/-- The class: every cycle has length at least 9, and two distinct vertices with at least three
neighbours each are joined by no walk of length below 7. -/
def InL {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) ∧
    ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length

/-- A deep vertex: exactly two neighbours `u1 ≠ u2`, each with at most one further neighbour,
and some edge avoids `v`. -/
def Deep {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ u1 u2 c1 c2 : Fin n, u1 ≠ u2 ∧ (∀ w, G.Adj v w ↔ w = u1 ∨ w = u2) ∧
    (∀ w, G.Adj u1 w → w = v ∨ w = c1) ∧ (∀ w, G.Adj u2 w → w = v ∨ w = c2) ∧
    ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v

/-- A run of six: distinct vertices `a' - a - s - t - b - b'` where `a, s, t, b` have exactly the
two neighbours on the run and `a'`, `b'` have at most one neighbour off it. -/
structure Run {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) : Prop where
  nd : [a', a, s, t, b, b'].Nodup
  ha : ∀ w, G.Adj a w ↔ w = a' ∨ w = s
  hs : ∀ w, G.Adj s w ↔ w = a ∨ w = t
  ht : ∀ w, G.Adj t w ↔ w = s ∨ w = b
  hb : ∀ w, G.Adj b w ↔ w = t ∨ w = b'
  ha' : ∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c
  hb' : ∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c

theorem Run.symm {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Run G b' b t s a a' where
  nd := by
    have := List.nodup_reverse.2 h.nd
    simpa using this
  ha := fun w => (h.hb w).trans Or.comm
  hs := fun w => (h.ht w).trans Or.comm
  ht := fun w => (h.hs w).trans Or.comm
  hb := fun w => (h.ha w).trans Or.comm
  ha' := h.hb'
  hb' := h.ha'

/-- In a run, `a` is deep. -/
theorem Run.deep_a {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G a := by
  have nd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨c, hc⟩ := h.ha'
  refine ⟨a', s, c, t, nd.1.2.1, h.ha, hc, fun w hw => (h.hs w).1 hw, s, t, (h.hs t).2 (Or.inr rfl), ?_, ?_⟩
  · exact fun e => nd.2.1.1 e.symm
  · exact fun e => nd.2.1.2.1 e.symm

/-- In a run, `s` is deep. -/
theorem Run.deep_s {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G s := by
  have nd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  refine ⟨a, t, a', b, nd.2.1.2.1, h.hs, fun w hw => ((h.ha w).1 hw).symm,
    fun w hw => (h.ht w).1 hw, t, b, (h.ht b).2 (Or.inr rfl), ?_, ?_⟩
  · exact fun e => nd.2.2.1.1 e.symm
  · exact fun e => nd.2.2.1.2.1 e.symm

theorem Run.deep_t {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G t := h.symm.deep_s

theorem Run.deep_b {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G b := h.symm.deep_a

/-- The bound for a size notion `Sz`: every size of `F G A` is at least `Phi1 G A - 1`. -/
def BoundOf {n : ℕ} (Sz : ((Fin n → Bool) → Bool) → ℕ → Prop) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Prop :=
  ∀ s : ℕ, Sz (F G A) s → Phi1 G A ≤ s + 1

end PEqualNP.MetaComplexity.Loc
