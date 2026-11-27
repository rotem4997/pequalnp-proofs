import PEqualNP.Search.Helpers.Duplicator
import PEqualNP.Search.Helpers.Graph

/-!
# Helpers: Tseitin formulas on graphs with numbered edges

Used by the refutation of `L-alg-002`. The Tseitin formula of a graph with charge 1 at one
vertex `v0` and 0 elsewhere says that at each vertex the number of true edges is odd exactly at
`v0`. It is unsatisfiable (each true edge is counted at both of its ends), its clauses have at
most 3 literals when every vertex has degree at most 3, and Duplicator has a strategy in the
pebble game on it whenever deleting few edges always leaves a component with more than half of
the vertices.
-/

namespace PEqualNP.Search.Helpers



variable {m n : ℕ}

/-- The clause of vertex `v` forbidding exactly the assignment that sets the edges of `T` true
and the other edges at `v` false. -/
def tseitinClause (G : EdgeGraph m n) (v : Fin m) (T : Finset (Fin n)) :
    PEqualNP.ProofComplexity.Clause (Fin n) :=
  (G.incident v).image fun e => (e, decide (e ∉ T))

open Classical in
/-- The Tseitin formula of `G` with charge 1 at `v0` and 0 elsewhere: at each vertex `v`, the
number of true edges at `v` is odd exactly when `v = v0`. -/
def tseitin (G : EdgeGraph m n) (v0 : Fin m) : Finset (PEqualNP.ProofComplexity.Clause (Fin n)) :=
  Finset.univ.biUnion fun v =>
    ((G.incident v).powerset.filter fun T => (T.card % 2 = 1) ≠ (v = v0)).image (tseitinClause G v)

theorem mem_tseitin {G : EdgeGraph m n} {v0 : Fin m} {C : PEqualNP.ProofComplexity.Clause (Fin n)} :
    C ∈ tseitin G v0 ↔
      ∃ v T, T ⊆ G.incident v ∧ ((T.card % 2 = 1) ≠ (v = v0)) ∧ tseitinClause G v T = C := by
  simp [tseitin, and_assoc]

theorem tseitin_width (G : EdgeGraph m n) (v0 : Fin m) (h : ∀ v, (G.incident v).card ≤ 3) :
    ∀ C ∈ tseitin G v0, C.card ≤ 3 := by
  intro C hC
  obtain ⟨v, T, -, -, rfl⟩ := mem_tseitin.1 hC
  exact Finset.card_image_le.trans (h v)

/-- The number of edges at `v` set true by `a`. -/
def tcount (G : EdgeGraph m n) (a : Fin n → Bool) (v : Fin m) : ℕ :=
  ((G.incident v).filter fun e => a e = true).card

/-- An assignment satisfies the clause of `v` and `T` unless its true edges at `v` are exactly
`T`. -/
theorem clauseSat_tseitinClause {G : EdgeGraph m n} {v : Fin m} {T : Finset (Fin n)}
    (hT : T ⊆ G.incident v) (a : Fin n → Bool) :
    PEqualNP.ProofComplexity.ClauseSat a (tseitinClause G v T) ↔ (G.incident v).filter (fun e => a e = true) ≠ T := by
  constructor
  · rintro ⟨l, hl, hal⟩ heq
    simp only [tseitinClause, Finset.mem_image] at hl
    obtain ⟨e, he, rfl⟩ := hl
    have : e ∈ (G.incident v).filter (fun e => a e = true) ↔ e ∈ T := by rw [heq]
    simp only [Finset.mem_filter, he, true_and] at this
    cases h : a e <;> simp_all
  · intro hne
    by_contra hns
    apply hne
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hae⟩
      by_contra heT
      exact hns ⟨(e, decide (e ∉ T)), Finset.mem_image_of_mem _ he, by simp [hae, heT]⟩
    · intro heT
      refine ⟨hT heT, ?_⟩
      by_contra hae
      exact hns ⟨(e, decide (e ∉ T)), Finset.mem_image_of_mem _ (hT heT), by simpa [heT] using hae⟩

/-- A satisfying assignment has an odd number of true edges exactly at `v0`. -/
theorem tcount_of_satisfies {G : EdgeGraph m n} {v0 : Fin m} {a : Fin n → Bool}
    (ha : PEqualNP.ProofComplexity.Satisfies a (↑(tseitin G v0) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) (v : Fin m) :
    (tcount G a v % 2 = 1 ↔ v = v0) := by
  by_contra hne
  have hsub : (G.incident v).filter (fun e => a e = true) ⊆ G.incident v := Finset.filter_subset _ _
  have hmem : tseitinClause G v ((G.incident v).filter (fun e => a e = true)) ∈ tseitin G v0 :=
    mem_tseitin.2 ⟨v, _, hsub, fun h => hne (by unfold tcount; rw [h]), rfl⟩
  exact (clauseSat_tseitinClause hsub a).1 (ha _ hmem) rfl

theorem card_ends (G : EdgeGraph m n) (e : Fin n) :
    (Finset.univ.filter fun v => (G.ends e).1 = v ∨ (G.ends e).2 = v).card = 2 := by
  have : (Finset.univ.filter fun v => (G.ends e).1 = v ∨ (G.ends e).2 = v) =
      {(G.ends e).1, (G.ends e).2} := by
    ext v; simp [eq_comm]
  rw [this, Finset.card_pair (G.loopless e)]

theorem sum_tcount (G : EdgeGraph m n) (a : Fin n → Bool) :
    ∑ v, tcount G a v = 2 * (Finset.univ.filter fun e => a e = true).card := by
  unfold tcount EdgeGraph.incident
  simp only [Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hae : a e = true
  · simp only [hae, and_true]
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, card_ends]
    simp
  · simp [hae]

theorem tseitin_unsat (G : EdgeGraph m n) (v0 : Fin m) :
    ¬ PEqualNP.ProofComplexity.Satisfiable
      (↑(tseitin G v0) : Set (PEqualNP.ProofComplexity.Clause (Fin n))) := by
  rintro ⟨a, ha⟩
  have h1 : (∑ v, tcount G a v) % 2 = 1 := by
    rw [Finset.sum_nat_mod]
    have : ∀ v, tcount G a v % 2 = if v = v0 then 1 else 0 := by
      intro v
      have := tcount_of_satisfies ha v
      split_ifs with hv <;> omega
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum_tcount] at h1
  omega

/-! ### The Duplicator strategy -/

/-- The assignment `a` breaks the charge condition of the Tseitin formula at `u`. -/
def Bad (G : EdgeGraph m n) (v0 : Fin m) (a : Fin n → Bool) (u : Fin m) : Prop :=
  ¬ (tcount G a u % 2 = 1 ↔ u = v0)

/-- Flipping an edge not at `u` keeps the count at `u`. -/
theorem tcount_flip_of_not_mem {G : EdgeGraph m n} {a : Fin n → Bool} {e : Fin n} {u : Fin m}
    (h : e ∉ G.incident u) : tcount G (Function.update a e (!a e)) u = tcount G a u := by
  unfold tcount
  congr 1
  apply Finset.filter_congr
  intro x hx
  have : x ≠ e := by rintro rfl; exact h hx
  rw [Function.update_of_ne this]

/-- Flipping an edge at `u` changes the parity of the count at `u`. -/
theorem tcount_flip_of_mem {G : EdgeGraph m n} {a : Fin n → Bool} {e : Fin n} {u : Fin m}
    (h : e ∈ G.incident u) :
    (tcount G (Function.update a e (!a e)) u % 2 = 1 ↔ ¬ tcount G a u % 2 = 1) := by
  unfold tcount
  set A := (G.incident u).filter fun x => a x = true
  set B := (G.incident u).filter fun x => Function.update a e (!a e) x = true
  have hAB : A.erase e = B.erase e := by
    ext x
    by_cases hx : x = e
    · subst hx; simp
    · simp [A, B, hx]
  cases hae : a e
  · have heA : e ∉ A := by simp [A, hae]
    have heB : e ∈ B := by simp [B, h, hae]
    have h1 := Finset.card_erase_add_one heB
    rw [← hAB, Finset.erase_eq_of_notMem heA] at h1
    omega
  · have heA : e ∈ A := by simp [A, h, hae]
    have heB : e ∉ B := by simp [B, hae]
    have h1 := Finset.card_erase_add_one heA
    rw [hAB, Finset.erase_eq_of_notMem heB] at h1
    omega

/-- Moving the violation along a path avoiding `S`, without changing the edges of `S`. -/
theorem move_violation {G : EdgeGraph m n} {v0 : Fin m} {S : Finset (Fin n)} {w v' : Fin m}
    (hr : G.Reach S w v') (a : Fin n → Bool) (ha : ∀ u, Bad G v0 a u ↔ u = w) :
    ∃ a' : Fin n → Bool, (∀ e ∈ S, a' e = a e) ∧ ∀ u, Bad G v0 a' u ↔ u = v' := by
  induction hr with
  | refl => exact ⟨a, fun _ _ => rfl, ha⟩
  | @tail x y _ hxy ih =>
    obtain ⟨a', ha'S, ha'⟩ := ih
    obtain ⟨e, heS, hends⟩ := hxy
    refine ⟨Function.update a' e (!a' e), fun f hf => ?_, fun u => ?_⟩
    · rw [Function.update_of_ne (by rintro rfl; exact heS hf)]
      exact ha'S f hf
    · have hxy : x ≠ y := by
        have := G.loopless e
        rcases hends with h | h <;> rw [h] at this <;> simp at this <;> grind
      have hinc : e ∈ G.incident u ↔ u = x ∨ u = y := by
        rcases hends with h | h <;> simp [EdgeGraph.incident, h, eq_comm, or_comm]
      have hu := ha' u
      by_cases hue : e ∈ G.incident u
      · have := tcount_flip_of_mem (a := a') hue
        unfold Bad at hu ⊢
        rcases hinc.1 hue with rfl | rfl
        · simp only [hxy, iff_false] at hu ⊢
          tauto
        · simp only [Ne.symm hxy, iff_false, iff_true] at hu ⊢
          tauto
      · have := tcount_flip_of_not_mem (a := a') hue
        unfold Bad at hu ⊢
        rw [this, hu]
        rw [hinc] at hue
        tauto

theorem adj_mono {G : EdgeGraph m n} {S S' : Finset (Fin n)} (h : S' ⊆ S) {u w : Fin m}
    (hadj : G.Adj S u w) : G.Adj S' u w := by
  obtain ⟨e, he, h2⟩ := hadj
  exact ⟨e, fun h' => he (h h'), h2⟩

theorem reach_mono {G : EdgeGraph m n} {S S' : Finset (Fin n)} (h : S' ⊆ S) {u w : Fin m}
    (hr : G.Reach S u w) : G.Reach S' u w := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih => exact ih.tail (adj_mono h hxy)

theorem reach_symm {G : EdgeGraph m n} {S : Finset (Fin n)} {u w : Fin m}
    (hr : G.Reach S u w) : G.Reach S w u := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
    obtain ⟨e, he, h⟩ := hxy
    exact Relation.ReflTransGen.head ⟨e, he, h.symm⟩ ih

theorem bigComp_mono {G : EdgeGraph m n} {S S' : Finset (Fin n)} (h : S' ⊆ S) {w : Fin m}
    (hb : G.BigComp S w) : G.BigComp S' w := by
  unfold EdgeGraph.BigComp at *
  refine lt_of_lt_of_le hb (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact reach_mono h

/-- Two big components of the same graph meet. -/
theorem reach_of_bigComp {G : EdgeGraph m n} {S : Finset (Fin n)} {w v : Fin m}
    (hw : G.BigComp S w) (hv : G.BigComp S v) : G.Reach S w v := by
  classical
  unfold EdgeGraph.BigComp at hw hv
  obtain ⟨x, hx⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.filter_subset (fun u => G.Reach S w u) Finset.univ)
    (Finset.filter_subset (fun u => G.Reach S v u) Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1.trans (reach_symm hx.2)

/-- If every edge at `w` is deleted, only `w` is reachable from `w`. -/
theorem reach_isolated {G : EdgeGraph m n} {S : Finset (Fin n)} {w x : Fin m}
    (hS : G.incident w ⊆ S) (hr : G.Reach S w x) : x = w := by
  induction hr with
  | refl => rfl
  | @tail y z _ hyz ih =>
    subst ih
    obtain ⟨e, he, h⟩ := hyz
    exfalso
    apply he
    apply hS
    rcases h with h | h <;> simp [EdgeGraph.incident, h]

/-- The positions of a partial assignment where Duplicator keeps the game going: few literals,
an extension to a full assignment violating the charge condition at exactly one vertex `w`, and
`w` in a big component after deleting the assigned edges. -/
def tseitinH (G : EdgeGraph m n) (v0 : Fin m) (k : ℕ) :
    Set (Finset (PEqualNP.ProofComplexity.Literal (Fin n))) :=
  {ρ | ρ.card ≤ k + 1 ∧ ∃ (a : Fin n → Bool) (w : Fin m), (∀ p ∈ ρ, a p.1 = p.2) ∧
    (∀ u, Bad G v0 a u ↔ u = w) ∧ G.BigComp (ρ.image Prod.fst) w}

theorem tseitin_duplicator (G : EdgeGraph m n) (v0 : Fin m) (k : ℕ) (hm : 2 ≤ m)
    (hbig : ∀ S : Finset (Fin n), S.card ≤ k + 1 → ∃ v, G.BigComp S v)
    (h0 : G.BigComp ∅ v0) :
    Nonempty (DuplicatorStrategy
      (↑(tseitin G v0) : Set (PEqualNP.ProofComplexity.Clause (Fin n))) k) := by
  refine ⟨⟨tseitinH G v0 k, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro ρ ⟨-, a, w, ha, -⟩ v b h1 h2
    have e1 := ha (v, b) h1
    have e2 := ha (v, !b) h2
    simp only at e1 e2
    rw [e1] at e2
    cases b <;> simp at e2
  · refine ⟨by simp, fun _ => false, v0, by simp, fun u => ?_, by simpa using h0⟩
    simp [Bad, tcount]
  · rintro ρ ⟨hc, a, w, ha, hw, hb⟩ σ hσ
    exact ⟨(Finset.card_le_card hσ).trans hc, a, w, fun p hp => ha p (hσ hp), hw,
      bigComp_mono (Finset.image_subset_image hσ) hb⟩
  · rintro ρ ⟨-, a, w, ha, hw, hb⟩ hk e
    by_cases he : e ∈ ρ.image Prod.fst
    · obtain ⟨⟨e', b⟩, hp, rfl⟩ := Finset.mem_image.1 he
      refine ⟨b, ?_⟩
      rw [Finset.insert_eq_of_mem hp]
      exact ⟨by omega, a, w, ha, hw, hb⟩
    · have hcard : (insert e (ρ.image Prod.fst)).card ≤ k + 1 :=
        (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := ρ) (f := Prod.fst); omega)
      obtain ⟨v', hv'⟩ := hbig _ hcard
      have hr : G.Reach (ρ.image Prod.fst) w v' :=
        reach_of_bigComp hb (bigComp_mono (Finset.subset_insert _ _) hv')
      obtain ⟨a', ha'S, ha'⟩ := move_violation hr a hw
      refine ⟨a' e, ⟨(Finset.card_insert_le _ _).trans (by omega), a', v', ?_, ha', ?_⟩⟩
      · intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · rfl
        · rw [ha'S _ (Finset.mem_image_of_mem _ hp)]
          exact ha p hp
      · rwa [Finset.image_insert]
  · rintro ρ ⟨-, a, w, ha, hw, hb⟩ C hC hf
    obtain ⟨u, T, hT, hpar, rfl⟩ := mem_tseitin.1 hC
    have hval : ∀ e ∈ G.incident u, (e, decide (e ∈ T)) ∈ ρ := by
      intro e he
      have := hf _ (Finset.mem_image_of_mem _ he)
      simpa using this
    have hfil : (G.incident u).filter (fun e => a e = true) = T := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hae⟩
        have := ha _ (hval e he)
        simp only at this
        rw [hae] at this
        simpa using this.symm
      · intro heT
        refine ⟨hT heT, ?_⟩
        have := ha _ (hval e (hT heT))
        simpa [heT] using this
    have hbad : Bad G v0 a u := by
      unfold Bad tcount
      rw [hfil]
      intro h
      exact hpar (propext h)
    have huw : u = w := (hw u).1 hbad
    subst huw
    have hS : G.incident u ⊆ ρ.image Prod.fst := fun e he =>
      Finset.mem_image.2 ⟨_, hval e he, rfl⟩
    classical
    unfold EdgeGraph.BigComp at hb
    have : (Finset.univ.filter fun x => G.Reach (ρ.image Prod.fst) u x) ⊆ {u} := by
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact reach_isolated hS
    have := Finset.card_le_card this
    simp at this
    omega

end PEqualNP.Search.Helpers
