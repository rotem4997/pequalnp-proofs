import PEqualNP.Search.Helpers.Graph

/-!
# Helpers: the split grid, a graph of degree at most 3 that keeps a big component

For every `s` there is a graph with all degrees at most 3 such that deleting any `s` edges
leaves a component with more than half of the vertices. The graph is the split grid: vertices
`a(i,j)` and `b(i,j)` for `i, j < M`, row edges `a(i,j) - a(i,j+1)` (cyclic in `j`), column edges
`b(i,j) - b(i+1,j)` (cyclic in `i`), and link edges `a(i,j) - b(i,j)`. We take `M = 3 s + 2`.
-/

namespace PEqualNP.Search.Helpers

variable {m n : ℕ}

theorem EdgeGraph.reach_symm (G : EdgeGraph m n) (S : Finset (Fin n)) {u w : Fin m}
    (h : G.Reach S u w) : G.Reach S w u := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨e, he, h'⟩ := hab
    exact .head ⟨e, he, h'.symm⟩ ih

/-- An edge graph built from structured vertex and edge types, relabelled by equivalences. -/
def EdgeGraph.ofEquiv {V E : Type*} (eV : V ≃ Fin m) (eE : E ≃ Fin n) (f : E → V × V)
    (hf : ∀ e, (f e).1 ≠ (f e).2) : EdgeGraph m n where
  ends e := (eV (f (eE.symm e)).1, eV (f (eE.symm e)).2)
  loopless _ h := hf _ (eV.injective h)

theorem EdgeGraph.ofEquiv_reach_of_edge {V E : Type*} (eV : V ≃ Fin m) (eE : E ≃ Fin n)
    (f : E → V × V) (hf : ∀ e, (f e).1 ≠ (f e).2) {S : Finset (Fin n)} {e : E}
    (he : eE e ∉ S) {x y : V} (hxy : f e = (x, y)) :
    (EdgeGraph.ofEquiv eV eE f hf).Reach S (eV x) (eV y) :=
  Relation.ReflTransGen.single ⟨eE e, he, Or.inl (by simp [EdgeGraph.ofEquiv, hxy])⟩

theorem EdgeGraph.ofEquiv_incident_card {V E : Type*} [Fintype E] [DecidableEq V]
    (eV : V ≃ Fin m) (eE : E ≃ Fin n) (f : E → V × V) (hf : ∀ e, (f e).1 ≠ (f e).2)
    (v : Fin m) :
    ((EdgeGraph.ofEquiv eV eE f hf).incident v).card ≤
      (Finset.univ.filter fun e => (f e).1 = eV.symm v ∨ (f e).2 = eV.symm v).card := by
  rw [← Finset.card_map eE.toEmbedding]
  apply Finset.card_le_card
  intro e he
  rw [EdgeGraph.incident, Finset.mem_filter] at he
  rw [Finset.mem_map_equiv]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases he.2 with h | h
  · left; rw [← h]; simp [EdgeGraph.ofEquiv]
  · right; rw [← h]; simp [EdgeGraph.ofEquiv]

namespace SplitGrid

variable (N : ℕ)

/-- Vertices: `inl (i,j)` is `a(i,j)`, `inr (i,j)` is `b(i,j)`. -/
abbrev V := (Fin (N + 2) × Fin (N + 2)) ⊕ (Fin (N + 2) × Fin (N + 2))

/-- Edges: row edges, column edges, link edges. -/
abbrev E := (Fin (N + 2) × Fin (N + 2)) ⊕ (Fin (N + 2) × Fin (N + 2)) ⊕
  (Fin (N + 2) × Fin (N + 2))

/-- The two ends of each edge. -/
def ends : E N → V N × V N
  | .inl (i, j) => (.inl (i, j), .inl (i, j + 1))
  | .inr (.inl (i, j)) => (.inr (i, j), .inr (i + 1, j))
  | .inr (.inr (i, j)) => (.inl (i, j), .inr (i, j))

/-- The row index of an edge. -/
def row : E N → Fin (N + 2)
  | .inl p => p.1
  | .inr (.inl p) => p.1
  | .inr (.inr p) => p.1

/-- The column index of an edge. -/
def col : E N → Fin (N + 2)
  | .inl p => p.2
  | .inr (.inl p) => p.2
  | .inr (.inr p) => p.2

theorem loopless (e : E N) : (ends N e).1 ≠ (ends N e).2 := by
  rcases e with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩ <;> simp [ends]

/-- The split grid as an edge graph. -/
noncomputable def G : EdgeGraph (Fintype.card (V N)) (Fintype.card (E N)) :=
  EdgeGraph.ofEquiv (Fintype.equivFin _) (Fintype.equivFin _) (ends N) (loopless N)

/-- Every vertex of the split grid meets at most 3 edges. -/
theorem deg_le (x : V N) :
    (Finset.univ.filter fun e => (ends N e).1 = x ∨ (ends N e).2 = x).card ≤ 3 := by
  rcases x with ⟨i, j⟩ | ⟨i, j⟩
  · refine (Finset.card_le_card (t := {.inl (i, j), .inl (i, j - 1), .inr (.inr (i, j))})
      ?_).trans Finset.card_le_three
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases e with ⟨i', j'⟩ | ⟨i', j'⟩ | ⟨i', j'⟩ <;> simp [ends] at he ⊢
    · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · simp
    · exact he
  · refine (Finset.card_le_card (t := {.inr (.inl (i, j)), .inr (.inl (i - 1, j)),
      .inr (.inr (i, j))}) ?_).trans Finset.card_le_three
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases e with ⟨i', j'⟩ | ⟨i', j'⟩ | ⟨i', j'⟩ <;> simp [ends] at he ⊢
    · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · simp
    · exact he

theorem line {R : V N → V N → Prop} (hR : ∀ {x y z}, R x y → R y z → R x z) (hrefl : ∀ x, R x x)
    (P : Fin (N + 2) → V N) (h : ∀ j, R (P j) (P (j + 1))) (j : Fin (N + 2)) :
    R (P 0) (P j) := by
  induction j using Fin.induction with
  | zero => exact hrefl _
  | succ j ih =>
    rw [← Fin.coeSucc_eq_succ]
    exact hR ih (h _)

theorem bigComp (s : ℕ) (hN : 3 * s ≤ N) (S : Finset (Fin (Fintype.card (E N))))
    (hS : S.card ≤ s) : ∃ v, (G N).BigComp S v := by
  classical
  set eV := Fintype.equivFin (V N)
  set eE := Fintype.equivFin (E N)
  set S' : Finset (E N) := S.map eE.symm.toEmbedding with hS'
  have hS'card : S'.card ≤ s := by rw [hS', Finset.card_map]; exact hS
  set Br := S'.image (row N)
  set Bc := S'.image (col N)
  have hBr : Br.card ≤ s := Finset.card_image_le.trans hS'card
  have hBc : Bc.card ≤ s := Finset.card_image_le.trans hS'card
  have hrow : ∀ e, row N e ∉ Br → eE e ∉ S := by
    intro e h hS
    apply h
    exact Finset.mem_image_of_mem _ (Finset.mem_map_equiv.2 (by simpa using hS))
  have hcol : ∀ e, col N e ∉ Bc → eE e ∉ S := by
    intro e h hS
    apply h
    exact Finset.mem_image_of_mem _ (Finset.mem_map_equiv.2 (by simpa using hS))
  have hex : ∀ B : Finset (Fin (N + 2)), B.card ≤ s → ∃ i, i ∉ B := by
    intro B hB
    by_contra h
    push Not at h
    have : B = Finset.univ := Finset.eq_univ_iff_forall.2 h
    rw [this, Finset.card_univ, Fintype.card_fin] at hB
    omega
  obtain ⟨i0, hi0⟩ := hex Br hBr
  obtain ⟨j0, hj0⟩ := hex Bc hBc
  -- reachability between structured vertices
  let R : V N → V N → Prop := fun x y => (G N).Reach S (eV x) (eV y)
  have hT : ∀ {x y z}, R x y → R y z → R x z := fun h1 h2 => Relation.ReflTransGen.trans h1 h2
  have hrefl : ∀ x, R x x := fun _ => Relation.ReflTransGen.refl
  have hsymm : ∀ x y, R x y → R y x := fun _ _ h => (G N).reach_symm S h
  have hedge : ∀ e x y, eE e ∉ S → ends N e = (x, y) → R x y := fun e x y he hxy =>
    EdgeGraph.ofEquiv_reach_of_edge eV eE (ends N) (loopless N) he hxy
  -- intact rows and columns
  have hrowline : ∀ i, i ∉ Br → ∀ j, R (.inl (i, 0)) (.inl (i, j)) := fun i hi =>
    line N (R := R) hT hrefl (fun j => .inl (i, j)) (fun j => hedge (.inl (i, j)) (.inl (i, j)) (.inl (i, j + 1)) (hrow _ hi) rfl)
  have hcolline : ∀ j, j ∉ Bc → ∀ i, R (.inr (0, j)) (.inr (i, j)) := fun j hj =>
    line N (R := R) hT hrefl (fun i => .inr (i, j))
      (fun i => hedge (.inr (.inl (i, j))) (.inr (i, j)) (.inr (i + 1, j)) (hcol _ hj) rfl)
  have hlink : ∀ i j, i ∉ Br → R (.inl (i, j)) (.inr (i, j)) := fun i j hi =>
    hedge (.inr (.inr (i, j))) (.inl (i, j)) (.inr (i, j)) (hrow _ hi) rfl
  -- every vertex of an intact row or column is reachable from `a(i0, 0)`
  have hreachA : ∀ i j, i ∉ Br → R (.inl (i0, 0)) (.inl (i, j)) := by
    intro i j hi
    have h1 := hrowline i0 hi0 j0
    have h2 := hlink i0 j0 hi0
    have h3 := hsymm _ _ (hcolline j0 hj0 i0)
    have h4 := hcolline j0 hj0 i
    have h5 := hsymm _ _ (hlink i j0 hi)
    have h6 := hsymm _ _ (hrowline i hi j0)
    have h7 := hrowline i hi j
    exact hT h1 (hT h2 (hT h3 (hT h4 (hT h5 (hT h6 h7)))))
  have hreachB : ∀ i j, j ∉ Bc → R (.inl (i0, 0)) (.inr (i, j)) := by
    intro i j hj
    have h1 := hrowline i0 hi0 j
    have h2 := hlink i0 j hi0
    have h3 := hsymm _ _ (hcolline j hj i0)
    have h4 := hcolline j hj i
    exact hT h1 (hT h2 (hT h3 h4))
  refine ⟨eV (.inl (i0, 0)), ?_⟩
  unfold EdgeGraph.BigComp
  set Q : Finset (V N) := (Brᶜ ×ˢ Finset.univ).disjSum (Finset.univ ×ˢ Bcᶜ)
  have hsub : Q.map eV.toEmbedding ⊆
      Finset.univ.filter fun u => (G N).Reach S (eV (.inl (i0, 0))) u := by
    intro u hu
    rw [Finset.mem_map_equiv] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have key : R (.inl (i0, 0)) (eV.symm u) := by
      rcases hx : eV.symm u with ⟨i, j⟩ | ⟨i, j⟩ <;> rw [hx] at hu <;>
        simp [Q, Finset.mem_disjSum] at hu
      · exact hreachA i j hu
      · exact hreachB i j hu
    simpa [R] using key
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_disjSum, Finset.card_product, Finset.card_product,
    Finset.card_compl, Finset.card_compl, Finset.card_univ, Fintype.card_fin] at hcard
  have hm : Fintype.card (V N) = (N + 2) * (N + 2) + (N + 2) * (N + 2) := by simp
  have ha : N + 2 - s ≤ N + 2 - Br.card := by omega
  have hb : N + 2 - s ≤ N + 2 - Bc.card := by omega
  have hc1 := Nat.mul_le_mul_right (N + 2) ha
  have hc2 := Nat.mul_le_mul_left (N + 2) hb
  have hlt : (N + 2) * (N + 2) < 2 * (N + 2 - s) * (N + 2) :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  nlinarith

end SplitGrid

/-- For every `s` there is a graph with all degrees at most 3 in which deleting any `s` edges
leaves a component with more than half of the vertices. -/
theorem splitGrid_exists (s : ℕ) : ∃ (m n : ℕ) (G : EdgeGraph m n), 2 ≤ m ∧
    (∀ v, (G.incident v).card ≤ 3) ∧
    ∀ S : Finset (Fin n), S.card ≤ s → ∃ v, G.BigComp S v := by
  classical
  refine ⟨_, _, SplitGrid.G (3 * s), ?_, ?_, fun S hS => SplitGrid.bigComp (3 * s) s le_rfl S hS⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  · intro v
    exact (EdgeGraph.ofEquiv_incident_card _ _ _ _ v).trans (SplitGrid.deg_le _ _)

end PEqualNP.Search.Helpers
