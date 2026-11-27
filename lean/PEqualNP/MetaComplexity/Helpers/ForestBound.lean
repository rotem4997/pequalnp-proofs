import PEqualNP.MetaComplexity.Helpers.ForestElim
import PEqualNP.MetaComplexity.Helpers.ForestGraph

/-!
# The edge function of a forest with free OR-inputs

Helper for `L-meta-104` (proofs only, no statement may use it). For a graph `G` on `Fin n` and
a set `A` of inputs, `F G A x` is true when some input of `A` is true or both ends of some edge
are true. Claim `Q`: if `G` is acyclic, no edge has an end in `A`, every vertex cover of `G`
has at least `k` vertices and `F G A` is not constant, then every circuit has at least
`|A| + |E| + k - 1` gates. Induction on the number of edges, at a good leaf of
`forest_good_leaf`: fixing the leaf `l` to false deletes the edge `lp`; fixing it to true
turns `p` into a free OR-input and deletes the edges at `p`.
-/

namespace PEqualNP.MetaComplexity.Helpers.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.PermInputs
open SimpleGraph

/-- The class: some input of `A` is true, or both ends of some edge are true. -/
noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

theorem F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

theorem F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

theorem F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp

/-- `F` depends on an end `u` of an edge `uv` with `v ∉ A`. -/
theorem F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

/-- `F` depends on every input of `A`. -/
theorem F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

/-- Fixing a leaf `l` (neighbour `p`, `l ∉ A`) to false deletes the edge `lp`. -/
theorem restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

/-- Fixing a leaf `l` (neighbour `p`, every neighbour of `p` is `l` or `q`) to true makes `p`
a free OR-input and deletes the edges at `p`. -/
theorem restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  -- edges of the smaller graph avoid `p` and `l`
  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

/-- Vertex covers. -/
def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

theorem cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

/-- Case of two leaves `l ≠ l'` at `p`: covers of `G` minus `lp` are as large as covers of `G`. -/
theorem cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega

theorem ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)

theorem ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

theorem noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

theorem del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

/-- Claim `Q`. -/
theorem claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push_neg at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push_neg at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push_neg at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

/-- The row: `Q` at `A = ∅`. -/
theorem forest_bound : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsAcyclic → (∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s →
    G.edgeFinset.card + k ≤ s + 1 := by
  intro n k s G _ hac hE hk hC
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  rw [hf] at hC
  have := claimQ _ n G ∅ k s rfl hac (by simp) (fun T hT => hk T hT) (Or.inr hE) hC
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [Finset.card_empty] at this
  omega

end PEqualNP.MetaComplexity.Helpers.Forest
