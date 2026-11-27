import PEqualNP.MetaComplexity.Helpers.ReductionPieces
import PEqualNP.MetaComplexity.L103
import PEqualNP.MetaComplexity.L204
import PEqualNP.MetaComplexity.L288
import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph
import PEqualNP.MetaComplexity.Helpers.RootOnlyBridge
import PEqualNP.MetaComplexity.L395
import PEqualNP.MetaComplexity.L398
import PEqualNP.MetaComplexity.L402

/-!
# G-FUN: the map of record is correct at the level of functions

Part 2 of the assembly of L-meta-444. From the placement rows (473, 474, 475, 478,
479, 489, 307 on the checked 103), the subdivision rows (285, 286, 290, 492 and the checked 288),
the circuit rows (395, 398, 402), the logic rows (376, 388 on the checked 204 and the checked
cover circuit of 221) and the gap G-OWN: an unsatisfiable formula goes to a YES instance, a
satisfiable one to a NO instance. Bridges B1 (cycle form), B2 (number of inputs, by `ring`),
B3 (edge count) and B4 (the three facts on the circuit) are written out below.
-/

namespace PEqualNP.MetaComplexity.Reduction

open PEqualNP.Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.CoverPromise
open PEqualNP.MetaComplexity.Helpers.OwnerLink (OWN REN)

/-! ## G-OWN, clause by clause (the form of the import map, section 4) -/

/-- G-OWN (1): the leading entries have no repetition. -/
def GOwn_c1 (ol : List (List ℕ)) : Prop := (ol.map (fun l : List ℕ => l.headD 0)).Nodup

/-- G-OWN (2): the set of leading entries is the forward cover F. -/
def GOwn_c2 {M : ℕ} (F : Finset (Fin M)) (ol : List (List ℕ)) : Prop :=
  ∀ j : Fin M, j ∈ F ↔ j.val ∈ ol.map (fun l : List ℕ => l.headD 0)

/-- G-OWN (3): no list shorter than 2. -/
def GOwn_c3 (ol : List (List ℕ)) : Prop := ∀ l ∈ ol, 2 ≤ l.length

/-- G-OWN (4): every entry is an input index. -/
def GOwn_c4 (M : ℕ) (ol : List (List ℕ)) : Prop := ∀ l ∈ ol, ∀ w ∈ l, w < M

/-- G-OWN (5): the owned pairs are exactly the edges of S. -/
def GOwn_c5 {M : ℕ} (S : SimpleGraph (Fin M)) (ol : List (List ℕ)) : Prop :=
  ∀ x y : Fin M, S.Adj x y ↔ ∃ l ∈ ol, (l.headD 0 = x.val ∧ y.val ∈ l.tail) ∨ (l.headD 0 = y.val ∧ x.val ∈ l.tail)

/-- G-OWN (6): the list lengths add up to the edge count (each edge once). -/
def GOwn_c6 {M : ℕ} (S : SimpleGraph (Fin M)) (ol : List (List ℕ)) : Prop :=
  (ol.map (fun l : List ℕ => l.tail.length)).sum = S.edgeSet.ncard

/-! G-OWN itself is the shared `OwnerLink.GOwn` of `Helpers/OwnerLinkDefs.lean` (the import map's
term, textually identical; its clauses (a), (b), (c) are `OwnerLink.GOwnA/B/C`). The six conjuncts
above are its conclusion, named for `fun_core`. -/

/-! ## Small facts -/

theorem asm_getD_ofFn {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem asm_headD_mem (l : List ℕ) (h : 2 ≤ l.length) : l.headD 0 ∈ l := by
  cases l with
  | nil => simp at h
  | cons a t => simp

/-! ## The core on the placed graph -/

theorem fun_core (h285 : Stmt285) (h286 : Stmt286) (h290 : Stmt290) (h376 : Stmt376)
    (h388 : Stmt388) (h492 : Stmt492)
    (m k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph (Fin m)) (TH : Finset (Fin m))
    (hTcov : ∀ u v : Fin m, H.Adj u v → u ∈ TH ∨ v ∈ TH) (hHe : ∃ a b : Fin m, H.Adj a b)
    (ol : List (List ℕ))
    (c1 : GOwn_c1 ol) (c2 : GOwn_c2 (fwdOf m k H TH) ol) (c3 : GOwn_c3 ol)
    (c4 : GOwn_c4 (m + 2 * k * m * m) ol) (c5 : GOwn_c5 (subdivOf m k H) ol)
    (c6 : GOwn_c6 (subdivOf m k H) ol) :
    ((∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → TH.card ≤ T.card) →
      LgpYes (m + 2 * k * m * m)
        (coverCircuitB (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail))))) ∧
    ((∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → TH.card ≤ T.card + 1) →
      (∃ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < TH.card) →
      LgpNo (m + 2 * k * m * m)
        (coverCircuitB (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail))))) := by
  classical
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hFcov, hFcard⟩ := PEqualNP.MetaComplexity.L288 k m H TH hk1 hTcov (subdivOf m k H) rfl
    (fwdOf m k H TH) (mem_fwdOf m k H TH)
  -- B1: cycles, from the sequence form of L-meta-285
  have hcyc : ∀ (v : Fin (m + 2 * k * m * m)) (c : (subdivOf m k H).Walk v v), c.IsCycle → 7 ≤ c.length := by
    have h := (PEqualNP.MetaComplexity.RootOnly.cycleHyp_iff (G := subdivOf m k H) (6 * k + 3)).mp
      (h285 k m H hk1 (subdivOf m k H) rfl)
    intro v c hc
    have := h v c hc
    omega
  have hhub : ∀ u v : Fin (m + 2 * k * m * m), u ≠ v → 3 ≤ ((subdivOf m k H).neighborSet u).ncard →
      3 ≤ ((subdivOf m k H).neighborSet v).ncard → ∀ p : (subdivOf m k H).Walk u v, 7 ≤ p.length := by
    intro u v huv hu hv p
    have := h492 k m H hk1 (subdivOf m k H) rfl u v huv hu hv p
    omega
  -- S has an edge
  have hHn : H.edgeSet.ncard ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hHe
    exact ((Set.ncard_pos (Set.toFinite _)).mpr ⟨s(a, b), (SimpleGraph.mem_edgeSet _).mpr hab⟩).ne'
  have hSe : ∃ i j : Fin (m + 2 * k * m * m), (subdivOf m k H).Adj i j := by
    have h := h286 k m H hk1 (subdivOf m k H) rfl
    have hne : (subdivOf m k H).edgeSet.ncard ≠ 0 := by
      rw [h]; exact Nat.mul_ne_zero (by omega) hHn
    obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero hne
    induction e using Sym2.ind with
    | h x y => exact ⟨x, y, (SimpleGraph.mem_edgeSet _).mp he⟩
  -- B4: the three facts on the circuit
  have hbound : ∀ p ∈ ol.map (fun l : List ℕ => (l.headD 0, l.tail)),
      p.1 < m + 2 * k * m * m ∧ ∀ w ∈ p.2, w < m + 2 * k * m * m := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
    exact ⟨c4 l hl _ (asm_headD_mem l (c3 l hl)), fun w hw => c4 l hl w (List.mem_of_mem_tail hw)⟩
  have hFC : FanInTwo (coverCircuitB (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail)))) := by
    intro g hg
    obtain ⟨h1, h2⟩ := (PEqualNP.MetaComplexity.L402 (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail)))).1 g hg
    refine ⟨?_, h2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
    tauto
  have hfun : circuitFun (m + 2 * k * m * m) (coverCircuitB (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail)))) =
      (fun x : Fin (m + 2 * k * m * m) → Bool => decide (∃ i j : Fin (m + 2 * k * m * m), (subdivOf m k H).Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    have h := PEqualNP.MetaComplexity.L398 (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail))) hbound x
    show (coverCircuitB _ _).eval (List.ofFn x) = _
    rw [Bool.eq_iff_iff, h, decide_eq_true_iff]
    constructor
    · rintro ⟨p, hp, h1, w, hw, h2⟩
      have hb := hbound p hp
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
      refine ⟨⟨l.headD 0, hb.1⟩, ⟨w, hb.2 w hw⟩, (c5 _ _).mpr ⟨l, hl, Or.inl ⟨rfl, hw⟩⟩, ?_, ?_⟩
      · rw [← asm_getD_ofFn x _ hb.1]; exact h1
      · rw [← asm_getD_ofFn x _ (hb.2 w hw)]; exact h2
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨l, hl, hcase⟩ := (c5 i j).mp hij
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨(l.headD 0, l.tail), List.mem_map.mpr ⟨l, hl, rfl⟩, ?_, j.val, h2, ?_⟩
        · show (List.ofFn x).getD (l.headD 0) false = true
          rw [h1, asm_getD_ofFn x _ i.isLt]; exact hi
        · rw [asm_getD_ofFn x _ j.isLt]; exact hj
      · refine ⟨(l.headD 0, l.tail), List.mem_map.mpr ⟨l, hl, rfl⟩, ?_, i.val, h2, ?_⟩
        · show (List.ofFn x).getD (l.headD 0) false = true
          rw [h1, asm_getD_ofFn x _ j.isLt]; exact hj
        · rw [asm_getD_ofFn x _ i.isLt]; exact hi
  -- the number of owners is |F|
  have hlen : (ol.map (fun l : List ℕ => l.headD 0)).length = (fwdOf m k H TH).card := by
    rw [← List.toFinset_card_of_nodup c1, ← Finset.card_image_of_injective _ Fin.val_injective]
    congr 1
    ext a
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · intro ha
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
      have hlt := c4 l hl _ (asm_headD_mem l (c3 l hl))
      exact ⟨⟨l.headD 0, hlt⟩, (c2 _).mpr ha, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact (c2 j).mp hj
  have hne : ol.map (fun l : List ℕ => (l.headD 0, l.tail)) ≠ [] := by
    intro h0
    have hol : ol = [] := List.map_eq_nil_iff.mp h0
    obtain ⟨i, j, hij⟩ := hSe
    rcases hFcov i j hij with h | h
    · have := (c2 i).mp h; simp [hol] at this
    · have := (c2 j).mp h; simp [hol] at this
  have hne2 : ∀ p ∈ ol.map (fun l : List ℕ => (l.headD 0, l.tail)), p.2 ≠ [] := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
    have := c3 l hl
    intro h0
    cases l with
    | nil => simp at this
    | cons a t => simp at h0; simp [h0] at this
  have hsize : (coverCircuitB (m + 2 * k * m * m) (ol.map (fun l : List ℕ => (l.headD 0, l.tail)))).size + 1 =
      (subdivOf m k H).edgeSet.ncard + (fwdOf m k H TH).card := by
    rw [PEqualNP.MetaComplexity.L395 _ _ hne hne2, List.map_map, List.length_map, ← hlen, List.length_map]
    have : ((fun p : ℕ × List ℕ => p.2.length) ∘ (fun l : List ℕ => (l.headD 0, l.tail))) =
        (fun l : List ℕ => l.tail.length) := rfl
    rw [this, c6]
  -- B3 and the upper bound from the checked cover circuit
  have hU : ∀ T : Finset (Fin (m + 2 * k * m * m)), (∀ i j, (subdivOf m k H).Adj i j → i ∈ T ∨ j ∈ T) →
      ∃ s : ℕ, s + 1 = (subdivOf m k H).edgeSet.ncard + T.card ∧
        HasCircuitSize (m + 2 * k * m * m) (fun x : Fin (m + 2 * k * m * m) → Bool =>
          decide (∃ i j : Fin (m + 2 * k * m * m), (subdivOf m k H).Adj i j ∧ x i = true ∧ x j = true)) s := by
    intro T hT
    obtain ⟨D, hD1, _, hD3, hD4⟩ := PEqualNP.MetaComplexity.CoverCircuit.graph_exact _ (subdivOf m k H) T hSe hT
    refine ⟨D.size, by rw [PEqualNP.MetaComplexity.RootOnly.edge_card_eq]; exact hD4, D, hD1, le_rfl, fun x => congrFun hD3 x⟩
  constructor
  · intro hmin
    refine (h376 PEqualNP.MetaComplexity.L204 _ (subdivOf m k H) _ (fwdOf m k H TH) hcyc hhub hSe hU hFcov hFC hfun hsize).mpr ?_
    intro U hU'
    have := h290 k m TH.card H hk1 hmin (subdivOf m k H) rfl U hU'
    omega
  · intro hwithin hlow
    refine h388 PEqualNP.MetaComplexity.L204 _ (subdivOf m k H) _ (fwdOf m k H TH) hcyc hhub hSe hU hFcov ?_ ?_ hFC hfun hsize
    · intro U hU'
      have := h290 k m (TH.card - 1) H hk1 (fun T hT => by have := hwithin T hT; omega) (subdivOf m k H) rfl U hU'
      omega
    · obtain ⟨T', hT'cov, hT'lt⟩ := hlow
      obtain ⟨h1, h2⟩ := PEqualNP.MetaComplexity.L288 k m H T' hk1 hT'cov (subdivOf m k H) rfl
        (fwdOf m k H T') (mem_fwdOf m k H T')
      exact ⟨_, h1, by omega⟩

/-! ## The formula level -/

/-- The adjacency of the placed graph, as the rows state it (needs L-meta-479 for looplessness). -/
theorem HOf_adj (h479 : Stmt479) (h489 : Stmt489) (φ : CNF) :
    ∀ a b : Fin (3 * (Eof φ + 1)), (HOf (Eof φ) φ).Adj a b ↔
      ∃ u v, (cvcGraph φ).Adj u v ∧ numOf (Eof φ) φ u = a.val ∧ numOf (Eof φ) φ v = b.val := by
  obtain ⟨he_lt, he_inj⟩ := h489 φ (eOf φ) (fun z => rfl)
  have hinj := h479 φ (Eof φ) (offOf φ) (eOf φ) rfl (fun i => rfl) he_lt he_inj (numOf (Eof φ) φ)
    (numOf_lit _ φ) (numOf_fresh _ φ) (numOf_pos _ φ) (numOf_end _ φ)
  intro a b
  simp only [HOf, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | ⟨u, v, huv, hu, hv⟩⟩
    · exact h
    · exact ⟨v, u, huv.symm, hv, hu⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨?_, Or.inl ⟨u, v, huv, hu, hv⟩⟩
    intro hab
    subst hab
    exact huv.ne (hinj u v v u huv huv.symm (hu.trans hv.symm))

/-- G-FUN at any k at least 3: the map `Rk k` sends unsatisfiable formulas to YES and satisfiable
ones to NO. -/
theorem fun_of_pieces_k (h285 : Stmt285) (h286 : Stmt286) (h290 : Stmt290) (h307 : Stmt307)
    (h376 : Stmt376) (h388 : Stmt388)
    (h473 : Stmt473) (h474 : Stmt474) (h475 : Stmt475) (h478 : Stmt478) (h479 : Stmt479)
    (h489 : Stmt489) (h492 : Stmt492) (hown : PEqualNP.MetaComplexity.Helpers.OwnerLink.GOwn) (k : ℕ) (hk : 3 ≤ k) (φ : CNF) :
    (¬ Satisfiable φ → LgpYes (Rk k φ).1 (Rk k φ).2) ∧
      (Satisfiable φ → LgpNo (Rk k φ).1 (Rk k φ).2) := by
  classical
  obtain ⟨he_lt, he_inj⟩ := h489 φ (eOf φ) (fun z => rfl)
  have hlt := h478 φ (Eof φ) (offOf φ) (eOf φ) rfl (fun i => rfl) he_lt he_inj (numOf (Eof φ) φ)
    (numOf_lit _ φ) (numOf_fresh _ φ) (numOf_pos _ φ) (numOf_end _ φ)
  have hinj := h479 φ (Eof φ) (offOf φ) (eOf φ) rfl (fun i => rfl) he_lt he_inj (numOf (Eof φ) φ)
    (numOf_lit _ φ) (numOf_fresh _ φ) (numOf_pos _ φ) (numOf_end _ φ)
  have hH := HOf_adj h479 h489 φ
  obtain ⟨hcov, hwithin, hiff⟩ := PEqualNP.MetaComplexity.L103 φ
  obtain ⟨hTcov, hTcard⟩ := h473 Vertex (cvcGraph φ) (3 * (Eof φ + 1)) (numOf (Eof φ) φ)
    (HOf (Eof φ) φ) (cvcCover φ) (THOf (Eof φ) φ) hlt hinj hH (h474 φ) (mem_THOf _ φ) hcov
  have hlb := h307 Vertex (cvcGraph φ) (3 * (Eof φ + 1)) (numOf (Eof φ) φ) (HOf (Eof φ) φ) hlt hinj hH
  have hHe : ∃ a b : Fin (3 * (Eof φ + 1)), (HOf (Eof φ) φ).Adj a b := by
    obtain ⟨u, v, huv⟩ := h475 φ
    exact ⟨⟨_, hlt u v huv⟩, ⟨_, hlt v u huv.symm⟩, (hH _ _).mpr ⟨u, v, huv, rfl, rfl⟩⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hown φ (Eof φ) k (offOf φ) (eOf φ) (by omega) rfl (fun i => rfl)
    (fun z => rfl) (numOf (Eof φ) φ) (numOf_lit _ φ) (numOf_fresh _ φ) (numOf_pos _ φ) (numOf_end _ φ)
    (HOf (Eof φ) φ) hH (THOf (Eof φ) φ) (mem_THOf _ φ) (subdivOf _ k (HOf (Eof φ) φ)) rfl
    (fwdOf _ k (HOf (Eof φ) φ) (THOf (Eof φ) φ)) (mem_fwdOf _ k _ _) (OWN (Eof φ) k (REN φ)) rfl
  have hcore := fun_core h285 h286 h290 h376 h388 h492 (3 * (Eof φ + 1)) k hk
    (HOf (Eof φ) φ) (THOf (Eof φ) φ) hTcov hHe (OWN (Eof φ) k (REN φ)) c1 c2 c3 c4 c5 c6
  -- B2: the number of inputs
  have hn : nOf (Eof φ) k = 3 * (Eof φ + 1) + 2 * k * (3 * (Eof φ + 1)) * (3 * (Eof φ + 1)) := by
    unfold nOf; ring
  show (¬ Satisfiable φ → LgpYes (nOf (Eof φ) k) (coverCircuitB (nOf (Eof φ) k) _)) ∧
    (Satisfiable φ → LgpNo (nOf (Eof φ) k) (coverCircuitB (nOf (Eof φ) k) _))
  rw [hn]
  refine ⟨fun hu => hcore.1 ?_, fun hs => hcore.2 ?_ ?_⟩
  · rw [hTcard]; exact (hlb (cvcCover φ).card).mp (hiff.mpr hu)
  · rw [hTcard]
    intro T hT
    have := (hlb ((cvcCover φ).card - 1)).mp (fun S0 hS0 => by have := hwithin S0 hS0; omega) T hT
    omega
  · by_contra hno
    push Not at hno
    exact (hiff.mp ((hlb (cvcCover φ).card).mpr (fun T hT => hTcard ▸ hno T hT))) hs

/-- G-FUN at the parameter of record k = 4. -/
theorem fun_of_pieces (h285 : Stmt285) (h286 : Stmt286) (h290 : Stmt290) (h307 : Stmt307)
    (h376 : Stmt376) (h388 : Stmt388)
    (h473 : Stmt473) (h474 : Stmt474) (h475 : Stmt475) (h478 : Stmt478) (h479 : Stmt479)
    (h489 : Stmt489) (h492 : Stmt492) (hown : PEqualNP.MetaComplexity.Helpers.OwnerLink.GOwn) :
    ∀ φ : CNF, (¬ Satisfiable φ → LgpYes (R φ).1 (R φ).2) ∧ (Satisfiable φ → LgpNo (R φ).1 (R φ).2) :=
  fun φ => fun_of_pieces_k h285 h286 h290 h307 h376 h388 h473 h474 h475 h478 h479
    h489 h492 hown kRec (by decide) φ

end PEqualNP.MetaComplexity.Reduction
