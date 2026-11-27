import PEqualNP.MetaComplexity.Helpers.EdgeFnPlan
import PEqualNP.MetaComplexity.Helpers.LocRes
import PEqualNP.MetaComplexity.Helpers.LocFree
import PEqualNP.MetaComplexity.Helpers.LocStruct

/-!
# Graph pieces and the induction of the full-basis bound (FULL-PROOF Theorem 6.1)

Statements of the graph pieces G1, G3, G4, G6 and of the class form A1 of the bound, on the shared
graph layer `LocGraph.lean` (`delV`, `tau`, `Phi1`, `AFree`, `Run`, `Deep`, `BoundOf`). G2 is not
restated: it is `Loc.ToolRes0`, `Loc.ToolRes1` (the residuals at a deep vertex) and `Loc.ToolDrop0`,
`Loc.ToolDrop1` (edge counts and covers), all basis-free and proved in `LocRes.lean`.

Proved here: `stmtG1` (heredity of (T)), `stmtG3` (the run gives `DeepHyp` and two deep inputs),
`stmtG4` (good leaf or run, for (T)), `stmtG6` (the leaf step), the deep step, the induction
`a1_of_pieces` (class form, any class closed under `delV` with the dichotomy), `lb_of_a1`,
`lb_of_pieces` and `lb_of_ml : StmtML → StmtLB`. The only open hypothesis is `StmtML`.

The induction uses closure under VERTEX deletion with the arity kept (`delV G X`): every residual,
at a leaf and at a deep vertex, is of that form. Measure: the edge count alone (every step deletes
an edge; the free inputs `A` are carried, no step S1).
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-! ## The class and the statements -/

/-- The class (T) of `StmtLB`: every cycle has length at least 7, and two distinct vertices with
at least three neighbours each are joined by no walk shorter than 7. -/
def T7 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) ∧
    ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length

/-- A good leaf (the conclusion of `Forest.forest_good_leaf`): a leaf `l` at `p` where `p` has at
most one further neighbour, or a second leaf `l'` at `p`. -/
def GoodLeaf {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ l p : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨ (∃ l', l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))

/-- A class of graphs closed under deleting every edge at a vertex set, the arity kept. -/
def Hered (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)), P n G → P n (delV G X)

/-- The dichotomy for a class: a graph of the class with an edge has a good leaf or a run. -/
def Dich (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), P n G → (∃ i j, G.Adj i j) →
    GoodLeaf G ∨ ∃ a' a s t b b' : Fin n, Run G a' a s t b b'

/-- Piece G1 (heredity of (T) under vertex deletion). Proved below (`stmtG1`). -/
def StmtG1 : Prop := Hered (fun _ G => T7 G)

/-- Piece G3. At a run, the semantic hypotheses of `StmtML` hold for `F G A` and the four inner
vertices, and that set has at least two elements (the repaired `DeepHyp` will ask for it). -/
def StmtG3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (A : Finset (Fin (n + 1)))
    (a' a s t b b' : Fin (n + 1)), AFree G A → Run G a' a s t b b' →
    DeepHyp (F G A) {a, s, t, b} ∧ 2 ≤ ({a, s, t, b} : Finset (Fin (n + 1))).card

/-- Piece G4 (FULL-PROOF 2.6 for the class (T)): `Loc.PStructure` with `InL` (cycles at least 9)
replaced by `T7` (cycles at least 7). -/
def StmtG4 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), T7 G → (∃ i j, G.Adj i j) →
    (¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q) →
    (¬ ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p) →
    ∃ a' a s t b b', Run G a' a s t b b'

/-- The induction hypothesis at `G`, class-free: the full-basis bound at every vertex deletion of
`G` with fewer edges, any free inputs that no edge meets. -/
def IHV {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (X A' : Finset (Fin n)), AFree (delV G X) A' →
    (delV G X).edgeSet.ncard < G.edgeSet.ncard → BoundOf (HasCircuitSize n) (delV G X) A'

/-- Piece G6, the leaf step (the two leaf cases of `Forest.claimQ`). Proved below (`stmtG6`). -/
def StmtG6 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), AFree G A → IHV G → GoodLeaf G →
    BoundOf (HasCircuitSize n) G A

/-- Piece A1, the class form of the bound at the full basis. -/
def StmtA1 (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), P n G → AFree G A →
    BoundOf (HasCircuitSize n) G A

/-! ## G1 -/

theorem stmtG1 : StmtG1 := by
  intro n G X hL
  have hle := delV_le G X
  refine ⟨fun v p hp => ?_, fun u v huv hu hv p => ?_⟩
  · have := hL.1 v (p.mapLe hle) (hp.mapLe hle)
    rwa [Walk.length_mapLe] at this
  · have hsub : ∀ w, (delV G X).neighborSet w ⊆ G.neighborSet w := fun w y hy => hle hy
    have := hL.2 u v huv (le_trans hu (Set.ncard_le_ncard (hsub u)))
      (le_trans hv (Set.ncard_le_ncard (hsub v))) (p.mapLe hle)
    rwa [Walk.length_mapLe] at this

/-! ## G3: the semantic hypotheses at a run -/

theorem F_false_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {z : Fin n → Bool}
    (S : Finset (Fin n)) (hz : ∀ i, z i = true → i ∈ S) (hA : ∀ a ∈ A, a ∉ S)
    (hE : ∀ i j, G.Adj i j → i ∈ S → j ∉ S) : F G A z = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
  · exact hA a ha (hz a h)
  · exact hE i j hij (hz i hi) (hz j hj)

theorem F_true_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {z : Fin n → Bool}
    (i j : Fin n) (hij : G.Adj i j) (hi : z i = true) (hj : z j = true) : F G A z = true :=
  (F_true G A z).2 (Or.inr ⟨i, j, hij, hi, hj⟩)

theorem F_mono {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {z x : Fin n → Bool}
    (h : ∀ i, z i = true → x i = true) (hz : F G A z = true) : F G A x = true := by
  rw [F_true] at hz ⊢
  rcases hz with ⟨a, ha, h'⟩ | ⟨i, j, hij, hi, hj⟩
  · exact Or.inl ⟨a, ha, h a h'⟩
  · exact Or.inr ⟨i, j, hij, h i hi, h j hj⟩

/-- H1 at one input: an edge avoiding `y`, and `y` not free. -/
theorem nc_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {y i j c : Fin n} (hij : G.Adj i j) (hi : i ≠ y) (hj : j ≠ y) (hyc : G.Adj y c) (b : Bool) :
    ∃ x x' : Fin n → Bool, F G A (Function.update x y b) ≠ F G A (Function.update x' y b) := by
  have hyA : y ∉ A := hinv y c hyc
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_true_of i j hij (by simp [Function.update_of_ne hi]) (by simp [Function.update_of_ne hj]),
    F_false_of {y} (fun k hk => by
      by_cases hk' : k = y
      · simp [hk']
      · simp [Function.update_of_ne hk'] at hk)
    (fun a ha h => by rw [Finset.mem_singleton] at h; exact hyA (h ▸ ha))
    (fun k l h hk hl => by
      rw [Finset.mem_singleton] at hk hl
      exact h.ne (hk.trans hl.symm))]
  simp

/-- H2 at one ordered pair: a neighbour `c` of `y` that is not `y'` and not a neighbour of `y'`,
and a neighbour `c'` of `y'` that is not `y`. -/
theorem nf_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {y y' c c' u1 u2 : Fin n} (hyy : y ≠ y') (hyc : G.Adj y c) (hcy' : c ≠ y')
    (hy' : ∀ w, G.Adj y' w → w = u1 ∨ w = u2) (hc1 : c ≠ u1) (hc2 : c ≠ u2)
    (hyc' : G.Adj y' c') (hc'y : c' ≠ y) : ¬ PairFunnel (F G A) y y' := by
  have hcA : c ∉ A := hinv c y hyc.symm
  have hy'A : y' ∉ A := hinv y' c' hyc'
  have hc'A : c' ∉ A := hinv c' y' hyc'.symm
  have hcy : c ≠ y := hyc.ne.symm
  have hc'y' : c' ≠ y' := hyc'.ne.symm
  have hncy' : ¬ G.Adj c y' := fun h => by
    rcases hy' c h.symm with h | h
    · exact hc1 h
    · exact hc2 h
  have f1 : ∀ d : Fin n, d ∉ A → ∀ z : Fin n → Bool, (∀ i, z i = true → i = d) →
      F G A z = false := fun d hd z hz =>
    F_false_of {d} (fun i hi => by rw [Finset.mem_singleton]; exact hz i hi)
      (fun a ha h => by rw [Finset.mem_singleton] at h; exact hd (h ▸ ha))
      (fun i j h hi hj => by
        rw [Finset.mem_singleton] at hi hj
        exact h.ne (hi.trans hj.symm))
  have T1 : F G A (set2 (pt {c}) y true y' false) = true :=
    F_true_of y c hyc (by simp [set2, hyy])
      (by simp [set2, pt, hcy, hcy'])
  have T2 : F G A (set2 (pt {c'}) y false y' true) = true :=
    F_true_of y' c' hyc' (by simp [set2])
      (by simp [set2, pt, hc'y, hc'y'])
  have Z1 : F G A (set2 (pt {c}) y false y' false) = false := f1 c hcA _ (fun i hi => by
    simp only [set2, Function.update_apply, pt] at hi
    split_ifs at hi <;> simp_all)
  have Z2 : F G A (set2 (pt {c'}) y false y' false) = false := f1 c' hc'A _ (fun i hi => by
    simp only [set2, Function.update_apply, pt] at hi
    split_ifs at hi <;> simp_all)
  have Z3 : F G A (set2 (pt {c}) y false y' true) = false := by
    refine F_false_of {c, y'} (fun i hi => ?_) (fun a ha h => ?_) (fun i j h hi hj => ?_)
    · simp only [set2, Function.update_apply, pt] at hi
      split_ifs at hi <;> simp_all
    · rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hcA (h ▸ ha)
      · exact hy'A (h ▸ ha)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact h.ne rfl
      · exact hncy' h
      · exact hncy' h.symm
      · exact h.ne rfl
  have h1 : ∃ x, F G A (set2 x y true y' false) ≠ F G A (set2 x y false y' false) :=
    ⟨pt {c}, by rw [T1, Z1]; simp⟩
  have h2 : ∃ x, F G A (set2 x y false y' true) ≠ F G A (set2 x y false y' false) :=
    ⟨pt {c'}, by rw [T2, Z2]; simp⟩
  have h3 : ∃ x, F G A (set2 x y true y' false) ≠ F G A (set2 x y false y' true) :=
    ⟨pt {c}, by rw [T1, Z3]; simp⟩
  obtain ⟨x1, h1⟩ := h1
  obtain ⟨x2, h2⟩ := h2
  obtain ⟨x3, h3⟩ := h3
  rintro ⟨a, b, hab⟩
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2

/-- H3 at one input `y ∈ D`: a neighbour `c ∈ D` of `y` all of whose neighbours are in `D`. -/
theorem win_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {D : Finset (Fin n)} {y c : Fin n} (hy : y ∈ D) (hc : c ∈ D) (hyc : G.Adj y c)
    (hcD : ∀ w, G.Adj c w → w ∈ D) (x : Fin n → Bool) (hx : F G A (zeroOn D x) = false) :
    ∃ x' : Fin n → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F G A x' = false ∧
      F G A (Function.update x' y true) = true := by
  have hcA : c ∉ A := hinv c y hyc.symm
  have hz : ∀ i, i ≠ c → Function.update (zeroOn D x) c true i = zeroOn D x i :=
    fun i hi => Function.update_of_ne hi _ _
  have hbad : ∀ P : Prop, F G A (zeroOn D x) = true → P := fun P h => by
    rw [hx] at h; exact absurd h (by simp)
  refine ⟨Function.update (zeroOn D x) c true, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hz i (fun h => hi (h ▸ hc))]
    simp [zeroOn, hi]
  · rw [hz y hyc.ne]
    simp [zeroOn, hy]
  · rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · have hac : a ≠ c := fun e => hcA (e ▸ ha)
      rw [hz a hac] at h
      exact hbad _ ((F_true G A _).2 (Or.inl ⟨a, ha, h⟩))
    · by_cases hic : i = c
      · subst hic
        have hjc : j ≠ i := hij.ne.symm
        rw [hz j hjc] at hj
        simp [zeroOn, hcD j hij] at hj
      by_cases hjc : j = c
      · subst hjc
        rw [hz i hic] at hi
        simp [zeroOn, hcD i hij.symm] at hi
      rw [hz i hic] at hi
      rw [hz j hjc] at hj
      exact hbad _ ((F_true G A _).2 (Or.inr ⟨i, j, hij, hi, hj⟩))
  · exact F_true_of y c hyc (by simp)
      (by rw [Function.update_of_ne hyc.ne.symm]; simp)

theorem stmtG3 : StmtG3 := by
  intro n G A a' a s t b b' hinv hr
  have nd := hr.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h01, h02, h03, h04, h05⟩, ⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := nd
  have haa' : G.Adj a a' := (hr.ha a').2 (Or.inl rfl)
  have has : G.Adj a s := (hr.ha s).2 (Or.inr rfl)
  have hsa : G.Adj s a := (hr.hs a).2 (Or.inl rfl)
  have hst : G.Adj s t := (hr.hs t).2 (Or.inr rfl)
  have hts : G.Adj t s := (hr.ht s).2 (Or.inl rfl)
  have htb : G.Adj t b := (hr.ht b).2 (Or.inr rfl)
  have hbt : G.Adj b t := (hr.hb t).2 (Or.inl rfl)
  have hbb' : G.Adj b b' := (hr.hb b').2 (Or.inr rfl)
  have ha1 : ∀ w, G.Adj a w → w = a' ∨ w = s := fun w h => (hr.ha w).1 h
  have hs1 : ∀ w, G.Adj s w → w = a ∨ w = t := fun w h => (hr.hs w).1 h
  have ht1 : ∀ w, G.Adj t w → w = s ∨ w = b := fun w h => (hr.ht w).1 h
  have hb1 : ∀ w, G.Adj b w → w = t ∨ w = b' := fun w h => (hr.hb w).1 h
  have mem : ∀ w, w = a ∨ w = s ∨ w = t ∨ w = b → w ∈ ({a, s, t, b} : Finset (Fin (n + 1))) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hw
  refine ⟨⟨?_, ?_, ?_, ?_, F_zero G A⟩, ?_⟩
  · intro y hy bv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h <;> rw [h]
    · exact nc_of hinv hst (Ne.symm h12) (Ne.symm h13) has bv
    · exact nc_of hinv htb (Ne.symm h23) (Ne.symm h24) hst bv
    · exact nc_of hinv has h13 h23 hts bv
    · exact nc_of hinv has h14 h24 hbt bv
  · intro y hy y' hy' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
    rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h'] at hne ⊢
    · exact absurd rfl hne
    · exact nf_of hinv hne haa' h02 hs1 h01 h03 hst (Ne.symm h13)
    · exact nf_of hinv hne haa' h03 ht1 h02 h04 htb (Ne.symm h14)
    · exact nf_of hinv hne haa' h04 hb1 h03 h05 hbb' (Ne.symm h15)
    · exact nf_of hinv hne hst (Ne.symm h13) ha1 (Ne.symm h03) (Ne.symm h23) haa' h02
    · exact absurd rfl hne
    · exact nf_of hinv hne hsa h13 ht1 h12 h14 htb (Ne.symm h24)
    · exact nf_of hinv hne hsa h14 hb1 h13 h15 hbb' (Ne.symm h25)
    · exact nf_of hinv hne htb (Ne.symm h14) ha1 (Ne.symm h04) (Ne.symm h24) haa' h03
    · exact nf_of hinv hne htb (Ne.symm h24) hs1 (Ne.symm h14) (Ne.symm h34) hsa h13
    · exact absurd rfl hne
    · exact nf_of hinv hne hts h24 hb1 h23 h25 hbb' (Ne.symm h35)
    · exact nf_of hinv hne hbb' (Ne.symm h15) ha1 (Ne.symm h05) (Ne.symm h25) haa' h04
    · exact nf_of hinv hne hbb' (Ne.symm h25) hs1 (Ne.symm h15) (Ne.symm h35) hsa h14
    · exact nf_of hinv hne hbb' (Ne.symm h35) ht1 (Ne.symm h25) (Ne.symm h45.1) hts h24
    · exact absurd rfl hne
  · intro y hy x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have nb : ∀ (w u v : Fin (n + 1)), (w = u ∨ w = v) → (u = a ∨ u = s ∨ u = t ∨ u = b) →
        (v = a ∨ v = s ∨ v = t ∨ v = b) → w ∈ ({a, s, t, b} : Finset (Fin (n + 1))) := by
      intro w u v hw hu hv
      rcases hw with rfl | rfl
      · exact mem _ hu
      · exact mem _ hv
    rcases hy with h | h | h | h <;> rw [h]
    · exact win_of hinv (mem a (by simp)) (mem s (by simp)) has
        (fun w hw => nb w a t (hs1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem s (by simp)) (mem t (by simp)) hst
        (fun w hw => nb w s b (ht1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem t (by simp)) (mem s (by simp)) hts
        (fun w hw => nb w a t (hs1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem b (by simp)) (mem t (by simp)) hbt
        (fun w hw => nb w s b (ht1 w hw) (by simp) (by simp)) x hx
  · intro x hx
    refine F_mono (fun i h => ?_) hx
    unfold zeroOn at h
    split_ifs at h <;> simp_all
  · have hsub : ({a, s} : Finset (Fin (n + 1))) ⊆ {a, s, t, b} := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      tauto
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h12] at this
    exact this

/-! ## G4 (copy of `Loc.Struct.thread` and `PStructure_proof` with cycles at least 7) -/

section G4
open PEqualNP.MetaComplexity.Loc.Struct

/-- A longest thread has length at least six. -/
theorem thread7 {n : ℕ} (G : SimpleGraph (Fin n)) (hL : T7 G)
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
  push Not at hlt
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

theorem stmtG4 : StmtG4 := by
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
    obtain ⟨x, q, hq, h6⟩ := thread7 G hL h1 u v huv.symm hv (Or.inl hu)
    exact run_of_thread hq h6
  · push Not at hb
    have nb : ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard := fun w h => by have := hb w; omega
    have go : ∀ u v, G.Adj v u → Two G v → ∃ a' a s t b b', Run G a' a s t b b' := by
      intro u v hvu hv
      obtain ⟨x, q, hq, h6⟩ := thread7 G hL h1 u v hvu hv (Or.inr nb)
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

end G4

/-! ## G6, the leaf step -/

theorem afree_delV {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (h : AFree G A)
    (X : Finset (Fin n)) : AFree (delV G X) A :=
  fun i j hij => h i j ((delV_adj G X i j).1 hij).1

theorem leaf_drop0 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p) :
    Phi1 G A ≤ Phi1 (delV G {l}) A + 2 ∧
      (delV G {l}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [Free.del_leaf G l p hleaf]
  have he := ncard_del1 G l p hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(l, p)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _) T hT)
  have := Finset.card_insert_le p T
  unfold Phi1
  constructor <;> omega

theorem leaf_drop1 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q)
    (hpA : p ∉ A) :
    Phi1 G A ≤ Phi1 (delV G (insert l {p})) (A ∪ {p}) + 2 ∧
      (delV G (insert l {p})).edgeSet.ncard < G.edgeSet.ncard := by
  rw [Free.del_leaf2 G l p q hleaf hp]
  obtain ⟨he1, he2⟩ := ncard_del2 G l p q hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(p, l), s(p, q)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rcases he with rfl | he
    · exact Sym2.mem_mk_left _ _
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact Sym2.mem_mk_left _ _) T hT)
  have := Finset.card_insert_le p T
  have hAp : (A ∪ {p}).card = A.card + 1 := by
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_notMem hpA]
  unfold Phi1
  rw [hAp]
  constructor <;> omega

theorem stmtG6 : StmtG6 := by
  intro n G A hinv hih hgood s hC
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := hgood
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hpl : p ≠ l := hlp.ne.symm
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
  obtain ⟨d0, e0⟩ := leaf_drop0 G A l p hlp hleaf
  have hrf : (fun x => F G A (Function.update x l false)) = F (delV G {l}) A :=
    funext fun x => Res.ToolRes0_proof _ G A l x hlA
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · obtain ⟨d1, e1⟩ := leaf_drop1 G A l p q hlp hleaf hq hpA
    by_cases h0 : A.Nonempty ∨ ∃ i j, (delV G {l}).Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F (delV G (insert l {p})) (A ∪ {p}) :=
        funext fun x => Res.ToolRes1_proof _ G A l {p} x hlA (fun w => by
          rw [Finset.mem_singleton]
          exact ⟨hleaf w, fun h => h ▸ hlp⟩)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc (delV G {l}) A h0
          refine ⟨x, y, ?_⟩
          rw [congrFun hrf x, congrFun hrf y]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc (delV G (insert l {p})) (A ∪ {p}) (Or.inl ⟨p, by simp⟩)
          refine ⟨x, y, ?_⟩
          rw [congrFun hrt x, congrFun hrt y]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have := hih {l} A (afree_delV hinv {l}) (by omega) s' hC'
        omega
      · rw [hrt] at hC'
        have hinv1 : AFree (delV G (insert l {p})) (A ∪ {p}) := by
          intro i j h hi
          obtain ⟨hij, hi1, -⟩ := (delV_adj G _ i j).1 h
          rcases Finset.mem_union.1 hi with hi | hi
          · exact hinv i j hij hi
          · exact hi1 (by rw [Finset.mem_singleton] at hi; simp [hi])
        have := hih (insert l {p}) (A ∪ {p}) hinv1 e1 s' hC'
        omega
    · push Not at h0
      obtain ⟨hA0, hG00⟩ := h0
      have he := noedge_ncard (delV G {l}) hG00
      have ht := tau_le (delV G {l}) ∅ (fun i j h => absurd h (hG00 i j))
      subst hA0
      unfold Phi1 at d0 ⊢
      rw [Finset.card_empty] at ht d0 ⊢
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : (delV G {l}).Adj p l' := (delV_adj G {l} p l').2 ⟨hpl', by simpa using hpl,
      by simpa using hl'l⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc (delV G {l}) A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      rw [congrFun hrf x, congrFun hrf y]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have htau : tau G ≤ tau (delV G {l}) := by
      obtain ⟨T, hT, hTc⟩ := tau_attained (delV G {l})
      rw [← hTc]
      rw [Free.del_leaf G l p hleaf] at hT
      exact cov_swap G l p l' (tau G) hl'l hpl' hleaf' (fun T h => tau_le G T h) T hT
    have := hih {l} A (afree_delV hinv {l}) (by omega) s0 hC'
    unfold Phi1 at this ⊢
    omega

/-! ## The deep step -/

theorem deep_mem {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (hr : Run G a' a s t b b') (y : Fin n) (hy : y ∈ ({a, s, t, b} : Finset (Fin n))) :
    Deep G y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact hr.deep_a
  · exact hr.deep_s
  · exact hr.deep_t
  · exact hr.deep_b

/-- The deep step: at a run, `StmtML` pays 3 at false or 4 at true at an inner vertex, and the
residual is again of the form `delV G X`. -/
theorem deep_step (hG3 : StmtG3) (hML : StmtML) (hR0 : ToolRes0) (hR1 : ToolRes1)
    (hD0 : ToolDrop0) (hD1 : ToolDrop1) {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (a' a s t b b' : Fin n) (hinv : AFree G A) (hih : IHV G) (hr : Run G a' a s t b b') :
    BoundOf (HasCircuitSize n) G A := by
  intro s0 hC
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := a.2; omega⟩
  obtain ⟨hD, h2⟩ := hG3 n' G A a' a s t b b' hinv hr
  have hne : ({a, s, t, b} : Finset (Fin (n' + 1))).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨y, hy, hpay⟩ := hML n' (F G A) _ s0 hD hne hC
  obtain ⟨u1, u2, c1, c2, hu12, hN, h1, h2', -⟩ := deep_mem hr y hy
  have hyu1 : G.Adj y u1 := (hN u1).2 (Or.inl rfl)
  have hyu2 : G.Adj y u2 := (hN u2).2 (Or.inr rfl)
  have hyA : y ∉ A := hinv y u1 hyu1
  rcases hpay with ⟨s', hs', hC'⟩ | ⟨s', hs', hC'⟩
  · have hf : (fun x => F G A (Function.update x y false)) = F (delV G {y}) A :=
      funext fun x => hR0 _ G A y x hyA
    rw [hf] at hC'
    obtain ⟨d, e⟩ := hD0 _ G A y u1 u2 hyu1 (fun w h => (hN w).1 h)
    have := hih {y} A (afree_delV hinv {y}) e s' hC'
    omega
  · have hf : (fun x => F G A (Function.update x y true)) =
        F (delV G (insert y {u1, u2})) (A ∪ {u1, u2}) :=
      funext fun x => hR1 _ G A y {u1, u2} x hyA (fun w => by
        rw [hN w]; simp)
    rw [hf] at hC'
    have hu1A : u1 ∉ A := hinv u1 y hyu1.symm
    have hu2A : u2 ∉ A := hinv u2 y hyu2.symm
    obtain ⟨d, e⟩ := hD1 _ G A y u1 u2 c1 c2 hN h1 h2' hu1A hu2A
    have hinv1 : AFree (delV G (insert y {u1, u2})) (A ∪ {u1, u2}) := by
      intro i j h hi
      obtain ⟨hij, hi1, -⟩ := (delV_adj G _ i j).1 h
      rcases Finset.mem_union.1 hi with hi | hi
      · exact hinv i j hij hi
      · exact hi1 (Finset.mem_insert_of_mem hi)
    have := hih _ _ hinv1 e s' hC'
    omega

/-! ## A1: the induction -/

/-- THE INDUCTION (FULL-PROOF Theorem 6.1, class form): for a class closed under `delV` in which
every graph with an edge has a good leaf or a run, the full-basis bound holds. -/
theorem a1_of_pieces {P : (n : ℕ) → SimpleGraph (Fin n) → Prop} (hH : Hered P) (hDi : Dich P)
    (hG3 : StmtG3) (hG6 : StmtG6) (hML : StmtML) (hR0 : ToolRes0) (hR1 : ToolRes1)
    (hD0 : ToolDrop0) (hD1 : ToolDrop1) : StmtA1 P := by
  suffices key : ∀ (e n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      G.edgeSet.ncard = e → P n G → AFree G A → BoundOf (HasCircuitSize n) G A from
    fun n G A hP hinv => key _ n G A rfl hP hinv
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ihe =>
  intro n G A he hP hinv
  have hih : IHV G := fun X A' hinv' hlt =>
    ihe _ (he ▸ hlt) n (delV G X) A' rfl (hH n G X hP) hinv'
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · intro s hC
    have hE' : ∀ i j, ¬ G.Adj i j := fun i j h => hE ⟨i, j, h⟩
    have hdep := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    have h0 := noedge_ncard G hE'
    have ht := tau_le G ∅ (fun i j h => absurd h (hE' i j))
    rw [Finset.card_empty] at ht
    unfold Phi1
    omega
  rcases hDi n G hP hE with hg | ⟨a', a, s, t, b, b', hr⟩
  · exact hG6 n G A hinv hih hg
  · exact deep_step hG3 hML hR0 hR1 hD0 hD1 G A a' a s t b b' hinv hih hr

/-- The dichotomy for (T) from G4. -/
theorem dich_of_g4 (hG4 : StmtG4) : Dich (fun _ G => T7 G) := by
  intro n G hT hE
  by_cases h1 : ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q
  · obtain ⟨l, p, q, h, h', h''⟩ := h1
    exact Or.inl ⟨l, p, h, h', Or.inl ⟨q, h''⟩⟩
  by_cases h2 : ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p
  · obtain ⟨l, p, l', h, h', h'', h3, h4⟩ := h2
    exact Or.inl ⟨l, p, h, h', Or.inr ⟨l', h3, h'', h4⟩⟩
  exact Or.inr (hG4 n G hT hE h1 h2)

/-- A2: the plan's `StmtLB` from the class form at (T). -/
theorem lb_of_a1 (h : StmtA1 (fun _ G => T7 G)) : StmtLB := by
  intro n k s G A hcyc hdist hinv _ hk hC
  have hb := h n G A ⟨hcyc, hdist⟩ hinv s hC
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  have := hk T hT
  unfold Phi1 at hb
  omega

/-- `StmtLB` from the open pieces G3, G4 and the circuit theorem `StmtML`. -/
theorem lb_of_pieces (hG3 : StmtG3) (hG4 : StmtG4) (hML : StmtML) : StmtLB :=
  lb_of_a1 (a1_of_pieces stmtG1 (dich_of_g4 hG4) hG3 stmtG6 hML Res.ToolRes0_proof
    Res.ToolRes1_proof Res.ToolDrop0_proof Res.ToolDrop1_proof)

/-- The plan's `StmtLB` from the circuit theorem alone. -/
theorem lb_of_ml (hML : StmtML) : StmtLB := lb_of_pieces stmtG3 stmtG4 hML

end PEqualNP.MetaComplexity.EdgeFn
