import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Monotone local-class bound (`L-meta-115`): the last cell and Theorem FC

Pieces `PLast` and `PFC` of `LocPlan.lean`. Tools of other builders are taken as explicit
hypotheses.

Paper: `routes/lifting/lgp/FO1-monotone-direct.md` section 5 (LAST CELL) and section 6.
-/

namespace PEqualNP.MetaComplexity.Loc.Last

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-! ## Small facts on gates of a clean NOT-free list -/

/-- A gate of a clean NOT-free list reading `w` is an AND or an OR of `w` and one more wire. -/
theorem shape {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p : ℕ} {g : Gate}
    (hp : gs[p]? = some g) {w : ℕ} (hw : w ∈ g.inputs) :
    ∃ y, y ∈ g.inputs ∧
      ((g.op = GateOp.and ∧ ∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x w && vl gs x y)) ∨
       (g.op = GateOp.or ∧ ∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x w || vl gs x y))) := by
  have hnot := hnf g (List.mem_of_getElem? hp)
  rcases hcl p g hp with ⟨h1, _⟩ | ⟨hop, j, k, _, _, hin⟩
  · exact absurd h1 hnot
  rw [hin] at hw
  have hw' : w = j ∨ w = k := by simpa using hw
  have key : ∃ y, y ∈ g.inputs ∧ ∀ x : Fin m → Bool,
      (vl gs x j && vl gs x k) = (vl gs x w && vl gs x y) ∧
      (vl gs x j || vl gs x k) = (vl gs x w || vl gs x y) := by
    rcases hw' with rfl | rfl
    · exact ⟨k, by rw [hin]; simp, fun x => ⟨rfl, rfl⟩⟩
    · exact ⟨j, by rw [hin]; simp, fun x => ⟨Bool.and_comm _ _, Bool.or_comm _ _⟩⟩
  obtain ⟨y, hy, hxy⟩ := key
  refine ⟨y, hy, ?_⟩
  rcases hop with h | h
  · refine Or.inl ⟨h, fun x => ?_⟩
    rw [vl_gate gs hcl x p g hp, h, hin, ← (hxy x).1]
    simp [GateOp.eval]
  · refine Or.inr ⟨h, fun x => ?_⟩
    rw [vl_gate gs hcl x p g hp, h, hin, ← (hxy x).2]
    simp [GateOp.eval]

theorem vl_in {m : ℕ} (gs : List Gate) (x : Fin m → Bool) (i : Fin m) :
    vl gs x (i : ℕ) = x i := by
  rw [vl_input gs x i i.isLt]

theorem pt_self {m : ℕ} (v : Fin m) : pt {v} v = true := by simp [pt]

/-- An OR reader of the input `t` is true at `e_t`. -/
theorem or_true {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) {q : ℕ} {t : Fin m} {w : ℕ}
    (h : OrRd gs q t w) : vl gs (pt {t}) (m + q) = true := by
  obtain ⟨g, hg, hop, hin⟩ := h
  rw [vl_gate gs hcl _ q g hg, hop]
  rcases hin with hin | hin <;> rw [hin] <;> simp [GateOp.eval, vl_in, pt_self]

/-- `F G ∅` is false at a unit point. -/
theorem F_unit {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : F G ∅ (pt {v}) = false := by
  cases h : F G ∅ (pt {v}) with
  | false => rfl
  | true =>
    rw [F_true] at h
    rcases h with ⟨a, ha, _⟩ | ⟨i, j, hij, hi, hj⟩
    · simp at ha
    · simp [pt] at hi hj
      subst hi; subst hj
      exact absurd rfl hij.ne

/-- `F G ∅` is true at the two ends of an edge. -/
theorem F_edge {n : ℕ} (G : SimpleGraph (Fin n)) (s t : Fin n) (h : G.Adj s t) :
    F G ∅ (pt {s, t}) = true := by
  rw [F_true]
  exact Or.inr ⟨s, t, h, by simp [pt], by simp [pt]⟩

/-! ## The last cell -/

/-- The core of the last cell, with the two readers of `e_t` ordered: `G2 < G1`. -/
theorem last_core (hP : ToolProp) (hU : ToolU) {n : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} {gs : List Gate} {o : ℕ} {a' a s t b b' : Fin n} {qa qs qt qb ws wt : ℕ}
    (hctx : Ctx G A gs o a' a s t b b') (hfan : Fan gs a s t b qa qs qt qb)
    (hws : OrRd gs qs s ws) (hwt : OrRd gs qt t wt)
    (hqs2 : ∀ q ∈ RdSet gs (n + qs), vl gs (pt {s}) (n + q) = false)
    (G1 G2 : ℕ) (hlt : G2 < G1) (hrd : RdSet gs (n + qt) = {G1, G2})
    (hq1 : vl gs (pt {t}) (n + G1) = false) (hq2 : vl gs (pt {t}) (n + G2) = false) :
    ∃ q, q ∈ RdSet gs (n + qs) ∧ q ∈ RdSet gs (n + qt) := by
  have hcl : CleanL n gs := hctx.cex.least.1
  have hnf : NotFree gs := hctx.cex.least.2.1
  have hcomp : Computes n gs o (F G A) := hctx.cex.least.2.2.1
  rw [hctx.hA] at hcomp
  have hst : G.Adj s t := (hctx.run.hs t).2 (Or.inr rfl)
  have hts : (t : ℕ) ≠ (s : ℕ) := fun h => hst.ne (Fin.ext h).symm
  have hqtT : vl gs (pt {t}) (n + qt) = true := or_true hcl hwt
  set D : Set ℕ := {(t : ℕ), n + qt} with hD
  have memD : ∀ j, j ∈ D ↔ j = t ∨ j = n + qt := fun j => by simp [hD]
  set x0 : Fin n → Bool := pt {s} with hx0
  set x1 : Fin n → Bool := pt {s, t} with hx1
  have hin : ∀ i : Fin n, (i : ℕ) ∉ D → x0 i = x1 i := by
    intro i hi
    have hit : i ≠ t := fun h => hi ((memD _).2 (Or.inl (by rw [h])))
    simp [hx0, hx1, pt, hit]
  -- a gate outside `D` that reads `D` is `G1` or `G2`
  have hgen : ∀ p g, gs[p]? = some g → n + p ∉ D →
      (∀ w ∈ g.inputs, w ∉ D) ∨ p = G1 ∨ p = G2 := by
    intro p g hp hpD
    by_cases hall : ∀ w ∈ g.inputs, w ∉ D
    · exact Or.inl hall
    right
    push_neg at hall
    obtain ⟨w, hw, hwD⟩ := hall
    rcases (memD w).1 hwD with rfl | rfl
    · have : p ∈ RdSet gs t := mem_rdSet.2 ⟨g, hp, hw⟩
      rw [hfan.ft, Finset.mem_singleton] at this
      exact absurd ((memD _).2 (Or.inr (by rw [this]))) hpD
    · have : p ∈ RdSet gs (n + qt) := mem_rdSet.2 ⟨g, hp, hw⟩
      rw [hrd] at this
      simpa using this
  -- shape of a quiet reader of `e_t`
  have quiet : ∀ Gi, Gi ∈ RdSet gs (n + qt) → vl gs (pt {t}) (n + Gi) = false →
      ∃ g y, gs[Gi]? = some g ∧ g.op = GateOp.and ∧ y ∈ g.inputs ∧ y < n + Gi ∧ y ∉ D ∧
        ∀ x : Fin n → Bool, vl gs x (n + Gi) = (vl gs x (n + qt) && vl gs x y) := by
    intro Gi hGi hq
    obtain ⟨g, hg, hw⟩ := mem_rdSet.1 hGi
    obtain ⟨y, hy, hsh⟩ := shape hcl hnf hg hw
    rcases hsh with ⟨hop, hv⟩ | ⟨_, hv⟩
    · have hyF : vl gs (pt {t}) y = false := by
        have := hv (pt {t}); rw [hq, hqtT] at this; simpa using this.symm
      refine ⟨g, y, hg, hop, hy, reads_lt hcl ⟨g, hg, hy⟩, ?_, hv⟩
      intro hyD
      rcases (memD y).1 hyD with rfl | rfl
      · rw [vl_in, pt_self] at hyF; exact absurd hyF (by simp)
      · rw [hqtT] at hyF; exact absurd hyF (by simp)
    · have := hv (pt {t}); rw [hq, hqtT] at this; simp at this
  -- a reader of `e_t` whose other operand is true at `e_s` reads `e_s`
  have finish : ∀ Gi g y, Gi ∈ RdSet gs (n + qt) → gs[Gi]? = some g → g.op = GateOp.and →
      y ∈ g.inputs → y < n + Gi → vl gs x0 y = true →
      ∃ q, q ∈ RdSet gs (n + qs) ∧ q ∈ RdSet gs (n + qt) := by
    intro Gi g y hGi hg hop hy hylt hyT
    have hGlen : Gi < gs.length := reads_len (mem_rdSet.1 hGi)
    by_cases hyn : y < n
    · exfalso
      have hy' : (⟨y, hyn⟩ : Fin n) = s := by
        rw [vl_input gs x0 y hyn] at hyT
        simpa [hx0, pt] using hyT
      have hR : Gi ∈ RdSet gs s := by
        refine mem_rdSet.2 ⟨g, hg, ?_⟩
        have : y = (s : ℕ) := by rw [← hy']
        rw [← this]; exact hy
      rw [hfan.fs, Finset.mem_singleton] at hR
      obtain ⟨g', hg', hop', _⟩ := hws
      rw [← hR, hg] at hg'
      cases hg'
      rw [hop] at hop'
      cases hop'
    · obtain ⟨p, rfl⟩ : ∃ p, y = n + p := ⟨y - n, by omega⟩
      have hplen : p < gs.length := by omega
      rcases hU n gs s qs ⟨hcl, hnf⟩ hfan.fs p hplen hyT with rfl | ⟨r, hr, hrT⟩
      · exact ⟨Gi, mem_rdSet.2 ⟨g, hg, hy⟩, hGi⟩
      · rw [hqs2 r hr] at hrT; exact absurd hrT (by simp)
  have hG1 : G1 ∈ RdSet gs (n + qt) := by rw [hrd]; simp
  have hG2 : G2 ∈ RdSet gs (n + qt) := by rw [hrd]; simp
  obtain ⟨g1, y1, hg1, hop1, hy1, hy1lt, hy1D, hv1⟩ := quiet G1 hG1 hq1
  obtain ⟨g2, y2, hg2, hop2, hy2, hy2lt, hy2D, hv2⟩ := quiet G2 hG2 hq2
  -- step 1: below `G2` every wire outside `D` agrees
  have ag2 : vl gs x0 y2 = vl gs x1 y2 := by
    refine hP n gs x0 x1 D (n + G2) hcl hin ?_ y2 hy2lt hy2D
    intro p g hp hpK hpD
    rcases hgen p g hp hpD with h | h | h
    · exact Or.inl h
    · omega
    · omega
  by_cases h2 : vl gs x0 y2 = true
  · exact finish G2 g2 y2 hG2 hg2 hop2 hy2 hy2lt h2
  have h2f : vl gs x0 y2 = false := by simpa using h2
  have agG2 : vl gs x0 (n + G2) = vl gs x1 (n + G2) := by
    rw [hv2, hv2, ← ag2, h2f]; simp
  -- step 2: below `G1` every wire outside `D` agrees
  have ag1 : vl gs x0 y1 = vl gs x1 y1 := by
    refine hP n gs x0 x1 D (n + G1) hcl hin ?_ y1 hy1lt hy1D
    intro p g hp hpK hpD
    rcases hgen p g hp hpD with h | h | h
    · exact Or.inl h
    · omega
    · subst h; exact Or.inr agG2
  by_cases h1 : vl gs x0 y1 = true
  · exact finish G1 g1 y1 hG1 hg1 hop1 hy1 hy1lt h1
  have h1f : vl gs x0 y1 = false := by simpa using h1
  have agG1 : vl gs x0 (n + G1) = vl gs x1 (n + G1) := by
    rw [hv1, hv1, ← ag1, h1f]; simp
  -- step 3: the output agrees, against `F(e_s) ≠ F(e_s + e_t)`
  exfalso
  have hoD : o ∉ D := by
    intro hoD
    have hF := hcomp (pt {t})
    rw [F_unit] at hF
    rcases (memD o).1 hoD with rfl | rfl
    · rw [vl_in, pt_self] at hF; exact absurd hF (by simp)
    · rw [hqtT] at hF; exact absurd hF (by simp)
  have ago : vl gs x0 o = vl gs x1 o := by
    refine hP n gs x0 x1 D (o + 1) hcl hin ?_ o (by omega) hoD
    intro p g hp hpK hpD
    rcases hgen p g hp hpD with h | h | h
    · exact Or.inl h
    · subst h; exact Or.inr agG1
    · subst h; exact Or.inr agG2
  rw [hcomp x0, hcomp x1, hx0, hx1, F_unit, F_edge G s t hst] at ago
  exact absurd ago (by simp)

/-- PIECE `PLast`, from `ToolProp` and `ToolU`. -/
theorem PLast_proof (hP : ToolProp) (hU : ToolU) : PLast := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt _ hqs2 hct hqt2
  obtain ⟨u, v, huv, hrd⟩ := Finset.card_eq_two.1 hct
  have hu : u ∈ RdSet gs (n + qt) := by rw [hrd]; simp
  have hv : v ∈ RdSet gs (n + qt) := by rw [hrd]; simp
  rcases lt_or_gt_of_ne huv with h | h
  · exact last_core hP hU hctx hfan hws hwt hqs2 v u h (by rw [hrd, Finset.pair_comm])
      (hqt2 v hv) (hqt2 u hu)
  · exact last_core hP hU hctx hfan hws hwt hqs2 u v h hrd (hqt2 u hu) (hqt2 v hv)

/-! ## Theorem FC -/

/-- A gate of a clean NOT-free list reading `w`: an AND or OR of `w` and one wire `y`. -/
theorem shape2 {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p : ℕ} {g : Gate}
    (hp : gs[p]? = some g) {w : ℕ} (hw : w ∈ g.inputs) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ y, y < m + p ∧ (g.inputs = [w, y] ∨ g.inputs = [y, w]) := by
  have hnot := hnf g (List.mem_of_getElem? hp)
  rcases hcl p g hp with ⟨h1, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd h1 hnot
  refine ⟨hop, ?_⟩
  rw [hin] at hw
  have hw' : w = j ∨ w = k := by simpa using hw
  rcases hw' with rfl | rfl
  · exact ⟨k, hk, Or.inl hin⟩
  · exact ⟨j, hj, Or.inr hin⟩

theorem val_and {m : ℕ} {hs : List Gate} (hcl : CleanL m hs) {p : ℕ} {g : Gate}
    (hp : hs[p]? = some g) (hop : g.op = GateOp.and) {w y : ℕ}
    (hin : g.inputs = [w, y] ∨ g.inputs = [y, w]) (x : Fin m → Bool) :
    vl hs x (m + p) = (vl hs x w && vl hs x y) := by
  rw [vl_gate hs hcl x p g hp, hop]
  rcases hin with hin | hin
  · rw [hin]; simp [GateOp.eval]
  · rw [hin]; simp [GateOp.eval, Bool.and_comm]

theorem val_or {m : ℕ} {hs : List Gate} (hcl : CleanL m hs) {p : ℕ} {g : Gate}
    (hp : hs[p]? = some g) (hop : g.op = GateOp.or) {w y : ℕ}
    (hin : g.inputs = [w, y] ∨ g.inputs = [y, w]) (x : Fin m → Bool) :
    vl hs x (m + p) = (vl hs x w || vl hs x y) := by
  rw [vl_gate hs hcl x p g hp, hop]
  rcases hin with hin | hin
  · rw [hin]; simp [GateOp.eval]
  · rw [hin]; simp [GateOp.eval, Bool.or_comm]

/-- A reader of `w` that is false at `e_v` while `w` is true there is an AND gate. -/
theorem quiet_and {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p : ℕ}
    {g : Gate} (hp : gs[p]? = some g) {w : ℕ} (hw : w ∈ g.inputs) (v : Fin m)
    (hwT : vl gs (pt {v}) w = true) (hq : vl gs (pt {v}) (m + p) = false) :
    g.op = GateOp.and ∧ ∃ y, y < m + p ∧ (g.inputs = [w, y] ∨ g.inputs = [y, w]) := by
  obtain ⟨hop, y, hy, hin⟩ := shape2 hcl hnf hp hw
  refine ⟨?_, y, hy, hin⟩
  rcases hop with h | h
  · exact h
  · have := val_or hcl hp h hin (pt {v})
    rw [hq, hwT] at this
    simp at this

theorem other_eq {g : Gate} {w y w' : ℕ} (hin : g.inputs = [w, y] ∨ g.inputs = [y, w])
    (h : w' ∈ g.inputs) (hne : w' ≠ w) : w' = y := by
  rcases hin with hin | hin <;> rw [hin] at h <;> simp at h <;> tauto

theorem other_of_two {S : Finset ℕ} (h : S.card = 2) {q : ℕ} (hq : q ∈ S) :
    ∃ r, r ≠ q ∧ S = {q, r} := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact ⟨v, huv.symm, rfl⟩
  · exact ⟨u, huv, Finset.pair_comm _ _⟩

/-- A function with prescribed values at distinct points. -/
theorem exists_fun (L : List (ℕ × ℕ)) (hnd : (L.map Prod.fst).Nodup) :
    ∃ f : ℕ → ℕ, ∀ pr ∈ L, f pr.1 = pr.2 := by
  induction L with
  | nil => exact ⟨id, by simp⟩
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨f, hf⟩ := ih hnd.2
    refine ⟨fun p => if p = hd.1 then hd.2 else f p, ?_⟩
    intro pr hpr
    rcases List.mem_cons.1 hpr with rfl | hpr
    · simp
    · have hne : pr.1 ≠ hd.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hpr)
      simp only [hne, if_false]
      exact hf pr hpr

/-- A set of aliases with listed targets is removable. -/
theorem rem_list {m : ℕ} {gs : List Gate} {o : ℕ} {P : Set (Fin m → Bool)} (L : List (ℕ × ℕ))
    (hnd : (L.map Prod.fst).Nodup)
    (h : ∀ pr ∈ L, pr.1 < gs.length ∧ pr.2 < m + pr.1 ∧
      ∀ x ∈ P, vl gs x (m + pr.1) = vl gs x pr.2) :
    ∃ tgt : ℕ → Option ℕ, Removable m gs o P (L.map Prod.fst).toFinset tgt ∧
      ∀ p, tgt p ≠ none := by
  obtain ⟨f, hf⟩ := exists_fun L hnd
  refine ⟨fun p => some (f p), ?_, fun p => by simp⟩
  intro p hp
  rw [List.mem_toFinset, List.mem_map] at hp
  obtain ⟨pr, hpr, rfl⟩ := hp
  obtain ⟨h1, h2, h3⟩ := h pr hpr
  refine ⟨h1, Or.inl ⟨f pr.1, rfl, ?_, ?_⟩⟩
  · rw [hf pr hpr]; exact h2
  · rw [hf pr hpr]; exact h3

theorem card_list {L : List (ℕ × ℕ)} (hnd : (L.map Prod.fst).Nodup) :
    (L.map Prod.fst).toFinset.card = L.length := by
  rw [List.toFinset_card_of_nodup hnd, List.length_map]

/-- PIECE `PFC`: the planner's three cases (section D of the plan note). -/
theorem PFC_proof (hRem : ToolRemoval) (hLow : ToolLower) (hSnoc : ToolSnoc)
    (h1a : ToolLemma1a) (hPay : ToolPayPair) (hLive : ToolLive) (hNA : ToolNoAlias)
    (hCons : ToolCons) : PFC := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt q hctx hfan hws hwt hcs hqs2 hct hqt2 hq1 hq2
  have hcl : CleanL n gs := hctx.cex.least.1
  have hnf : NotFree gs := hctx.cex.least.2.1
  have hcomp : Computes n gs o (F G A) := hctx.cex.least.2.2.1
  have hinv : AFree G A := hctx.cex.inv
  have hst : G.Adj s t := (hctx.run.hs t).2 (Or.inr rfl)
  have hd1 : qs ≠ qt := (hCons n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt).1
  have hA : A = ∅ := hctx.hA
  have hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y :=
    ⟨pt {s}, pt {s, t}, by rw [hA, F_unit, F_edge G s t hst]; simp⟩
  have hoLen : o < n + gs.length := (hLive n _ gs o hctx.cex.least hnc).1
  have hLiv := (hLive n _ gs o hctx.cex.least hnc).2
  -- the five gates
  obtain ⟨Gas, hGasq, hRs⟩ := other_of_two hcs hq1
  obtain ⟨Gtb, hGtbq, hRt⟩ := other_of_two hct hq2
  have hGas : Gas ∈ RdSet gs (n + qs) := by rw [hRs]; simp
  have hGtb : Gtb ∈ RdSet gs (n + qt) := by rw [hRt]; simp
  have hqsT := or_true hcl hws
  have hqtT := or_true hcl hwt
  obtain ⟨gq, hgq, hwq⟩ := mem_rdSet.1 hq2
  obtain ⟨hopq, yq, _, hinq⟩ := quiet_and hcl hnf hgq hwq t hqtT (hqt2 q hq2)
  obtain ⟨gtb, hgtb, hwtb⟩ := mem_rdSet.1 hGtb
  obtain ⟨hoptb, y, hylt, hintb⟩ := quiet_and hcl hnf hgtb hwtb t hqtT (hqt2 Gtb hGtb)
  obtain ⟨gas, hgas, hwas⟩ := mem_rdSet.1 hGas
  obtain ⟨hopas, u, _, hinas⟩ := quiet_and hcl hnf hgas hwas s hqsT (hqs2 Gas hGas)
  obtain ⟨gqs, hgqs, hopqs, hinqs⟩ := id hws
  obtain ⟨gqt, hgqt, hopqt, hinqt⟩ := id hwt
  have hwsq : n + qs ∈ gq.inputs := by
    obtain ⟨g', hg', hw'⟩ := mem_rdSet.1 hq1
    rw [hgq] at hg'; cases hg'; exact hw'
  have hyq : n + qs = yq := other_eq hinq hwsq (by omega)
  rw [← hyq] at hinq
  -- order
  have o1 : n + qs < n + q := reads_lt hcl ⟨gq, hgq, hwsq⟩
  have o2 : n + qt < n + q := reads_lt hcl ⟨gq, hgq, hwq⟩
  have o3 : n + qt < n + Gtb := reads_lt hcl ⟨gtb, hgtb, hwtb⟩
  have o4 : n + qs < n + Gas := reads_lt hcl ⟨gas, hgas, hwas⟩
  have hwslt : ws < n + qs := by
    refine reads_lt hcl ⟨gqs, hgqs, ?_⟩
    rcases hinqs with h | h <;> rw [h] <;> simp
  have hd9 : qs ≠ Gtb := by
    intro h; rw [h, hgtb] at hgqs; cases hgqs; rw [hoptb] at hopqs; cases hopqs
  have hd10 : qt ≠ Gas := by
    intro h; rw [h, hgas] at hgqt; cases hgqt; rw [hopas] at hopqt; cases hopqt
  have hd8 : Gtb ≠ Gas := by
    intro h
    subst h
    rw [hgtb] at hgas; cases hgas
    have hy' : n + qs = y := other_eq hintb hwas (by omega)
    rw [← hy'] at hintb
    have e1 := val_and hcl hgq hopq hinq
    have e2 := val_and hcl hgtb hoptb hintb
    rcases lt_or_gt_of_ne hGtbq with h | h
    · exact hNA n _ gs o hctx.cex.least hnc q (reads_len ⟨gq, hgq, hwq⟩) (n + Gtb) (by omega)
        (fun x => by rw [e1, e2])
    · exact hNA n _ gs o hctx.cex.least hnc Gtb (reads_len ⟨gtb, hgtb, hwtb⟩) (n + q)
        (by omega) (fun x => by rw [e1, e2])
  have lq : q < gs.length := reads_len ⟨gq, hgq, hwq⟩
  have n12 : qs ≠ qt := hd1
  have n13 : qs ≠ q := by omega
  have n14 : qs ≠ Gtb := hd9
  have n15 : qs ≠ Gas := by omega
  have n23 : qt ≠ q := by omega
  have n24 : qt ≠ Gtb := by omega
  have n25 : qt ≠ Gas := hd10
  have n34 : q ≠ Gtb := hGtbq.symm
  have n35 : q ≠ Gas := hGasq.symm
  have n45 : Gtb ≠ Gas := hd8
  have ltb : Gtb < gs.length := reads_len ⟨gtb, hgtb, hwtb⟩
  have las : Gas < gs.length := reads_len ⟨gas, hgas, hwas⟩
  have lqs : qs < gs.length := by omega
  have lqt : qt < gs.length := by omega
  -- the subcube and the local values
  set P : Set (Fin n → Bool) := {x | x t = true ∧ x s = false} with hP
  have loc : ∀ hs : List Gate, CleanL n hs → hs[qs]? = some gqs → hs[qt]? = some gqt →
      hs[q]? = some gq → hs[Gtb]? = some gtb → ∀ x ∈ P,
        vl hs x (n + qs) = vl hs x ws ∧ vl hs x (n + qt) = vl hs x t ∧
        vl hs x (n + q) = vl hs x (n + qs) ∧ vl hs x (n + Gtb) = vl hs x y := by
    intro hs hcs' e1 e2 e3 e4 x hx
    have hxt : vl hs x t = true := by rw [vl_in]; exact hx.1
    have hxs : vl hs x s = false := by rw [vl_in]; exact hx.2
    have v1 := val_or hcs' e1 hopqs hinqs x
    have v2 := val_or hcs' e2 hopqt hinqt x
    have v3 := val_and hcs' e3 hopq hinq x
    have v4 := val_and hcs' e4 hoptb hintb x
    rw [hxs, Bool.false_or] at v1
    rw [hxt, Bool.true_or] at v2
    rw [v2, Bool.true_and] at v3 v4
    exact ⟨v1, v2.trans hxt.symm, v3, v4⟩
  have locg := loc gs hcl hgqs hgqt hgq hgtb
  have hL1 : ∀ x ∈ P, vl gs x ws = true → vl gs x o = true := by
    intro x hx hw
    rw [hcomp x]
    by_contra hF
    have := h1a n G A gs o s t qs ws hinv hcl hcomp hfan.fs hws hst x hx.1 (by simpa using hF)
    rw [hw] at this; exact absurd this (by simp)
  have pay : ∀ (gs' : List Gate) (o' : ℕ), MClean n gs' → gs'.length + 5 ≤ gs.length →
      (∀ x ∈ P, vl gs' x o' = vl gs x o) → False := by
    intro gs' o' hm hl hv
    exact hPay n G A gs o a' a s t b b' gs' o' hctx.cex hctx.run hm hl
      (fun x hxt hxs => by rw [hv x ⟨hxt, hxs⟩, hcomp x])
  have nd4 : ∀ (j1 j2 j3 j4 : ℕ), ([(qs, j1), (qt, j2), (q, j3), (Gtb, j4)].map Prod.fst).Nodup := by
    intro j1 j2 j3 j4
    simp [List.nodup_cons, n12, n13, n14, n23, n24, n34]
  -- the four aliases (in any list with the same four gates)
  have al4 : ∀ hs : List Gate, CleanL n hs → hs.length = gs.length → hs[qs]? = some gqs →
      hs[qt]? = some gqt → hs[q]? = some gq → hs[Gtb]? = some gtb →
      ∀ pr ∈ [(qs, ws), (qt, (t : ℕ)), (q, n + qs), (Gtb, y)], pr.1 < hs.length ∧
        pr.2 < n + pr.1 ∧ ∀ x ∈ P, vl hs x (n + pr.1) = vl hs x pr.2 := by
    intro hs hcs' hlen e1 e2 e3 e4 pr hpr
    have lc := loc hs hcs' e1 e2 e3 e4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl
    · exact ⟨by omega, hwslt, fun x hx => (lc x hx).1⟩
    · exact ⟨by omega, by have := t.isLt; simp; omega, fun x hx => (lc x hx).2.1⟩
    · exact ⟨by omega, o1, fun x hx => (lc x hx).2.2.1⟩
    · exact ⟨by omega, hylt, fun x hx => (lc x hx).2.2.2⟩
  by_cases c1 : o = n + Gas ∨ (y = n + Gas ∧ o = n + Gtb)
  · -- case (1): `G_as` is an alias of `w_s` on the subcube
    have hGasA : ∀ x ∈ P, vl gs x (n + Gas) = vl gs x ws := by
      intro x hx
      have hv := val_and hcl hgas hopas hinas x
      rw [(locg x hx).1] at hv
      cases hw : vl gs x ws
      · rw [hv, hw]; simp
      · have hoT := hL1 x hx hw
        rcases c1 with h | ⟨hy, h⟩
        · rw [← h]; exact hoT
        · rw [h, val_and hcl hgtb hoptb hintb x, hy] at hoT
          simp only [Bool.and_eq_true] at hoT
          exact hoT.2
    set L : List (ℕ × ℕ) := [(qs, ws), (qt, (t : ℕ)), (q, n + qs), (Gtb, y), (Gas, ws)] with hL
    have hnd : (L.map Prod.fst).Nodup := by
      simp [hL, List.nodup_cons, n12, n13, n14, n15, n23, n24, n25, n34, n35, n45]
    have hal : ∀ pr ∈ L, pr.1 < gs.length ∧ pr.2 < n + pr.1 ∧
        ∀ x ∈ P, vl gs x (n + pr.1) = vl gs x pr.2 := by
      intro pr hpr
      rw [hL, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact al4 gs hcl rfl hgqs hgqt hgq hgtb _ (by simp)
      have hpr' : pr ∈ [(qt, (t : ℕ)), (q, n + qs), (Gtb, y)] ++ [(Gas, ws)] := by simpa using hpr
      rcases List.mem_append.1 hpr' with h | h
      · exact al4 gs hcl rfl hgqs hgqt hgq hgtb _ (List.mem_cons_of_mem _ h)
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨las, by omega, hGasA⟩
    obtain ⟨tgt, hrem, hnn⟩ := rem_list (o := o) (P := P) L hnd hal
    obtain ⟨gs', r, hcl', hnf', hlen', _, hr⟩ := hRem n gs o P _ tgt hcl hrem
    rw [card_list hnd] at hlen'
    obtain ⟨_, hro⟩ := hr o hoLen (fun p _ h => absurd h (hnn p))
    exact pay gs' (r o) ⟨hcl', hnf' hnf⟩ (by simp [hL] at hlen'; omega) hro
  by_cases c2 : ∃ R, R ∉ [qs, qt, q, Gtb, Gas] ∧
      (Reads gs R (n + Gas) ∨ (y = n + Gas ∧ Reads gs R (n + Gtb)))
  · -- case (2): lower `G_as`, six aliases, one OR added
    obtain ⟨R, hRn, hRr⟩ := c2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hRn
    obtain ⟨r1, r2, r3, r4, r5⟩ := hRn
    have hlow := hLow n gs o P s Gas ws ⟨hcl, hnf⟩ las (by omega) (fun x hx => hx.2)
      (fun x hx h => by
        rw [val_and hcl hgas hopas hinas x, (locg x hx).1] at h
        simp only [Bool.and_eq_true] at h
        exact h.1)
      hL1
    set gs1 := gs.set Gas ⟨GateOp.and, [(s : ℕ), (s : ℕ)]⟩ with hgs1
    obtain ⟨⟨hcl1, hnf1⟩, hval1, hpre1⟩ := hlow
    have hlen1 : gs1.length = gs.length := by simp [hgs1]
    have same : ∀ p, p ≠ Gas → gs1[p]? = gs[p]? := by
      intro p hp; simp [hgs1, List.getElem?_set, Ne.symm hp]
    have e1 := same qs (by omega)
    have e2 := same qt hd10
    have e3 := same q hGasq.symm
    have e4 := same Gtb hd8
    rw [hgqs] at e1; rw [hgqt] at e2; rw [hgq] at e3; rw [hgtb] at e4
    have lc1 := loc gs1 hcl1 e1 e2 e3 e4
    have hGas1 : ∀ x ∈ P, vl gs1 x (n + Gas) = false := by
      intro x hx
      have hg : gs1[Gas]? = some ⟨GateOp.and, [(s : ℕ), (s : ℕ)]⟩ := by
        simp [hgs1, List.getElem?_set, las]
      rw [val_and hcl1 hg rfl (Or.inl rfl) x, vl_in, hx.2]; rfl
    -- `R` is an alias in `gs1`
    obtain ⟨gR, hgR, w0, hw0, hw0F⟩ : ∃ gR, gs[R]? = some gR ∧ ∃ w0, w0 ∈ gR.inputs ∧
        ∀ x ∈ P, vl gs1 x w0 = false := by
      rcases hRr with ⟨gR, hgR, hw⟩ | ⟨hy, gR, hgR, hw⟩
      · exact ⟨gR, hgR, _, hw, hGas1⟩
      · refine ⟨gR, hgR, _, hw, fun x hx => ?_⟩
        rw [(lc1 x hx).2.2.2, hy]; exact hGas1 x hx
    have eR := same R r5
    rw [hgR] at eR
    have hRlen : R < gs.length := reads_len ⟨gR, hgR, hw0⟩
    obtain ⟨jR, hjR, hRA⟩ : ∃ jR, jR < n + R ∧ ∀ x ∈ P, vl gs1 x (n + R) = vl gs1 x jR := by
      obtain ⟨hop, v, hv, hin⟩ := shape2 hcl1 hnf1 eR hw0
      rcases hop with h | h
      · refine ⟨s, by have := s.isLt; omega, fun x hx => ?_⟩
        rw [val_and hcl1 eR h hin x, hw0F x hx, vl_in, hx.2]; rfl
      · refine ⟨v, hv, fun x hx => ?_⟩
        rw [val_or hcl1 eR h hin x, hw0F x hx, Bool.false_or]
    set L : List (ℕ × ℕ) :=
      [(qs, ws), (qt, (t : ℕ)), (q, n + qs), (Gtb, y), (Gas, (s : ℕ)), (R, jR)] with hL
    have hnd : (L.map Prod.fst).Nodup := by
      simp [hL, List.nodup_cons, n12, n13, n14, n15, n23, n24, n25, n34, n35, n45, Ne.symm r1,
        Ne.symm r2, Ne.symm r3, Ne.symm r4, Ne.symm r5]
    have hal : ∀ pr ∈ L, pr.1 < gs1.length ∧ pr.2 < n + pr.1 ∧
        ∀ x ∈ P, vl gs1 x (n + pr.1) = vl gs1 x pr.2 := by
      intro pr hpr
      have hpr' : pr ∈ [(qs, ws), (qt, (t : ℕ)), (q, n + qs), (Gtb, y)] ++
          [(Gas, (s : ℕ)), (R, jR)] := by simpa [hL] using hpr
      rcases List.mem_append.1 hpr' with h | h
      · exact al4 gs1 hcl1 hlen1 e1 e2 e3 e4 _ h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · refine ⟨by omega, by have := s.isLt; simp; omega, fun x hx => ?_⟩
          rw [hGas1 x hx, vl_in, hx.2]
        · exact ⟨by omega, hjR, hRA⟩
    obtain ⟨tgt, hrem, hnn⟩ := rem_list (o := o) (P := P) L hnd hal
    obtain ⟨gs2, r, hcl2, hnf2, hlen2, _, hr⟩ := hRem n gs1 o P _ tgt hcl1 hrem
    rw [card_list hnd] at hlen2
    obtain ⟨hro1, hro⟩ := hr o (by omega) (fun p _ h => absurd h (hnn p))
    obtain ⟨hrw1, hrw⟩ := hr ws (by omega) (fun p _ h => absurd h (hnn p))
    obtain ⟨hm3, hv3⟩ := hSnoc n gs2 (r o) (r ws) ⟨hcl2, hnf2 hnf1⟩ hro1 hrw1
    refine pay _ (n + gs2.length) hm3 (by simp [hL] at hlen2; simp; omega) (fun x hx => ?_)
    rw [(hv3 x).1, hro x hx, hrw x hx, hpre1 x ws (by omega), hval1 x hx]
  · -- case (3): `G_as` is an orphan
    have nc1 : o ≠ n + Gas := fun h => c1 (Or.inl h)
    have nc2 : ∀ R, Reads gs R (n + Gas) → R ∈ [qs, qt, q, Gtb, Gas] := by
      intro R h; by_contra hn; exact c2 ⟨R, hn, Or.inl h⟩
    have hyG : y ≠ n + Gas := by
      intro hy
      have nc3 : ∀ R, Reads gs R (n + Gtb) → R ∈ [qs, qt, q, Gtb, Gas] := by
        intro R h; by_contra hn; exact c2 ⟨R, hn, Or.inr ⟨hy, h⟩⟩
      obtain ⟨R, hR⟩ := hLiv Gtb ltb (fun h => c1 (Or.inr ⟨hy, h⟩))
      have hRr := mem_rdSet.1 hR
      have hlt := reads_lt hcl hRr
      have hRm := nc3 R hRr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hRm
      rcases hRm with rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · obtain ⟨g', hg', hw'⟩ := hRr
        rw [hgq] at hg'; cases hg'
        rcases hinq with h | h <;> rw [h] at hw' <;> simp at hw' <;> omega
      · omega
      · omega
    obtain ⟨f, hf⟩ := exists_fun _ (nd4 ws t (n + qs) y)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hf
    obtain ⟨f1, f2, f3, f4⟩ := hf
    set S : Finset ℕ := ([qs, qt, q, Gtb, Gas] : List ℕ).toFinset with hS
    have hal := al4 gs hcl rfl hgqs hgqt hgq hgtb
    let tgt : ℕ → Option ℕ := fun p => if p = Gas then none else some (f p)
    have hrem : Removable n gs o P S tgt := by
      intro p hp
      rw [hS, List.mem_toFinset] at hp
      have hp' := hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨h1, h2, h3⟩ := hal (p, ws) (by simp)
        refine ⟨h1, Or.inl ⟨ws, ?_, h2, h3⟩⟩
        simp only [tgt, if_neg (show p ≠ Gas by omega), f1]
      · obtain ⟨h1, h2, h3⟩ := hal (p, t) (by simp)
        refine ⟨h1, Or.inl ⟨t, ?_, h2, h3⟩⟩
        simp only [tgt, if_neg hd10, f2]
      · obtain ⟨h1, h2, h3⟩ := hal (p, n + qs) (by simp)
        refine ⟨h1, Or.inl ⟨n + qs, ?_, h2, h3⟩⟩
        simp only [tgt, if_neg hGasq.symm, f3]
      · obtain ⟨h1, h2, h3⟩ := hal (p, y) (by simp)
        refine ⟨h1, Or.inl ⟨y, ?_, h2, h3⟩⟩
        simp only [tgt, if_neg hd8, f4]
      · refine ⟨las, Or.inr ⟨by simp [tgt], nc1, fun R h => ?_, fun p' hp'' => ?_⟩⟩
        · rw [hS, List.mem_toFinset]; exact nc2 R h
        · rw [hS, List.mem_toFinset] at hp''
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp''
          have ht := t.isLt
          rcases hp'' with rfl | rfl | rfl | rfl | rfl
          · simp only [tgt, if_neg (show p' ≠ p by omega), f1]; simp; omega
          · simp only [tgt, if_neg hd10, f2]; simp; omega
          · simp only [tgt, if_neg hGasq.symm, f3]; simp; omega
          · simp only [tgt, if_neg hd8, f4]; simpa using hyG
          · simp [tgt]
    have hcardS : S.card = 5 := by
      rw [hS, List.toFinset_card_of_nodup]
      · rfl
      · simp [List.nodup_cons, n12, n13, n14, n15, n23, n24, n25, n34, n35, n45]
    obtain ⟨gs', r, hcl', hnf', hlen', _, hr⟩ := hRem n gs o P S tgt hcl hrem
    obtain ⟨_, hro⟩ := hr o hoLen (fun p hp h => by
      by_cases hpg : p = Gas
      · rw [hpg]; exact nc1
      · simp [tgt, hpg] at h)
    exact pay gs' (r o) ⟨hcl', hnf' hnf⟩ (by omega) hro

end PEqualNP.MetaComplexity.Loc.Last
