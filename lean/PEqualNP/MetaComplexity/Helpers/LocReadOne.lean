import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class: the cells B1-AND and B1-OR (a single reader of `e_t`)

Proofs of the pieces `PReadOneAnd` and `PReadOneOr` of `LocPlan.lean`, from the tools
`ToolProp`, `ToolMono`, `ToolCons`, `ToolPay1`, `ToolRemoval`, `ToolLive` and `ToolNoAlias`
(taken as hypotheses).

Paper: `routes/lifting/lgp/FO1-monotone-direct.md`, section 5, cells B1, B1-AND, B1-OR and the
SHORTCUT. Route. Both cells reach an AND gate `q = AND(c, y)` through which alone `x_t` reaches
the output (`q = r` in B1-AND; `q` the reader of `r = OR(e_t, z)` in B1-OR, the other shapes
paying at `x_t := 1`). Then `flip` gives `y(e_s) = y(e_b) = 1` (if `y` were false at `e_s`, the
output would agree at `e_s` and `e_s + e_t`), and `finish` closes: a reader of `e_s` other than
`y` makes `s` pay at `x_s := 1`; otherwise `y` is the only reader of `e_s` and, on `x_b = 1`,
the output ignores `x_s`, against `F(e_a + e_s + e_b) = 1`, `F(e_a + e_b) = 0`.
-/

namespace PEqualNP.MetaComplexity.Loc.ReadOne

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc
open SimpleGraph

/-! ## Gate shapes -/

theorem vl_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) : vl gs x (i : ℕ) = x i :=
  vl_input gs x i i.isLt

theorem andRd_val {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) {q c y : ℕ} (h : AndRd gs q c y)
    (x : Fin n → Bool) : vl gs x (n + q) = (vl gs x c && vl gs x y) := by
  obtain ⟨g, hg, hop, hin⟩ := h
  rw [vl_gate gs hcl x q g hg, hop]
  rcases hin with hin | hin <;> rw [hin] <;> simp [GateOp.eval, Bool.and_comm]

theorem orRd_val {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) {q c y : ℕ} (h : OrRd gs q c y)
    (x : Fin n → Bool) : vl gs x (n + q) = (vl gs x c || vl gs x y) := by
  obtain ⟨g, hg, hop, hin⟩ := h
  rw [vl_gate gs hcl x q g hg, hop]
  rcases hin with hin | hin <;> rw [hin] <;> simp [GateOp.eval, Bool.or_comm]

theorem andRd_lt {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) {q c y : ℕ} (h : AndRd gs q c y) :
    c < n + q ∧ y < n + q ∧ Reads gs q c ∧ Reads gs q y := by
  obtain ⟨g, hg, _, hin⟩ := h
  have hc : c ∈ g.inputs := by rcases hin with hin | hin <;> simp [hin]
  have hy : y ∈ g.inputs := by rcases hin with hin | hin <;> simp [hin]
  exact ⟨(hcl q g hg).lt c hc, (hcl q g hg).lt y hy, ⟨g, hg, hc⟩, ⟨g, hg, hy⟩⟩

theorem orRd_lt {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) {q c y : ℕ} (h : OrRd gs q c y) :
    c < n + q ∧ y < n + q ∧ Reads gs q c ∧ Reads gs q y := by
  obtain ⟨g, hg, _, hin⟩ := h
  have hc : c ∈ g.inputs := by rcases hin with hin | hin <;> simp [hin]
  have hy : y ∈ g.inputs := by rcases hin with hin | hin <;> simp [hin]
  exact ⟨(hcl q g hg).lt c hc, (hcl q g hg).lt y hy, ⟨g, hg, hc⟩, ⟨g, hg, hy⟩⟩

/-- A wire read by `AND(c, y)` is `c` or `y`. -/
theorem reads_and {gs : List Gate} {q c y w : ℕ} (h : AndRd gs q c y) (hr : Reads gs q w) :
    w = c ∨ w = y := by
  obtain ⟨g, hg, _, hin⟩ := h
  obtain ⟨g', hg', hw⟩ := hr
  rw [hg] at hg'
  cases hg'
  rcases hin with hin | hin <;> rw [hin] at hw <;> simp at hw <;> tauto

theorem not_orRd {gs : List Gate} {q : ℕ} {g : Gate} (hg : gs[q]? = some g)
    (hop : g.op = GateOp.and) (c w : ℕ) : ¬ OrRd gs q c w := by
  rintro ⟨g', hg', hop', _⟩
  rw [hg] at hg'
  cases hg'
  rw [hop] at hop'
  cases hop'

theorem not_andRd {gs : List Gate} {q : ℕ} {g : Gate} (hg : gs[q]? = some g)
    (hop : g.op = GateOp.or) (c w : ℕ) : ¬ AndRd gs q c w := by
  rintro ⟨g', hg', hop', _⟩
  rw [hg] at hg'
  cases hg'
  rw [hop] at hop'
  cases hop'

theorem and_ne_or {gs : List Gate} {q q' c y c' w : ℕ} (h : AndRd gs q c y)
    (h' : OrRd gs q' c' w) : q ≠ q' := by
  rintro rfl
  obtain ⟨g, hg, hop, _⟩ := h
  exact not_orRd hg hop c' w h'

/-- A gate of a clean NOT-free list reading `w` is `AND(w, w')` or `OR(w, w')`. -/
theorem rd_shape {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) (hnf : NotFree gs) {q w : ℕ}
    (h : Reads gs q w) : ∃ w', AndRd gs q w w' ∨ OrRd gs q w w' := by
  obtain ⟨g, hg, hw⟩ := h
  rcases hcl q g hg with ⟨hnot, _⟩ | ⟨hop, j, k, _, _, hin⟩
  · exact absurd hnot (hnf g (List.mem_of_getElem? hg))
  · rw [hin] at hw
    simp at hw
    rcases hw with rfl | rfl <;> rcases hop with hop | hop
    · exact ⟨k, Or.inl ⟨g, hg, hop, Or.inl hin⟩⟩
    · exact ⟨k, Or.inr ⟨g, hg, hop, Or.inl hin⟩⟩
    · exact ⟨j, Or.inl ⟨g, hg, hop, Or.inr hin⟩⟩
    · exact ⟨j, Or.inr ⟨g, hg, hop, Or.inr hin⟩⟩

theorem or_true {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) {q c w : ℕ} (h : OrRd gs q c w)
    (x : Fin n → Bool) (hc : vl gs x c = true) : vl gs x (n + q) = true := by
  rw [orRd_val hcl h x, hc, Bool.true_or]

/-- A gate reading a wire that is true on `{x_v = 1}` is an alias there of an earlier wire. -/
theorem reader_alias {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) (hnf : NotFree gs) (v : Fin n)
    {q w : ℕ} (h : Reads gs q w) (hw : ∀ x : Fin n → Bool, x v = true → vl gs x w = true) :
    ∃ j, j < n + q ∧ ∀ x : Fin n → Bool, x v = true → vl gs x (n + q) = vl gs x j := by
  obtain ⟨w', hs | hs⟩ := rd_shape hcl hnf h
  · refine ⟨w', (andRd_lt hcl hs).2.1, fun x hx => ?_⟩
    rw [andRd_val hcl hs x, hw x hx, Bool.true_and]
  · have := v.isLt
    refine ⟨v, by omega, fun x hx => ?_⟩
    rw [orRd_val hcl hs x, hw x hx, Bool.true_or, vl_in, hx]

/-- A gate true on `{x_v = 1}` is an alias there of the input wire `v`. -/
theorem true_alias {n : ℕ} {gs : List Gate} (v : Fin n) (p : ℕ)
    (h : ∀ x : Fin n → Bool, x v = true → vl gs x (n + p) = true) :
    ∃ j, j < n + p ∧ ∀ x : Fin n → Bool, x v = true → vl gs x (n + p) = vl gs x j := by
  have := v.isLt
  exact ⟨v, by omega, fun x hx => by rw [h x hx, vl_in, hx]⟩

/-! ## The function at unit points -/

theorem F_pt {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    F G ∅ (pt S) = true ↔ ∃ i j, G.Adj i j ∧ i ∈ S ∧ j ∈ S := by
  rw [F_true]
  simp [pt]

theorem F_single {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : F G ∅ (pt {v}) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨i, j, hij, hi, hj⟩ := (F_pt G _).1 h
  simp at hi hj
  subst hi
  subst hj
  exact G.irrefl hij

theorem F_edge {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u v : Fin n)
    (h : G.Adj u v) (hu : u ∈ S) (hv : v ∈ S) : F G ∅ (pt S) = true :=
  (F_pt G S).2 ⟨u, v, h, hu, hv⟩

theorem F_nonadj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (hn : ¬ G.Adj u v) :
    F G ∅ (pt {u, v}) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨i, j, hij, hi, hj⟩ := (F_pt G _).1 h
  simp at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact G.irrefl hij
  · exact hn hij
  · exact hn hij.symm
  · exact G.irrefl hij

theorem run_ne {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') :
    a ≠ s ∧ a ≠ b ∧ s ≠ t ∧ s ≠ b ∧ t ≠ b ∧ a' ≠ b ∧ a ≠ t := by
  have nd := h.nd
  simp [List.nodup_cons] at nd
  tauto

/-! ## Paying at a deep vertex with four aliases -/

/-- Four distinct gates, each an alias of an earlier wire on `{x_v = 1}` with `v` deep: the
removal tool gives a list four gates shorter computing `F` there, which `ToolPay1` forbids. -/
theorem pay1_four (hRem : ToolRemoval) (hPay : ToolPay1) (hLive : ToolLive) {n : ℕ}
    {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ} (hc : Cex G A gs o)
    (hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y) (v : Fin n) (hd : Deep G v)
    (p1 p2 p3 p4 j1 j2 j3 j4 : ℕ) (hnd : [p1, p2, p3, p4].Nodup)
    (l1 : p1 < gs.length) (l2 : p2 < gs.length) (l3 : p3 < gs.length) (l4 : p4 < gs.length)
    (h1 : j1 < n + p1 ∧ ∀ x : Fin n → Bool, x v = true → vl gs x (n + p1) = vl gs x j1)
    (h2 : j2 < n + p2 ∧ ∀ x : Fin n → Bool, x v = true → vl gs x (n + p2) = vl gs x j2)
    (h3 : j3 < n + p3 ∧ ∀ x : Fin n → Bool, x v = true → vl gs x (n + p3) = vl gs x j3)
    (h4 : j4 < n + p4 ∧ ∀ x : Fin n → Bool, x v = true → vl gs x (n + p4) = vl gs x j4) :
    False := by
  classical
  have nd := hnd
  simp [List.nodup_cons] at nd
  obtain ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := nd
  let tgt : ℕ → Option ℕ := fun p =>
    if p = p1 then some j1 else if p = p2 then some j2 else if p = p3 then some j3 else some j4
  let S : Finset ℕ := [p1, p2, p3, p4].toFinset
  have hS : S.card = 4 := List.toFinset_card_of_nodup hnd
  have hR : Removable n gs o {x | x v = true} S tgt := by
    intro p hp
    simp only [S, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨l1, Or.inl ⟨j1, by simp [tgt], h1.1, h1.2⟩⟩
    · exact ⟨l2, Or.inl ⟨j2, by simp [tgt, Ne.symm h12], h2.1, h2.2⟩⟩
    · exact ⟨l3, Or.inl ⟨j3, by simp [tgt, Ne.symm h13, Ne.symm h23], h3.1, h3.2⟩⟩
    · exact ⟨l4, Or.inl ⟨j4, by simp [tgt, Ne.symm h14, Ne.symm h24, Ne.symm h34], h4.1,
        h4.2⟩⟩
  obtain ⟨gs', r, hcl', hnf', hlen, -, hr⟩ := hRem n gs o {x | x v = true} S tgt hc.least.1 hR
  have hl := hLive n (F G A) gs o hc.least hnc
  obtain ⟨-, hro⟩ := hr o hl.1 (fun p _ h => by
    simp only [tgt] at h
    split_ifs at h)
  exact hPay n G A gs o v gs' (r o) hc hd ⟨hcl', hnf' hc.least.2.1⟩ (by omega)
    (fun x hx => by rw [hro x hx]; exact hc.least.2.2.1 x)

/-! ## The flip and the shortcut -/

/-- `q = AND(c, y)` is the only gate outside the wire set `D` that reads `D`, `D` holds the
input `t`, and `y`, `q` and the output lie outside `D`. If `x`, `x'` differ only at `t` and the
function differs at them, then `y` is true at `x`: else `q` is false at both points, and every
wire outside `D` agrees. -/
theorem flip (hProp : ToolProp) {n : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin n → Bool) → Bool}
    (hcl : CleanL n gs) (hcomp : Computes n gs o f) (D : Set ℕ) (t : Fin n) (q c y : ℕ)
    (hq : AndRd gs q c y) (htD : (t : ℕ) ∈ D) (hqD : n + q ∉ D) (hyD : y ∉ D)
    (hrd : ∀ p g, gs[p]? = some g → n + p ∉ D → (∃ w ∈ g.inputs, w ∈ D) → p = q)
    (ho : o ∉ D) (hoL : o < n + gs.length) (x x' : Fin n → Bool)
    (hxx : ∀ i : Fin n, i ≠ t → x i = x' i) (hF : f x ≠ f x') : vl gs x y = true := by
  by_contra hy
  have hy' : vl gs x y = false := by simpa using hy
  have hin : ∀ i : Fin n, (i : ℕ) ∉ D → x i = x' i :=
    fun i hi => hxx i (fun h => hi (by rw [h]; exact htD))
  have hylt := (andRd_lt hcl hq).2.1
  have hyy : vl gs x y = vl gs x' y := by
    refine hProp n gs x x' D (n + q) hcl hin ?_ y hylt hyD
    intro p g hp hpK hpD
    by_cases hr : ∃ w ∈ g.inputs, w ∈ D
    · exact absurd (hrd p g hp hpD hr) (by omega)
    · left
      intro w hw hwD
      exact hr ⟨w, hw, hwD⟩
  have hq1 : vl gs x (n + q) = false := by rw [andRd_val hcl hq, hy', Bool.and_false]
  have hq2 : vl gs x' (n + q) = false := by rw [andRd_val hcl hq, ← hyy, hy', Bool.and_false]
  have hoo := hProp n gs x x' D (n + gs.length) hcl hin (by
    intro p g hp _ hpD
    by_cases hr : ∃ w ∈ g.inputs, w ∈ D
    · right
      rw [hrd p g hp hpD hr, hq1, hq2]
    · left
      intro w hw hwD
      exact hr ⟨w, hw, hwD⟩) o hoL ho
  exact hF (by rw [← hcomp x, ← hcomp x', hoo])

/-- The common end of both cells: an AND gate `q = AND(c, y)` with `c` not `e_s` and `y` true at
`e_s` and `e_b`. Paper: B1-AND (i), (ii) and the SHORTCUT. -/
theorem finish (hProp : ToolProp) (hMono : ToolMono) (hCons : ToolCons) (hPay : ToolPay1)
    (hRem : ToolRemoval) (hLive : ToolLive) {n : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} {gs : List Gate} {o : ℕ} {a' a s t b b' : Fin n}
    {qa qs qt qb ws wt : ℕ} (hctx : Ctx G A gs o a' a s t b b')
    (hfan : Fan gs a s t b qa qs qt qb) (hws : OrRd gs qs s ws) (hwt : OrRd gs qt t wt)
    (q c y : ℕ) (hq : AndRd gs q c y) (hcq : c ≠ n + qs) (hys : vl gs (pt {s}) y = true)
    (hyb : vl gs (pt {b}) y = true) : False := by
  have hcons := hCons n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hc := hctx.cex
  have hrun := hctx.run
  have hA := hctx.hA
  subst hA
  have hcl := hc.least.1
  have hnf := hc.least.2.1
  have hcomp := hc.least.2.2.1
  obtain ⟨has, hab, hst, hsb, htb, ha'b, hat⟩ := run_ne hrun
  have hnc := F_nc G ∅ (Or.inr ⟨s, t, (hrun.hs t).2 (Or.inr rfl)⟩)
  have hl := hLive n _ gs o hc.least hnc
  -- `y` is a gate
  have hyn : n ≤ y := by
    by_contra hlt
    push_neg at hlt
    rw [vl_input gs (pt {s}) y hlt] at hys
    rw [vl_input gs (pt {b}) y hlt] at hyb
    simp [pt] at hys hyb
    exact hsb (by rw [← hys, ← hyb])
  obtain ⟨py, rfl⟩ : ∃ py, y = n + py := ⟨y - n, by omega⟩
  -- `y` is not `e_s`
  have hqs_b : vl gs (pt {b}) (n + qs) = false := by
    rw [orRd_val hcl hws, vl_in, hcons.2.2.2]
    simp [pt, hsb]
  have hpyqs : py ≠ qs := by
    rintro rfl
    rw [hqs_b] at hyb
    exact absurd hyb (by simp)
  have hyP : ∀ x : Fin n → Bool, x s = true → vl gs x (n + py) = true := fun x hx =>
    hMono n gs ⟨hcl, hnf⟩ (pt {s}) x (fun i hi => by simp [pt] at hi; rw [hi]; exact hx) _ hys
  have hqsP : ∀ x : Fin n → Bool, x s = true → vl gs x (n + qs) = true := fun x hx =>
    or_true hcl hws x (by rw [vl_in]; exact hx)
  have hqlt := andRd_lt hcl hq
  by_cases hex : ∃ q2, Reads gs q2 (n + qs) ∧ q2 ≠ py
  · -- (ii): `s` pays at `x_s := 1`
    obtain ⟨q2, hq2, hq2y⟩ := hex
    have hqss := (orRd_lt hcl hws).2.2.1
    obtain ⟨j1, hj1⟩ := reader_alias hcl hnf s hqss (fun x hx => by rw [vl_in]; exact hx)
    obtain ⟨j2, hj2⟩ := true_alias s py hyP
    obtain ⟨j3, hj3⟩ := reader_alias hcl hnf s hqlt.2.2.2 hyP
    obtain ⟨j4, hj4⟩ := reader_alias hcl hnf s hq2 hqsP
    have l1 := reads_len hqss
    have l3 := reads_len hqlt.2.2.2
    have l4 := reads_len hq2
    have hpyq : py < q := by have := hqlt.2.1; omega
    have hqsq : qs ≠ q := fun h => and_ne_or hq hws h.symm
    have hqsq2 : qs < q2 := by have := reads_lt hcl hq2; omega
    have hqq2 : q ≠ q2 := by
      rintro rfl
      rcases reads_and hq hq2 with h | h
      · exact hcq h.symm
      · exact hpyqs (by omega)
    exact pay1_four hRem hPay hLive hc hnc s hrun.deep_s qs py q q2 j1 j2 j3 j4
      (by simp [List.nodup_cons]; omega) l1 (by omega) l3 l4 hj1 hj2 hj3 hj4
  · -- SHORTCUT: `y` is the only reader of `e_s`; on `x_b = 1` the output ignores `x_s`
    push_neg at hex
    let D : Set ℕ := {w | w = (s : ℕ) ∨ w = n + qs}
    have hin : ∀ i : Fin n, (i : ℕ) ∉ D → pt {a, s, b} i = pt {a, b} i := by
      intro i hi
      have his : i ≠ s := fun h => hi (Or.inl (by rw [h]))
      simp [pt, his]
    have hyb' : ∀ x : Fin n → Bool, x b = true → vl gs x (n + py) = true := fun x hx =>
      hMono n gs ⟨hcl, hnf⟩ (pt {b}) x (fun i hi => by simp [pt] at hi; rw [hi]; exact hx) _ hyb
    have hoD : o ∉ D := by
      rintro (h | h)
      · have := hcomp (pt {s})
        rw [h, vl_in, F_single] at this
        simp [pt] at this
      · have := hcomp (pt {s})
        rw [h, hqsP _ (by simp [pt]), F_single] at this
        exact absurd this (by simp)
    have hoo := hProp n gs (pt {a, s, b}) (pt {a, b}) D (n + gs.length) hcl hin (by
      intro p g hp _ hpD
      by_cases hr : ∃ w ∈ g.inputs, w ∈ D
      · obtain ⟨w, hw, hwD⟩ := hr
        rcases hwD with rfl | rfl
        · have hm := mem_rdSet.2 ⟨g, hp, hw⟩
          rw [hfan.fs] at hm
          simp at hm
          subst hm
          exact absurd (Or.inr rfl) hpD
        · have := hex p ⟨g, hp, hw⟩
          subst this
          right
          rw [hyb' _ (by simp [pt]), hyb' _ (by simp [pt])]
      · left
        intro w hw hwD
        exact hr ⟨w, hw, hwD⟩) o hl.1 hoD
    have h1 : F G ∅ (pt {a, s, b}) = true :=
      F_edge G _ a s ((hrun.ha s).2 (Or.inr rfl)) (by simp) (by simp)
    have h2 : F G ∅ (pt {a, b}) = false := by
      apply F_nonadj
      intro h
      rcases (hrun.ha b).1 h with h | h
      · exact ha'b h.symm
      · exact hsb h.symm
    rw [← hcomp] at h1 h2
    rw [hoo] at h1
    rw [h1] at h2
    exact absurd h2 (by simp)

/-! ## The two cells -/

/-- PIECE `PReadOneAnd`: `e_t` does not have a single reader that is an AND gate. -/
theorem PReadOneAnd_proof (hProp : ToolProp) (hMono : ToolMono) (hCons : ToolCons)
    (hPay : ToolPay1) (hRem : ToolRemoval) (hLive : ToolLive) (hNoA : ToolNoAlias) :
    PReadOneAnd := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt r g hctx hfan hws hwt hr hg hop
  have hcons := hCons n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hc := hctx.cex
  have hrun := hctx.run
  have hA := hctx.hA
  subst hA
  have hcl := hc.least.1
  have hnf := hc.least.2.1
  have hcomp := hc.least.2.2.1
  obtain ⟨has, hab, hst, hsb, htb, ha'b, hat⟩ := run_ne hrun
  have hnc := F_nc G ∅ (Or.inr ⟨s, t, (hrun.hs t).2 (Or.inr rfl)⟩)
  have hl := hLive n _ gs o hc.least hnc
  have htn := t.isLt
  have hrq : Reads gs r (n + qt) := mem_rdSet.1 (by rw [hr]; exact Finset.mem_singleton_self r)
  obtain ⟨y, hy | hy⟩ := rd_shape hcl hnf hrq
  swap
  · exact not_orRd hg hop _ _ hy
  have hqtr := reads_lt hcl hrq
  have hqt_t : vl gs (pt {t}) (n + qt) = true :=
    or_true hcl hwt _ (by rw [vl_in]; simp [pt])
  have hot : o ≠ t := by
    intro h
    have := hcomp (pt {t})
    rw [h, vl_in, F_single] at this
    simp [pt] at this
  have hoqt : o ≠ n + qt := by
    intro h
    have := hcomp (pt {t})
    rw [h, hqt_t, F_single] at this
    exact absurd this (by simp)
  have hyqt : y ≠ n + qt := by
    rintro rfl
    apply hNoA n _ gs o hc.least hnc r (reads_len hrq) (n + qt) (by omega)
    intro x
    rw [andRd_val hcl hy, Bool.and_self]
  have hyt : y ≠ t := by
    intro h
    have hrt : Reads gs r t := by rw [← h]; exact (andRd_lt hcl hy).2.2.2
    have hm := mem_rdSet.2 hrt
    rw [hfan.ft] at hm
    simp at hm
    omega
  let D : Set ℕ := {w | w = (t : ℕ) ∨ w = n + qt}
  have hrd : ∀ p g, gs[p]? = some g → n + p ∉ D → (∃ w ∈ g.inputs, w ∈ D) → p = r := by
    rintro p g' hp hpD ⟨w, hw, hwD⟩
    rcases hwD with rfl | rfl
    · have hm := mem_rdSet.2 ⟨g', hp, hw⟩
      rw [hfan.ft] at hm
      simp at hm
      subst hm
      exact absurd (Or.inr rfl) hpD
    · have hm := mem_rdSet.2 ⟨g', hp, hw⟩
      rw [hr] at hm
      simpa using hm
  have fl := flip hProp hcl hcomp D t r (n + qt) y hy (Or.inl rfl)
    (by rintro (h | h) <;> omega) (by rintro (h | h); exact hyt h; exact hyqt h) hrd
    (by rintro (h | h); exact hot h; exact hoqt h) hl.1
  have hys := fl (pt {s}) (pt {s, t}) (fun i hi => by simp [pt, hi])
    (by rw [F_single, F_edge G _ s t ((hrun.hs t).2 (Or.inr rfl)) (by simp) (by simp)]; simp)
  have hyb := fl (pt {b}) (pt {t, b}) (fun i hi => by simp [pt, hi])
    (by rw [F_single, F_edge G _ t b ((hrun.ht b).2 (Or.inr rfl)) (by simp) (by simp)]; simp)
  exact finish hProp hMono hCons hPay hRem hLive hctx hfan hws hwt r (n + qt) y hy
    (fun h => hcons.1 (by omega)) hys hyb

/-- PIECE `PReadOneOr`: `e_t` does not have a single reader that is an OR gate. -/
theorem PReadOneOr_proof (hProp : ToolProp) (hMono : ToolMono) (hCons : ToolCons)
    (hPay : ToolPay1) (hRem : ToolRemoval) (hLive : ToolLive) (hNoA : ToolNoAlias) :
    PReadOneOr := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt r g hctx hfan hws hwt hr hg hop
  have hcons := hCons n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hc := hctx.cex
  have hrun := hctx.run
  have hA := hctx.hA
  subst hA
  have hcl := hc.least.1
  have hnf := hc.least.2.1
  have hcomp := hc.least.2.2.1
  obtain ⟨has, hab, hst, hsb, htb, ha'b, hat⟩ := run_ne hrun
  have hnc := F_nc G ∅ (Or.inr ⟨s, t, (hrun.hs t).2 (Or.inr rfl)⟩)
  have hl := hLive n _ gs o hc.least hnc
  have htn := t.isLt
  have hrq : Reads gs r (n + qt) := mem_rdSet.1 (by rw [hr]; exact Finset.mem_singleton_self r)
  obtain ⟨z, hz | hz⟩ := rd_shape hcl hnf hrq
  · exact not_andRd hg hop _ _ hz
  have hqtr := reads_lt hcl hrq
  have hte : (pt {t} : Fin n → Bool) t = true := by simp [pt]
  have hP_qt : ∀ x : Fin n → Bool, x t = true → vl gs x (n + qt) = true := fun x hx =>
    or_true hcl hwt x (by rw [vl_in]; exact hx)
  have hP_r : ∀ x : Fin n → Bool, x t = true → vl gs x (n + r) = true := fun x hx =>
    or_true hcl hz x (hP_qt x hx)
  have hoff : ∀ w, (∀ x : Fin n → Bool, x t = true → vl gs x w = true) → o ≠ w := by
    intro w hw h
    have := hcomp (pt {t})
    rw [h, hw _ hte, F_single] at this
    exact absurd this (by simp)
  have hot : o ≠ t := hoff t (fun x hx => by rw [vl_in]; exact hx)
  have hlr : r < gs.length := reads_len hrq
  have hqtt := (orRd_lt hcl hwt).2.2.1
  have lqt := reads_len hqtt
  obtain ⟨j0, hj0⟩ := reader_alias hcl hnf t hqtt (fun x hx => by rw [vl_in]; exact hx)
  obtain ⟨j1, hj1⟩ := reader_alias hcl hnf t hrq hP_qt
  by_cases two : ∃ q1 q2, Reads gs q1 (n + r) ∧ Reads gs q2 (n + r) ∧ q1 ≠ q2
  · -- `r` has two readers: `t` pays at `x_t := 1`
    obtain ⟨q1, q2, h1, h2, h12⟩ := two
    obtain ⟨j2, hj2⟩ := reader_alias hcl hnf t h1 hP_r
    obtain ⟨j3, hj3⟩ := reader_alias hcl hnf t h2 hP_r
    have := reads_lt hcl h1
    have := reads_lt hcl h2
    exact pay1_four hRem hPay hLive hc hnc t hrun.deep_t qt r q1 q2 j0 j1 j2 j3
      (by simp [List.nodup_cons]; omega) lqt hlr (reads_len h1) (reads_len h2) hj0 hj1 hj2 hj3
  push_neg at two
  obtain ⟨q, hqm⟩ := hl.2 r hlr (hoff _ hP_r)
  have hq := mem_rdSet.1 hqm
  have hrq' := reads_lt hcl hq
  obtain ⟨y, hy | hy⟩ := rd_shape hcl hnf hq
  swap
  · -- `q = OR(r, y)`: `q` and a reader of it; `t` pays at `x_t := 1`
    have hP_q : ∀ x : Fin n → Bool, x t = true → vl gs x (n + q) = true := fun x hx =>
      or_true hcl hy x (hP_r x hx)
    obtain ⟨q', hq'm⟩ := hl.2 q (reads_len hq) (hoff _ hP_q)
    have hq' := mem_rdSet.1 hq'm
    obtain ⟨j2, hj2⟩ := reader_alias hcl hnf t hq hP_r
    obtain ⟨j3, hj3⟩ := reader_alias hcl hnf t hq' hP_q
    have := reads_lt hcl hq'
    exact pay1_four hRem hPay hLive hc hnc t hrun.deep_t qt r q q' j0 j1 j2 j3
      (by simp [List.nodup_cons]; omega) lqt hlr (reads_len hq) (reads_len hq') hj0 hj1 hj2 hj3
  -- `q = AND(r, y)`: as the AND cell with `q` for `r`
  have hyr : y ≠ n + r := by
    rintro rfl
    apply hNoA n _ gs o hc.least hnc q (reads_len hq) (n + r) (by omega)
    intro x
    rw [andRd_val hcl hy, Bool.and_self]
  have hyqt : y ≠ n + qt := by
    intro h
    have hqq : Reads gs q (n + qt) := by rw [← h]; exact (andRd_lt hcl hy).2.2.2
    have hm := mem_rdSet.2 hqq
    rw [hr] at hm
    simp at hm
    omega
  have hyt : y ≠ t := by
    intro h
    have hqq : Reads gs q t := by rw [← h]; exact (andRd_lt hcl hy).2.2.2
    have hm := mem_rdSet.2 hqq
    rw [hfan.ft] at hm
    simp at hm
    omega
  let D : Set ℕ := {w | w = (t : ℕ) ∨ w = n + qt ∨ w = n + r}
  have hrd : ∀ p g, gs[p]? = some g → n + p ∉ D → (∃ w ∈ g.inputs, w ∈ D) → p = q := by
    rintro p g' hp hpD ⟨w, hw, hwD⟩
    rcases hwD with rfl | rfl | rfl
    · have hm := mem_rdSet.2 ⟨g', hp, hw⟩
      rw [hfan.ft] at hm
      simp at hm
      subst hm
      exact absurd (Or.inr (Or.inl rfl)) hpD
    · have hm := mem_rdSet.2 ⟨g', hp, hw⟩
      rw [hr] at hm
      simp at hm
      subst hm
      exact absurd (Or.inr (Or.inr rfl)) hpD
    · exact two p q ⟨g', hp, hw⟩ hq
  have fl := flip hProp hcl hcomp D t q (n + r) y hy (Or.inl rfl)
    (by rintro (h | h | h) <;> omega)
    (by rintro (h | h | h); exact hyt h; exact hyqt h; exact hyr h) hrd
    (by
      rintro (h | h | h)
      · exact hot h
      · exact hoff _ hP_qt h
      · exact hoff _ hP_r h) hl.1
  have hys := fl (pt {s}) (pt {s, t}) (fun i hi => by simp [pt, hi])
    (by rw [F_single, F_edge G _ s t ((hrun.hs t).2 (Or.inr rfl)) (by simp) (by simp)]; simp)
  have hyb := fl (pt {b}) (pt {t, b}) (fun i hi => by simp [pt, hi])
    (by rw [F_single, F_edge G _ t b ((hrun.ht b).2 (Or.inr rfl)) (by simp) (by simp)]; simp)
  have hrqs : n + r ≠ n + qs := by
    intro h
    have hrs : r = qs := by omega
    have h1 := hP_r _ hte
    rw [hrs, orRd_val hcl hws, vl_in, hcons.2.2.1] at h1
    simp [pt, hst] at h1
  exact finish hProp hMono hCons hPay hRem hLive hctx hfan hws hwt q (n + r) y hy hrqs hys hyb

end PEqualNP.MetaComplexity.Loc.ReadOne
