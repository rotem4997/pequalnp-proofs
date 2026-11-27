import PEqualNP.MetaComplexity.Helpers.MachineOwnCnf
import PEqualNP.MetaComplexity.Helpers.MachineOwnInner

/-!
# Helper module (proofs only): the lists written for one item `(i, j)`

Parts A to E of `blkO`, each a string machine on any context carrying the code of `ψ` and the
unary numbers `E`, `k`, `i`, `j` with `i < |ψ|` and `j ≤ w i`. Every filtered range of the
statement is read as a range with a guard (`filter_flatMap`, `encNs_filter_map`). Facts about
the literal `(i, j)` are used only under the guard `j < w i` (selections with refined domains).
-/

namespace PEqualNP.MetaComplexity.MachineOwn

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.SearchHelpers.SatV

local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-- The bound of the input type. -/
def bnd (φ : CNF) : Prop :=
  ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : Clause => c.length + 1)).sum

theorem filter_flatMap {β γ : Type} (L : List β) (p : β → Bool) (g : β → List γ) :
    (L.filter p).flatMap g = L.flatMap (fun x => if p x then g x else []) := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases h : p x <;> simp [List.filter_cons, h, ih]

theorem encNs_filter_map {β : Type} (L : List β) (p : β → Bool) (g : β → ℕ) :
    encNs ((L.filter p).map g) = L.flatMap (fun x => if p x then encN (g x) else []) := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases h : p x <;> simp [List.filter_cons, h, ih, encNs_cons]

section

variable {α : Type} {D : α → Prop} {ea : α → List Bool}

theorem SP.andD {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (hP : SP D ea (fun a => bflag (decide (P a))))
    (hQ : SP (fun a => D a ∧ P a) ea (fun a => bflag (decide (Q a)))) :
    SP D ea (fun a => bflag (decide (P a ∧ Q a))) :=
  (SP.iteD hP hQ (sp_const [])).congr (fun a _ => by by_cases h : P a <;> simp [h, bflag])

theorem sp_pos {ψ : α → CNF} {E O J : α → ℕ} (hE : SP D ea (fun a => un (E a)))
    (hO : SP D ea (fun a => un (offO (ψ a) (O a)))) (hJ : SP D ea (fun a => un (J a))) :
    SP D ea (fun a => un (posO (E a) (ψ a) (O a) (J a))) :=
  (((sp_num 2).mul (hE.add (sp_num 1))).add hO).add hJ

/-- The context of an item: the code of `ψ`, `E`, `k`, `i`, `j`. -/
structure ICtx (D : α → Prop) (ea : α → List Bool) (ψ : α → CNF) (E K I J : α → ℕ) : Prop where
  x : SP D ea (fun a => encodeCNF (ψ a))
  e : SP D ea (fun a => un (E a))
  k : SP D ea (fun a => un (K a))
  i : SP D ea (fun a => un (I a))
  j : SP D ea (fun a => un (J a))
  dom : ∀ a, D a → I a < (ψ a).length ∧ J a ≤ wO (ψ a) (I a) ∧ bnd (ψ a)

variable {ψ : α → CNF} {E K I J : α → ℕ}

theorem ICtx.mono (c : ICtx D ea ψ E K I J) {D' : α → Prop} (h : ∀ a, D' a → D a) :
    ICtx D' ea ψ E K I J :=
  ⟨c.x.mono h, c.e.mono h, c.k.mono h, c.i.mono h, c.j.mono h, fun a ha => c.dom a (h a ha)⟩

theorem ICtx.up (c : ICtx D ea ψ E K I J) {D' : α × ℕ → Prop} (h : ∀ q, D' q → D q.1) :
    ICtx D' (ext ea) (fun q => ψ q.1) (fun q => E q.1) (fun q => K q.1) (fun q => I q.1)
      (fun q => J q.1) :=
  ⟨c.x.up h, c.e.up h, c.k.up h, c.i.up h, c.j.up h, fun q hq => c.dom q.1 (h q hq)⟩

theorem ICtx.w (c : ICtx D ea ψ E K I J) : SP D ea (fun a => un (wO (ψ a) (I a))) := sp_w c.x c.i

theorem ICtx.off (c : ICtx D ea ψ E K I J) : SP D ea (fun a => un (offO (ψ a) (I a))) :=
  sp_off c.x c.i (fun a ha => (c.dom a ha).1.le)

theorem ICtx.f (c : ICtx D ea ψ E K I J) : SP D ea (fun a => un (fO (ψ a) (I a))) :=
  sp_f c.x c.i (fun a ha => (c.dom a ha).1)

theorem ICtx.pos (c : ICtx D ea ψ E K I J) : SP D ea (fun a => un (posO (E a) (ψ a) (I a) (J a))) :=
  sp_pos c.e c.off c.j

/-- Literal facts, on the part of the domain where `j < w i`. -/
theorem ICtx.lit (c : ICtx D ea ψ E K I J) {D' : α → Prop}
    (h : ∀ a, D' a → D a ∧ J a < wO (ψ a) (I a)) :
    SP D' ea (fun a => encodeLiteral (litO (ψ a) (I a) (J a))) :=
  sp_lit (c.x.mono (fun a ha => (h a ha).1)) (c.i.mono (fun a ha => (h a ha).1))
    (c.j.mono (fun a ha => (h a ha).1))
    (fun a ha => ⟨(c.dom a (h a ha).1).1, (h a ha).2⟩)

theorem ICtx.var (c : ICtx D ea ψ E K I J) {D' : α → Prop}
    (h : ∀ a, D' a → D a ∧ J a < wO (ψ a) (I a)) :
    SP D' ea (fun a => un (litO (ψ a) (I a) (J a)).1) :=
  sp_var (c.x.mono (fun a ha => (h a ha).1)) (c.lit h) (fun a ha =>
    var_lt_code _ (c.dom a (h a ha).1).2.2 _ _ (c.dom a (h a ha).1).1 (h a ha).2)

theorem ICtx.sign (c : ICtx D ea ψ E K I J) {D' : α → Prop}
    (h : ∀ a, D' a → D a ∧ J a < wO (ψ a) (I a)) :
    SP D' ea (fun a => bflag (litO (ψ a) (I a) (J a)).2) := sp_sign (c.lit h)

theorem ICtx.lt (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => bflag (decide (J a < wO (ψ a) (I a)))) := c.j.ltN c.w

/-! ## Part A -/

theorem ICtx.partA (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => flatS (blkA (E a) (K a) (ψ a) (I a) (J a))) := by
  have hT : SP (fun a => D a ∧ J a < wO (ψ a) (I a)) ea (fun a => flatS (innerO (E a) (K a)
      (2 * (litO (ψ a) (I a) (J a)).1 + (if (litO (ψ a) (I a) (J a)).2 then 1 else 0))
      (posO (E a) (ψ a) (I a) (J a)) (litO (ψ a) (I a) (J a)).2)) := by
    have c' := c.mono (D' := fun a => D a ∧ J a < wO (ψ a) (I a)) (fun a ha => ha.1)
    exact sp_inner c'.e c'.k (((sp_num 2).mul (c.var (fun a ha => ha))).add
      ((c.sign (fun a ha => ha)).congr (fun a _ => bflag_un _))) c'.pos (c.sign (fun a ha => ha))
  have hE' : SP (fun a => D a ∧ ¬ J a < wO (ψ a) (I a)) ea (fun a => flatS (innerO (E a) (K a)
      (2 * E a + 1) (posO (E a) (ψ a) (I a) (J a)) true)) := by
    have c' := c.mono (D' := fun a => D a ∧ ¬ J a < wO (ψ a) (I a)) (fun a ha => ha.1)
    exact sp_inner c'.e c'.k (((sp_num 2).mul c'.e).add (sp_num 1)) c'.pos (sp_const [true])
  exact (SP.iteD c.lt hT hE').congr (fun a _ => by unfold blkA; split_ifs <;> rfl)

/-! ## Part B -/

theorem ICtx.partB (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => flatS (blkB (E a) (K a) (ψ a) (I a) (J a))) := by
  let D' : α × ℕ → Prop := fun q => D q.1 ∧ q.2 < wO (ψ q.1) (I q.1) + 1
  have c' := c.up (D' := D') (fun q hq => hq.1)
  have hfl : SP D' (ext ea) (fun q => bflag (decide (J q.1 ≠ fO (ψ q.1) (I q.1)))) :=
    (c'.j.eqN c'.f).notF
  have hin : SP D' (ext ea) (fun q => flatS (innerO (E q.1) (K q.1) (posO (E q.1) (ψ q.1) (I q.1) (J q.1))
      (posO (E q.1) (ψ q.1) (I q.1) q.2) (decide (J q.1 ≠ fO (ψ q.1) (I q.1))))) :=
    sp_inner c'.e c'.k c'.pos (sp_pos c'.e c'.off sp_idx) (hfl.congr (fun q _ => rfl))
  have hb : SP D' (ext ea) (fun q => if J q.1 < q.2 then flatS (innerO (E q.1) (K q.1)
      (posO (E q.1) (ψ q.1) (I q.1) (J q.1)) (posO (E q.1) (ψ q.1) (I q.1) q.2)
      (decide (J q.1 ≠ fO (ψ q.1) (I q.1)))) else []) :=
    SP.ite (c'.j.ltN sp_idx) hin (sp_const [])
  refine (SP.loop (B := fun a l => if J a < l then flatS (innerO (E a) (K a)
      (posO (E a) (ψ a) (I a) (J a)) (posO (E a) (ψ a) (I a) l)
      (decide (J a ≠ fO (ψ a) (I a)))) else []) (c.w.add (sp_num 1)) hb).congr (fun a _ => ?_)
  unfold blkB
  rw [flatS_flatMap, filter_flatMap]
  apply List.flatMap_congr
  intro l _
  by_cases h : J a < l <;> simp [h]


/-! ## Part C -/

theorem ICtx.first (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => bflag (decide (J a < wO (ψ a) (I a) ∧
      (litO (ψ a) (I a) (J a)).1 = offO (ψ a) (I a) + J a))) :=
  SP.andD c.lt ((c.var (fun a ha => ha)).eqN
    ((c.off.mono (fun a ha => ha.1)).add (c.j.mono (fun a ha => ha.1))))

theorem ICtx.partC (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => flatS (blkC (E a) (K a) (ψ a) (I a) (J a))) := by
  let D' : α → Prop := fun a => D a ∧ (J a < wO (ψ a) (I a) ∧
      (litO (ψ a) (I a) (J a)).1 = offO (ψ a) (I a) + J a)
  have c' := c.mono (D' := D') (fun a ha => ha.1)
  have hv := c.var (D' := D') (fun a ha => ⟨ha.1, ha.2.1⟩)
  have hT : SP D' ea (fun a => flatS (innerO (E a) (K a) (2 * (litO (ψ a) (I a) (J a)).1)
      (2 * (litO (ψ a) (I a) (J a)).1 + 1) false)) :=
    sp_inner (B := fun _ => false) c'.e c'.k ((sp_num 2).mul hv) (((sp_num 2).mul hv).add (sp_num 1))
      (sp_const (bflag false))
  exact (SP.iteD c.first hT (sp_const [])).congr (fun a _ => by
    unfold PEqualNP.MetaComplexity.MachineOwn.blkC; split_ifs <;> rfl)

/-! ## Part D -/

theorem ICtx.partD (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => flatS (blkD (E a) (K a) (ψ a) (I a) (J a))) := by
  -- the first optional entry
  have hneg : SP (fun a => D a ∧ J a < wO (ψ a) (I a)) ea
      (fun a => bflag (decide ((litO (ψ a) (I a) (J a)).2 = false))) :=
    ((c.sign (fun a ha => ha)).sel (sp_const [true]) (sp_const [])).congr (fun a _ => by
      cases (litO (ψ a) (I a) (J a)).2 <;> rfl)
  let D1 : α → Prop := fun a => D a ∧ (J a < wO (ψ a) (I a) ∧ (litO (ψ a) (I a) (J a)).2 = false)
  have c1 := c.mono (D' := D1) (fun a ha => ha.1)
  have hv1 := c.var (D' := D1) (fun a ha => ⟨ha.1, ha.2.1⟩)
  have hA1 : SP D ea (fun a => encNs (if J a < wO (ψ a) (I a) ∧ (litO (ψ a) (I a) (J a)).2 = false
      then [XO (E a) (K a) (2 * (litO (ψ a) (I a) (J a)).1) (posO (E a) (ψ a) (I a) (J a)) (2 * K a)]
      else [])) :=
    (SP.iteD (SP.andD c.lt hneg) (sp_X c1.e c1.k ((sp_num 2).mul hv1) c1.pos
      ((sp_num 2).mul c1.k)).encN (sp_const [])).congr (fun a _ => by
        split_ifs <;> simp [encNs_cons])
  -- the second optional entry
  have hA2 : SP D ea (fun a => encNs (if fO (ψ a) (I a) < J a
      then [XO (E a) (K a) (posO (E a) (ψ a) (I a) (fO (ψ a) (I a))) (posO (E a) (ψ a) (I a) (J a))
        (2 * K a)] else [])) :=
    (SP.ite (c.f.ltN c.j) (sp_X c.e c.k (sp_pos c.e c.off c.f) c.pos
      ((sp_num 2).mul c.k)).encN (sp_const [])).congr (fun a _ => by
        split_ifs <;> simp [encNs_cons])
  -- the later items of the clause
  let D' : α × ℕ → Prop := fun q => D q.1 ∧ q.2 < wO (ψ q.1) (I q.1) + 1
  have c' := c.up (D' := D') (fun q hq => hq.1)
  have hb : SP D' (ext ea) (fun q => if J q.1 < q.2 then encN (XO (E q.1) (K q.1)
      (posO (E q.1) (ψ q.1) (I q.1) (J q.1)) (posO (E q.1) (ψ q.1) (I q.1) q.2) 1) else []) :=
    SP.ite (c'.j.ltN sp_idx)
      (sp_X c'.e c'.k c'.pos (sp_pos c'.e c'.off sp_idx) (sp_num 1)).encN (sp_const [])
  have hL3 : SP D ea (fun a => encNs (((List.range (wO (ψ a) (I a) + 1)).filter
      (fun l : ℕ => decide (J a < l))).map
      (fun l : ℕ => XO (E a) (K a) (posO (E a) (ψ a) (I a) (J a)) (posO (E a) (ψ a) (I a) l) 1))) :=
    (SP.loop (B := fun a l => if J a < l then encN (XO (E a) (K a)
      (posO (E a) (ψ a) (I a) (J a)) (posO (E a) (ψ a) (I a) l) 1) else [])
      (c.w.add (sp_num 1)) hb).congr (fun a _ => by
        rw [encNs_filter_map]
        apply List.flatMap_congr
        intro l _
        by_cases h : J a < l <;> simp [h])
  have hT := (sp_const [true]).app (c.pos.encN.app ((hA1.app (hA2.app hL3)).app (sp_const [false])))
  exact (SP.ite ((c.j.eqN c.f).notF) hT (sp_const [])).congr (fun a _ => by
    unfold PEqualNP.MetaComplexity.MachineOwn.blkD
    by_cases h : J a ≠ fO (ψ a) (I a)
    · rw [if_pos h, if_pos h]
      simp only [flatS_single, encNs_cons, encNs_append, List.append_assoc, List.cons_append,
        List.singleton_append, List.nil_append]
    · rw [if_neg h, if_neg h]; rfl)

/-! ## Part E -/

theorem sp_occ {V : α → ℕ} (hx : SP D ea (fun a => encodeCNF (ψ a)))
    (hE : SP D ea (fun a => un (E a))) (hK : SP D ea (fun a => un (K a)))
    (hV : SP D ea (fun a => un (V a))) (hVc : SP D ea (fun a => vcode (V a))) :
    SP D ea (fun a => encNs (occO (E a) (K a) (ψ a) (V a))) := by
  let D3 : α × ℕ → Prop := fun q => D q.1 ∧ q.2 < (ψ q.1).length
  let D4 : (α × ℕ) × ℕ → Prop := fun r => D3 r.1 ∧ r.2 < wO (ψ r.1.1) r.1.2
  have up4 : ∀ {F : α → List Bool}, SP D ea F → SP D4 (ext (ext ea)) (fun r => F r.1.1) :=
    fun h => (h.up (D' := D3) (fun q hq => hq.1)).up (fun r hr => hr.1)
  have hi' : SP D4 (ext (ext ea)) (fun r => un r.1.2) := sp_idx.up (fun r hr => hr.1)
  have hlit : SP D4 (ext (ext ea)) (fun r => encodeLiteral (litO (ψ r.1.1) r.1.2 r.2)) :=
    sp_lit (up4 hx) hi' sp_idx (fun r hr => ⟨hr.1.2, hr.2⟩)
  have hfl : SP D4 (ext (ext ea)) (fun r => bflag (decide ((litO (ψ r.1.1) r.1.2 r.2).1 = V r.1.1 ∧
      (litO (ψ r.1.1) r.1.2 r.2).2 = true))) :=
    (hlit.eqF ((sp_const [true, true]).app (up4 hVc))).congr (fun r _ => by
      have e : ([true, true] ++ vcode (V r.1.1)) = encodeLiteral (V r.1.1, true) := by
        simp [encodeLiteral_eq]
      rw [e]
      have : (encodeLiteral (litO (ψ r.1.1) r.1.2 r.2) = encodeLiteral (V r.1.1, true)) ↔
          ((litO (ψ r.1.1) r.1.2 r.2).1 = V r.1.1 ∧ (litO (ψ r.1.1) r.1.2 r.2).2 = true) := by
        constructor
        · intro h; have := PEqualNP.Library.SearchHelpers.TwoSat.encodeLiteral_injective h
          rw [this]; simp
        · intro h; rw [← h.1, ← h.2]
      simp only [this])
  have hb4 : SP D4 (ext (ext ea)) (fun r => if (litO (ψ r.1.1) r.1.2 r.2).1 = V r.1.1 ∧
      (litO (ψ r.1.1) r.1.2 r.2).2 = true then
        encN (XO (E r.1.1) (K r.1.1) (2 * V r.1.1 + 1) (posO (E r.1.1) (ψ r.1.1) r.1.2 r.2) 1)
      else []) :=
    SP.ite hfl (sp_X (up4 hE) (up4 hK) (((sp_num 2).mul (up4 hV)).add (sp_num 1))
      (sp_pos (up4 hE) (sp_off (up4 hx) hi' (fun r hr => hr.1.2.le)) sp_idx) (sp_num 1)).encN
      (sp_const [])
  have hb3 : SP D3 (ext ea) (fun q => (List.range (wO (ψ q.1) q.2)).flatMap (fun j' =>
      if (litO (ψ q.1) q.2 j').1 = V q.1 ∧ (litO (ψ q.1) q.2 j').2 = true then
        encN (XO (E q.1) (K q.1) (2 * V q.1 + 1) (posO (E q.1) (ψ q.1) q.2 j') 1) else [])) :=
    SP.loop (B := fun q j' => if (litO (ψ q.1) q.2 j').1 = V q.1 ∧ (litO (ψ q.1) q.2 j').2 = true then
        encN (XO (E q.1) (K q.1) (2 * V q.1 + 1) (posO (E q.1) (ψ q.1) q.2 j') 1) else [])
      (sp_w (hx.up (fun q hq => hq.1)) sp_idx) hb4
  refine (SP.loop (B := fun a i' => (List.range (wO (ψ a) i')).flatMap (fun j' =>
      if (litO (ψ a) i' j').1 = V a ∧ (litO (ψ a) i' j').2 = true then
        encN (XO (E a) (K a) (2 * V a + 1) (posO (E a) (ψ a) i' j') 1) else []))
    (sp_ncl hx) hb3).congr (fun a _ => ?_)
  unfold occO
  rw [encNs_flatMap]
  apply List.flatMap_congr
  intro i' _
  rw [encNs_filter_map]
  apply List.flatMap_congr
  intro j' _
  simp

theorem ICtx.partE (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => flatS (blkE (E a) (K a) (ψ a) (I a) (J a))) := by
  let D' : α → Prop := fun a => D a ∧ (J a < wO (ψ a) (I a) ∧
      (litO (ψ a) (I a) (J a)).1 = offO (ψ a) (I a) + J a)
  have c' := c.mono (D' := D') (fun a ha => ha.1)
  have h' : ∀ a, D' a → D a ∧ J a < wO (ψ a) (I a) := fun a ha => ⟨ha.1, ha.2.1⟩
  have hv := c.var h'
  have hvc : SP D' ea (fun a => vcode (litO (ψ a) (I a) (J a)).1) :=
    ((c.lit h').post cpt_drop2).congr (fun a _ => by simp [encodeLiteral_eq])
  have hT := (sp_const [true]).app (((((sp_num 2).mul hv).add (sp_num 1)).encN.app
    ((sp_X c'.e c'.k ((sp_num 2).mul hv) (((sp_num 2).mul hv).add (sp_num 1))
      ((sp_num 2).mul c'.k)).encN.app
      (sp_occ c'.x c'.e c'.k hv hvc))).app (sp_const [false]))
  exact (SP.iteD c.first hT (sp_const [])).congr (fun a _ => by
    unfold PEqualNP.MetaComplexity.MachineOwn.blkE
    by_cases h : J a < wO (ψ a) (I a) ∧ (litO (ψ a) (I a) (J a)).1 = offO (ψ a) (I a) + J a
    · rw [if_pos h, if_pos h]
      simp only [flatS_single, encNs_cons, List.append_assoc, List.cons_append,
        List.singleton_append, List.nil_append]
    · rw [if_neg h, if_neg h]; rfl)

theorem ICtx.blk (c : ICtx D ea ψ E K I J) :
    SP D ea (fun a => flatS (blkO (E a) (K a) (ψ a) (I a) (J a))) :=
  ((((c.partA.app c.partB).app c.partC).app c.partD).app c.partE).congr (fun a _ => by
    simp only [blkO, flatS_append])

end

end PEqualNP.MetaComplexity.MachineOwn
