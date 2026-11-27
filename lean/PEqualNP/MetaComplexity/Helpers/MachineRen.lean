import PEqualNP.MetaComplexity.Helpers.MachineRenDefs

/-!
# Helper module (proofs only): the renaming by earliest occurrence is polynomial-time computable

The statement of row L-meta-500, from the string machines of `MachineOwnGeneric` and the item
reading of `MachineOwnCnf`. A loop over the item indices `q` below the code length writes
`bodyR` of item `q`; for a literal item the new variable is the count `cntR` (a loop over `p`
with an inner loop over `p' ≤ p` comparing variable codes), written in binary by the iterated
increment, as in `sp_vcode`. Old variables are never made unary: only their codes are compared.
-/

namespace PEqualNP.MetaComplexity.MachineRen

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.MetaComplexity.MachineOwn

/-! ## The count is the earliest occurrence -/

theorem ren_bflag_mem {b : Bool} {x : Bool} (h : x ∈ bflag b) : x = true := by
  cases b <;> simp_all [bflag]

theorem ren_cnt_un (M : ℕ) (L : List (Option Literal)) (t : List Bool) :
    cntR M L t = un (cntR M L t).length :=
  un_length_eq _ (fun x hx => by
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hx
    exact ren_bflag_mem hp)

theorem ren_vcode_ne (v : ℕ) : vcode v ≠ [] := by simp [vcode]

/-- The variable code of item `p` is `vcode v` exactly when item `p` is a literal of variable `v`. -/
theorem ren_tt_item (L : List (Option Literal)) (p v : ℕ) :
    (itemAt L p).tail.tail = vcode v ↔
      (L[p]?).any (fun o => o.any (fun l' : Literal => l'.1 == v)) = true := by
  unfold itemAt
  rcases h : L[p]? with _ | o
  · simp only [Option.elim, List.tail_nil, Option.any_none]
    exact ⟨fun e => (ren_vcode_ne v e.symm).elim, fun e => by simp at e⟩
  · rcases o with _ | l
    · simp only [Option.elim, icode, List.tail_cons, Option.any_some, Option.any_none]
      exact ⟨fun e => (ren_vcode_ne v e.symm).elim, fun e => by simp at e⟩
    · simp only [Option.elim, icode, encodeLiteral_eq, List.tail_cons, Option.any_some,
        beq_iff_eq]
      exact ⟨fun e => vcode_injective e, fun e => by rw [e]⟩

theorem ren_inner_nil (L : List (Option Literal)) (t : List Bool) (p : ℕ) :
    innerR L t p = [] ↔ ∀ p' < p + 1, (itemAt L p').tail.tail ≠ t := by
  unfold innerR
  rw [List.flatMap_eq_nil_iff]
  constructor
  · intro h p' hp' e
    have := h p' (List.mem_range.mpr hp')
    simp [e, bflag] at this
  · intro h p' hp'
    have := h p' (List.mem_range.mp hp')
    simp [this, bflag]

theorem ren_range_lt (M k : ℕ) (hk : k ≤ M) :
    (List.range M).flatMap (fun p => bflag (decide (p < k))) = un k := by
  induction M generalizing k with
  | zero => obtain rfl : k = 0 := by omega
            rfl
  | succ M ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : k ≤ M
    · rw [ih k h]; simp [bflag]; omega
    · obtain rfl : k = M + 1 := by omega
      have e : (List.range M).flatMap (fun p => bflag (decide (p < M + 1))) = un M := by
        have := ih M le_rfl
        rw [← this]
        apply List.flatMap_congr
        intro p hp
        have hp := List.mem_range.mp hp
        simp [hp, Nat.lt_succ_of_lt hp]
      rw [e]; simp [bflag, un, List.replicate_succ']

theorem ren_cnt_eq (M : ℕ) (L : List (Option Literal)) (hM : L.length ≤ M) (l : Literal)
    (hl : some l ∈ L) :
    cntR M L (vcode l.1) =
      un (L.findIdx (fun o : Option Literal => o.any (fun l' : Literal => l'.1 == l.1))) := by
  set f := fun o : Option Literal => o.any (fun l' : Literal => l'.1 == l.1) with hf
  have hlt : L.findIdx f < L.length :=
    List.findIdx_lt_length_of_exists ⟨some l, hl, by simp [hf]⟩
  have key : ∀ p, (innerR L (vcode l.1) p = []) ↔ p < L.findIdx f := by
    intro p
    rw [ren_inner_nil]
    constructor
    · intro h
      by_contra hp
      apply h (L.findIdx f) (by omega)
      rw [ren_tt_item, List.getElem?_eq_getElem hlt]
      simpa [hf] using (List.findIdx_getElem (w := hlt))
    · intro hp p' hp' e
      rw [ren_tt_item] at e
      have hp'' : p' < L.findIdx f := by omega
      have h1 : p' < L.length := by omega
      rw [List.getElem?_eq_getElem h1] at e
      have := List.not_of_lt_findIdx hp''
      simp only [Option.any_some] at e
      have h2 : Option.any (fun l' : Literal => l'.1 == l.1) L[p'] = false := this
      rw [h2] at e
      exact Bool.false_ne_true e
  unfold cntR
  rw [← ren_range_lt M (L.findIdx f) (by omega)]
  apply List.flatMap_congr
  intro p _
  simp only [key]

/-! ## The body on items, and the whole output -/

theorem ren_body_lit (M : ℕ) (L : List (Option Literal)) (hM : L.length ≤ M) (l : Literal)
    (hl : some l ∈ L) :
    bodyR M L (icode (some l)) =
      encodeLiteral (L.findIdx (fun o : Option Literal => o.any (fun l' : Literal => l'.1 == l.1)),
        l.2) := by
  have h1 : icode (some l) = encodeLiteral l := rfl
  have hne : encodeLiteral l ≠ [] := by simp [encodeLiteral_eq]
  have hend : isEnd (encodeLiteral l) = false := by simp [encodeLiteral_eq, isEnd]
  unfold bodyR
  rw [h1, signF_lit]
  have htt : (encodeLiteral l).tail.tail = vcode l.1 := by simp [encodeLiteral_eq]
  rw [htt, ren_cnt_eq M L hM l hl, un_length]
  rw [encodeLiteral_eq (_, l.2)]
  cases hs : l.2 <;> simp [sel, bflag, isEnd, encodeLiteral_eq]

theorem ren_body_end (M : ℕ) (L : List (Option Literal)) : bodyR M L (icode none) = [false, false] :=
  rfl

theorem ren_body_nil (M : ℕ) (L : List (Option Literal)) : bodyR M L [] = [] := rfl

theorem ren_out (M : ℕ) (L : List (Option Literal)) (hM : L.length ≤ M) (ψ : CNF)
    (hψ : ∀ c ∈ ψ, ∀ l ∈ c, some l ∈ L) :
    (items ψ).flatMap (fun o => bodyR M L (icode o)) =
      encodeCNF (ψ.map (fun c : Clause => c.map (fun l : Literal =>
        (L.findIdx (fun o : Option Literal => o.any (fun l' : Literal => l'.1 == l.1)), l.2)))) := by
  induction ψ with
  | nil => rfl
  | cons c ψ ih =>
    rw [items_cons, List.flatMap_append, ih (fun c' hc' => hψ c' (List.mem_cons_of_mem _ hc')),
      List.map_cons]
    have hc : ∀ l ∈ c, some l ∈ L := hψ c List.mem_cons_self
    simp only [encodeCNF, List.flatMap_cons, encodeClause, List.flatMap_append, List.flatMap_map,
      ren_body_end, List.append_assoc]
    congr 1
    apply List.flatMap_congr
    intro l hl
    exact ren_body_lit M L hM l (hc l hl)

theorem ren_items_mem (φ : CNF) : ∀ c ∈ φ, ∀ l ∈ c, some l ∈ items φ := by
  intro c hc l hl
  unfold items
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_append_left _ (List.mem_map_of_mem hl)⟩

theorem ren_out_eq (φ : CNF) (M : ℕ) (hM : (items φ).length ≤ M) :
    (items φ).flatMap (fun o => bodyR M (items φ) (icode o)) = encodeCNF (renF φ) :=
  ren_out M (items φ) hM φ (ren_items_mem φ)

/-! ## The machines -/

section

variable {α : Type} {D : α → Prop} {ea : α → List Bool}

theorem ren_sp_vcodeOf {Q : α → ℕ} (hQ : SP D ea (fun a => un (Q a))) :
    SP D ea (fun a => vcode (Q a)) :=
  (((SP.iterGrow PEqualNP.Library.SearchHelpers.S2D.cpt_incB 1
    PEqualNP.Library.SearchHelpers.S2D.incB_length hQ (sp_const [])).post
      PEqualNP.Library.SearchHelpers.S2D.cpt_dig).app (sp_const [false, true])).congr
    (fun a _ => by rw [incB_iter, vcode_eq_dig])

theorem ren_sp_cnt {ψ : α → CNF} (hx : SP D ea (fun a => encodeCNF (ψ a))) {T : α → List Bool}
    (hT : SP D ea T) :
    SP D ea (fun a => cntR (encodeCNF (ψ a)).length (items (ψ a)) (T a)) := by
  let D3 : α × ℕ → Prop := fun q => D q.1 ∧ q.2 < (encodeCNF (ψ q.1)).length
  let D4 : (α × ℕ) × ℕ → Prop := fun r => D3 r.1 ∧ r.2 < r.1.2 + 1
  have up4 : ∀ {F : α → List Bool}, SP D ea F → SP D4 (ext (ext ea)) (fun r => F r.1.1) :=
    fun h => (h.up (D' := D3) (fun q hq => hq.1)).up (fun r hr => hr.1)
  have b4 : SP D4 (ext (ext ea)) (fun r =>
      bflag (decide ((itemAt (items (ψ r.1.1)) r.2).tail.tail = T r.1.1))) :=
    ((sp_item (up4 hx) sp_idx).post cpt_drop2).eqF (up4 hT)
  have i3 : SP D3 (ext ea) (fun q => innerR (items (ψ q.1)) (T q.1) q.2) :=
    SP.loop (D := D3) (ea := ext ea) (N := fun q => q.2 + 1)
      (B := fun q p' => bflag (decide ((itemAt (items (ψ q.1)) p').tail.tail = T q.1)))
      (sp_idx.add (sp_num 1)) b4
  have b3 : SP D3 (ext ea) (fun q => bflag (decide (innerR (items (ψ q.1)) (T q.1) q.2 = []))) :=
    i3.eqF (sp_const [])
  exact SP.loop (D := D) (ea := ea) (N := fun a => (encodeCNF (ψ a)).length)
    (B := fun a p => bflag (decide (innerR (items (ψ a)) (T a) p = []))) (sp_codeLen hx) b3

theorem ren_sp_body {ψ : α → CNF} (hx : SP D ea (fun a => encodeCNF (ψ a))) {It : α → List Bool}
    (hIt : SP D ea It) :
    SP D ea (fun a => bodyR (encodeCNF (ψ a)).length (items (ψ a)) (It a)) := by
  have hc : SP D ea (fun a => un (cntR (encodeCNF (ψ a)).length (items (ψ a)) (It a).tail.tail).length) :=
    (ren_sp_cnt hx (hIt.post cpt_drop2)).congr (fun a _ => ren_cnt_un _ _ _)
  have hlit : SP D ea (fun a => [true] ++ sel (signF (It a)) [false] [true] ++
      vcode (cntR (encodeCNF (ψ a)).length (items (ψ a)) (It a).tail.tail).length) :=
    ((sp_const [true]).app ((hIt.post cpt_signF).sel (sp_const [false]) (sp_const [true]))).app
      (ren_sp_vcodeOf hc)
  exact (hIt.sel (sp_const []) ((hIt.post SearchHelpers.KSat.Hard.cpt_isEndF).sel hlit
    (sp_const [false, false]))).congr (fun a _ => rfl)

end

abbrev ren_D1 : CNF × ℕ → Prop := fun q => True ∧ q.2 < (encodeCNF q.1).length

theorem ren_sp_x1 : SP ren_D1 (ext encodeCNF) (fun q => encodeCNF q.1) :=
  SP.up (D := fun _ => True) (ea := encodeCNF) (F := fun φ => encodeCNF φ) sp_id
    (fun _ _ => trivial)

theorem ren_sp_it : SP ren_D1 (ext encodeCNF) (fun q => itemAt (items q.1) q.2) :=
  sp_item (D := ren_D1) (ea := ext encodeCNF) (ψ := fun q => q.1) ren_sp_x1 sp_idx

theorem ren_sp_b1 : SP ren_D1 (ext encodeCNF) (fun q =>
    bodyR (encodeCNF q.1).length (items q.1) (itemAt (items q.1) q.2)) :=
  ren_sp_body (D := ren_D1) (ea := ext encodeCNF) (ψ := fun q => q.1) ren_sp_x1 ren_sp_it

theorem ren_sp_N : SP (fun _ => True) encodeCNF (fun φ : CNF => un (encodeCNF φ).length) :=
  sp_codeLen (D := fun _ => True) (ea := encodeCNF) (ψ := fun φ => φ) sp_id

theorem ren_sp_L : SP (fun _ => True) encodeCNF (fun φ : CNF =>
    (List.range (encodeCNF φ).length).flatMap
      (fun q => bodyR (encodeCNF φ).length (items φ) (itemAt (items φ) q))) :=
  SP.loop (D := fun _ => True) (ea := encodeCNF) (N := fun φ => (encodeCNF φ).length)
    (B := fun φ q => bodyR (encodeCNF φ).length (items φ) (itemAt (items φ) q)) ren_sp_N ren_sp_b1

theorem ren_sp_main : SP (fun _ => True) encodeCNF (fun φ => encodeCNF (renF φ)) := by
  refine ren_sp_L.congr (fun φ _ => ?_)
  rw [itemLoop (bodyR (encodeCNF φ).length (items φ)) (ren_body_nil _ _) (items φ) _
    (items_le_code φ)]
  exact ren_out_eq φ _ (items_le_code φ)

theorem ren_cpt : ComputableInPolyTime encodeCNF encodeCNF renF := cpt_of_SP ren_sp_main

theorem machineRen_renaming : PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.Search.encodeCNF (fun φ : PEqualNP.Search.CNF => φ.map (fun c : PEqualNP.Search.Clause => c.map (fun l : PEqualNP.Search.Literal => ((φ.flatMap (fun c' : PEqualNP.Search.Clause => c'.map some ++ [none])).findIdx (fun o : Option PEqualNP.Search.Literal => o.any (fun l' : PEqualNP.Search.Literal => l'.1 == l.1)), l.2)))) :=
  ren_cpt

end PEqualNP.MetaComplexity.MachineRen
