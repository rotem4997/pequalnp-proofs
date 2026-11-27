import PEqualNP.MetaComplexity.Helpers.MachineOwnGeneric
import PEqualNP.MetaComplexity.Helpers.MachineOwnDefs
import PEqualNP.Library.SearchHelpers.SearchToDecision
import PEqualNP.Library.SearchHelpers.SatVerifier

/-!
# Helper module (proofs only): reading a CNF code inside a context

The code of a formula is the sequence of its items (each literal, and an end item closing each
clause). Item `q` is `headI (dropI^[q] x)` (library item functions), and a loop over `q` below
the code length visits every item once. From this, as string machines on any context that
carries the code of `ψ` and unary indices: the number of clauses, the widths (one loop), the width
of clause `i` (lookup), the item index `offO ψ i` (a loop sum), the first positive literal `fO ψ i`
(leading run of a per-item sign string), the code of literal `(i, j)`, its sign, and its variable
in unary (a loop over `u` below the code length testing `vcode u` against the variable code; the
variable is below the item count by the input type, so below the code length).
-/

namespace PEqualNP.MetaComplexity.MachineOwn

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
  PEqualNP.Library.SearchHelpers.SatV

local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ## Items -/

def items (ψ : CNF) : List (Option Literal) := ψ.flatMap (fun c => c.map some ++ [none])

def icode (o : Option Literal) : List Bool := o.elim [false, false] encodeLiteral

def itemAt (L : List (Option Literal)) (q : ℕ) : List Bool := (L[q]?).elim [] icode

theorem items_cons (c : Clause) (ψ : CNF) :
    items (c :: ψ) = (c.map some ++ [none]) ++ items ψ := by
  simp [items]

theorem encodeCNF_items (ψ : CNF) : encodeCNF ψ = (items ψ).flatMap icode := by
  induction ψ with
  | nil => rfl
  | cons c ψ ih =>
    rw [items_cons, List.flatMap_append, ← ih]
    simp [encodeCNF, encodeClause, icode, List.flatMap_map]

theorem dropI_icode (o : Option Literal) (r : List Bool) : dropI (icode o ++ r) = r := by
  cases o with
  | none => rfl
  | some l => exact dropI_lit l r

theorem headI_icode (o : Option Literal) (r : List Bool) : headI (icode o ++ r) = icode o := by
  cases o with
  | none => rfl
  | some l => exact headI_lit l r

theorem dropI_nil_iter (q : ℕ) : dropI^[q] [] = [] := Function.iterate_fixed rfl q

theorem headI_dropI_iter (L : List (Option Literal)) (q : ℕ) :
    headI (dropI^[q] (L.flatMap icode)) = itemAt L q := by
  induction q generalizing L with
  | zero =>
    cases L with
    | nil => rfl
    | cons o L => simp [itemAt, List.flatMap_cons, headI_icode]
  | succ q ih =>
    cases L with
    | nil => simp [dropI_nil_iter, itemAt]; rfl
    | cons o L =>
      rw [Function.iterate_succ_apply, List.flatMap_cons, dropI_icode, ih]
      simp [itemAt]

theorem icode_ne (o : Option Literal) : icode o ≠ [] := by
  cases o with
  | none => simp [icode]
  | some l => simp [icode, encodeLiteral]

theorem length_le_flat (L : List (Option Literal)) : L.length ≤ (L.flatMap icode).length := by
  induction L with
  | nil => simp
  | cons o L ih =>
    have := List.length_pos_of_ne_nil (icode_ne o)
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem items_length (ψ : CNF) :
    (items ψ).length = (ψ.map (fun c : Clause => c.length + 1)).sum := by
  induction ψ with
  | nil => rfl
  | cons c ψ ih => simp [items_cons, ih]; omega

theorem items_le_code (ψ : CNF) : (items ψ).length ≤ (encodeCNF ψ).length := by
  rw [encodeCNF_items]; exact length_le_flat _

/-- A loop over all `q` below a bound visits every item once. -/
theorem itemLoop (h : List Bool → List Bool) (h0 : h [] = []) (L : List (Option Literal))
    (N : ℕ) (hN : L.length ≤ N) :
    (List.range N).flatMap (fun q => h (itemAt L q)) = L.flatMap (fun o => h (icode o)) := by
  induction L generalizing N with
  | nil =>
    simp only [List.flatMap_nil]
    rw [List.flatMap_eq_nil_iff]
    intro q _
    simp [itemAt, h0]
  | cons o L ih =>
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    have e : ∀ q, itemAt (o :: L) (q + 1) = itemAt L q := fun q => by simp [itemAt]
    simp only [e]
    rw [ih M (by simp at hN; omega)]
    simp [itemAt]

/-- The item at index `offO ψ i + j`. -/
theorem items_at (ψ : CNF) (i j : ℕ) (hi : i < ψ.length) (hj : j ≤ wO ψ i) :
    itemAt (items ψ) (offO ψ i + j) =
      if j < wO ψ i then encodeLiteral (litO ψ i j) else [false, false] := by
  induction ψ generalizing i with
  | nil => simp at hi
  | cons c ψ ih =>
    cases i with
    | zero =>
      simp only [wO, List.getD_cons_zero] at hj ⊢
      have ho : offO (c :: ψ) 0 = 0 := by simp [offO]
      rw [ho, Nat.zero_add, itemAt, items_cons, List.append_assoc]
      by_cases h : j < c.length
      · rw [List.getElem?_append_left (by simpa using h)]
        simp [h, litO, icode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      · have hj' : j = c.length := by omega
        subst hj'
        rw [List.getElem?_append_right (by simp)]
        simp [icode]
    | succ i =>
      simp only [wO, List.getD_cons_succ] at hj ⊢
      have ho : offO (c :: ψ) (i + 1) = (c.length + 1) + offO ψ i := by
        simp [offO]
      have hl : litO (c :: ψ) (i + 1) j = litO ψ i j := by simp [litO]
      rw [ho, hl, itemAt, items_cons, List.getElem?_append_right (by simp; omega)]
      have e : c.length + 1 + offO ψ i + j - (c.map some ++ [none]).length = offO ψ i + j := by
        simp; omega
      rw [e]
      exact ih i (by simp at hi; omega) hj

/-! ## Small string facts -/

theorem un_flatMap_all (s : List Bool) : s.filterMap (fun _ => some true) = un s.length := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [ih, un_succ]

theorem cpt_unLen : CPTs (fun s => un s.length) :=
  filterMap_polyTime _ _ _ (fun _ : Bool => some true) (fun s => (un_flatMap_all s).symm)

theorem incB_iter (u : ℕ) : PEqualNP.Library.SearchHelpers.S2D.incB^[u] [] = Nat.bits u := by
  induction u with
  | zero => simp
  | succ u ih => rw [Function.iterate_succ_apply', ih, PEqualNP.Library.SearchHelpers.S2D.bits_succ]

theorem vcode_eq_dig (u : ℕ) :
    vcode u = PEqualNP.Library.SearchHelpers.S2D.dig (Nat.bits u) ++ [false, true] := rfl

theorem isEnd_icode (o : Option Literal) : isEnd (icode o) = o.isNone := by
  cases o with
  | none => rfl
  | some l => simpa [icode] using isEnd_lit l []

/-- Exactly one term of the sum is nonempty. -/
theorem sum_single (N v : ℕ) (hv : v < N) :
    (List.range N).flatMap (fun u => if u = v then un u else []) = un v := by
  have h0 : ∀ M, M ≤ v → (List.range M).flatMap (fun u => if u = v then un u else []) = [] := by
    intro M hM
    rw [List.flatMap_eq_nil_iff]
    intro u hu
    simp at hu
    simp; omega
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : v < N
    · rw [ih h]; simp; omega
    · have : v = N := by omega
      subst this
      rw [h0 v le_rfl]; simp

section

variable {α : Type} {D : α → Prop} {ea : α → List Bool} {ψ : α → CNF}

/-! ## Machines on a context carrying the code -/

theorem sp_item (hx : SP D ea (fun a => encodeCNF (ψ a))) {Q : α → ℕ}
    (hQ : SP D ea (fun a => un (Q a))) : SP D ea (fun a => itemAt (items (ψ a)) (Q a)) :=
  ((SP.iter SearchHelpers.KSat.Hard.cpt_dropI dropI_length hQ hx).post SearchHelpers.KSat.Hard.cpt_headI).congr
    (fun a _ => by rw [encodeCNF_items, headI_dropI_iter])

theorem sp_codeLen (hx : SP D ea (fun a => encodeCNF (ψ a))) :
    SP D ea (fun a => un (encodeCNF (ψ a)).length) := hx.post cpt_unLen

/-- An item loop: a fixed string function of each item, concatenated over all items. -/
theorem sp_itemLoop (hx : SP D ea (fun a => encodeCNF (ψ a))) {h : List Bool → List Bool}
    (hh : CPTs h) (h0 : h [] = []) :
    SP D ea (fun a => (items (ψ a)).flatMap (fun o => h (icode o))) := by
  have hb : SP (fun q : α × ℕ => D q.1 ∧ q.2 < (encodeCNF (ψ q.1)).length) (ext ea)
      (fun q => h (itemAt (items (ψ q.1)) q.2)) :=
    (sp_item (hx.up (fun q hq => hq.1)) sp_idx).post hh
  exact (SP.loop (sp_codeLen hx) hb).congr (fun a _ => itemLoop h h0 _ _ (items_le_code _))

theorem ncl_spec (φ : CNF) :
    (items φ).flatMap (fun o => bflag (isEnd (icode o))) = un φ.length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [items_cons, List.flatMap_append, ih]
    have : (c.map some).flatMap (fun o => bflag (isEnd (icode o))) = [] := by
      rw [List.flatMap_eq_nil_iff]; intro o ho
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp ho; simp [isEnd_icode, bflag]
    rw [List.flatMap_append, this]
    simp [isEnd_icode, bflag, un_succ]

theorem sp_ncl (hx : SP D ea (fun a => encodeCNF (ψ a))) : SP D ea (fun a => un (ψ a).length) :=
  (sp_itemLoop hx SearchHelpers.KSat.Hard.cpt_isEndF rfl).congr (fun a _ => ncl_spec _)

/-- One symbol per item: `[true]` for a literal, `[true, false]` for an end item. -/
def wsym (it : List Bool) : List Bool := sel it [] (sel (bflag (isEnd it)) [true] [true, false])

theorem cpt_wsym : CPTs wsym :=
  cpt_sel cpt_id (cpt_const []) (cpt_sel SearchHelpers.KSat.Hard.cpt_isEndF (cpt_const _) (cpt_const _))

theorem widths_spec (φ : CNF) :
    (items φ).flatMap (fun o => wsym (icode o)) = encNs (φ.map List.length) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [items_cons, List.flatMap_append, ih]
    have : (c.map some).flatMap (fun o => wsym (icode o)) = un c.length := by
      induction c with
      | nil => rfl
      | cons l c ihc =>
        simp only [List.map_cons, List.flatMap_cons, ihc, List.length_cons, un_succ]
        have h1 : icode (some l) ≠ [] := icode_ne _
        simp [wsym, sel, h1, isEnd_icode, bflag]
    simp only [List.flatMap_append, this, List.map_cons, encNs_cons, encN_eq]
    simp [wsym, icode, sel, bflag, isEnd]

theorem sp_widths (hx : SP D ea (fun a => encodeCNF (ψ a))) :
    SP D ea (fun a => encNs ((ψ a).map List.length)) :=
  (sp_itemLoop hx cpt_wsym rfl).congr (fun a _ => widths_spec _)

theorem getD_map_length (φ : CNF) (i : ℕ) : (φ.map List.length).getD i 0 = wO φ i := by
  simp [wO, List.getD_eq_getElem?_getD]
  cases φ[i]? <;> rfl

theorem sp_w (hx : SP D ea (fun a => encodeCNF (ψ a))) {I : α → ℕ}
    (hI : SP D ea (fun a => un (I a))) : SP D ea (fun a => un (wO (ψ a) (I a))) :=
  (((SP.iter cpt_dropN dropN_length hI (sp_widths hx)).post cpt_hd).post cpt_tail).congr
    (fun a _ => by rw [lookup_spec, getD_map_length])

theorem off_spec (φ : CNF) (i : ℕ) (hi : i ≤ φ.length) :
    (List.range i).flatMap (fun i' => un (wO φ i' + 1)) = un (offO φ i) := by
  induction i with
  | zero => simp [offO]
  | succ i ih =>
    rw [List.range_succ, List.flatMap_append, ih (by omega)]
    have ht : φ.take (i + 1) = φ.take i ++ [φ[i]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    have hw : wO φ i = (φ[i]'(by omega)).length := by
      simp [wO, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < φ.length by omega)]
    have ua : ∀ m n : ℕ, un m ++ un n = un (m + n) := fun m n => by
      simp only [un, List.replicate_add]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [ua]
    congr 1
    rw [hw]
    simp only [offO, ht, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega

theorem sp_off (hx : SP D ea (fun a => encodeCNF (ψ a))) {I : α → ℕ}
    (hI : SP D ea (fun a => un (I a))) (hD : ∀ a, D a → I a ≤ (ψ a).length) :
    SP D ea (fun a => un (offO (ψ a) (I a))) := by
  have hb : SP (fun q : α × ℕ => D q.1 ∧ q.2 < I q.1) (ext ea)
      (fun q => un (wO (ψ q.1) q.2 + 1)) :=
    (sp_w (hx.up (fun q hq => hq.1)) sp_idx).add (sp_num 1)
  exact (SP.loop hI hb).congr (fun a ha => off_spec _ _ (hD a ha))

/-! ## The first positive literal -/

/-- Per item: `[true]` for a negative literal, `[false]` for a positive one or an end item. -/
def ssym (it : List Bool) : List Bool :=
  sel (bflag (isEnd it)) (sel (hd it.tail) [true] [false]) [false]

theorem cpt_ssym : CPTs ssym :=
  cpt_sel SearchHelpers.KSat.Hard.cpt_isEndF (cpt_sel (cpt_comp cpt_tail cpt_hd) (cpt_const _) (cpt_const _))
    (cpt_const _)

theorem ssym_lit (l : Literal) : ssym (encodeLiteral l) = if l.2 then [false] else [true] := by
  rw [encodeLiteral_eq]
  cases h : l.2 <;> simp [ssym, isEnd, bflag, sel, hd]

theorem range_items (c : Clause) (F : Literal → List Bool) (Z : List Bool) :
    (List.range (c.length + 1)).flatMap
      (fun j => if j < c.length then F (c.getD j (0, false)) else Z) = c.flatMap F ++ Z := by
  induction c with
  | nil => simp
  | cons l c ih =>
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.length_cons, Nat.succ_lt_succ_iff, List.getD_cons_succ, ih]
    simp

theorem hd_signs (c : Clause) :
    hd (c.flatMap (fun l : Literal => if l.2 then [false] else [true]) ++ [false]) =
      un (c.findIdx (fun l : Literal => l.2)) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    cases h : l.2
    · simp only [List.flatMap_cons, h, List.findIdx_cons]
      simp [hd] at ih ⊢
      rw [ih]; simp [un_succ]
    · simp [List.findIdx_cons, h, hd]

theorem sp_f (hx : SP D ea (fun a => encodeCNF (ψ a))) {I : α → ℕ}
    (hI : SP D ea (fun a => un (I a))) (hD : ∀ a, D a → I a < (ψ a).length) :
    SP D ea (fun a => un (fO (ψ a) (I a))) := by
  have hb : SP (fun q : α × ℕ => D q.1 ∧ q.2 < wO (ψ q.1) (I q.1) + 1) (ext ea)
      (fun q => ssym (itemAt (items (ψ q.1)) (offO (ψ q.1) (I q.1) + q.2))) :=
    (sp_item (hx.up (fun q hq => hq.1))
      (((sp_off hx hI (fun a ha => (hD a ha).le)).up (fun q hq => hq.1)).add sp_idx)).post cpt_ssym
  refine ((SP.loop (B := fun a j => ssym (itemAt (items (ψ a)) (offO (ψ a) (I a) + j)))
    ((sp_w hx hI).add (sp_num 1)) hb).post cpt_hd).congr (fun a ha => ?_)
  have e : ∀ j ∈ List.range (wO (ψ a) (I a) + 1),
      ssym (itemAt (items (ψ a)) (offO (ψ a) (I a) + j)) =
        if j < wO (ψ a) (I a) then
          (fun l : Literal => if l.2 then [false] else [true]) ((ψ a).getD (I a) [] |>.getD j (0, false))
        else [false] := by
    intro j hj
    rw [items_at _ _ _ (hD a ha) (by simp at hj; omega)]
    by_cases h1 : j < wO (ψ a) (I a)
    · rw [if_pos h1, if_pos h1, ssym_lit]; rfl
    · rw [if_neg h1, if_neg h1]; rfl
  rw [List.flatMap_congr e]
  have := range_items ((ψ a).getD (I a) []) (fun l : Literal => if l.2 then [false] else [true]) [false]
  exact (congrArg hd this).trans (hd_signs _)

/-! ## The literal `(i, j)`: code, sign, variable -/

theorem sp_lit (hx : SP D ea (fun a => encodeCNF (ψ a))) {I J : α → ℕ}
    (hI : SP D ea (fun a => un (I a))) (hJ : SP D ea (fun a => un (J a)))
    (hD : ∀ a, D a → I a < (ψ a).length ∧ J a < wO (ψ a) (I a)) :
    SP D ea (fun a => encodeLiteral (litO (ψ a) (I a) (J a))) :=
  (sp_item hx ((sp_off hx hI (fun a ha => (hD a ha).1.le)).add hJ)).congr (fun a ha => by
    rw [items_at _ _ _ (hD a ha).1 (hD a ha).2.le, if_pos (hD a ha).2])

/-- The sign of a literal from its code. -/
def signF (it : List Bool) : List Bool := sel (hd it.tail) [] [true]

theorem cpt_signF : CPTs signF := cpt_sel (cpt_comp cpt_tail cpt_hd) (cpt_const _) (cpt_const _)

theorem signF_lit (l : Literal) : signF (encodeLiteral l) = bflag l.2 := by
  rw [encodeLiteral_eq]
  cases h : l.2 <;> simp [signF, bflag, sel, hd]

theorem sp_sign {L : α → Literal} (hL : SP D ea (fun a => encodeLiteral (L a))) :
    SP D ea (fun a => bflag (L a).2) :=
  (hL.post cpt_signF).congr (fun a _ => signF_lit _)

theorem sp_vcode {D' : α × ℕ → Prop} : SP D' (ext ea) (fun q => vcode q.2) :=
  (((SP.iterGrow PEqualNP.Library.SearchHelpers.S2D.cpt_incB 1
    PEqualNP.Library.SearchHelpers.S2D.incB_length sp_idx (sp_const [])).post
      PEqualNP.Library.SearchHelpers.S2D.cpt_dig).app (sp_const [false, true])).congr
    (fun q _ => by rw [incB_iter, vcode_eq_dig])

theorem cpt_drop2 : CPTs (fun s => s.tail.tail) := cpt_comp cpt_tail cpt_tail

theorem sp_var (hx : SP D ea (fun a => encodeCNF (ψ a))) {L : α → Literal}
    (hL : SP D ea (fun a => encodeLiteral (L a)))
    (hB : ∀ a, D a → (L a).1 < (encodeCNF (ψ a)).length) :
    SP D ea (fun a => un (L a).1) := by
  have h1 : SP (fun q : α × ℕ => D q.1 ∧ q.2 < (encodeCNF (ψ q.1)).length) (ext ea)
      (fun q => (encodeLiteral (L q.1)).tail.tail) :=
    SP.post (H := fun s => s.tail.tail) (F := fun q : α × ℕ => encodeLiteral (L q.1)) cpt_drop2
      (hL.up (D' := fun q : α × ℕ => D q.1 ∧ q.2 < (encodeCNF (ψ q.1)).length) (fun q hq => hq.1))
  have hb : SP (fun q : α × ℕ => D q.1 ∧ q.2 < (encodeCNF (ψ q.1)).length) (ext ea)
      (fun q => if vcode q.2 = (encodeLiteral (L q.1)).tail.tail then un q.2 else []) :=
    SP.ite (sp_vcode.eqF h1) sp_idx (sp_const [])
  refine (SP.loop (B := fun a u => if vcode u = (encodeLiteral (L a)).tail.tail then un u else [])
    (sp_codeLen hx) hb).congr (fun a ha => ?_)
  have e : ∀ u ∈ List.range (encodeCNF (ψ a)).length,
      (if vcode u = (encodeLiteral (L a)).tail.tail then un u else []) =
        (if u = (L a).1 then un u else []) := by
    intro u _
    have : (encodeLiteral (L a)).tail.tail = vcode (L a).1 := by simp [encodeLiteral_eq]
    rw [this]
    by_cases h : u = (L a).1
    · simp [h]
    · have h' : vcode u ≠ vcode (L a).1 := fun e => h (vcode_injective e)
      simp [h, h']
  rw [List.flatMap_congr e, sum_single _ _ (hB a ha)]

/-- The bound of the input type puts every variable below the code length. -/
theorem var_lt_code (φ : CNF)
    (hb : ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : Clause => c.length + 1)).sum)
    (i j : ℕ) (hi : i < φ.length) (hj : j < wO φ i) : (litO φ i j).1 < (encodeCNF φ).length := by
  have hc : φ.getD i [] ∈ φ := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hl : litO φ i j ∈ φ.getD i [] := by
    unfold litO; rw [List.getD_eq_getElem _ _ (show j < (φ.getD i []).length from hj)]
    exact List.getElem_mem _
  have := hb _ hc _ hl
  have h2 := items_le_code φ
  rw [items_length] at h2
  omega

end

end PEqualNP.MetaComplexity.MachineOwn
