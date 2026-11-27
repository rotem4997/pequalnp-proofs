import PEqualNP.Defs
import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.SearchHelpers.TwoSatCPT
import PEqualNP.Library.Machines.LenLE

/-!
# Helper module (proofs only): string machines on a context, and the loop with a shared context

`SP D ea F`: some polynomial-time machine on bit strings sends the code `ea a` to `F a` for every
`a` with `D a`. Every closure below is one combinator of the library on bit strings:

* constants, appends (`cpt_app2`), selection (`cpt_sel`), post-composition (`cpt_comp`), unary
  products (`cpt_mulU2`), the equality flag (`TwoSat.cpt_eqF`), the length comparison
  (`LenCmp.lenLE_polyTime`);
* the context extended by a loop index, `ext ea (a, i) = pairB (un i) (ea a)`: lifting
  (`cpt_unpairB2`) and the index (`cpt_unpairB1`);
* the loop `SP.loop`: a body on the extended context, concatenated over `i < N a`, is again a
  string machine on the context (the library loop `cpt_flatMapRange` with `arg = id`).

A list of lists `S` is written `flatS S` (each list as `true` and its tuple code), so that its
code is `flatS S ++ [false]` and appends and concatenated loops are string appends and loops.
-/

namespace PEqualNP.MetaComplexity.MachineOwn

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
  PEqualNP.CircuitLowerBounds

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem own_cptE {f f' : List Bool → List Bool} (h : CPTs f) (e : ∀ a, f a = f' a) :
    CPTs f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- A string machine re-read on encoded inputs and outputs. -/
theorem own_lift {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {F : List Bool → List Bool} {f : α → β} (hF : CPTs F) (h : ∀ a, F (ea a) = eb (f a)) :
    ComputableInPolyTime ea eb f := by
  obtain ⟨c⟩ := hF
  have h1 : ComputableInPolyTime ea (fun x : List Bool => x) (fun a => F (ea a)) :=
    ⟨⟨c.toTM2ComputableAux, c.time, fun a => c.outputsFun (ea a)⟩⟩
  have e : (fun a => F (ea a)) = (fun a => eb (f a)) := funext h
  rw [e] at h1
  obtain ⟨c1⟩ := h1
  exact ⟨⟨c1.toTM2ComputableAux, c1.time, fun a => c1.outputsFun a⟩⟩

/-- A string machine computes `F` on the codes of the elements in the domain `D`. -/
def SP {α : Type} (D : α → Prop) (ea : α → List Bool) (F : α → List Bool) : Prop :=
  ∃ G : List Bool → List Bool, CPTs G ∧ ∀ a, D a → G (ea a) = F a

/-- The context extended by a loop index. -/
def ext {α : Type} (ea : α → List Bool) : α × ℕ → List Bool := fun q => pairB (un q.2) (ea q.1)

/-- A list of lists, each list as `true` and its tuple code, without the final terminator. -/
def flatS (S : List (List ℕ)) : List Bool := S.flatMap (fun t => true :: encL t)

@[simp] theorem flatS_nil : flatS [] = [] := rfl

theorem flatS_append (S T : List (List ℕ)) : flatS (S ++ T) = flatS S ++ flatS T := by
  simp [flatS]

theorem flatS_flatMap {β : Type} (L : List β) (B : β → List (List ℕ)) :
    flatS (L.flatMap B) = L.flatMap (fun b => flatS (B b)) := by
  simp [flatS, List.flatMap_assoc]

theorem flatS_single (t : List ℕ) : flatS [t] = true :: (encNs t ++ [false]) := by
  simp [flatS, encL]

theorem flatS_map {β : Type} (L : List β) (g : β → List ℕ) :
    flatS (L.map g) = L.flatMap (fun b => flatS [g b]) := by
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.map_cons, List.flatMap_cons, flatS] at ih ⊢; rw [ih]; simp

theorem encNs_flatMap {β : Type} (L : List β) (B : β → List ℕ) :
    encNs (L.flatMap B) = L.flatMap (fun b => encNs (B b)) := by
  simp [encNs, List.flatMap_assoc]

theorem encNs_map {β : Type} (L : List β) (g : β → ℕ) :
    encNs (L.map g) = L.flatMap (fun b => encN (g b)) := by
  induction L with
  | nil => rfl
  | cons b L ih => simp only [List.map_cons, List.flatMap_cons, encNs] at ih ⊢; rw [ih]

theorem encodeList_unary (t : List ℕ) :
    encodeList (fun a : ℕ => List.replicate a true ++ [false]) t = encL t := by
  induction t with
  | nil => rfl
  | cons a l ih =>
    simp only [encodeList, List.flatMap_cons, List.cons_append] at ih ⊢
    simp only [encL, encNs, List.flatMap_cons, encN, un, List.replicate_succ, List.cons_append,
      List.append_assoc] at ih ⊢
    rw [← ih]

theorem encodeList_LL (S : List (List ℕ)) :
    encodeList (encodeList (fun a : ℕ => List.replicate a true ++ [false])) S = flatS S ++ [false] := by
  rw [encodeList]
  simp only [encodeList_unary]
  rfl

section

variable {α : Type} {D : α → Prop} {ea : α → List Bool}

theorem SP.congr {F F' : α → List Bool} (h : SP D ea F) (e : ∀ a, D a → F a = F' a) :
    SP D ea F' := by
  obtain ⟨G, hG, eG⟩ := h
  exact ⟨G, hG, fun a ha => (eG a ha).trans (e a ha)⟩

theorem SP.mono {F : α → List Bool} {D' : α → Prop} (h : SP D ea F) (e : ∀ a, D' a → D a) :
    SP D' ea F := by
  obtain ⟨G, hG, eG⟩ := h
  exact ⟨G, hG, fun a ha => eG a (e a ha)⟩

theorem sp_const (l : List Bool) : SP D ea (fun _ => l) := ⟨fun _ => l, cpt_const l, fun _ _ => rfl⟩

theorem sp_id : SP D ea ea := ⟨fun x => x, cpt_id, fun _ _ => rfl⟩

theorem SP.app {F₁ F₂ : α → List Bool} (h₁ : SP D ea F₁) (h₂ : SP D ea F₂) :
    SP D ea (fun a => F₁ a ++ F₂ a) := by
  obtain ⟨G₁, hG₁, e₁⟩ := h₁
  obtain ⟨G₂, hG₂, e₂⟩ := h₂
  exact ⟨fun s => G₁ s ++ G₂ s, cpt_app2 hG₁ hG₂, fun a ha => by simp only [e₁ a ha, e₂ a ha]⟩

theorem SP.post {F : α → List Bool} {H : List Bool → List Bool} (hH : CPTs H) (h : SP D ea F) :
    SP D ea (fun a => H (F a)) := by
  obtain ⟨G, hG, e⟩ := h
  exact ⟨fun s => H (G s), cpt_comp hG hH, fun a ha => by simp only [e a ha]⟩

theorem SP.mulU {F₁ F₂ : α → List Bool} (h₁ : SP D ea F₁) (h₂ : SP D ea F₂) :
    SP D ea (fun a => PEqualNP.Library.Universal.mulU (F₁ a) (F₂ a)) := by
  obtain ⟨G₁, hG₁, e₁⟩ := h₁
  obtain ⟨G₂, hG₂, e₂⟩ := h₂
  exact ⟨fun s => PEqualNP.Library.Universal.mulU (G₁ s) (G₂ s), cpt_mulU2 hG₁ hG₂, fun a ha => by simp only [e₁ a ha, e₂ a ha]⟩

theorem SP.sel {F T E : α → List Bool} (hF : SP D ea F) (hT : SP D ea T) (hE : SP D ea E) :
    SP D ea (fun a => PEqualNP.Library.Universal.sel (F a) (T a) (E a)) := by
  obtain ⟨G₁, hG₁, e₁⟩ := hF
  obtain ⟨G₂, hG₂, e₂⟩ := hT
  obtain ⟨G₃, hG₃, e₃⟩ := hE
  exact ⟨fun s => PEqualNP.Library.Universal.sel (G₁ s) (G₂ s) (G₃ s), cpt_sel hG₁ hG₂ hG₃,
    fun a ha => by simp only [e₁ a ha, e₂ a ha, e₃ a ha]⟩

theorem SP.eqF {F₁ F₂ : α → List Bool} (h₁ : SP D ea F₁) (h₂ : SP D ea F₂) :
    SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (F₁ a = F₂ a))) := by
  obtain ⟨G₁, hG₁, e₁⟩ := h₁
  obtain ⟨G₂, hG₂, e₂⟩ := h₂
  exact ⟨fun s => PEqualNP.Library.Universal.bflag (decide (G₁ s = G₂ s)),
    PEqualNP.Library.SearchHelpers.TwoSat.cpt_eqF hG₁ hG₂, fun a ha => by simp only [e₁ a ha, e₂ a ha]⟩

theorem cpt_leS {a b : List Bool → List Bool} (ha : CPTs a) (hb : CPTs b) :
    CPTs (fun s => if decide ((a s).length ≤ (b s).length) then [true] else []) :=
  cpt_bitFlag (cpt_comp (cpt_pair hb ha) LenCmp.lenLE_polyTime)

theorem SP.leF {F₁ F₂ : α → List Bool} (h₁ : SP D ea F₁) (h₂ : SP D ea F₂) :
    SP D ea (fun a => if decide ((F₁ a).length ≤ (F₂ a).length) then [true] else []) := by
  obtain ⟨G₁, hG₁, e₁⟩ := h₁
  obtain ⟨G₂, hG₂, e₂⟩ := h₂
  exact ⟨fun s => if decide ((G₁ s).length ≤ (G₂ s).length) then [true] else [],
    cpt_leS hG₁ hG₂, fun a ha => by simp only [e₁ a ha, e₂ a ha]⟩

/-! ## Extended contexts and the loop -/

theorem SP.up {F : α → List Bool} (h : SP D ea F) {D' : α × ℕ → Prop}
    (hD : ∀ q, D' q → D q.1) : SP D' (ext ea) (fun q => F q.1) := by
  obtain ⟨G, hG, e⟩ := h
  exact ⟨fun s => G (unpairB s).2, cpt_comp cpt_unpairB2 hG,
    fun q hq => by simp only [ext, unpairB_pairB]; exact e q.1 (hD q hq)⟩

theorem sp_idx {D' : α × ℕ → Prop} : SP D' (ext ea) (fun q => un q.2) :=
  ⟨fun s => (unpairB s).1, cpt_unpairB1, fun q _ => by simp only [ext, unpairB_pairB]⟩

theorem SP.loop {N : α → ℕ} {B : α → ℕ → List Bool} (hN : SP D ea (fun a => un (N a)))
    (hB : SP (fun q => D q.1 ∧ q.2 < N q.1) (ext ea) (fun q => B q.1 q.2)) :
    SP D ea (fun a => (List.range (N a)).flatMap (B a)) := by
  obtain ⟨GN, hGN, eN⟩ := hN
  obtain ⟨GB, hGB, eB⟩ := hB
  refine ⟨fun s => (List.range (GN s).length).flatMap fun i => GB (pairB (un i) s),
    PEqualNP.Library.SearchHelpers.Tab.StepW.cpt_flatMapRange (arg := fun x => x) hGB hGN cpt_id,
    fun a ha => ?_⟩
  simp only [eN a ha, un_length]
  apply List.flatMap_congr
  intro i hi
  exact eB (a, i) ⟨ha, List.mem_range.mp hi⟩

/-! ## Numbers in unary -/

theorem sp_num (c : ℕ) : SP D ea (fun _ => un c) := sp_const _

theorem SP.add {A B : α → ℕ} (h₁ : SP D ea (fun a => un (A a))) (h₂ : SP D ea (fun a => un (B a))) :
    SP D ea (fun a => un (A a + B a)) :=
  (h₁.app h₂).congr (fun a _ => by simp only [un, List.replicate_add])

theorem SP.mul {A B : α → ℕ} (h₁ : SP D ea (fun a => un (A a))) (h₂ : SP D ea (fun a => un (B a))) :
    SP D ea (fun a => un (A a * B a)) :=
  (h₁.mulU h₂).congr (fun a _ => by simp [PEqualNP.Library.Universal.mulU])

theorem SP.encN {A : α → ℕ} (h : SP D ea (fun a => un (A a))) :
    SP D ea (fun a => PEqualNP.Library.Universal.encN (A a)) :=
  ((sp_const [true]).app (h.app (sp_const [false]))).congr (fun a _ => by
    simp [PEqualNP.Library.Universal.encN, un_succ])

/-! ## Flags: `bflag` of a decidable condition -/

theorem SP.ite {P : α → Prop} [DecidablePred P] {T E : α → List Bool}
    (hP : SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (P a))))
    (hT : SP D ea T) (hE : SP D ea E) : SP D ea (fun a => if P a then T a else E a) :=
  (hP.sel hE hT).congr (fun a _ => by
    by_cases h : P a <;> simp [h, PEqualNP.Library.Universal.bflag, PEqualNP.Library.Universal.sel])

theorem SP.eqN {A B : α → ℕ} (h₁ : SP D ea (fun a => un (A a))) (h₂ : SP D ea (fun a => un (B a))) :
    SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (A a = B a))) :=
  (h₁.eqF h₂).congr (fun a _ => by
    have : (un (A a) = un (B a)) ↔ A a = B a := ⟨un_inj, fun h => by rw [h]⟩
    simp only [this])

theorem SP.ltN {A B : α → ℕ} (h₁ : SP D ea (fun a => un (A a))) (h₂ : SP D ea (fun a => un (B a))) :
    SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (A a < B a))) :=
  ((h₁.add (sp_num 1)).leF h₂).congr (fun a _ => by
    simp only [un_length, PEqualNP.Library.Universal.bflag]
    by_cases h : A a < B a
    · simp [h, Nat.succ_le_of_lt h]
    · simp [h])

theorem SP.andF {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (h₁ : SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (P a))))
    (h₂ : SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (Q a)))) :
    SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (P a ∧ Q a))) :=
  (h₁.sel (sp_const []) h₂).congr (fun a _ => by
    by_cases hp : P a <;> by_cases hq : Q a <;>
      simp [hp, hq, PEqualNP.Library.Universal.bflag, PEqualNP.Library.Universal.sel])

theorem SP.notF {P : α → Prop} [DecidablePred P]
    (h₁ : SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (P a)))) :
    SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (¬ P a))) :=
  (h₁.sel (sp_const [true]) (sp_const [])).congr (fun a _ => by
    by_cases hp : P a <;> simp [hp, PEqualNP.Library.Universal.bflag, PEqualNP.Library.Universal.sel])

/-! ## Iteration and selection with refined domains -/

theorem SP.iter {g : List Bool → List Bool} (hg : CPTs g) (hgl : ∀ s, (g s).length ≤ s.length)
    {Q : α → ℕ} {X : α → List Bool} (hQ : SP D ea (fun a => un (Q a))) (hX : SP D ea X) :
    SP D ea (fun a => g^[Q a] (X a)) := by
  obtain ⟨GQ, hGQ, eQ⟩ := hQ
  obtain ⟨GX, hGX, eX⟩ := hX
  exact ⟨fun s => g^[(GQ s).length] (GX s), cpt_iterLen hg hgl hGQ hGX,
    fun a ha => by simp only [eQ a ha, eX a ha, un_length]⟩

theorem SP.iterGrow {g : List Bool → List Bool} (hg : CPTs g) (k : ℕ)
    (hgl : ∀ s, (g s).length ≤ s.length + k)
    {Q : α → ℕ} {X : α → List Bool} (hQ : SP D ea (fun a => un (Q a))) (hX : SP D ea X) :
    SP D ea (fun a => g^[Q a] (X a)) := by
  obtain ⟨GQ, hGQ, eQ⟩ := hQ
  obtain ⟨GX, hGX, eX⟩ := hX
  exact ⟨fun s => g^[(GQ s).length] (GX s), PEqualNP.Library.Universal.cpt_iterGrow hg k hgl hGQ hGX,
    fun a ha => by simp only [eQ a ha, eX a ha, un_length]⟩

theorem SP.iteD {P : α → Prop} [DecidablePred P] {T E : α → List Bool}
    (hP : SP D ea (fun a => PEqualNP.Library.Universal.bflag (decide (P a))))
    (hT : SP (fun a => D a ∧ P a) ea T) (hE : SP (fun a => D a ∧ ¬ P a) ea E) :
    SP D ea (fun a => if P a then T a else E a) := by
  obtain ⟨G₁, hG₁, e₁⟩ := hP
  obtain ⟨G₂, hG₂, e₂⟩ := hT
  obtain ⟨G₃, hG₃, e₃⟩ := hE
  refine ⟨fun s => PEqualNP.Library.Universal.sel (G₁ s) (G₃ s) (G₂ s), cpt_sel hG₁ hG₃ hG₂,
    fun a ha => ?_⟩
  simp only [e₁ a ha]
  by_cases h : P a
  · simp [h, PEqualNP.Library.Universal.bflag, PEqualNP.Library.Universal.sel, e₂ a ⟨ha, h⟩]
  · simp [h, PEqualNP.Library.Universal.bflag, PEqualNP.Library.Universal.sel, e₃ a ⟨ha, h⟩]

/-- The typed bridge: a string machine on the codes, everywhere, is a polynomial-time machine. -/
theorem cpt_of_SP {β : Type} {e : β → List Bool} {f : α → β}
    (h : SP (fun _ => True) ea (fun a => e (f a))) : ComputableInPolyTime ea e f := by
  obtain ⟨G, hG, eG⟩ := h
  exact own_lift hG (fun a => eG a trivial)

end

end PEqualNP.MetaComplexity.MachineOwn
