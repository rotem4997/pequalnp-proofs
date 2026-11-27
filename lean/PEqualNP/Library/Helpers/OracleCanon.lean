import PEqualNP.Library.Helpers.OracleClock
import PEqualNP.Library.Helpers.OracleTranslate
import PEqualNP.Library.Helpers.StmtCountable
import PEqualNP.Library.Machines.Run
import Mathlib.Data.Finsupp.Encodable

/-!
# Every oracle machine behaves like one from a countable family

Helper module (proofs only, no statement may use it).

* `CodeData a b c d`: an oracle machine with stack indices `Fin a`, labels `Fin b`, internal
  states `Fin c` and every alphabet `Fin d`, with an input map `Bool → Fin d` and an accepting
  output symbol. `Code` gathers them over all sizes; it is a countable type (`code_countable`).
* `canonData M ιin o`: the translation of an oracle machine `M`, with input map `ιin` and output
  symbol `o`, onto such types. Only the finitely many symbols that can ever be on a stack (the
  pushed ones, the input symbols, and `o`) are kept, numbered in `Fin d`.
* `accepts_canon`: relative to every oracle, for every clock and input, the translation accepts
  exactly when `M` does.
-/

open Turing

namespace PEqualNP.Library.Helpers.Enum

/-- An oracle machine over finite numbered types, with input map and accepting symbol. -/
structure CodeData (a b c d : ℕ) where
  k₀ : Fin a
  k₁ : Fin a
  kq : Fin a
  main : Fin b
  ask : Fin b
  yes : Fin b
  no : Fin b
  init : Fin c
  m : Fin b → TM2.Stmt (fun _ : Fin a => Fin d) (Fin b) (Fin c)
  qb : Fin d → Bool
  ιin : Bool → Fin d
  o : Fin d

/-- The oracle machine of a code. -/
def CodeData.toM {a b c d : ℕ} (C : CodeData a b c d) : OracleTM2 where
  tm := @FinTM2.mk (Fin a) _ _ C.k₀ C.k₁ (fun _ => Fin d) (Fin b) C.main _ (Fin c) C.init _ _ C.m
  kq := C.kq
  queryBit := C.qb
  ask := C.ask
  yes := C.yes
  no := C.no

instance codeData_countable (a b c d : ℕ) : Countable (CodeData a b c d) := by
  let f : CodeData a b c d →
      (Fin a × Fin a × Fin a) × (Fin b × Fin b × Fin b × Fin b) × Fin c ×
        (Fin b → TM2.Stmt (fun _ : Fin a => Fin d) (Fin b) (Fin c)) × (Fin d → Bool) ×
        (Bool → Fin d) × Fin d :=
    fun C => ((C.k₀, C.k₁, C.kq), (C.main, C.ask, C.yes, C.no), C.init, C.m, C.qb, C.ιin, C.o)
  refine Function.Injective.countable (f := f) ?_
  intro C C' h
  cases C; cases C'
  simp only [f, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩, h8, h9, h10, h11, h12⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rfl

/-- All codes. -/
abbrev Code := Σ n : ℕ × ℕ × ℕ × ℕ, CodeData n.1 n.2.1 n.2.2.1 n.2.2.2

theorem code_countable : Countable Code := inferInstance

/-- Acceptance by a code within `t` steps. -/
def Code.Accepts (C : Code) (A : Language Bool) (t : ℕ) (x : List Bool) : Prop :=
  Enum.Accepts C.2.toM A C.2.ιin C.2.o t x

section canon

variable (M : OracleTM2) (ιin : Bool → M.tm.Γ M.tm.k₀) (o : M.tm.Γ M.tm.k₁)

/-- The symbols that can ever be on a stack, together with `o`. -/
def Tset : Set (Σ k, M.tm.Γ k) :=
  ((⋃ l, pushSet (M.tm.m l)) ∪ Set.range (fun b => (⟨M.tm.k₀, ιin b⟩ : Σ k, M.tm.Γ k))) ∪
    {⟨M.tm.k₁, o⟩}

theorem Tset_finite : (Tset M ιin o).Finite := by
  have := M.tm.ΛFin
  have := M.tm.σFin
  exact ((Set.finite_iUnion (fun l => pushSet_finite (M.tm.m l))).union
    (Set.finite_range _)).union (Set.finite_singleton _)

/-- The number of kept symbols. -/
noncomputable def dT : ℕ := Nat.card (Tset M ιin o)

/-- Numbering of the kept symbols. -/
noncomputable def tEquiv : Tset M ιin o ≃ Fin (dT M ιin o) :=
  have := (Tset_finite M ιin o).to_subtype
  Finite.equivFin _

open Classical in
/-- The symbol map: kept symbols by their number, others to the last value. -/
noncomputable def piT (x : Σ k, M.tm.Γ k) : Fin (dT M ιin o + 1) :=
  if h : x ∈ Tset M ιin o then (tEquiv M ιin o ⟨x, h⟩).castSucc else Fin.last _

theorem piT_inj {x y : Σ k, M.tm.Γ k} (hx : x ∈ Tset M ιin o) (hy : y ∈ Tset M ιin o)
    (h : piT M ιin o x = piT M ιin o y) : x = y := by
  unfold piT at h
  rw [dif_pos hx, dif_pos hy] at h
  have := (tEquiv M ιin o).injective (Fin.castSucc_injective _ h)
  exact congrArg Subtype.val this

open Classical in
/-- The partial inverse of the symbol map on stack `k`. -/
noncomputable def iotaT (k : M.tm.K) (i : Fin (dT M ιin o + 1)) : Option (M.tm.Γ k) :=
  if h : ∃ s, (⟨k, s⟩ : Σ k, M.tm.Γ k) ∈ Tset M ιin o ∧ piT M ιin o ⟨k, s⟩ = i then
    some h.choose else none

theorem iotaT_piT (k : M.tm.K) (s : M.tm.Γ k) (hs : (⟨k, s⟩ : Σ k, M.tm.Γ k) ∈ Tset M ιin o) :
    iotaT M ιin o k (piT M ιin o ⟨k, s⟩) = some s := by
  have hex : ∃ s', (⟨k, s'⟩ : Σ k, M.tm.Γ k) ∈ Tset M ιin o ∧
      piT M ιin o ⟨k, s'⟩ = piT M ιin o ⟨k, s⟩ := ⟨s, hs, rfl⟩
  unfold iotaT
  rw [dif_pos hex]
  have h := piT_inj M ιin o hex.choose_spec.1 hs hex.choose_spec.2
  rw [Sigma.mk.inj_iff] at h
  exact congrArg some (eq_of_heq h.2)

/-- Numbering of the stack indices. -/
noncomputable def eK : M.tm.K ≃ Fin (@Fintype.card M.tm.K M.tm.kFin) :=
  @Fintype.equivFin M.tm.K M.tm.kFin

/-- Numbering of the labels. -/
noncomputable def eΛ : M.tm.Λ ≃ Fin (@Fintype.card M.tm.Λ M.tm.ΛFin) :=
  @Fintype.equivFin M.tm.Λ M.tm.ΛFin

/-- Numbering of the internal states. -/
noncomputable def eσ : M.tm.σ ≃ Fin (@Fintype.card M.tm.σ M.tm.σFin) :=
  @Fintype.equivFin M.tm.σ M.tm.σFin

/-- The translated machine as a code. -/
noncomputable def canonData : CodeData (@Fintype.card M.tm.K M.tm.kFin)
    (@Fintype.card M.tm.Λ M.tm.ΛFin) (@Fintype.card M.tm.σ M.tm.σFin) (dT M ιin o + 1) where
  k₀ := eK M M.tm.k₀
  k₁ := eK M M.tm.k₁
  kq := eK M M.kq
  main := eΛ M M.tm.main
  ask := eΛ M M.ask
  yes := eΛ M M.yes
  no := eΛ M M.no
  init := eσ M M.tm.initialState
  m := fun l => tr (eK M) (eΛ M) (eσ M) (piT M ιin o) (iotaT M ιin o) (M.tm.m ((eΛ M).symm l))
  qb := fun i => (iotaT M ιin o M.kq i).elim false M.queryBit
  ιin := fun b => piT M ιin o ⟨M.tm.k₀, ιin b⟩
  o := piT M ιin o ⟨M.tm.k₁, o⟩

/-- The translated machine as a code. -/
noncomputable def canon : Code :=
  ⟨(@Fintype.card M.tm.K M.tm.kFin, @Fintype.card M.tm.Λ M.tm.ΛFin,
    @Fintype.card M.tm.σ M.tm.σFin, dT M ιin o + 1), canonData M ιin o⟩

/-- The translation of configurations. -/
noncomputable abbrev cmap (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ) :
    TM2.Cfg (canonData M ιin o).toM.tm.Γ (canonData M ιin o).toM.tm.Λ
      (canonData M ιin o).toM.tm.σ :=
  mapC (eK M) (eΛ M) (eσ M) (piT M ιin o) c

theorem hιT : ∀ k s, (⟨k, s⟩ : Σ k, M.tm.Γ k) ∈ Tset M ιin o →
    iotaT M ιin o k (piT M ιin o ⟨k, s⟩) = some s := iotaT_piT M ιin o

theorem pushSet_sub (l : M.tm.Λ) : pushSet (M.tm.m l) ⊆ Tset M ιin o :=
  fun _ hx => Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨l, hx⟩))

open Classical in
theorem step_canon (A : Language Bool) (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ)
    (hc : Good (Tset M ιin o) c.stk) :
    (canonData M ιin o).toM.step A (cmap M ιin o c) = (M.step A c).map (cmap M ιin o) ∧
      ∀ c', M.step A c = some c' → Good (Tset M ιin o) c'.stk := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    refine ⟨rfl, ?_⟩
    intro c' h
    simp [OracleTM2.step] at h
  | some l =>
    by_cases hl : l = M.ask
    · subst hl
      have hq : ((mapS (eK M) (piT M ιin o) S (eK M M.kq)).reverse.map
          (canonData M ιin o).qb) = (S M.kq).reverse.map M.queryBit := by
        rw [mapS_apply, ← List.map_reverse, List.map_map]
        refine List.map_congr_left (fun s hs => ?_)
        simp only [Function.comp, canonData]
        rw [iotaT_piT M ιin o _ _ (hc _ s (List.mem_reverse.mp hs))]
        rfl
      have hgood : Good (Tset M ιin o) (Function.update S M.kq []) :=
        good_update _ hc _ _ (by simp)
      have e1 : (cmap M ιin o ⟨some M.ask, v, S⟩).l = some (canonData M ιin o).toM.ask := rfl
      have e2 : (⟨some M.ask, v, S⟩ : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ).l = some M.ask := rfl
      refine ⟨?_, ?_⟩
      · unfold OracleTM2.step
        rw [if_pos e1, if_pos e2]
        simp only [Option.map_some]
        congr 1
        show (⟨some (if (mapS (eK M) (piT M ιin o) S (eK M M.kq)).reverse.map
            (canonData M ιin o).qb ∈ A then eΛ M M.yes else eΛ M M.no), eσ M v,
            Function.update (mapS (eK M) (piT M ιin o) S) (eK M M.kq) []⟩ :
              TM2.Cfg (fun _ => Fin (dT M ιin o + 1)) _ _) = mapC (eK M) (eΛ M) (eσ M) (piT M ιin o) _
        rw [hq]
        simp only [mapC, mapS_update, List.map_nil, Option.map_some, apply_ite (eΛ M)]
      · intro c' h
        unfold OracleTM2.step at h
        rw [if_pos e2] at h
        cases h
        exact hgood
    · have hl' : eΛ M l ≠ eΛ M M.ask := fun h => hl ((eΛ M).injective h)
      have key := stepAux_tr (eK M) (eΛ M) (eσ M) (Tset M ιin o) (hιT M ιin o) (M.tm.m l)
        (pushSet_sub M ιin o l) v S hc
      have e1 : ¬ (cmap M ιin o ⟨some l, v, S⟩).l = some (canonData M ιin o).toM.ask :=
        fun h => hl' (Option.some.inj h)
      have e2 : ¬ (⟨some l, v, S⟩ : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ).l = some M.ask :=
        fun h => hl (Option.some.inj h)
      refine ⟨?_, ?_⟩
      · unfold OracleTM2.step
        rw [if_neg e1, if_neg e2]
        show some (TM2.stepAux (tr (eK M) (eΛ M) (eσ M) (piT M ιin o) (iotaT M ιin o)
          (M.tm.m ((eΛ M).symm (eΛ M l)))) (eσ M v) (mapS (eK M) (piT M ιin o) S)) =
            some (mapC (eK M) (eΛ M) (eσ M) (piT M ιin o) (TM2.stepAux (M.tm.m l) v S))
        rw [Equiv.symm_apply_apply, key.1]
      · intro c' h
        unfold OracleTM2.step at h
        rw [if_neg e2] at h
        cases h
        exact key.2

theorem run_canon (A : Language Bool) (n : ℕ) : ∀ (c : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ),
    Good (Tset M ιin o) c.stk →
      runFrom (canonData M ιin o).toM A (cmap M ιin o c) n = (runFrom M A c n).map (cmap M ιin o) ∧
        ∀ c', runFrom M A c n = some c' → Good (Tset M ιin o) c'.stk := by
  induction n with
  | zero =>
    intro c hc
    refine ⟨rfl, fun c' h => ?_⟩
    rw [runFrom_zero] at h
    cases h
    exact hc
  | succ n ih =>
    intro c hc
    obtain ⟨h1, h2⟩ := step_canon M ιin o A c hc
    rw [runFrom_succ, runFrom_succ, h1]
    cases hs : M.step A c with
    | none => exact ⟨rfl, fun c' h => by cases h⟩
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      exact ih c' (h2 c' hs)

theorem init_canon (x : List Bool) :
    cmap M ιin o (initList M.tm (x.map ιin)) =
      initList (canonData M ιin o).toM.tm (x.map (canonData M ιin o).ιin) := by
  rw [Machines.initList_eq, Machines.initList_eq]
  show (⟨some (eΛ M M.tm.main), eσ M M.tm.initialState,
      mapS (eK M) (piT M ιin o) (Function.update (fun _ => []) M.tm.k₀ (x.map ιin))⟩ :
        TM2.Cfg (fun _ : Fin _ => Fin (dT M ιin o + 1)) _ _) =
      ⟨some (eΛ M M.tm.main), eσ M M.tm.initialState, Function.update (fun _ => [])
        (eK M M.tm.k₀) (x.map (fun b => piT M ιin o ⟨M.tm.k₀, ιin b⟩))⟩
  rw [mapS_update, mapS_empty, List.map_map]
  rfl

theorem halt_canon :
    cmap M ιin o (haltC M [o]) = haltC (canonData M ιin o).toM [(canonData M ιin o).o] := by
  unfold haltC
  rw [Machines.haltList_eq, Machines.haltList_eq]
  show (⟨none, eσ M M.tm.initialState,
      mapS (eK M) (piT M ιin o) (Function.update (fun _ => []) M.tm.k₁ [o])⟩ :
        TM2.Cfg (fun _ : Fin _ => Fin (dT M ιin o + 1)) (Fin _) _) =
      ⟨none, eσ M M.tm.initialState, Function.update (fun _ => [])
        (eK M M.tm.k₁) [piT M ιin o ⟨M.tm.k₁, o⟩]⟩
  rw [mapS_update, mapS_empty, List.map_cons, List.map_nil]

theorem good_init (x : List Bool) :
    Good (Tset M ιin o) (initList M.tm (x.map ιin)).stk := by
  rw [Machines.initList_eq]
  refine good_update _ (fun _ _ h => by cases h) _ _ (fun s hs => ?_)
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  exact Or.inl (Or.inr ⟨b, rfl⟩)

theorem good_halt : Good (Tset M ιin o) (haltC M [o]).stk := by
  unfold haltC
  rw [Machines.haltList_eq]
  refine good_update _ (fun _ _ h => by cases h) _ _ (fun s hs => ?_)
  rw [List.mem_singleton.mp hs]
  exact Or.inr rfl

theorem accepts_canon (A : Language Bool) (t : ℕ) (x : List Bool) :
    (canon M ιin o).Accepts A t x ↔ Accepts M A ιin o t x := by
  show Accepts (canonData M ιin o).toM A (canonData M ιin o).ιin (canonData M ιin o).o t x ↔ _
  unfold Accepts
  rw [← init_canon, ← halt_canon]
  refine exists_congr (fun s => and_congr_right (fun _ => ?_))
  obtain ⟨h1, h2⟩ := run_canon M ιin o A s _ (good_init M ιin o x)
  rw [h1]
  constructor
  · intro h
    obtain ⟨c', hc', e⟩ := Option.map_eq_some_iff.mp h
    rw [hc']
    exact congrArg some (mapC_inj (eK M) (eΛ M) (eσ M) (Tset M ιin o) (hιT M ιin o)
      (eΛ M).injective (h2 c' hc') (good_halt M ιin o) e)
  · intro h
    rw [h]
    rfl

end canon

end PEqualNP.Library.Helpers.Enum
