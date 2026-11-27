import PEqualNP.Defs
import PEqualNP.Search.Helpers.ResLinQ
import Mathlib.Tactic

/-!
# Helpers: from Res(lin) refutations to rectangle dags

A Res(lin) refutation with lines of at most `w` equations and coefficients bounded by `M`
gives a rectangle dag for the same formula, for any split of the variables, whose size is
the length of the refutation times a polynomial in `(2 * card V * M + 1) ^ w`. This is the
standard simulation (Sokolov 2017, Beame and Whitmeyer 2025).

Each line is cut into pieces: the points falsifying the line on which the first player's
partial sums of the equations take a fixed value vector. Each piece is a rectangle. A piece
of a derived line is covered by chains that sort its points by the value vectors of the
premises, ending in pieces of the premises.
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.Search

set_option linter.unusedSectionVars false

section

variable {V : Type} [Fintype V] [DecidableEq V] (side : V → Bool)
  (F : Set (PEqualNP.ProofComplexity.Clause V))

/-! ## Extensions of a rectangle dag -/

/-- `RectExt side F ρ β`: putting the list `β` in front of any valid dag that contains every
node of `ρ` gives a valid dag. -/
def RectExt (ρ β : List (Set (V → Bool))) : Prop :=
  ∀ ρ', IsRectDag side F ρ' → (∀ R ∈ ρ, R ∈ ρ') → IsRectDag side F (β ++ ρ')

variable {side F}

theorem rectExt_nil (ρ : List (Set (V → Bool))) : RectExt side F ρ [] :=
  fun _ h _ => h

theorem rectExt_split {ρ β : List (Set (V → Bool))} {R : Set (V → Bool)}
    (hβ : RectExt side F ρ β) (hR : IsRect side R)
    (h : ∃ R₁ ∈ β ++ ρ, ∃ R₂ ∈ β ++ ρ, R ⊆ R₁ ∪ R₂) : RectExt side F ρ (R :: β) := by
  intro ρ' hd hs
  obtain ⟨R₁, h1, R₂, h2, hsub⟩ := h
  have hm : ∀ X ∈ β ++ ρ, X ∈ β ++ ρ' := by
    intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (hs X h)
  exact IsRectDag.split (hβ ρ' hd hs) hR (hm _ h1) (hm _ h2) hsub

theorem rectExt_sink {ρ β : List (Set (V → Bool))} {R : Set (V → Bool)}
    (hβ : RectExt side F ρ β) (hR : IsRect side R)
    (hC : ∃ C ∈ F, ∀ a ∈ R, ¬ PEqualNP.ProofComplexity.ClauseSat a C) :
    RectExt side F ρ (R :: β) :=
  fun ρ' hd hs => IsRectDag.sink (hβ ρ' hd hs) hR hC

theorem rectExt_mono {ρ ρ₀ β : List (Set (V → Bool))} (h : RectExt side F ρ β)
    (hs : ∀ R ∈ ρ, R ∈ ρ₀) : RectExt side F ρ₀ β :=
  fun ρ' hd hs' => h ρ' hd fun R hR => hs' R (hs R hR)

theorem rectExt_append {ρ β₁ β₂ : List (Set (V → Bool))} (h1 : RectExt side F ρ β₁)
    (h2 : RectExt side F (β₁ ++ ρ) β₂) : RectExt side F ρ (β₂ ++ β₁) := by
  intro ρ' hd hs
  rw [List.append_assoc]
  apply h2 (β₁ ++ ρ') (h1 ρ' hd hs)
  intro R hR
  rcases List.mem_append.mp hR with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (hs R h)

theorem rectExt_flatMap {α : Type} {ρ : List (Set (V → Bool))} (g : α → List (Set (V → Bool)))
    (S : List α) (h : ∀ s ∈ S, RectExt side F ρ (g s)) : RectExt side F ρ (S.flatMap g) := by
  induction S with
  | nil => exact rectExt_nil ρ
  | cons s S ih =>
    rw [List.flatMap_cons]
    refine rectExt_append (ih fun x hx => h x (List.mem_cons_of_mem _ hx)) ?_
    exact rectExt_mono (h s List.mem_cons_self) fun R hR => List.mem_append_right _ hR

/-! ## Chains -/

theorem rect_inter {X : Set (V → Bool)} {f : (V → Bool) → List ℤ} (hX : IsRect side X)
    (hf : ∀ a b, f (mix side a b) = f a) (p : List ℤ → Prop) :
    IsRect side (X ∩ {a | p (f a)}) := by
  intro a ha b hb
  refine ⟨hX a ha.1 b hb.1, ?_⟩
  show p (f (mix side a b))
  rw [hf]
  exact ha.2

/-- The chain sorting the points of `X` by the value `f a` along the list `S`: the nodes
`X ∩ {a | f a ∈ S'}` for every suffix `S'` of `S`, longest first. -/
def rectChain (X : Set (V → Bool)) (f : (V → Bool) → List ℤ) :
    List (List ℤ) → List (Set (V → Bool))
  | [] => [X ∩ {a | f a ∈ ([] : List (List ℤ))}]
  | s :: S => (X ∩ {a | f a ∈ s :: S}) :: rectChain X f S

theorem rectChain_head (X : Set (V → Bool)) (f : (V → Bool) → List ℤ) (S : List (List ℤ)) :
    X ∩ {a | f a ∈ S} ∈ rectChain X f S := by
  cases S <;> simp [rectChain]

theorem rectChain_length (X : Set (V → Bool)) (f : (V → Bool) → List ℤ) (S : List (List ℤ)) :
    (rectChain X f S).length = S.length + 1 := by
  induction S with
  | nil => simp [rectChain]
  | cons s S ih => simp [rectChain, ih]

theorem rectChain_ext {ρ : List (Set (V → Bool))} {X : Set (V → Bool)}
    {f : (V → Bool) → List ℤ} (hX : IsRect side X) (hf : ∀ a b, f (mix side a b) = f a)
    (h0 : ∅ ∈ ρ) (S : List (List ℤ)) (hS : ∀ s ∈ S, ∃ R ∈ ρ, X ∩ {a | f a = s} ⊆ R) :
    RectExt side F ρ (rectChain X f S) := by
  induction S with
  | nil =>
    refine rectExt_split (rectExt_nil ρ) (rect_inter hX hf _) ⟨∅, by simpa using h0, ∅,
      by simpa using h0, ?_⟩
    intro a ha
    simp at ha
  | cons s S ih =>
    have ih' := ih fun x hx => hS x (List.mem_cons_of_mem _ hx)
    obtain ⟨R, hR, hsub⟩ := hS s List.mem_cons_self
    refine rectExt_split ih' (rect_inter hX hf _) ⟨R, List.mem_append_right _ hR,
      X ∩ {a | f a ∈ S}, List.mem_append_left _ (rectChain_head X f S), ?_⟩
    rintro a ⟨haX, hfa⟩
    rcases List.mem_cons.mp hfa with h | h
    · exact Or.inl (hsub ⟨haX, h⟩)
    · exact Or.inr ⟨haX, h⟩

/-! ## Values of the first player -/

variable (side)

/-- The first player's part of the left-hand side of `e` at `a`. -/
def aval (e : QEq V) (a : V → Bool) : ℤ :=
  ∑ v, if side v then e.1 v * (if a v then 1 else 0) else 0

/-- The second player's part of the left-hand side of `e` at `a`. -/
def bval (e : QEq V) (a : V → Bool) : ℤ :=
  ∑ v, if side v then 0 else e.1 v * (if a v then 1 else 0)

/-- The first player's value vector of a line. -/
def lineVec (L : QLine V) (a : V → Bool) : List ℤ := L.map fun e => aval side e a

/-- A piece of a line: the falsifying points with a given value vector. -/
def piece (L : QLine V) (t : List ℤ) : Set (V → Bool) :=
  {a | lineVec side L a = t ∧ ¬ QLine.Holds a L}

variable {side}

theorem holds_iff (e : QEq V) (a : V → Bool) :
    QEq.Holds a e ↔ aval side e a + bval side e a = e.2 := by
  unfold QEq.Holds aval bval
  rw [← Finset.sum_add_distrib]
  have : ∀ v, (if side v then e.1 v * (if a v then 1 else 0) else 0) +
      (if side v then 0 else e.1 v * (if a v then 1 else 0)) =
      e.1 v * (if a v then 1 else 0) := by
    intro v; split_ifs <;> simp
  simp only [this]

theorem aval_mix (e : QEq V) (a b : V → Bool) : aval side e (mix side a b) = aval side e a := by
  unfold aval mix
  exact Finset.sum_congr rfl fun v _ => by cases side v <;> simp

theorem bval_mix (e : QEq V) (a b : V → Bool) : bval side e (mix side a b) = bval side e b := by
  unfold bval mix
  exact Finset.sum_congr rfl fun v _ => by cases side v <;> simp

theorem lineVec_mix (L : QLine V) (a b : V → Bool) :
    lineVec side L (mix side a b) = lineVec side L a := by
  simp [lineVec, aval_mix]

theorem holds_mix (L : QLine V) {a b : V → Bool} (h : lineVec side L a = lineVec side L b) :
    QLine.Holds (mix side a b) L ↔ QLine.Holds b L := by
  have h' := List.map_inj_left.mp h
  unfold QLine.Holds
  constructor
  · rintro ⟨e, he, hh⟩
    refine ⟨e, he, ?_⟩
    rw [holds_iff] at hh ⊢
    rw [aval_mix, bval_mix, h' e he] at hh
    exact hh
  · rintro ⟨e, he, hh⟩
    refine ⟨e, he, ?_⟩
    rw [holds_iff] at hh ⊢
    rw [aval_mix, bval_mix, h' e he]
    exact hh

theorem piece_rect (L : QLine V) (t : List ℤ) : IsRect side (piece side L t) := by
  rintro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩
  refine ⟨by rw [lineVec_mix]; exact ha1, ?_⟩
  rw [holds_mix L (ha1.trans hb1.symm)]
  exact hb2

theorem holdsPart_rect (L L₁ : QLine V) (t s : List ℤ) :
    IsRect side (piece side L t ∩ {a | lineVec side L₁ a = s ∧ QLine.Holds a L₁}) := by
  rintro a ⟨ha0, ha1, ha2⟩ b ⟨hb0, hb1, hb2⟩
  refine ⟨piece_rect L t a ha0 b hb0, by rw [lineVec_mix]; exact ha1, ?_⟩
  rw [holds_mix L₁ (ha1.trans hb1.symm)]
  exact hb2

/-! ## Value vectors -/

/-- The integers from `-B` to `B`. -/
def valRange (B : ℕ) : List ℤ :=
  List.map (fun i : ℕ => (i : ℤ) - (B : ℤ)) (List.range (2 * B + 1))

/-- All lists of length `k` with entries from `-B` to `B`. -/
def valVecs (B : ℕ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (valRange B).flatMap fun x => (valVecs B k).map (x :: ·)

theorem mem_valRange {B : ℕ} {x : ℤ} (h : |x| ≤ B) : x ∈ valRange B := by
  simp only [valRange, List.mem_map, List.mem_range]
  refine ⟨(x + B).toNat, ?_, ?_⟩
  · rw [abs_le] at h; omega
  · rw [abs_le] at h; omega

theorem mem_valVecs {B : ℕ} (t : List ℤ) (h : ∀ x ∈ t, |x| ≤ B) : t ∈ valVecs B t.length := by
  induction t with
  | nil => simp [valVecs]
  | cons x t ih =>
    simp only [valVecs, List.length_cons, List.mem_flatMap, List.mem_map]
    exact ⟨x, mem_valRange (h x List.mem_cons_self),
      t, ih fun y hy => h y (List.mem_cons_of_mem _ hy), rfl⟩

theorem valVecs_length (B k : ℕ) : (valVecs B k).length = (2 * B + 1) ^ k := by
  induction k with
  | zero => simp [valVecs]
  | succ k ih =>
    simp only [valVecs, List.length_flatMap, List.length_map, ih]
    rw [List.map_const', List.sum_replicate, valRange, List.length_map, List.length_range,
      smul_eq_mul, pow_succ, mul_comm]

theorem aval_abs (e : QEq V) (a : V → Bool) {M : ℕ} (he : ∀ v, (e.1 v).natAbs ≤ M) :
    |aval side e a| ≤ (Fintype.card V * M : ℕ) := by
  unfold aval
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ v ∈ (Finset.univ : Finset V),
      |(if side v then e.1 v * (if a v then 1 else 0) else 0)| ≤ (M : ℤ) := by
    intro v _
    have hv : |e.1 v| ≤ (M : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast he v
    split_ifs <;> simp [hv]
  refine (Finset.sum_le_sum this).trans ?_
  simp

theorem lineVec_mem {L : QLine V} {M : ℕ} (hL : ∀ e ∈ L, ∀ v, (e.1 v).natAbs ≤ M)
    (a : V → Bool) : lineVec side L a ∈ valVecs (Fintype.card V * M) L.length := by
  have := mem_valVecs (B := Fintype.card V * M) (lineVec side L a) (by
    intro x hx
    simp only [lineVec, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact aval_abs e a (hL e he))
  simpa [lineVec] using this

/-! ## Blocks of nodes for one line -/

variable (side)

/-- The nodes covering one piece `piece L t` of a line with premises `L₁` and `L₂`. -/
def pieceBlock (B : ℕ) (L L₁ L₂ : QLine V) (t : List ℤ) : List (Set (V → Bool)) :=
  piece side L t ::
    (rectChain (piece side L t) (lineVec side L₁) (valVecs B L₁.length) ++
      (valVecs B L₁.length).flatMap fun s =>
        (piece side L t ∩ {a | lineVec side L₁ a = s}) ::
          rectChain (piece side L t ∩ {a | lineVec side L₁ a = s ∧ QLine.Holds a L₁})
            (lineVec side L₂) (valVecs B L₂.length))

/-- The nodes covering all pieces of a line with premises `L₁` and `L₂`. -/
def lineBlock (B : ℕ) (L L₁ L₂ : QLine V) : List (Set (V → Bool)) :=
  (valVecs B L.length).flatMap fun t => pieceBlock side B L L₁ L₂ t

variable {side}

theorem pieceBlock_ext {ρ : List (Set (V → Bool))} {M : ℕ} (L L₁ L₂ : QLine V) (t : List ℤ)
    (h0 : ∅ ∈ ρ)
    (h1 : ∀ s ∈ valVecs (Fintype.card V * M) L₁.length, piece side L₁ s ∈ ρ)
    (h2 : ∀ s ∈ valVecs (Fintype.card V * M) L₂.length, piece side L₂ s ∈ ρ)
    (hb1 : ∀ e ∈ L₁, ∀ v, (e.1 v).natAbs ≤ M) (hb2 : ∀ e ∈ L₂, ∀ v, (e.1 v).natAbs ≤ M)
    (hsound : ∀ a, ¬ QLine.Holds a L → QLine.Holds a L₁ → ¬ QLine.Holds a L₂) :
    RectExt side F ρ (pieceBlock side (Fintype.card V * M) L L₁ L₂ t) := by
  set B := Fintype.card V * M
  set S₁ := valVecs B L₁.length
  set S₂ := valVecs B L₂.length
  set P := piece side L t
  set flat := S₁.flatMap fun s =>
    (P ∩ {a | lineVec side L₁ a = s}) ::
      rectChain (P ∩ {a | lineVec side L₁ a = s ∧ QLine.Holds a L₁}) (lineVec side L₂) S₂
  have hflat : RectExt side F ρ flat := by
    refine rectExt_flatMap _ S₁ fun s hs => ?_
    have hc : RectExt side F ρ
        (rectChain (P ∩ {a | lineVec side L₁ a = s ∧ QLine.Holds a L₁}) (lineVec side L₂) S₂) := by
      refine rectChain_ext (holdsPart_rect L L₁ t s) (fun a b => lineVec_mix L₂ a b) h0 S₂ ?_
      intro s' hs'
      refine ⟨piece side L₂ s', h2 s' hs', ?_⟩
      rintro a ⟨⟨⟨_, haL⟩, _, haL₁⟩, has'⟩
      exact ⟨has', hsound a haL haL₁⟩
    refine rectExt_split hc
      (rect_inter (piece_rect L t) (fun a b => lineVec_mix L₁ a b) (fun x => x = s))
      ⟨piece side L₁ s, List.mem_append_right _ (h1 s hs), _,
        List.mem_append_left _ (rectChain_head _ _ S₂), ?_⟩
    rintro a ⟨haP, has⟩
    by_cases hh : QLine.Holds a L₁
    · exact Or.inr ⟨⟨haP, has, hh⟩, lineVec_mem hb2 a⟩
    · exact Or.inl ⟨has, hh⟩
  have hchain : RectExt side F (flat ++ ρ) (rectChain P (lineVec side L₁) S₁) := by
    refine rectChain_ext (piece_rect L t) (fun a b => lineVec_mix L₁ a b)
      (List.mem_append_right _ h0) S₁ ?_
    intro s hs
    refine ⟨P ∩ {a | lineVec side L₁ a = s}, List.mem_append_left _ ?_, le_rfl⟩
    exact List.mem_flatMap.mpr ⟨s, hs, List.mem_cons_self⟩
  have hboth := rectExt_append hflat hchain
  refine rectExt_split hboth (piece_rect L t) ⟨_, List.mem_append_left _
    (List.mem_append_left _ (rectChain_head P (lineVec side L₁) S₁)), _, List.mem_append_left _
    (List.mem_append_left _ (rectChain_head P (lineVec side L₁) S₁)), ?_⟩
  intro a ha
  exact Or.inl ⟨ha, lineVec_mem hb1 a⟩

theorem pieceBlock_length (B : ℕ) (L L₁ L₂ : QLine V) (t : List ℤ) {w : ℕ}
    (h1 : L₁.length ≤ w) (h2 : L₂.length ≤ w) :
    (pieceBlock side B L L₁ L₂ t).length ≤ 6 * ((2 * B + 1) ^ w) ^ 2 := by
  have hP : 1 ≤ (2 * B + 1) ^ w := Nat.one_le_pow _ _ (by omega)
  have hS₁ : (valVecs B L₁.length).length ≤ (2 * B + 1) ^ w := by
    rw [valVecs_length]; exact Nat.pow_le_pow_right (by omega) h1
  have hS₂ : (valVecs B L₂.length).length ≤ (2 * B + 1) ^ w := by
    rw [valVecs_length]; exact Nat.pow_le_pow_right (by omega) h2
  set P := (2 * B + 1) ^ w
  simp only [pieceBlock, List.length_cons, List.length_append, rectChain_length,
    List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul]
  have h3 := Nat.mul_le_mul hS₁ hS₂
  have h4 : P ≤ P * P := Nat.le_mul_of_pos_left P hP
  nlinarith

theorem lineBlock_length (B : ℕ) (L L₁ L₂ : QLine V) {w : ℕ} (h : L.length ≤ w)
    (h1 : L₁.length ≤ w) (h2 : L₂.length ≤ w) :
    (lineBlock side B L L₁ L₂).length ≤ 6 * ((2 * B + 1) ^ w) ^ 3 := by
  have hS : (valVecs B L.length).length ≤ (2 * B + 1) ^ w := by
    rw [valVecs_length]; exact Nat.pow_le_pow_right (by omega) h
  simp only [lineBlock, List.length_flatMap]
  have hsum := List.sum_le_length_nsmul
    ((valVecs B L.length).map fun t => (pieceBlock side B L L₁ L₂ t).length)
    (6 * ((2 * B + 1) ^ w) ^ 2) (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨t, _, rfl⟩ := hx
      exact pieceBlock_length B L L₁ L₂ t h1 h2)
  rw [List.length_map, smul_eq_mul] at hsum
  refine hsum.trans ?_
  calc (valVecs B L.length).length * (6 * ((2 * B + 1) ^ w) ^ 2)
      ≤ (2 * B + 1) ^ w * (6 * ((2 * B + 1) ^ w) ^ 2) := Nat.mul_le_mul_right _ hS
    _ = 6 * ((2 * B + 1) ^ w) ^ 3 := by ring

/-! ## The construction -/

theorem resLinQ_nonempty_of_derivation (π : List (QLine V)) (h : IsResLinQDerivation F π) :
    π ≠ [] → ∃ C, C ∈ F := by
  induction h with
  | nil => intro h; exact absurd rfl h
  | ax C _ hC _ _ => intro _; exact ⟨C, hC⟩
  | res _ _ _ h1 _ ih => intro _; exact ih (List.ne_nil_of_mem h1)
  | weaken _ hC _ ih => intro _; exact ih (List.ne_nil_of_mem hC)

theorem resLinQ_build (hF : ∃ C, C ∈ F) (M w : ℕ) (π : List (QLine V))
    (hπ : IsResLinQDerivation F π)
    (hb : ∀ L ∈ π, L.length ≤ w ∧ ∀ e ∈ L, ∀ v, (e.1 v).natAbs ≤ M) :
    ∃ ρ : List (Set (V → Bool)), IsRectDag side F ρ ∧ ∅ ∈ ρ ∧
      (∀ L ∈ π, ∀ t ∈ valVecs (Fintype.card V * M) L.length, piece side L t ∈ ρ) ∧
      ρ.length ≤ 1 + π.length * (6 * ((2 * (Fintype.card V * M) + 1) ^ w) ^ 3) := by
  set B := Fintype.card V * M
  set K := 6 * ((2 * B + 1) ^ w) ^ 3
  -- the generic step for a line with premises
  have step : ∀ (π : List (QLine V)) (L L₁ L₂ : QLine V), L₁ ∈ π → L₂ ∈ π →
      (∀ a, ¬ QLine.Holds a L → QLine.Holds a L₁ → ¬ QLine.Holds a L₂) →
      (∀ L' ∈ L :: π, L'.length ≤ w ∧ ∀ e ∈ L', ∀ v, (e.1 v).natAbs ≤ M) →
      (∃ ρ : List (Set (V → Bool)), IsRectDag side F ρ ∧ ∅ ∈ ρ ∧
        (∀ L ∈ π, ∀ t ∈ valVecs B L.length, piece side L t ∈ ρ) ∧
        ρ.length ≤ 1 + π.length * K) →
      ∃ ρ : List (Set (V → Bool)), IsRectDag side F ρ ∧ ∅ ∈ ρ ∧
        (∀ L' ∈ L :: π, ∀ t ∈ valVecs B L'.length, piece side L' t ∈ ρ) ∧
        ρ.length ≤ 1 + (L :: π).length * K := by
    intro π L L₁ L₂ hL₁ hL₂ hsound hb' ⟨ρ, hd, h0, hp, hl⟩
    have hb₁ := hb' L₁ (List.mem_cons_of_mem _ hL₁)
    have hb₂ := hb' L₂ (List.mem_cons_of_mem _ hL₂)
    have hbL := hb' L List.mem_cons_self
    have hext : RectExt side F ρ (lineBlock side B L L₁ L₂) :=
      rectExt_flatMap _ _ fun t _ =>
        pieceBlock_ext L L₁ L₂ t h0 (hp L₁ hL₁) (hp L₂ hL₂) hb₁.2 hb₂.2 hsound
    refine ⟨lineBlock side B L L₁ L₂ ++ ρ, hext ρ hd fun R hR => hR,
      List.mem_append_right _ h0, ?_, ?_⟩
    · intro L' hL' t ht
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, ht, List.mem_cons_self⟩)
      · exact List.mem_append_right _ (hp L' hL' t ht)
    · have := lineBlock_length (side := side) B L L₁ L₂ hbL.1 hb₁.1 hb₂.1
      simp only [List.length_append, List.length_cons]
      simp only [K] at hl this ⊢
      nlinarith
  induction hπ with
  | nil =>
    refine ⟨[∅], IsRectDag.sink IsRectDag.nil (by intro a ha; simp at ha)
      (by obtain ⟨C, hC⟩ := hF; exact ⟨C, hC, by simp⟩), by simp, by simp, by simp⟩
  | @ax π L C _ hC hLC ih =>
    obtain ⟨ρ, hd, h0, hp, hl⟩ := ih fun L' hL' => hb L' (List.mem_cons_of_mem _ hL')
    have hext : RectExt side F ρ ((valVecs B L.length).flatMap fun t => [piece side L t]) := by
      refine rectExt_flatMap _ _ fun t _ => rectExt_sink (rectExt_nil ρ) (piece_rect L t)
        ⟨C, hC, fun a ha hsat => ha.2 ?_⟩
      obtain ⟨l, hl, hal⟩ := hsat
      exact ⟨litQEq l, (hLC _).mpr ⟨l, hl, rfl⟩, litQEq_holds a l hal⟩
    refine ⟨_ ++ ρ, hext ρ hd fun R hR => hR, List.mem_append_right _ h0, ?_, ?_⟩
    · intro L' hL' t ht
      rcases List.mem_cons.mp hL' with rfl | hL'
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, ht, List.mem_singleton_self _⟩)
      · exact List.mem_append_right _ (hp L' hL' t ht)
    · have hS : (valVecs B L.length).length ≤ (2 * B + 1) ^ w := by
        rw [valVecs_length]
        exact Nat.pow_le_pow_right (by omega) (hb L List.mem_cons_self).1
      have hP : (2 * B + 1) ^ w ≤ K := by
        have h1 : 1 ≤ (2 * B + 1) ^ w := Nat.one_le_pow _ _ (by omega)
        have : (2 * B + 1) ^ w ≤ ((2 * B + 1) ^ w) ^ 3 := by
          calc (2 * B + 1) ^ w = ((2 * B + 1) ^ w) ^ 1 := (pow_one _).symm
            _ ≤ ((2 * B + 1) ^ w) ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
        simp only [K]
        omega
      have hlen : ((valVecs B L.length).flatMap fun t => [piece side L t]).length =
          (valVecs B L.length).length := by
        simp [List.length_flatMap]
      simp only [List.length_append, List.length_cons, hlen]
      nlinarith
  | @res π e e' C D α β _ h1 h2 ih =>
    obtain hρ := ih fun L' hL' => hb L' (List.mem_cons_of_mem _ hL')
    refine step π _ (e :: C) (e' :: D) h1 h2 ?_ hb hρ
    intro a hn hh1 hh2
    apply hn
    obtain ⟨f, hf, hfa⟩ := hh1
    obtain ⟨g, hg, hga⟩ := hh2
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨_, List.mem_cons_self, combo_holds a f g α β hfa hga⟩
      · exact ⟨g, List.mem_cons_of_mem _ (List.mem_append_right _ hg), hga⟩
    · exact ⟨f, List.mem_cons_of_mem _ (List.mem_append_left _ hf), hfa⟩
  | @weaken π C D _ hC himp ih =>
    obtain hρ := ih fun L' hL' => hb L' (List.mem_cons_of_mem _ hL')
    exact step π D C C hC hC (fun a hn hh _ => hn (himp a hh)) hb hρ

end

/-- A Res(lin) refutation with lines of at most `w` equations and coefficients of absolute
value at most `M` gives a rectangle dag for the same formula, for any split `side`, of size at
most the length of the refutation times `(8 * (2 * card V * M + 1) ^ w) ^ 3`. -/
theorem resLinQ_to_rectDag {V : Type} [Fintype V] [DecidableEq V] (side : V → Bool)
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.Search.QLine V)) (M w : ℕ)
    (hπ : PEqualNP.Search.IsResLinQRefutation F π)
    (hb : ∀ L ∈ π, L.length ≤ w ∧ ∀ e ∈ L, ∀ v, (e.1 v).natAbs ≤ M) :
    ∃ ρ : List (Set (V → Bool)), PEqualNP.Search.IsRectDagFor side F ρ ∧
      ρ.length ≤ π.length * (8 * (2 * Fintype.card V * M + 1) ^ w) ^ 3 := by
  obtain ⟨hd, hnil⟩ := hπ
  have hF := resLinQ_nonempty_of_derivation π hd (List.ne_nil_of_mem hnil)
  obtain ⟨ρ, hρ, _, hp, hl⟩ := resLinQ_build (side := side) hF M w π hd hb
  refine ⟨ρ, ⟨hρ, ?_⟩, ?_⟩
  · have hm := hp [] hnil [] (by simp [valVecs])
    have heq : piece side ([] : QLine V) [] = Set.univ := by
      ext a; simp [piece, lineVec, QLine.Holds]
    rwa [heq] at hm
  · have hn : 1 ≤ π.length := List.length_pos_of_mem hnil
    have hP : 1 ≤ (2 * (Fintype.card V * M) + 1) ^ w := Nat.one_le_pow _ _ (by omega)
    rw [show 2 * Fintype.card V * M = 2 * (Fintype.card V * M) by ring, mul_pow]
    set P := ((2 * (Fintype.card V * M) + 1) ^ w) ^ 3
    have hP3 : 1 ≤ P := Nat.one_le_pow _ _ hP
    have h1 : 1 ≤ π.length * P := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    nlinarith

end PEqualNP.Search.Helpers
