import PEqualNP.MetaComplexity.Helpers.FewNotBound
import PEqualNP.MetaComplexity.Helpers.OneNotPiece

/-!
# The few-NOT conditional: the plan module

Unverified, a conjecture on paper until a checker accepts a row. This file fixes the
vocabulary and the interfaces of the build, states one Prop per piece, and proves the
assembly: the pieces imply the recorded plane form of the conditional, through
a GENERAL family (sets of `d` points, two sharing at most one point, a kill bound `kappa`).

Recorded statements appear here verbatim as Props and are only ever hypotheses, never
imported or proved: L-meta-270 (`H270`), L-meta-669 (`H669`), L-meta-708 (`PSub`), L-meta-709
(`PSplit`), L-meta-713 (`H713`). The recursion of the plane is `fewNotBound` of
`Helpers/FewNotBound.lean`; the general recursion is `fewNotGenG`.
-/

namespace PEqualNP.MetaComplexity.FewNot

open PEqualNP.CircuitLowerBounds

/-- The recorded statement of the checked row L-meta-270, verbatim (a hypothesis). -/
def H270 : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

/-- The recorded statement of the row L-meta-669, verbatim (a hypothesis). -/
def H669 : Prop :=
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

/-- SUB-FAMILY: the recorded statement of L-meta-708, verbatim (a conjecture being proved elsewhere; a hypothesis here). -/
def PSub : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1)

/-- FIRST-NOT SPLIT: the recorded statement of L-meta-709, verbatim (a conjecture being proved elsewhere; a hypothesis here). -/
def PSplit : Prop :=
  ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨ ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ), s = s' + 1 ∧ gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } : PEqualNP.CircuitLowerBounds.Gate) :: post ∧ ins.length ≤ 2 ∧ (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ g' : PEqualNP.CircuitLowerBounds.Gate, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) → g'.inputs.length ≤ 2 → (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length, ∀ i : Fin (pre ++ g' :: post).length, ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s', ι' j = i

/-- The recorded statement of the row L-meta-713 (general count), verbatim (a hypothesis). -/
def H713 : Prop :=
  ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r


/-! ## Vocabulary -/

/-- The four family hypotheses of the plane: sets of `q + 1` points, two sets share at most
one point, two distinct points lie in a common set, a point lies in at most `q + 1` sets. -/
def Fam (n m q : ℕ) (S : Fin m → Finset (Fin n)) : Prop :=
  (∀ i : Fin m, (S i).card = q + 1) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) ∧
  (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1)

/-- Gates AND, OR, NOT, each reading at most two wires (the clause of the target term). -/
def OpsOK (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

/-- Gates AND, OR, each reading at most two wires (the clause of `on1_piece_h` and of
L-meta-669). -/
def AndOr2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

/-- At most `s` NOT gates, by an index map (the clause of the target term). -/
def NotAtMost (s : ℕ) (gates : List Gate) : Prop :=
  ∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not → ∃ j : Fin s, ι j = i

/-- The window W(y, K): inputs with every point of `y` true and at most `K` further true
points. -/
def Win {n : ℕ} (y : Finset (Fin n)) (K : ℕ) (x : Fin n → Bool) : Prop :=
  (∀ p ∈ y, x p = true) ∧ (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K

/-- The window clause of the target term, literally: the outputs of the sets missing `y` are
right on the window W(y, K). -/
def Right {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → (∀ p ∈ y, x p = true) →
    (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K →
    Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)

theorem fnp_right_iff_win {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates : List Gate) (out : Fin m → ℕ) :
    Right S y K gates out ↔ ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → Win y K x →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) :=
  ⟨fun h w x hd hw => h w x hd hw.1 hw.2, fun h w x hd h1 h2 => h w x hd ⟨h1, h2⟩⟩

/-- The plane claim at `s` NOT gates, for one family, all `b K y gates out`. -/
def Claim (n m q : ℕ) (S : Fin m → Finset (Fin n)) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotBound m q s b K ≤ gates.length

/-- The conclusion of the target term (after the two hypotheses), in the vocabulary. -/
def BoundPlane : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) →
    (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1) →
    ∀ s : ℕ, Claim n m q S s

/-- The target term in the vocabulary. -/
def TargetPlane : Prop := H270 → H669 → BoundPlane

/-- Plan step 2, the plane COUNT (being proved elsewhere; the recorded L-meta-686 is not
complete in this tree, so this is the plan's own text): at least `m - (b q + 1)` sets miss a
set of at most `b` points. -/
def PCount : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), Fam n m q S → ∀ (b : ℕ) (y : Finset (Fin n)),
    y.card ≤ b → (if b = 0 then m else m - (b * q + 1)) ≤
      (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card

/-! ## The general family (sets of `d` points, a kill bound `kappa`) -/

/-- The general recursion: leaf yield `(m - kappa b) * min K (d - 1)`, step a maximum over
EVERY split point `j ≤ K` (the step uses only `j ≤ K`, never `d`). For the plane (`d = q + 1`,
`kappaPlane q`) the recorded `fewNotBound` (range `j ≤ min K (q + 1)`) is a LOWER bound of it
(`fnp_plane_le_genG`). -/
def fewNotGenG (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (m - kappa b') * min K' (d - 1))
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (K' + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

theorem fnp_genG_zero (m d : ℕ) (kappa : ℕ → ℕ) (b K : ℕ) :
    fewNotGenG m d kappa 0 b K = (m - kappa b) * min K (d - 1) := rfl

theorem fnp_genG_succ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) :
    fewNotGenG m d kappa (s + 1) b K = (List.range (K + 1)).foldr
      (fun (j acc : ℕ) => max acc (min (fewNotGenG m d kappa s (b + j) (K - j))
        (fewNotGenG m d kappa s b j))) 0 := rfl

/-- The general family: every set has `d` points, two sets share at most one point, and the
KILL BOUND at the current base: a set `y` of at most `b` points meets at most `kappa b` of the
sets (a count of the sets NOT disjoint from `y`: no natural subtraction). -/
def FamG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) : Prop :=
  (∀ i : Fin m, (S i).card = d) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ (b : ℕ) (y : Finset (Fin n)), y.card ≤ b →
    (Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y)).card ≤ kappa b)

/-- The general claim at `s` NOT gates: for the CURRENT base `y` (at most `b` points). -/
def ClaimG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotGenG m d kappa s b K ≤ gates.length

/-- The general conclusion. -/
def BoundG : Prop :=
  ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ), FamG n m d S kappa →
    ∀ s : ℕ, ClaimG n m d S kappa s

/-- The split as the step uses it, at `s + 1` NOT gates (proved from the row: `fnp_splitS`). -/
def PSplitS : Prop :=
  ∀ (gates : List Gate) (s : ℕ), OpsOK gates → NotAtMost (s + 1) gates →
    NotAtMost s gates ∨
    ∃ (pre post : List Gate) (ins : List ℕ),
      gates = pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post ∧ AndOr2 pre ∧
      OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post)

theorem fnp_splitS (h : PSplit) : PSplitS := by
  intro gates s hops hnot
  rcases h (s + 1) gates hops hnot with hno | ⟨s', pre, post, ins, hs, heq, _, hpre, hvar⟩
  · left
    obtain ⟨ι, _⟩ := hnot
    refine ⟨fun _ => ι 0, fun i hi => ?_⟩
    rcases (hno _ (List.get_mem gates i)).1 with h' | h' <;> rw [h'] at hi <;> cases hi
  · obtain rfl : s' = s := by omega
    right
    have ha := hvar { op := GateOp.and, inputs := [] } (Or.inl rfl) (by simp)
    have ho := hvar { op := GateOp.or, inputs := [] } (Or.inr rfl) (by simp)
    exact ⟨pre, post, ins, heq, hpre, ha.1, ho.1, ha.2, ho.2⟩

/-- L-meta-669 at the base: `T` the points FORCED TRUE (the base `y`), `Z` the forced-false
ones (none in a window: `Z = ∅`). In the recorded text `T` wins on an overlap (`if i ∈ T then
true else if i ∈ Z then false else x i`). -/
def H669at : Prop :=
  ∀ (n : ℕ) (gates : List Gate) (y : Finset (Fin n)), AndOr2 gates →
    ∃ (gates' : List Gate) (r : ℕ → ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      gates'.length ≤ gates.length ∧ ∀ o : ℕ,
      (∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i)) ≠
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x' i))) →
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i))

theorem fnp_669_at (h : H669) : H669at := fun n gates y hg => h n gates y ∅ hg

/-- General BASE CASE: from L-meta-270, L-meta-669 at the base (`T = y`, `Z = ∅`) and the
sub-family row L-meta-708, the claim at no NOT gate. -/
def PBaseG : Prop :=
  H270 → H669at → PSub → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ClaimG n m d S kappa 0

/-- General STEP: from the split, the claim at `s` gives the claim at `s + 1` (with the
built pieces `on1_piece_h`, `on1_piece_d`, `on1_piece_u_cheap` and `fn_foldr_max_le`). -/
def PStepG : Prop :=
  PSplitS → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ∀ s : ℕ, ClaimG n m d S kappa s → ClaimG n m d S kappa (s + 1)

/-- MONOTONICITY of `fewNotGenG` (a statement, NOT a hypothesis of the assembly: the step does not
need it, because `ClaimG` is stated for `y.card ≤ b` and `Right` on the smaller window
follows from `Right` on the larger one). Up in `K`, down in `s`, and down in `b` when `kappa`
is monotone (without that, down in `b` fails: see the report). -/
def PMono : Prop :=
  ∀ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ),
    fewNotGenG m d kappa s b K ≤ fewNotGenG m d kappa s b (K + 1) ∧
    fewNotGenG m d kappa (s + 1) b K ≤ fewNotGenG m d kappa s b K ∧
    ((∀ b', kappa b' ≤ kappa (b' + 1)) → fewNotGenG m d kappa s (b + 1) K ≤ fewNotGenG m d kappa s b K)

/-- The general assembly, proved. -/
theorem fnp_assemblyG (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG) :
    H270 → H669 → BoundG := by
  intro h270 h669 n m d S kappa hF s
  induction s with
  | zero => exact hB h270 (fnp_669_at h669) hS n m d S kappa hF
  | succ s ih => exact hSt (fnp_splitS hSp) n m d S kappa hF s ih

/-! ## Fit of the built pieces with `PSplitS` -/

/-- `on1_piece_h` takes `AndOr2 pre` as it is (definitional). -/
example (n : ℕ) (pre : List Gate) (ins : List ℕ) (hpre : AndOr2 pre) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false)
      = true) :
    ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn y)).getD i false).headD false)
      = true :=
  OneNot.on1_piece_h n pre ins hpre x y hxy hx

/-- The in-place variants have the length of the list. -/
theorem fnp_variant_length (pre post : List Gate) (g g' : Gate) :
    (pre ++ g :: post).length = (pre ++ g' :: post).length := by simp

/-! ## The plane as an instance -/

/-- The kill bound of the plane. -/
def kappaPlane (q : ℕ) : ℕ → ℕ := fun b => if b = 0 then 0 else b * q + 1

/-- The right-fold maximum is monotone in its terms and in its range. -/
theorem fnp_foldr_max_mono {f g : ℕ → ℕ} {r r' : ℕ} (hr : r ≤ r')
    (hfg : ∀ j ∈ List.range r, f j ≤ g j) :
    (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤
      (List.range r').foldr (fun (j acc : ℕ) => max acc (g j)) 0 :=
  fn_foldr_max_le fun j hj => le_trans (hfg j hj)
    (fn_le_foldr_max (List.mem_range.mpr (lt_of_lt_of_le (List.mem_range.mp hj) hr)))

/-- The recorded plane recursion is a LOWER bound of the general one at the plane parameters
(equal at no NOT gate; the general step takes the maximum over the larger range `j ≤ K`). -/
theorem fnp_plane_le_genG (m q : ℕ) :
    ∀ s b K : ℕ, fewNotBound m q s b K ≤ fewNotGenG m (q + 1) (kappaPlane q) s b K
  | 0, b, K => by
    rw [fnp_genG_zero, fn_G_zero, kappaPlane]
    simp only [Nat.add_sub_cancel]
    split_ifs <;> simp
  | s + 1, b, K => by
    rw [fnp_genG_succ, fn_G_succ]
    exact fnp_foldr_max_mono (Nat.add_le_add_right (min_le_left _ _) 1) fun j _ =>
      min_le_min (fnp_plane_le_genG m q s _ _) (fnp_plane_le_genG m q s _ _)

/-- From COUNT, the plane family is a general family with `d = q + 1` and `kappaPlane q`. -/
theorem fnp_famG_of_fam (hC : PCount) (n m q : ℕ) (S : Fin m → Finset (Fin n))
    (hF : Fam n m q S) : FamG n m (q + 1) S (kappaPlane q) := by
  refine ⟨hF.1, hF.2.1, fun b y hy => ?_⟩
  have hc := hC n m q S hF b y hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun w : Fin m => Disjoint (S w) y)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  unfold kappaPlane
  split_ifs at hc ⊢ <;> omega

theorem fnp_claim_of_claimG (n m q : ℕ) (S : Fin m → Finset (Fin n)) (s : ℕ)
    (h : ClaimG n m (q + 1) S (kappaPlane q) s) : Claim n m q S s := by
  intro b K y gates out hy hops hnot hr
  exact le_trans (fnp_plane_le_genG m q s b K) (h b K y gates out hy hops hnot hr)

theorem fnp_assemblyPlane (hC : PCount) (hS : PSub) (hSp : PSplit) (hB : PBaseG)
    (hSt : PStepG) : TargetPlane := by
  intro h270 h669 n m q S h1 h2 h3 h4 s
  exact fnp_claim_of_claimG n m q S s
    (fnp_assemblyG hS hSp hB hSt h270 h669 n m (q + 1) S (kappaPlane q)
      (fnp_famG_of_fam hC n m q S ⟨h1, h2, h3, h4⟩) s)

/-! ## The restricted family as an instance (kill bound from a degree bound) -/

/-- If every point lies in at most `r` sets, `b * r` is a kill bound (proved here; it is also
what the recorded L-meta-713 says, `fnp_kill_of_713`). -/
theorem fnp_kill_of_degree {n m : ℕ} (S : Fin m → Finset (Fin n)) (r : ℕ)
    (hdeg : ∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) :
    ∀ (b : ℕ) (y : Finset (Fin n)), y.card ≤ b →
      (Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y)).card ≤ b * r := by
  intro b y hy
  have hsub : Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y) ⊆
      y.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i)) := by
    intro w hw
    rw [Finset.mem_filter, Finset.not_disjoint_iff] at hw
    obtain ⟨p, hpS, hpy⟩ := hw.2
    exact Finset.mem_biUnion.mpr ⟨p, hpy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpS⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ y, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card :=
        Finset.card_biUnion_le
    _ ≤ y.card * r := by
        have := Finset.sum_le_card_nsmul y _ r (fun p _ => hdeg p)
        simpa using this
    _ ≤ b * r := Nat.mul_le_mul_right r hy

/-- The same kill bound from the recorded L-meta-713 as a hypothesis. -/
theorem fnp_kill_of_713 (h : H713) {n m : ℕ} (S : Fin m → Finset (Fin n)) (r : ℕ)
    (hdeg : ∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) :
    ∀ (b : ℕ) (y : Finset (Fin n)), y.card ≤ b →
      (Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y)).card ≤ b * r := by
  intro b y hy
  have h1 := h n m r S y hdeg
  have he : Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y) =
      Finset.univ.filter (fun i : Fin m => ∃ p ∈ y, p ∈ S i) := by
    ext w; simp only [Finset.mem_filter, Finset.not_disjoint_iff]
    exact ⟨fun ⟨hu, p, h1, h2⟩ => ⟨hu, p, h2, h1⟩, fun ⟨hu, p, h1, h2⟩ => ⟨hu, p, h2, h1⟩⟩
  rw [he]
  exact h1.trans (Nat.mul_le_mul_right r hy)

/-- The restricted family statement: sets of `d` points, pairwise at most one common point,
every point in at most `r` sets, is a general family with `kappa b = b * r`. -/
theorem fnp_famG_of_degree {n m d : ℕ} (S : Fin m → Finset (Fin n)) (r : ℕ)
    (hcard : ∀ i : Fin m, (S i).card = d) (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) :
    FamG n m d S (fun b => b * r) :=
  ⟨hcard, hpair, fnp_kill_of_degree S r hdeg⟩

/-! ## First instances: lines restricted to 3 columns -/

/-- The value of the recursion for `q = 8`, `d = 3`, one NOT gate, every input. -/
theorem fnp_inst_q8_value : fewNotGenG 64 3 (fun b => b * 8) 1 0 24 = 96 := by decide

set_option maxRecDepth 100000 in
/-- The value of the recursion for `q = 16`, `d = 3`, two NOT gates, every input. -/
theorem fnp_inst_q16_value : fewNotGenG 256 3 (fun b => b * 16) 2 0 48 = 320 := by decide

set_option maxRecDepth 100000 in
/-- The value of the recursion for `q = 16`, `d = 4`, two NOT gates, every input. -/
theorem fnp_inst_q16d4_value : fewNotGenG 256 4 (fun b => b * 16) 2 0 64 = 432 := by decide

/-- The line of slope `a` and intercept `t` over `Z/q` on columns `c < d`, point `(c, v)`
numbered `c * q + v`. -/
def fnp_affLine (q d a t : ℕ) : Finset ℕ :=
  (Finset.range d).image (fun c => c * q + (a * c + t) % q)

/-- Over `Z/8` (not a field) two lines on columns 0, 1, 2 share TWO points: slope 0 and slope
4, intercept 0 (points (0, 0) and (2, 0)). The family over `Z/8` is not a general family. -/
theorem fnp_z8_two_common : (fnp_affLine 8 3 0 0 ∩ fnp_affLine 8 3 4 0).card = 2 := by decide

/-- Instance (i) as a corollary statement: any family of 64 sets of 3 points on 24 inputs,
pairwise at most one common point, each point in at most 8 sets (the lines over the field of
8 elements on 3 columns are one), and any circuit with at most one NOT gate computing the 64
ORs on every input has at least 96 gates. -/
theorem fnp_inst_q8 (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG)
    (h270 : H270) (h669 : H669) (S : Fin 64 → Finset (Fin 24))
    (hcard : ∀ i, (S i).card = 3) (hpair : ∀ i j : Fin 64, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p : Fin 24, (Finset.univ.filter (fun i : Fin 64 => p ∈ S i)).card ≤ 8)
    (gates : List Gate) (out : Fin 64 → ℕ) (hops : OpsOK gates) (hnot : NotAtMost 1 gates)
    (hright : Right S ∅ 24 gates out) : 96 ≤ gates.length := by
  have := fnp_assemblyG hS hSp hB hSt h270 h669 24 64 3 S (fun b => b * 8)
    (fnp_famG_of_degree S 8 hcard hpair hdeg) 1 0 24 ∅ gates out (by simp) hops hnot hright
  rwa [fnp_inst_q8_value] at this

/-- Instance (ii) as a corollary statement: 256 sets of 3 points on 48 inputs, each point in
at most 16 sets, at most two NOT gates: at least 320 gates. -/
theorem fnp_inst_q16 (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG)
    (h270 : H270) (h669 : H669) (S : Fin 256 → Finset (Fin 48))
    (hcard : ∀ i, (S i).card = 3) (hpair : ∀ i j : Fin 256, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p : Fin 48, (Finset.univ.filter (fun i : Fin 256 => p ∈ S i)).card ≤ 16)
    (gates : List Gate) (out : Fin 256 → ℕ) (hops : OpsOK gates) (hnot : NotAtMost 2 gates)
    (hright : Right S ∅ 48 gates out) : 320 ≤ gates.length := by
  have := fnp_assemblyG hS hSp hB hSt h270 h669 48 256 3 S (fun b => b * 16)
    (fnp_famG_of_degree S 16 hcard hpair hdeg) 2 0 48 ∅ gates out (by simp) hops hnot hright
  rwa [fnp_inst_q16_value] at this

/-- Instance (iii) as a corollary statement: 256 sets of 4 points on 64 inputs, pairwise at
most one common point, each point in at most 16 sets, at most two NOT gates: at least 432
gates. -/
theorem fnp_inst_q16d4 (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG)
    (h270 : H270) (h669 : H669) (S : Fin 256 → Finset (Fin 64))
    (hcard : ∀ i, (S i).card = 4) (hpair : ∀ i j : Fin 256, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p : Fin 64, (Finset.univ.filter (fun i : Fin 256 => p ∈ S i)).card ≤ 16)
    (gates : List Gate) (out : Fin 256 → ℕ) (hops : OpsOK gates) (hnot : NotAtMost 2 gates)
    (hright : Right S ∅ 64 gates out) : 432 ≤ gates.length := by
  have := fnp_assemblyG hS hSp hB hSt h270 h669 64 256 4 S (fun b => b * 16)
    (fnp_famG_of_degree S 16 hcard hpair hdeg) 2 0 64 ∅ gates out (by simp) hops hnot hright
  rwa [fnp_inst_q16d4_value] at this

/-! ## Definitional check against the target term (pasted verbatim) -/

/-- `TargetPlane` is definitionally the recorded plane term of the conditional. -/
theorem fnp_target_iff_term : TargetPlane ↔
    (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) → (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1) → ∀ (s b K : ℕ) (y : Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), y.card ≤ b → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → (∀ p ∈ y, x p = true) → (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun b' K' : ℕ => (if b' = 0 then m else m - (b' * q + 1)) * min K' q) (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) => (List.range (min K' (q + 1) + 1)).foldr (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0) s b K ≤ gates.length :=
  Iff.rfl

/-- The conditional itself, the target term verbatim, from the general pieces and COUNT. -/
theorem fnp_conditional (hC : PCount) (hS : PSub) (hSp : PSplit) (hB : PBaseG)
    (hSt : PStepG) :
    (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin m, p ∈ S i ∧ p' ∈ S i) → (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ q + 1) → ∀ (s b K : ℕ) (y : Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), y.card ≤ b → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → (∀ p ∈ y, x p = true) → (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun b' K' : ℕ => (if b' = 0 then m else m - (b' * q + 1)) * min K' q) (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) => (List.range (min K' (q + 1) + 1)).foldr (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0) s b K ≤ gates.length :=
  fnp_target_iff_term.mp (fnp_assemblyPlane hC hS hSp hB hSt)

end PEqualNP.MetaComplexity.FewNot
