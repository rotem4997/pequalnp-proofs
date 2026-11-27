import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart2

/-!
# The flag rewiring of a one-dirty-AND circuit

`Flag` fixes the two operands of `g` on opposite sides, with their one partner vertex each (`zz 0`, `zz 1`) and no
AND whose partners hold both. `core`: delete `g`; an AND reading `g` with `zz i` among its partners becomes the
star `x (zz i) AND (the other operand of g)`, any other AND reading `g` is zeroed, and an OR reading `g` is fed
`Mode i` of its type `i` (its variables lie on the side of the other operand): a star gate, the other operand, or
one vertex. Where the modes are valid, keep the edges of `g` off the corner, and the corner is kept, the circuit
shrinks. `ov` names the gate of operand 0 when only `g` reads it and it becomes a star.
-/

namespace PEqualNP.MetaComplexity.FlagCore

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

/-- Vertex `y` is a variable of operand `i` of `g`. -/
def V (C : Circuit) (g : ℕ) (i : Fin 2) (y : Fin n) : Prop := wireVal n C (opnd C g i) (unitInput y) = true

inductive Mode (n : ℕ)
  | gate (k : ℕ)
  | fac
  | vtx (t : Fin n)

def Mode.src (C : Circuit) (g : ℕ) (i : Fin 2) : Mode n → Src n ℕ
  | .gate k => some (Sum.inr k)
  | .fac => srcOf n (opnd C g (1 - i))
  | .vtx t => some (Sum.inl t)

def Mode.val (C : Circuit) (g : ℕ) (zz : Fin 2 → Fin n) (i : Fin 2) (x : Fin n → Bool) : Mode n → Bool
  | .gate _ => x (zz i) && wireVal n C (opnd C g (1 - i)) x
  | .fac => wireVal n C (opnd C g (1 - i)) x
  | .vtx t => x t

structure Flag (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (s : Fin n → Bool)
    (zz : Fin 2 → Fin n) : Prop where
  one : OneDirty G C g
  bip : ∀ u v, G.Adj u v → s u ≠ s v
  off : ∀ w, gateVal n C g (unitInput w) = false
  mem : ∀ i, V C g i (zz i)
  side : ∀ i y, V C g i y → s y = s (zz i)
  opp : s (zz 0) ≠ s (zz 1)
  adj : ∀ i y, V C g (1 - i) y → G.Adj (zz i) y
  uniq : ∀ i k q, k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k q → V C g i q → q = zz i
  noflag : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ (PZ C g k (zz 0) ∧ PZ C g k (zz 1))
  nd : ∀ k < C.gates.length, Low G C (n + k) → OrReaches n C (n + k) g → k ≠ g →
    ∃ y, wireVal n C (n + k) (unitInput y) = true
  wit : ∀ i, ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ PZ C g k (zz i)

/-- An AND reading `g` whose partners hold `zz i`. -/
def Killer (C : Circuit) (g : ℕ) (zz : Fin 2 → Fin n) (i : Fin 2) (k : ℕ) : Prop :=
  k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ (∃ c, opnd C k c = n + g) ∧ PZ C g k (zz i)

def Spec (C : Circuit) (g : ℕ) (zz : Fin 2 → Fin n) (ov : Option ℕ) (i : Fin 2) (k : ℕ) : Prop :=
  Killer C g zz i k ∨ (i = 0 ∧ ov = some k)

open Classical in
/-- The type of a low gate reaching `g`. -/
noncomputable def ty (C : Circuit) (s : Fin n → Bool) (zz : Fin 2 → Fin n) (k : ℕ) : Fin 2 :=
  if ∃ y, wireVal n C (n + k) (unitInput y) = true ∧ s y = s (zz 1) then 0 else 1

section

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ} {s : Fin n → Bool}
  {zz : Fin 2 → Fin n}

theorem opp' (F : Flag G C g s zz) (i : Fin 2) : s (zz i) ≠ s (zz (1 - i)) := by
  fin_cases i
  · exact F.opp
  · exact F.opp.symm

/-- The partners of an AND above a low gate reaching `g` lie on the side of the gate's type. -/
theorem side_partner (F : Flag G C g s zz) (k : ℕ) (hk : k < C.gates.length) (hl : Low G C (n + k))
    (hr : OrReaches n C (n + k) g) (hkg : k ≠ g) (T : ℕ) (hT : T < C.gates.length)
    (hTo : (gateAt C T).op = GateOp.and) (c : Fin 2) (hc : OrReaches n C (opnd C T c) k) (q : Fin n)
    (hq : wireVal n C (opnd C T (1 - c)) (unitInput q) = true) :
    s q = s (zz (ty C s zz k)) ∧ ∀ y, wireVal n C (n + k) (unitInput y) = true → s y ≠ s q := by
  have H := F.one
  have hlt := opnd_lt C H.ao T hT c
  have hTg : T ≠ g := by
    rintro rfl
    exact not_reach_opnd C H.ao T H.hg c (reach_trans C H.ao k T hk hr _ (by omega) hc)
  have hopp : ∀ y, wireVal n C (n + k) (unitInput y) = true → s y ≠ s q := by
    intro y hy
    refine F.bip _ _ (and_pair' H T hT hTo hTg c y q ?_ hq)
    exact (reach_le C H.ao k _ (by omega) hc).2 _ hy
  refine ⟨?_, hopp⟩
  obtain ⟨y0, hy0⟩ := F.nd k hk hl hr hkg
  have h01 := F.opp
  unfold ty
  split_ifs with h
  · obtain ⟨y, hy, hsy⟩ := h
    have h1 := hopp y hy
    rw [hsy] at h1
    revert h1 h01
    cases s q <;> cases s (zz 0) <;> cases s (zz 1) <;> simp
  · have h1 := hopp y0 hy0
    have h2 : s y0 ≠ s (zz 1) := fun h3 => h ⟨y0, hy0, h3⟩
    revert h1 h2
    cases s q <;> cases s y0 <;> cases s (zz 1) <;> simp

/-- The variables of a low gate reaching `g` lie opposite its type. -/
theorem side_var (F : Flag G C g s zz) (k : ℕ) (hk : k < C.gates.length) (hl : Low G C (n + k))
    (hr : OrReaches n C (n + k) g) (hkg : k ≠ g) (y : Fin n) (hy : wireVal n C (n + k) (unitInput y) = true) :
    s y ≠ s (zz (ty C s zz k)) := by
  have H := F.one
  obtain ⟨T, hT, hTo, c, hc⟩ := above_and H k hk hl
  have hlt := opnd_lt C H.ao T hT c
  have hlt' := opnd_lt C H.ao T hT (1 - c)
  have hcg := reach_trans C H.ao k g hk hr _ (by omega) hc
  obtain ⟨q, _, hq⟩ := (pure_val H T hT hTo (1 - c) (not_both' H T hT hTo c hcg) (fun _ => true)).1
    (ones_val C H.ao _ (by omega))
  obtain ⟨h1, h2⟩ := side_partner F k hk hl hr hkg T hT hTo c hc q hq
  rw [← h1]
  exact h2 y hy

theorem ty_eq (F : Flag G C g s zz) (k j : ℕ) (hk : k < C.gates.length) (hl : Low G C (n + k))
    (hr : OrReaches n C (n + k) g) (hkg : k ≠ g) (hj : j < C.gates.length) (hlj : Low G C (n + j))
    (hrj : OrReaches n C (n + j) g) (hjg : j ≠ g)
    (hsub : ∀ y, wireVal n C (n + j) (unitInput y) = true → wireVal n C (n + k) (unitInput y) = true) :
    ty C s zz j = ty C s zz k := by
  obtain ⟨y, hy⟩ := F.nd j hj hlj hrj hjg
  have h1 := side_var F j hj hlj hrj hjg y hy
  have h2 := side_var F k hk hl hr hkg y (hsub y hy)
  have h01 := F.opp
  by_contra hne
  have h3 : ty C s zz k = 1 - ty C s zz j := fin2 _ _ hne
  rw [h3] at h2
  have h4 := opp' F (ty C s zz j)
  revert h1 h2 h4
  cases s y <;> cases s (zz (ty C s zz j)) <;> cases s (zz (1 - ty C s zz j)) <;> simp

theorem not_both_killer (F : Flag G C g s zz) (k : ℕ) (h0 : Killer C g zz 0 k) (h1 : Killer C g zz 1 k) : False :=
  F.noflag k h0.1 h0.2.1 ⟨h0.2.2.2, h1.2.2.2⟩

/-- Where `g` is on at an edge, the edge is a variable of each operand. -/
theorem g_edge (F : Flag G C g s zz) (p q : Fin n) (hg : gateVal n C g (pairInput p q) = true) :
    ∃ a b, V C g 0 a ∧ V C g 1 b ∧ pairInput p q = pairInput a b ∧ a ≠ b := by
  have H := F.one
  obtain ⟨h0, h1⟩ := (val_and C H.ao g H.hg H.gand _).1 hg
  obtain ⟨a, ha, hwa⟩ := (opnd_val H 0 _).1 h0
  obtain ⟨b, hb, hwb⟩ := (opnd_val H 1 _).1 h1
  have hab : a ≠ b := by
    rintro rfl
    have h2 := F.side 0 a hwa
    have h3 := F.side 1 a hwb
    exact F.opp (h2.symm.trans h3)
  refine ⟨a, b, hwa, hwb, ?_, hab⟩
  simp only [pairInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · exact LeafBound.pairInput_comm _ _
  · exact absurd rfl hab

/-- Which vertices the pair input of `a` and `b` turns on. -/
theorem pair_on (a b y : Fin n) : pairInput a b y = true ↔ y = a ∨ y = b := by
  simp [pairInput]

theorem core (F : Flag G C g s zz) (M : Fin 2 → Mode n) (ov : Option ℕ)
    (hgate : ∀ i k, M i = Mode.gate k → Spec C g zz ov i k)
    (hov1 : ov ≠ none → (∃ t, M 1 = Mode.vtx t) ∧ ∀ k, ¬ Killer C g zz 1 k)
    (hov : ∀ ia, ov = some ia → ia < C.gates.length ∧ opnd C g 0 = n + ia ∧
      ∀ k < C.gates.length, k ≠ g → ∀ c, opnd C k c ≠ n + ia)
    (hval : ∀ i x k q, k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k q → s q = s (zz i) →
      (M i).val C g zz i x = true → x q = true → graphFun G ∅ x = true)
    (hedge : ∀ i y, V C g (1 - i) y → y ≠ zz (1 - i) → (M i).val C g zz i (pairInput (zz i) y) = true)
    (hcor : (∃ i, (M i).val C g zz i (pairInput (zz 0) (zz 1)) = true) ∨
      ∃ T < C.gates.length, (gateAt C T).op = GateOp.and ∧ T ≠ g ∧
        ∀ c, ∃ y, pairInput (zz 0) (zz 1) y = true ∧ wireVal n C (opnd C T c) (unitInput y) = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have H := F.one
  have hAO := H.ao
  have hgl := H.hg
  obtain ⟨o, hol, hoo, hob⟩ := out_gate H
  have hog : o ≠ g := by
    rintro rfl
    exact H.dirty hob
  have ha_lt := opnd_lt C hAO g hgl
  have ha_low : ∀ i, Low G C (opnd C g i) := fun i => low_opnd H g hgl i (Or.inr H.gand)
  have ha_nr : ∀ i, ¬ OrReaches n C (opnd C g i) g := not_reach_opnd C hAO g hgl
  -- operand 1 of `g` is not the gate of operand 0
  have hne01 : opnd C g 0 ≠ opnd C g 1 := by
    intro h
    have h1 := F.mem 0
    unfold V at h1
    rw [h] at h1
    exact F.opp (F.side 1 _ h1)
  have hovne : ∀ ia, ov = some ia → opnd C g 1 ≠ n + ia := by
    intro ia h h2
    exact hne01 ((hov ia h).2.1.trans h2.symm)
  have hovg : ∀ ia, ov = some ia → ia < g := by
    intro ia h
    have h1 := (hov ia h).2.1
    have h2 := ha_lt 0
    omega
  have hovlow : ∀ ia, ov = some ia → Low G C (n + ia) ∧ (gateAt C ia).op = GateOp.or := by
    intro ia h
    have h1 := ha_low 0
    rw [(hov ia h).2.1] at h1
    refine ⟨h1, ?_⟩
    rcases LeafBound.ao_op hAO (hov ia h).1 with ho | ho
    · have := low_and H ia (hov ia h).1 ho h1
      have := hovg ia h
      omega
    · exact ho
  have hkg : ∀ i k, Killer C g zz i k → g < k ∧ k ≠ g := by
    rintro i k ⟨hk, ho, ⟨c, hc⟩, hp⟩
    have h1 := opnd_lt C hAO k hk c
    exact ⟨by omega, by omega⟩
  have hspeclt : ∀ i k, Spec C g zz ov i k → k < C.gates.length ∧ k ≠ g := by
    rintro i k (h | ⟨_, h⟩)
    · exact ⟨h.1, (hkg i k h).2⟩
    · have := hovg k h
      exact ⟨(hov k h).1, by omega⟩
  have hspecex : ∀ k, Spec C g zz ov 0 k → ¬ Spec C g zz ov 1 k := by
    rintro k (h | ⟨_, h⟩) (h' | ⟨h', _⟩)
    · exact not_both_killer F k h h'
    · exact absurd h' (by decide)
    · exact (hov1 (by rw [h]; simp)).2 k h'
    · exact absurd h' (by decide)
  -- an OR is special only as the gate `ov`
  have hspecor : ∀ i k, (gateAt C k).op = GateOp.or → Spec C g zz ov i k → ov = some k := by
    rintro i k ho (h | ⟨_, h⟩)
    · have h2 := h.2.1
      rw [ho] at h2
      cases h2
    · exact h
  let P : Prog n ℕ :=
    { isAnd := fun k => if Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k then true else isA (gateAt C k).op
      src := fun k c =>
        if Spec C g zz ov 0 k then (if c = 0 then some (Sum.inl (zz 0)) else srcOf n (opnd C g 1))
        else if Spec C g zz ov 1 k then (if c = 0 then some (Sum.inl (zz 1)) else srcOf n (opnd C g 0))
        else if opnd C k c = n + g then
          (if (gateAt C k).op = GateOp.and then none else (M (ty C s zz k)).src C g (ty C s zz k))
        else srcOf n (opnd C k c) }
  let rank : ℕ → ℕ := fun k => if Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k then g else k
  let K := (Finset.range C.gates.length).erase g
  have hK : ∀ k, k ∈ K ↔ k ≠ g ∧ k < C.gates.length := by
    intro k
    simp only [K, Finset.mem_erase, Finset.mem_range]
  -- a factor source reads a plain gate below `g`
  have hfac : ∀ i j, srcOf n (opnd C g i) = some (Sum.inr j) → (i = 0 → ov = none) →
      j ∈ K ∧ rank j < g := by
    intro i j hj hi
    have hw := srcOf_inr _ _ hj
    have h1 := ha_lt i
    have hjg : j < g := by omega
    refine ⟨(hK j).2 ⟨by omega, by omega⟩, ?_⟩
    have hns : ¬ (Spec C g zz ov 0 j ∨ Spec C g zz ov 1 j) := by
      have : ∀ d, ¬ Spec C g zz ov d j := by
        rintro d (h | ⟨_, h⟩)
        · have := (hkg d j h).1
          omega
        · rcases srcOf_cases (n := n) (opnd C g i) with _ | _
          all_goals
            by_cases hi0 : i = 0
            · rw [hi hi0] at h
              exact absurd h (by simp)
            · have hi1 : i = 1 := fin2_one i hi0
              subst hi1
              exact hovne j h hw
      rintro (h | h)
      · exact this 0 h
      · exact this 1 h
    simp only [rank, ite_eq_right hns]
    exact hjg
  have hov0 : ∀ k, Spec C g zz ov 1 k → ov = none := by
    rintro k (h | ⟨h, _⟩)
    · by_contra hne
      exact (hov1 hne).2 k h
    · exact absurd h (by decide)
  have hrankspec : ∀ i k, Spec C g zz ov i k → rank k = g := by
    intro i k h
    have : Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k := by
      fin_cases i
      · exact Or.inl h
      · exact Or.inr h
    simp only [rank, ite_eq_left this]
  have hcl : Closed P rank K := by
    intro k hk c j hj
    obtain ⟨hkng, hkl⟩ := (hK k).1 hk
    by_cases h0 : Spec C g zz ov 0 k
    · have hj' : (if c = 0 then some (Sum.inl (zz 0)) else srcOf n (opnd C g 1)) = some (Sum.inr j) := by
        simpa only [P, ite_eq_left h0] using hj
      split_ifs at hj' with hc
      · simp at hj'
      · rw [hrankspec 0 k h0]
        exact hfac 1 j hj' (fun h => absurd h (by decide))
    · by_cases h1 : Spec C g zz ov 1 k
      · have hj' : (if c = 0 then some (Sum.inl (zz 1)) else srcOf n (opnd C g 0)) = some (Sum.inr j) := by
          simpa only [P, ite_eq_right h0, ite_eq_left h1] using hj
        split_ifs at hj' with hc
        · simp at hj'
        · rw [hrankspec 1 k h1]
          exact hfac 0 j hj' (fun _ => hov0 k h1)
      · have hrk : rank k = k := by
          have : ¬ (Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k) := by
            rintro (h | h)
            · exact h0 h
            · exact h1 h
          simp only [rank, ite_eq_right this]
        rw [hrk]
        by_cases hc : opnd C k c = n + g
        · have hgk : g < k := by
            have := opnd_lt C hAO k hkl c
            omega
          have hj' : (if (gateAt C k).op = GateOp.and then none
              else (M (ty C s zz k)).src C g (ty C s zz k)) = some (Sum.inr j) := by
            simpa only [P, ite_eq_right h0, ite_eq_right h1, ite_eq_left hc] using hj
          split_ifs at hj' with ho
          generalize hi : ty C s zz k = i at hj'
          rcases hm : M i with k0 | _ | t
          · rw [hm] at hj'
            have hkj : k0 = j := by simpa [Mode.src] using hj'
            subst hkj
            have hs := hgate i k0 hm
            obtain ⟨a1, a2⟩ := hspeclt i k0 hs
            refine ⟨(hK k0).2 ⟨a2, a1⟩, ?_⟩
            rw [hrankspec i k0 hs]
            exact hgk
          · rw [hm] at hj'
            have h2 := hfac (1 - i) j hj' (fun h => by
              by_contra hne
              obtain ⟨t, ht⟩ := (hov1 hne).1
              have hi1 : i = 1 := fin2_one' i h
              rw [hi1, ht] at hm
              exact absurd hm (by simp))
            exact ⟨h2.1, h2.2.trans hgk⟩
          · rw [hm] at hj'
            simp [Mode.src] at hj'
        · have hj' : srcOf n (opnd C k c) = some (Sum.inr j) := by
            simpa only [P, ite_eq_right h0, ite_eq_right h1, ite_eq_right hc] using hj
          have hw := srcOf_inr _ _ hj'
          have hlt := opnd_lt C hAO k hkl c
          have hjg : j ≠ g := by
            rintro rfl
            exact hc hw
          refine ⟨(hK j).2 ⟨hjg, by omega⟩, ?_⟩
          by_cases hsj : Spec C g zz ov 0 j ∨ Spec C g zz ov 1 j
          · simp only [rank, ite_eq_left hsj]
            have : ∃ d, Spec C g zz ov d j := by
              rcases hsj with h | h
              · exact ⟨0, h⟩
              · exact ⟨1, h⟩
            obtain ⟨d, h | ⟨_, h⟩⟩ := this
            · have := (hkg d j h).1
              omega
            · exact absurd hw ((hov j h).2.2 k hkl hkng c)
          · simp only [rank, ite_eq_right hsj]
            omega
  obtain ⟨v, hv⟩ := sol_exists P rank K hcl
  -- gates not special keep their operation
  have hplain : ∀ k, ¬ Spec C g zz ov 0 k → ¬ Spec C g zz ov 1 k → P.isAnd k = isA (gateAt C k).op := by
    intro k h0 h1
    have : ¬ (Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k) := by
      rintro (h | h)
      · exact h0 h
      · exact h1 h
    simp only [P, ite_eq_right this]
  have hsrcp : ∀ k c, ¬ Spec C g zz ov 0 k → ¬ Spec C g zz ov 1 k → opnd C k c ≠ n + g →
      P.src k c = srcOf n (opnd C k c) := by
    intro k c h0 h1 hc
    simp only [P, ite_eq_right h0, ite_eq_right h1, ite_eq_right hc]
  -- pure low gates keep their values
  have hpure : ∀ k, k < C.gates.length → k ≠ g → Low G C (n + k) → ¬ OrReaches n C (n + k) g → ov ≠ some k →
      ∀ x, v k x = gateVal n C k x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkl hkng hl hr hovk x
      have hor : (gateAt C k).op = GateOp.or := by
        rcases LeafBound.ao_op hAO hkl with ho | ho
        · exact absurd (low_and H k hkl ho hl) hkng
        · exact ho
      have h0 : ¬ Spec C g zz ov 0 k := fun h => hovk (hspecor 0 k hor h)
      have h1 : ¬ Spec C g zz ov 1 k := fun h => hovk (hspecor 1 k hor h)
      have hcr : ∀ c, ¬ OrReaches n C (opnd C k c) g := fun c h =>
        hr ((reach_gate C hAO k g hkl).2 (Or.inr ⟨hor, c, h⟩))
      have hc : ∀ c, opnd C k c ≠ n + g := fun c h => hcr c (by rw [h]; exact reach_self C hAO g hgl)
      have hs : ∀ c, srcAt x (fun j => v j x) (P.src k c) = wireVal n C (opnd C k c) x := by
        intro c
        rw [hsrcp k c h0 h1 (hc c)]
        have hlt := opnd_lt C hAO k hkl c
        rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
        · rw [ha, srcOf_input, wireVal_lt C _ a.2]
          rfl
        · have hlow := low_opnd H k hkl c (Or.inl hl)
          have hrj := hcr c
          have hcj := hc c
          rw [hj] at hlow hrj hcj ⊢
          rw [srcOf_gate]
          refine ih j (by omega) (by omega) (by omega) hlow hrj ?_ x
          intro h
          exact (hov j h).2.2 k hkl hkng c hj
      have e := hv x k ((hK k).2 ⟨hkng, hkl⟩)
      simp only at e
      rw [e, hs, hs, hplain k h0 h1]
      exact (gate_eq C hAO k hkl x).symm
  have hpureW : ∀ w < n + C.gates.length, Low G C w → ¬ OrReaches n C w g → w ≠ n + g →
      (∀ ia, ov = some ia → w ≠ n + ia) → ∀ x, srcAt x (fun j => v j x) (srcOf n w) = wireVal n C w x := by
    intro w hw hl hr hwg hwo x
    rcases srcOf_cases (n := n) w with ⟨a, ha⟩ | ⟨j, hj⟩
    · rw [ha, srcOf_input, wireVal_lt C _ a.2]
      rfl
    · rw [hj] at hl hr hwg hwo hw ⊢
      rw [srcOf_gate]
      exact hpure j (by omega) (by omega) hl hr (fun h => hwo j h rfl) x
  have hfacv : ∀ i, (i = 0 → ov = none) → ∀ x,
      srcAt x (fun j => v j x) (srcOf n (opnd C g i)) = wireVal n C (opnd C g i) x := by
    intro i hi x
    have h1 := ha_lt i
    refine hpureW _ (by omega) (ha_low i) (ha_nr i) (by omega) ?_ x
    intro ia h
    by_cases hi0 : i = 0
    · rw [hi hi0] at h
      exact absurd h (by simp)
    · have hi1 : i = 1 := fin2_one i hi0
      subst hi1
      exact hovne ia h
  have hspec : ∀ i k, Spec C g zz ov i k → ∀ x, v k x = (x (zz i) && wireVal n C (opnd C g (1 - i)) x) := by
    intro i k hs x
    obtain ⟨hkl, hkng⟩ := hspeclt i k hs
    have e := hv x k ((hK k).2 ⟨hkng, hkl⟩)
    simp only at e
    rw [e]
    fin_cases i
    · have h0 : Spec C g zz ov 0 k := hs
      have e1 : P.isAnd k = true := by simp only [P, ite_eq_left (Or.inl h0 : Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k)]
      have e2 : P.src k 0 = some (Sum.inl (zz 0)) := by simp only [P, ite_eq_left h0, ite_true]
      have e3 : P.src k 1 = srcOf n (opnd C g 1) := by
        simp only [P, ite_eq_left h0]
        rfl
      rw [e1, e2, e3, hfacv 1 (fun h => absurd h (by decide)) x]
      rfl
    · have h1 : Spec C g zz ov 1 k := hs
      have h0 : ¬ Spec C g zz ov 0 k := fun h => hspecex k h h1
      have e1 : P.isAnd k = true := by simp only [P, ite_eq_left (Or.inr h1 : Spec C g zz ov 0 k ∨ Spec C g zz ov 1 k)]
      have e2 : P.src k 0 = some (Sum.inl (zz 1)) := by simp only [P, ite_eq_right h0, ite_eq_left h1, ite_true]
      have e3 : P.src k 1 = srcOf n (opnd C g 0) := by
        simp only [P, ite_eq_right h0, ite_eq_left h1]
        rfl
      rw [e1, e2, e3, hfacv 0 (fun _ => hov0 k h1) x]
      rfl
  have hmode : ∀ i x, srcAt x (fun j => v j x) ((M i).src C g i) = (M i).val C g zz i x := by
    intro i x
    rcases hm : M i with k0 | _ | t
    · exact hspec i k0 (hgate i k0 hm) x
    · refine hfacv (1 - i) (fun h => ?_) x
      by_contra hne
      obtain ⟨t, ht⟩ := (hov1 hne).1
      have hi1 : i = 1 := fin2_one' i h
      rw [hi1, ht] at hm
      exact absurd hm (by simp)
    · rfl
  -- low gates reaching `g`
  have hnew : ∀ k, k < C.gates.length → k ≠ g → Low G C (n + k) → OrReaches n C (n + k) g → ∀ x,
      (v k x = true ↔ (∃ y, x y = true ∧ wireVal n C (n + k) (unitInput y) = true) ∨
        (M (ty C s zz k)).val C g zz (ty C s zz k) x = true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkl hkng hl hr x
      have hor : (gateAt C k).op = GateOp.or := by
        rcases LeafBound.ao_op hAO hkl with ho | ho
        · exact absurd (low_and H k hkl ho hl) hkng
        · exact ho
      have hovk : ov ≠ some k := by
        intro h
        have h1 := (reach_le C hAO g _ (by omega) hr).1
        have h2 := hovg k h
        omega
      have h0 : ¬ Spec C g zz ov 0 k := fun h => hovk (hspecor 0 k hor h)
      have h1 : ¬ Spec C g zz ov 1 k := fun h => hovk (hspecor 1 k hor h)
      have hunit : ∀ y, wireVal n C (n + k) (unitInput y) = true ↔
          ∃ c, wireVal n C (opnd C k c) (unitInput y) = true := fun y => val_or' C hAO k hkl hor (unitInput y)
      have hop : ∀ c, srcAt x (fun j => v j x) (P.src k c) = true ↔
          (∃ y, x y = true ∧ wireVal n C (opnd C k c) (unitInput y) = true) ∨
          (OrReaches n C (opnd C k c) g ∧ (M (ty C s zz k)).val C g zz (ty C s zz k) x = true) := by
        intro c
        have hlt := opnd_lt C hAO k hkl c
        have hlow := low_opnd H k hkl c (Or.inl hl)
        by_cases hc : opnd C k c = n + g
        · have e : P.src k c = (M (ty C s zz k)).src C g (ty C s zz k) := by
            have : ¬ (gateAt C k).op = GateOp.and := by
              rw [hor]; intro h'; cases h'
            simp only [P, ite_eq_right h0, ite_eq_right h1, ite_eq_left hc, ite_eq_right this]
          rw [e, hmode, hc]
          constructor
          · intro h
            exact Or.inr ⟨reach_self C hAO g hgl, h⟩
          · rintro (⟨y, _, hy⟩ | ⟨_, h⟩)
            · have h2 : gateVal n C g (unitInput y) = true := hy
              rw [F.off y] at h2
              exact absurd h2 (by decide)
            · exact h
        · rw [hsrcp k c h0 h1 hc]
          by_cases hrc : OrReaches n C (opnd C k c) g
          · rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
            · rw [ha] at hrc
              exact absurd hrc (reach_input C _ g a.2)
            · rw [hj] at hrc hlow hc ⊢
              rw [srcOf_gate]
              have hjk : j < k := by omega
              have hjg : j ≠ g := by
                rintro rfl
                exact hc rfl
              have hty : ty C s zz j = ty C s zz k :=
                ty_eq F k j hkl hl hr hkng (by omega) hlow hrc hjg fun y hy =>
                  (hunit y).2 ⟨c, by rw [hj]; exact hy⟩
              have h2 := ih j hjk (by omega) hjg hlow hrc x
              rw [hty] at h2
              show v j x = true ↔ _
              rw [h2]
              constructor
              · rintro (h | h)
                · exact Or.inl h
                · exact Or.inr ⟨hrc, h⟩
              · rintro (h | ⟨_, h⟩)
                · exact Or.inl h
                · exact Or.inr h
          · rw [hpureW _ (by omega) hlow hrc hc (fun ia h => (hov ia h).2.2 k hkl hkng c) x,
              val_low H _ (by omega) hlow x]
            constructor
            · rintro (h | ⟨h, _⟩)
              · exact Or.inl h
              · exact absurd h hrc
            · rintro (h | ⟨h, _⟩)
              · exact Or.inl h
              · exact absurd h hrc
      have e := hv x k ((hK k).2 ⟨hkng, hkl⟩)
      simp only at e
      have hA : P.isAnd k = false := by
        rw [hplain k h0 h1, hor]; rfl
      rw [e, hA, opv_or, hop 0, hop 1]
      constructor
      · rintro ((⟨y, hy, h⟩ | ⟨_, h⟩) | (⟨y, hy, h⟩ | ⟨_, h⟩))
        · exact Or.inl ⟨y, hy, (hunit y).2 ⟨0, h⟩⟩
        · exact Or.inr h
        · exact Or.inl ⟨y, hy, (hunit y).2 ⟨1, h⟩⟩
        · exact Or.inr h
      · rintro (⟨y, hy, h⟩ | h)
        · obtain ⟨c, hc⟩ := (hunit y).1 h
          fin_cases c
          · exact Or.inl (Or.inl ⟨y, hy, hc⟩)
          · exact Or.inr (Or.inl ⟨y, hy, hc⟩)
        · rcases (reach_gate C hAO k g hkl).1 hr with h2 | ⟨_, c, hc⟩
          · exact absurd h2.symm hkng
          · fin_cases c
            · exact Or.inl (Or.inr ⟨hc, h⟩)
            · exact Or.inr (Or.inr ⟨hc, h⟩)
  -- an operand of an AND that is not `g`'s wire, reaching `g`
  have hopr : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ Spec C g zz ov 0 k → ¬ Spec C g zz ov 1 k →
      ∀ c, opnd C k c ≠ n + g → OrReaches n C (opnd C k c) g →
      ∃ j, j < C.gates.length ∧ opnd C k c = n + j ∧ j ≠ g ∧ Low G C (n + j) ∧ OrReaches n C (n + j) g ∧
        ∀ x, (srcAt x (fun i => v i x) (P.src k c) = true ↔
          (∃ y, x y = true ∧ wireVal n C (opnd C k c) (unitInput y) = true) ∨
          (M (ty C s zz j)).val C g zz (ty C s zz j) x = true) := by
    intro k hkl ho h0 h1 c hc hr
    have hlt := opnd_lt C hAO k hkl c
    have hlow := low_opnd H k hkl c (Or.inr ho)
    rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
    · rw [ha] at hr
      exact absurd hr (reach_input C _ g a.2)
    · refine ⟨j, by omega, hj, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        exact hc hj
      · rw [← hj]; exact hlow
      · rw [← hj]; exact hr
      · intro x
        rw [hsrcp k c h0 h1 hc, hj, srcOf_gate]
        rw [hj] at hr hlow hc
        exact hnew j (by omega) (by rintro rfl; exact hc rfl) hlow hr x
  -- a pure operand of a kept AND keeps its value
  have hopp : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → ¬ Spec C g zz ov 0 k →
      ¬ Spec C g zz ov 1 k → ∀ c, ¬ OrReaches n C (opnd C k c) g → ∀ x,
      srcAt x (fun i => v i x) (P.src k c) = wireVal n C (opnd C k c) x := by
    intro k hkl ho hkng h0 h1 c hr x
    have hlt := opnd_lt C hAO k hkl c
    have hc : opnd C k c ≠ n + g := fun h => hr (by rw [h]; exact reach_self C hAO g hgl)
    rw [hsrcp k c h0 h1 hc]
    exact hpureW _ (by omega) (low_opnd H k hkl c (Or.inr ho)) hr hc (fun ia h => (hov ia h).2.2 k hkl hkng c) x
  have handv : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → ¬ Spec C g zz ov 0 k →
      ¬ Spec C g zz ov 1 k → ∀ x, (v k x = true ↔ ∀ c, srcAt x (fun i => v i x) (P.src k c) = true) := by
    intro k hkl ho hkng h0 h1 x
    have e := hv x k ((hK k).2 ⟨hkng, hkl⟩)
    simp only at e
    have hA : P.isAnd k = true := by
      rw [hplain k h0 h1, ho]; rfl
    rw [e, hA, opv_and]
    constructor
    · rintro ⟨a, b⟩ c
      fin_cases c
      · exact a
      · exact b
    · intro h
      exact ⟨h 0, h 1⟩
  -- nothing below `F` rises above `F`
  have hupper : ∀ x, graphFun G ∅ x = false → ∀ k, k < C.gates.length → BelowF G C k → v k x = false := by
    intro x hx k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hkl hb
      have hkng : k ≠ g := by
        rintro rfl
        exact H.dirty hb
      by_contra hne
      have hvt : v k x = true := by simpa using hne
      have contra : graphFun G ∅ x = true → False := fun h => by
        rw [hx] at h
        exact absurd h (by decide)
      have hstar : ∀ i, Spec C g zz ov i k → False := by
        intro i hs
        rw [hspec i k hs x, Bool.and_eq_true] at hvt
        obtain ⟨h1, h2⟩ := hvt
        obtain ⟨y, hy, hw⟩ := (opnd_val H (1 - i) x).1 h2
        exact contra ((graphFun_empty G x).2 ⟨zz i, y, F.adj i y hw, h1, hy⟩)
      have h0 : ¬ Spec C g zz ov 0 k := hstar 0
      have h1 : ¬ Spec C g zz ov 1 k := hstar 1
      rcases LeafBound.ao_op hAO hkl with ho | ho
      · have hall := (handv k hkl ho hkng h0 h1 x).1 hvt
        by_cases hgr : ∃ c, opnd C k c = n + g
        · obtain ⟨c, hc⟩ := hgr
          have h2 := hall c
          have e : P.src k c = none := by
            simp only [P, ite_eq_right h0, ite_eq_right h1, ite_eq_left hc, ite_eq_left ho]
          rw [e] at h2
          exact Bool.false_ne_true h2
        · have hc : ∀ c, opnd C k c ≠ n + g := fun c h => hgr ⟨c, h⟩
          by_cases hr : ∃ c, OrReaches n C (opnd C k c) g
          · obtain ⟨c, hr⟩ := hr
            obtain ⟨j, hjl, hj, hjg, hjlow, hjr, hjv⟩ := hopr k hkl ho h0 h1 c (hc c) hr
            have hnr := not_both' H k hkl ho c hr
            have h3 := hall (1 - c)
            rw [hopp k hkl ho hkng h0 h1 (1 - c) hnr x] at h3
            obtain ⟨q, hq, hqw⟩ := (pure_val H k hkl ho (1 - c) hnr x).1 h3
            have hpz : PZ C g k q := (pz_iff C g k q).2 ⟨c, hr, hqw⟩
            rcases (hjv x).1 (hall c) with ⟨y, hy, hyw⟩ | hm
            · exact contra ((graphFun_empty G x).2 ⟨y, q, and_pair' H k hkl ho hkng c y q hyw hqw, hy, hq⟩)
            · have hside := (side_partner F j hjl hjlow hjr hjg k hkl ho c
                (by rw [hj]; exact reach_self C hAO j hjl) q hqw).1
              exact contra (hval _ x k q hkl ho hpz hside hm hq)
          · have hnr : ∀ c, ¬ OrReaches n C (opnd C k c) g := fun c h => hr ⟨c, h⟩
            refine contra (hb x ((val_and C hAO k hkl ho x).2 ⟨?_, ?_⟩))
            · rw [← hopp k hkl ho hkng h0 h1 0 (hnr 0) x]
              exact hall 0
            · rw [← hopp k hkl ho hkng h0 h1 1 (hnr 1) x]
              exact hall 1
      · have e := hv x k ((hK k).2 ⟨hkng, hkl⟩)
        simp only at e
        have hA : P.isAnd k = false := by
          rw [hplain k h0 h1, ho]; rfl
        rw [hvt, hA] at e
        have hop : ∀ c, srcAt x (fun j => v j x) (P.src k c) = false := by
          intro c
          have hlt := opnd_lt C hAO k hkl c
          have hbel : ∀ z, wireVal n C (opnd C k c) z = true → graphFun G ∅ z = true :=
            fun z hz => below_or hAO k hkl ho hb c z hz
          have hc : opnd C k c ≠ n + g := by
            intro h
            refine H.dirty fun z hz => hbel z ?_
            rw [h]; exact hz
          rw [hsrcp k c h0 h1 hc]
          rcases srcOf_cases (n := n) (opnd C k c) with ⟨a, ha⟩ | ⟨j, hj⟩
          · rw [ha] at hbel
            exact absurd hbel (input_low _ a.2)
          · rw [hj] at hbel ⊢
            rw [srcOf_gate]
            exact ih j (by omega) (by omega) hbel
        rw [hop 0, hop 1] at e
        exact absurd e (by decide)
  -- a true AND below `F` reaches the output
  have hrise : ∀ x, ∀ p < C.gates.length, BelowF G C p → v p x = true → v o x = true := by
    intro x p hp hb hpv
    have hup : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → BelowF G C j → ∀ b i, opnd C j b = n + i →
      BelowF G C i → v i x = true → v j x = true := by
      intro j hj hop hbj c i hi hbi hvi
      have hjng : j ≠ g := by
        rintro rfl
        exact H.dirty hbj
      have hbj' : ∀ d, ¬ Spec C g zz ov d j := by
        intro d h
        have h2 := hspecor d j hop h
        exact (hovlow j h2).1 hbj
      have h0 := hbj' 0
      have h1 := hbj' 1
      have hig : i ≠ g := by
        rintro rfl
        exact H.dirty hbi
      have e := hv x j ((hK j).2 ⟨hjng, hj⟩)
      simp only at e
      have hA : P.isAnd j = false := by
        rw [hplain j h0 h1, hop]; rfl
      have hsi : srcAt x (fun k => v k x) (P.src j c) = true := by
        rw [hsrcp j c h0 h1 (by omega), hi, srcOf_gate]
        exact hvi
      rw [e, hA, opv_or]
      fin_cases c
      · exact Or.inl hsi
      · exact Or.inr hsi
    obtain ⟨o', ho', hvo⟩ := top_up H (fun k => v k x) hup p hp hb hpv
    have : o' = o := by omega
    rw [this] at hvo
    exact hvo
  -- a top whose partners hold `zz i` accepts where the mode and `zz i` are on
  have hkeep : ∀ i k, k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k (zz i) → ∀ x,
      x (zz i) = true → wireVal n C (opnd C g (1 - i)) x = true → (M i).val C g zz i x = true → v k x = true := by
    intro i k hkl ho hp x hxz hxv hm
    have hkng := pz_ne H k (zz i) hp
    by_cases hki : Killer C g zz i k
    · rw [hspec i k (Or.inl hki) x, hxz, hxv]
      rfl
    · have hkiller : ∀ c, opnd C k c ≠ n + g := fun c hc => hki ⟨hkl, ho, ⟨c, hc⟩, hp⟩
      have hns : ∀ d, ¬ Spec C g zz ov d k := by
        rintro d (h | ⟨_, h⟩)
        · obtain ⟨c, hc⟩ := h.2.2.1
          exact hkiller c hc
        · have h2 := (hovlow k h).2
          rw [ho] at h2
          cases h2
      obtain ⟨c, hr, hzw⟩ := (pz_iff C g k (zz i)).1 hp
      obtain ⟨j, hjl, hj, hjg, hjlow, hjr, hjv⟩ := hopr k hkl ho (hns 0) (hns 1) c (hkiller c) hr
      have hside := (side_partner F j hjl hjlow hjr hjg k hkl ho c
        (by rw [hj]; exact reach_self C hAO j hjl) (zz i) hzw).1
      have hti : ty C s zz j = i := by
        by_contra hne
        have h2 : ty C s zz j = 1 - i := fin2 _ _ (fun h => hne h.symm)
        rw [h2] at hside
        exact opp' F i hside
      refine (handv k hkl ho hkng (hns 0) (hns 1) x).2 fun d => ?_
      have hd : d = c ∨ d = 1 - c := fin2_or c d
      rcases hd with rfl | rfl
      · refine (hjv x).2 (Or.inr ?_)
        rw [hti]
        exact hm
      · rw [hopp k hkl ho hkng (hns 0) (hns 1) _ (not_both' H k hkl ho c hr) x]
        have hlt := opnd_lt C hAO k hkl (1 - c)
        exact mono C hAO _ _ (unit_le (zz i) x hxz) _ (by omega) hzw
  -- every edge is accepted
  have hlower : ∀ p q, G.Adj p q → v o (pairInput p q) = true := by
    intro p q hpq
    set e := pairInput p q with he
    have hFe : graphFun G ∅ e = true := (graphFun_empty G e).2 ⟨p, q, hpq, by simp [he, pairInput], by simp [he, pairInput]⟩
    obtain ⟨T, hT, hTo, hTb, hTe⟩ := top_down H e hFe
    have hTg : T ≠ g := by
      rintro rfl
      exact H.dirty hTb
    -- acceptance through `g` at the partner `zz i`
    have hthru : ∀ i k, k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k (zz i) → e (zz i) = true →
        ∀ y, V C g (1 - i) y → e = pairInput (zz i) y → v o e = true := by
      intro i k hkl ho hp hez y hy hey
      have hvy : wireVal n C (opnd C g (1 - i)) e = true := (opnd_val H (1 - i) e).2 ⟨y, by rw [hey]; simp [pairInput], hy⟩
      by_cases hyz : y = zz (1 - i)
      · -- the corner
        have hcore : e = pairInput (zz 0) (zz 1) := by
          rw [hey, hyz]
          fin_cases i
          · rfl
          · exact LeafBound.pairInput_comm _ _
        have hcon : ∀ d, e (zz d) = true := by
          intro d
          rw [hcore]
          fin_cases d <;> simp [pairInput]
        rcases hcor with ⟨d, hd⟩ | ⟨T', hT', hTo', hTg', hTv⟩
        · obtain ⟨k', hk', hko', hkp'⟩ := F.wit d
          have hbk : BelowF G C k' := H.others k' hk' hko' (pz_ne H k' _ hkp')
          refine hrise e k' hk' hbk (hkeep d k' hk' hko' hkp' e (hcon d) ?_ ?_)
          · exact (opnd_val H (1 - d) e).2 ⟨zz (1 - d), hcon _, F.mem _⟩
          · rw [hcore]; exact hd
        · have hbk : BelowF G C T' := H.others T' hT' hTo' hTg'
          refine hrise e T' hT' hbk ?_
          by_cases hs : ∃ d, Spec C g zz ov d T'
          · obtain ⟨d, hs⟩ := hs
            rw [hspec d T' hs e, hcon d, (opnd_val H (1 - d) e).2 ⟨zz (1 - d), hcon _, F.mem _⟩]
            rfl
          · have hns : ∀ d, ¬ Spec C g zz ov d T' := fun d h => hs ⟨d, h⟩
            have hTv' : ∀ c, ∃ y, e y = true ∧ wireVal n C (opnd C T' c) (unitInput y) = true := by
              intro c
              obtain ⟨y', h1, h2⟩ := hTv c
              exact ⟨y', by rw [hcore]; exact h1, h2⟩
            refine (handv T' hT' hTo' hTg' (hns 0) (hns 1) e).2 fun c => ?_
            have hlt := opnd_lt C hAO T' hT' c
            obtain ⟨y', hy1, hy2⟩ := hTv' c
            by_cases hr : OrReaches n C (opnd C T' c) g
            · have hcg : opnd C T' c ≠ n + g := by
                intro h
                rw [h] at hy2
                have h2 : gateVal n C g (unitInput y') = true := hy2
                rw [F.off] at h2
                exact absurd h2 (by decide)
              obtain ⟨j, _, _, _, _, _, hjv⟩ := hopr T' hT' hTo' (hns 0) (hns 1) c hcg hr
              exact (hjv e).2 (Or.inl ⟨y', hy1, hy2⟩)
            · rw [hopp T' hT' hTo' hTg' (hns 0) (hns 1) c hr e]
              exact mono C hAO _ _ (unit_le y' e hy1) _ (by omega) hy2
      · have hbk : BelowF G C k := H.others k hkl ho (pz_ne H k _ hp)
        refine hrise e k hkl hbk (hkeep i k hkl ho hp e hez hvy ?_)
        rw [hey]
        exact hedge i y hy hyz
    -- a partner vertex on at an edge where `g` is on
    have hgon : ∀ k q', k < C.gates.length → (gateAt C k).op = GateOp.and → PZ C g k q' → e q' = true →
        gateVal n C g e = true → v o e = true := by
      intro k q' hkl ho hp hq' hge
      obtain ⟨a, b, ha, hb, hab, _⟩ := g_edge F p q hge
      rw [← he] at hab
      rw [hab] at hq'
      rcases (pair_on a b q').1 hq' with rfl | rfl
      · have hz := F.uniq 0 k q' hkl ho hp ha
        subst hz
        exact hthru 0 k hkl ho hp (by rw [hab]; simp [pairInput]) b hb hab
      · have hz := F.uniq 1 k q' hkl ho hp hb
        subst hz
        refine hthru 1 k hkl ho hp (by rw [hab]; simp [pairInput]) a ha ?_
        rw [hab]
        exact LeafBound.pairInput_comm _ _
    have hTv := (val_and' C hAO T hT hTo e)
    by_cases hr : ∃ c, OrReaches n C (opnd C T c) g
    · obtain ⟨c, hr⟩ := hr
      obtain ⟨h1, h2⟩ := (hTv c).1 hTe
      have hnr := not_both' H T hT hTo c hr
      obtain ⟨q', hq', hqw⟩ := (pure_val H T hT hTo (1 - c) hnr e).1 h2
      have hpz : PZ C g T q' := (pz_iff C g T q').2 ⟨c, hr, hqw⟩
      have hlt := opnd_lt C hAO T hT c
      rcases (val_low H _ (by omega) (low_opnd H T hT c (Or.inr hTo)) e).1 h1 with ⟨y, hy, hyw⟩ | ⟨_, hge⟩
      · by_cases hcg : opnd C T c = n + g
        · rw [hcg] at hyw
          have h3 : gateVal n C g (unitInput y) = true := hyw
          rw [F.off] at h3
          exact absurd h3 (by decide)
        · have hns : ∀ d, ¬ Spec C g zz ov d T := by
            rintro d (h | ⟨_, h⟩)
            · obtain ⟨c', hc'⟩ := h.2.2.1
              have : c' = c := by
                by_contra hne
                have h3 : c' = 1 - c := fin2 c c' (fun h => hne h.symm)
                rw [h3] at hc'
                exact hnr (by rw [hc']; exact reach_self C hAO g hgl)
              rw [this] at hc'
              exact hcg hc'
            · have h3 := (hovlow T h).2
              rw [hTo] at h3
              cases h3
          refine hrise e T hT hTb ((handv T hT hTo hTg (hns 0) (hns 1) e).2 fun d => ?_)
          have hd : d = c ∨ d = 1 - c := fin2_or c d
          rcases hd with rfl | rfl
          · obtain ⟨j, _, _, _, _, _, hjv⟩ := hopr T hT hTo (hns 0) (hns 1) d hcg hr
            exact (hjv e).2 (Or.inl ⟨y, hy, hyw⟩)
          · rw [hopp T hT hTo hTg (hns 0) (hns 1) _ hnr e]
            exact h2
      · exact hgon T q' hT hTo hpz hq' hge
    · have hnr : ∀ c, ¬ OrReaches n C (opnd C T c) g := fun c h => hr ⟨c, h⟩
      have hns : ∀ d, ¬ Spec C g zz ov d T := by
        rintro d (h | ⟨_, h⟩)
        · obtain ⟨c', hc'⟩ := h.2.2.1
          exact hnr c' (by rw [hc']; exact reach_self C hAO g hgl)
        · have h3 := (hovlow T h).2
          rw [hTo] at h3
          cases h3
      refine hrise e T hT hTb ((handv T hT hTo hTg (hns 0) (hns 1) e).2 fun d => ?_)
      rw [hopp T hT hTo hTg (hns 0) (hns 1) d (hnr d) e]
      have h3 := (hTv d).1 hTe
      exact h3.1
  obtain ⟨D, hD, hs, hf⟩ := fold_computes G P rank v K hcl hv (some (Sum.inr o))
    (fun j hj => by
      have : o = j := by simpa using hj
      rw [← this]
      exact (hK o).2 ⟨hog, hol⟩)
    (adj_of_AO G C hAO H.comp (by omega))
    (fun x hx => by
      by_contra hne
      have h := hupper x (by simpa using hne) o hol hob
      have hx' : v o x = true := hx
      rw [h] at hx'
      exact absurd hx' (by decide))
    (fun p q hpq => hlower p q hpq)
  refine ⟨D, hD, lt_of_le_of_lt hs ?_, hf⟩
  have h1 : (kept P v K).card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have h2 : K.card = C.gates.length - 1 := by
    simp only [K]
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hgl), Finset.card_range]
  show _ < C.gates.length
  omega

end

end PEqualNP.MetaComplexity.FlagCore
