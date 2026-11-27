import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9208

open PEqualNP.ProofComplexity PEqualNP.Search

section generic
variable {W : Type}

def Closed (G : Set (Clause W)) (U : Set (Literal W)) : Prop :=
  ∀ D ∈ G, ∀ l ∈ D, (∀ l' ∈ D, l' ≠ l → negLit l' ∈ U) → l ∈ U

def Calm (G : Set (Clause W)) (U : Set (Literal W)) : Prop :=
  ∀ D ∈ G, ∃ l ∈ D, negLit l ∉ U

def Cons (U : Set (Literal W)) : Prop := ∀ l ∈ U, negLit l ∉ U

theorem negLit_negLit (l : Literal W) : negLit (negLit l) = l := by
  simp [negLit]

theorem shield {G : Set (Clause W)} {U A : Set (Literal W)} (hC : Closed G U) (hA : A ⊆ U)
    {l : Literal W} (h : UPForces G A l) : l ∈ U := by
  induction h with
  | hyp h => exact hA h
  | unit hD hl _ ih => exact hC _ hD _ hl (fun l' hl' hne => ih l' hl' hne)

theorem not_rup {G : Set (Clause W)} {U : Set (Literal W)} {C : Clause W} (hC : Closed G U)
    (hK : Calm G U) (hA : negLit '' (↑C : Set (Literal W)) ⊆ U) : ¬ IsRUP G C := by
  rintro ⟨D, hD, hall⟩
  obtain ⟨l, hl, hn⟩ := hK D hD
  exact hn (shield hC hA (hall l hl))

theorem up_mono {G G' : Set (Clause W)} {A A' : Set (Literal W)} (hG : G ⊆ G') (hA : A ⊆ A')
    {l : Literal W} (h : UPForces G A l) : UPForces G' A' l := by
  induction h with
  | hyp h => exact UPForces.hyp (hA h)
  | unit hD hl _ ih => exact UPForces.unit (hG hD) hl (fun l' hl' hne => ih l' hl' hne)

theorem rup_mono {G G' : Set (Clause W)} {C C' : Clause W} (hG : G ⊆ G') (hC : C ⊆ C')
    (h : IsRUP G C) : IsRUP G' C' := by
  obtain ⟨D, hD, hall⟩ := h
  refine ⟨D, hG hD, fun l hl => up_mono hG ?_ (hall l hl)⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hC hx, rfl⟩

theorem rup_self {G : Set (Clause W)} {C : Clause W} (h : C ∈ G) : IsRUP G C :=
  ⟨C, h, fun l hl => UPForces.hyp ⟨l, hl, rfl⟩⟩

theorem up_dom {G G' : Set (Clause W)} (hdom : ∀ D ∈ G, ∃ D' ∈ G', D' ⊆ D) {A : Set (Literal W)}
    {l : Literal W} (h : UPForces G A l) :
    UPForces G' A l ∨ ∃ D' ∈ G', ∀ x ∈ D', UPForces G' A (negLit x) := by
  induction h with
  | hyp h => exact Or.inl (UPForces.hyp h)
  | @unit D l hD hl _ ih =>
    by_cases hconf : ∃ D' ∈ G', ∀ x ∈ D', UPForces G' A (negLit x)
    · exact Or.inr hconf
    · have hall : ∀ l' ∈ D, l' ≠ l → UPForces G' A (negLit l') := by
        intro l' hl' hne
        rcases ih l' hl' hne with h1 | h1
        · exact h1
        · exact absurd h1 hconf
      obtain ⟨D', hD', hsub⟩ := hdom D hD
      by_cases hlD : l ∈ D'
      · exact Or.inl (UPForces.unit hD' hlD (fun l' hl' hne => hall l' (hsub hl') hne))
      · exact Or.inr ⟨D', hD', fun x hx => hall x (hsub hx) (fun h => hlD (h ▸ hx))⟩

theorem rup_dom {G G' : Set (Clause W)} (hdom : ∀ D ∈ G, ∃ D' ∈ G', D' ⊆ D) {C : Clause W}
    (h : IsRUP G C) : IsRUP G' C := by
  obtain ⟨D, hD, hall⟩ := h
  by_cases hconf : ∃ D' ∈ G', ∀ x ∈ D', UPForces G' (negLit '' (↑C : Set (Literal W))) (negLit x)
  · obtain ⟨D', hD', h'⟩ := hconf
    exact ⟨D', hD', h'⟩
  · have hall' : ∀ x ∈ D, UPForces G' (negLit '' (↑C : Set (Literal W))) (negLit x) := by
      intro x hx
      rcases up_dom hdom (hall x hx) with h1 | h1
      · exact h1
      · exact absurd h1 hconf
    obtain ⟨D', hD', hsub⟩ := hdom D hD
    exact ⟨D', hD', fun x hx => hall' x (hsub hx)⟩

-- A run over a base: newest first, each clause RUP over the base and the older ones.
def RunOver (G0 : Set (Clause W)) : List (Clause W) → Prop
  | [] => True
  | C :: Cs => RunOver G0 Cs ∧ IsRUP (G0 ∪ {D | D ∈ Cs}) C

-- Robustness, semantically.
def RobS (G0 : Set (Clause W)) : ℕ → Set (Literal W) → Prop
  | 0, S => ∃ U, S ⊆ U ∧ Closed G0 U ∧ Calm G0 U ∧ Cons U
  | k+1, S => RobS G0 k S ∧ ∀ m : Literal W, RobS G0 k (S ∪ {negLit m}) ∨ RobS G0 k (S ∪ {m})

theorem robS_sound (G0 : Set (Clause W)) : ∀ (k : ℕ) (S : Set (Literal W)), RobS G0 k S →
    ∀ Cs : List (Clause W), Cs.length = k → RunOver G0 Cs →
    ∃ U, S ⊆ U ∧ Closed (G0 ∪ {D | D ∈ Cs}) U ∧ Calm (G0 ∪ {D | D ∈ Cs}) U ∧ Cons U := by
  intro k
  induction k with
  | zero =>
    intro S hS Cs hlen _
    obtain ⟨U, h1, h2, h3, h4⟩ := hS
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    refine ⟨U, h1, ?_, ?_, h4⟩
    · intro D hD; rcases hD with hD | hD
      · exact h2 D hD
      · exact absurd hD (List.not_mem_nil)
    · intro D hD; rcases hD with hD | hD
      · exact h3 D hD
      · exact absurd hD (List.not_mem_nil)
  | succ k ih =>
    intro S hS Cs hlen hrun
    obtain ⟨hS0, hSm⟩ := hS
    match Cs, hlen, hrun with
    | C :: Cs', hlen, ⟨hrun', hC⟩ =>
      have hlen' : Cs'.length = k := by simpa using hlen
      set Γ := G0 ∪ {D | D ∈ Cs'} with hΓ
      obtain ⟨U0, hU0S, hU0c, hU0k, hU0n⟩ := ih S hS0 Cs' hlen' hrun'
      let T : Set (Literal W) := {l | UPForces Γ S l}
      have hTU0 : T ⊆ U0 := fun l hl => shield hU0c hU0S hl
      have hST : S ⊆ T := fun l hl => UPForces.hyp hl
      have hTc : Closed Γ T := fun D hD l hl hrest => UPForces.unit hD hl hrest
      have hmem : ∀ D, D ∈ G0 ∪ {D | D ∈ C :: Cs'} ↔ D = C ∨ D ∈ Γ := by
        intro D
        simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, hΓ]
        tauto
      by_cases hfire : ∃ m ∈ C, m ∉ T ∧ ∀ l' ∈ C, l' ≠ m → negLit l' ∈ T
      · obtain ⟨m, hmC, hmT, hrest⟩ := hfire
        rcases hSm m with ha | hb
        · exfalso
          obtain ⟨U1, hU1S, hU1c, hU1k, _⟩ := ih _ ha Cs' hlen' hrun'
          have hTU1 : T ⊆ U1 := fun l hl =>
            shield hU1c (fun x hx => hU1S (Or.inl hx)) hl
          apply not_rup hU1c hU1k _ hC
          rintro _ ⟨x, hx, rfl⟩
          by_cases hxm : x = m
          · subst hxm; exact hU1S (Or.inr rfl)
          · exact hTU1 (hrest x hx hxm)
        · obtain ⟨U2, hU2S, hU2c, hU2k, hU2n⟩ := ih _ hb Cs' hlen' hrun'
          have hmU2 : m ∈ U2 := hU2S (Or.inr rfl)
          refine ⟨U2, fun x hx => hU2S (Or.inl hx), ?_, ?_, hU2n⟩
          · intro D hD l hl hr
            rcases (hmem D).1 hD with rfl | hD'
            · by_cases hlm : l = m
              · rw [hlm]; exact hmU2
              · exact absurd (hr m hmC (Ne.symm hlm)) (hU2n m hmU2)
            · exact hU2c D hD' l hl hr
          · intro D hD
            rcases (hmem D).1 hD with rfl | hD'
            · exact ⟨m, hmC, hU2n m hmU2⟩
            · exact hU2k D hD'
      · refine ⟨T, hST, ?_, ?_, fun l hl hn => hU0n l (hTU0 hl) (hTU0 hn)⟩
        · intro D hD l hl hr
          rcases (hmem D).1 hD with rfl | hD'
          · by_contra hlT
            exact hfire ⟨l, hl, hlT, hr⟩
          · exact hTc D hD' l hl hr
        · intro D hD
          rcases (hmem D).1 hD with rfl | hD'
          · by_contra hno
            simp only [not_exists, not_and, not_not] at hno
            apply not_rup hU0c hU0k _ hC
            rintro _ ⟨x, hx, rfl⟩
            exact hTU0 (hno x hx)
          · obtain ⟨l, hl, hn⟩ := hU0k D hD'
            exact ⟨l, hl, fun h => hn (hTU0 h)⟩

end generic

abbrev V := Fin (3+1) × Fin 3

def idx (l : Literal V) : ℕ := (bif l.2 then 0 else 12) + 3 * l.1.1.val + l.1.2.val

theorem idx_lt : ∀ l : Literal V, idx l < 24 := by decide
theorem idx_inj : ∀ l l' : Literal V, idx l = idx l' → l = l' := by decide
theorem idx_surj : ∀ k < 24, ∃ l : Literal V, idx l = k := by decide
def flip (k : ℕ) : ℕ := bif Nat.blt k 12 then k + 12 else k - 12
theorem idx_neg : ∀ l : Literal V, idx (negLit l) = flip (idx l) := by decide
theorem flip_flip : ∀ k < 24, flip (flip k) = k := by decide

def decode (x : ℕ) : Clause V := Finset.univ.filter fun l => x.testBit (idx l) = true

theorem mem_decode {x : ℕ} {l : Literal V} : l ∈ decode x ↔ x.testBit (idx l) = true := by
  simp [decode]

-- raw bit operations used by the computation
def nm (x : ℕ) : ℕ := Nat.lor (Nat.shiftLeft (Nat.land x 4095) 12) (Nat.land (Nat.shiftRight x 12) 4095)
def andn (x y : ℕ) : ℕ := Nat.xor x (Nat.land x y)

theorem testBit_andn (x y i : ℕ) : (andn x y).testBit i = (x.testBit i && !y.testBit i) := by
  unfold andn
  rw [show Nat.xor x (Nat.land x y) = x ^^^ (x &&& y) from rfl, Nat.testBit_xor, Nat.testBit_and]
  cases x.testBit i <;> cases y.testBit i <;> rfl

theorem testBit_nm (x k : ℕ) (hk : k < 24) : (nm x).testBit k = x.testBit (flip k) := by
  unfold nm flip
  rw [show Nat.lor (Nat.shiftLeft (Nat.land x 4095) 12) (Nat.land (Nat.shiftRight x 12) 4095)
      = ((x &&& 4095) <<< 12) ||| ((x >>> 12) &&& 4095) from rfl]
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_shiftRight, show (4095 : ℕ) = 2 ^ 12 - 1 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_one]
  by_cases h : k < 12
  · have : Nat.blt k 12 = true := Nat.blt_eq.mpr h
    simp only [this, cond_true]
    have h1 : ¬ (k ≥ 12) := by omega
    simp [h1, h, Nat.add_comm]
  · have : Nat.blt k 12 = false := by
      cases h' : Nat.blt k 12
      · rfl
      · exact absurd (Nat.blt_eq.mp h') h
    simp only [this, cond_false]
    have h1 : k ≥ 12 := by omega
    have h2 : k - 12 < 12 := by omega
    simp [h1, h2, h]

theorem mem_decode_nm {x : ℕ} {l : Literal V} : negLit l ∈ decode x ↔ l ∈ decode (nm x) := by
  rw [mem_decode, mem_decode, testBit_nm x _ (idx_lt l), idx_neg]

theorem testBit_lt {x k : ℕ} (hx : x < 2 ^ 24) (h : x.testBit k = true) : k < 24 := by
  by_contra hk
  have : x < 2 ^ k := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_eq_false_of_lt this] at h
  exact absurd h (by simp)

theorem exists_bit {r : ℕ} (h : r ≠ 0) : ∃ i, r.testBit i = true := by
  by_contra hno
  push Not at hno
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  simp [hno i]

-- the verifier for one clause d against T (nT = nm T)
def okD (T nT d : ℕ) : Bool :=
  let r := andn d nT
  !(Nat.beq r 0) && (!(Nat.beq (Nat.land r T) 0) || !(Nat.beq (Nat.land r (r - 1)) 0))

theorem okD_sound {T d : ℕ} (hd : d < 2 ^ 24) (h : okD T (nm T) d = true) :
    (∃ l ∈ decode d, negLit l ∉ decode T) ∧
    (∀ l ∈ decode d, (∀ l' ∈ decode d, l' ≠ l → negLit l' ∈ decode T) → l ∈ decode T) := by
  unfold okD at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  have hr0 : andn d (nm T) ≠ 0 := by
    intro hz; rw [hz] at h0; exact absurd h0 (by decide)
  have hbit : ∀ i, (andn d (nm T)).testBit i = true → i < 24 ∧ ∃ l : Literal V, idx l = i ∧
      l ∈ decode d ∧ negLit l ∉ decode T := by
    intro i hi
    rw [testBit_andn] at hi
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hi
    have hi24 := testBit_lt hd hi.1
    obtain ⟨l, rfl⟩ := idx_surj i hi24
    refine ⟨hi24, l, rfl, mem_decode.mpr hi.1, ?_⟩
    rw [mem_decode_nm, mem_decode]
    simp [hi.2]
  constructor
  · obtain ⟨i, hi⟩ := exists_bit hr0
    obtain ⟨_, l, _, hl, hn⟩ := hbit i hi
    exact ⟨l, hl, hn⟩
  · intro l hl hrest
    -- every bit of r is the bit of l
    have honly : ∀ i, (andn d (nm T)).testBit i = true → i = idx l := by
      intro i hi
      obtain ⟨_, l', rfl, hl', hn'⟩ := hbit i hi
      by_contra hne
      exact hn' (hrest l' hl' (fun h => hne (by rw [h])))
    obtain ⟨i, hi⟩ := exists_bit hr0
    have hil := honly i hi
    subst hil
    have hr : andn d (nm T) = 2 ^ idx l := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_two_pow]
      by_cases hj : j = idx l
      · subst hj; simp [hi]
      · have : (andn d (nm T)).testBit j = false := by
          by_contra hc
          exact hj (honly j (by simpa using hc))
        rw [this]; simp [Ne.symm hj]
    rw [hr] at h1
    rcases h1 with h1 | h1
    · have hne : (2 ^ idx l) &&& T ≠ 0 := by
        intro hz
        rw [show Nat.land (2 ^ idx l) T = (2 ^ idx l) &&& T from rfl, hz] at h1
        exact absurd h1 (by decide)
      obtain ⟨j, hj⟩ := exists_bit hne
      rw [Nat.testBit_and, Nat.testBit_two_pow] at hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      obtain ⟨rfl, hj⟩ := hj
      exact mem_decode.mpr hj
    · exfalso
      have : Nat.land (2 ^ idx l) (2 ^ idx l - 1) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [show Nat.land (2 ^ idx l) (2 ^ idx l - 1) = (2 ^ idx l) &&& (2 ^ idx l - 1) from rfl,
          Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
        simp only [Nat.zero_testBit]
        by_cases hj : idx l = j
        · subst hj; simp
        · simp [hj]
      rw [this] at h1
      exact absurd h1 (by decide)

def allOk (T nT : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => okD T nT d && allOk T nT ds

theorem allOk_mem {T nT : ℕ} : ∀ {G : List ℕ}, allOk T nT G = true → ∀ d ∈ G, okD T nT d = true
  | [], _, d, hd => absurd hd (List.not_mem_nil)
  | e :: es, h, d, hd => by
    unfold allOk at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h.1
    · exact allOk_mem h.2 d hd

-- The clause set given by a list of masks.
def setOf (G : List ℕ) : Set (Clause V) := {D | ∃ d ∈ G, D = decode d}

theorem allOk_sound {T : ℕ} {G : List ℕ} (hG : ∀ d ∈ G, d < 2 ^ 24) (h : allOk T (nm T) G = true) :
    Calm (setOf G) (↑(decode T)) ∧ Closed (setOf G) (↑(decode T)) := by
  constructor
  · rintro D ⟨d, hd, rfl⟩
    obtain ⟨l, hl, hn⟩ := (okD_sound (hG d hd) (allOk_mem h d hd)).1
    exact ⟨l, hl, by simpa using hn⟩
  · rintro D ⟨d, hd, rfl⟩ l hl hr
    have := (okD_sound (hG d hd) (allOk_mem h d hd)).2 l hl (fun l' hl' hne => by simpa using hr l' hl' hne)
    simpa using this

theorem cons_sound {T : ℕ} (h : Nat.beq (Nat.land T (nm T)) 0 = true) : Cons (↑(decode T) : Set (Literal V)) := by
  intro l hl hn
  simp only [Finset.mem_coe] at hl hn
  rw [mem_decode_nm] at hn
  rw [mem_decode] at hl hn
  have : (T &&& nm T).testBit (idx l) = true := by rw [Nat.testBit_and, hl, hn]; rfl
  rw [show T &&& nm T = Nat.land T (nm T) from rfl, Nat.eq_of_beq_eq_true h] at this
  simp at this

-- the formula as masks: four pigeon clauses, then the hole clauses
def F0 : List ℕ := [7, 56, 448, 3584, 36864, 266240, 2101248, 294912, 2129920, 2359296, 73728, 532480, 4202496, 589824, 4259840, 4718592, 147456, 1064960, 8404992, 1179648, 8519680, 9437184]

theorem F0_lt : ∀ d ∈ F0, d < 2 ^ 24 := by decide

-- a fast closure heuristic (its result is checked, never trusted)
def colF (P c : ℕ) : ℕ := bif Nat.beq (Nat.land P c) 0 then 0 else andn c P
def holeF (T : ℕ) : ℕ :=
  Nat.shiftLeft (Nat.lor (colF (Nat.land T 4095) 585)
    (Nat.lor (colF (Nat.land T 4095) 1170) (colF (Nat.land T 4095) 2340))) 12
def pigA (N : ℕ) : ℕ := Nat.land N 585
def pigB (N : ℕ) : ℕ := Nat.land (Nat.shiftRight N 1) 585
def pigC (N : ℕ) : ℕ := Nat.land (Nat.shiftRight N 2) 585
def pigF (T : ℕ) : ℕ :=
  Nat.lor (andn (Nat.land (pigB (Nat.shiftRight T 12)) (pigC (Nat.shiftRight T 12))) (pigA (Nat.shiftRight T 12)))
    (Nat.lor (Nat.shiftLeft (andn (Nat.land (pigA (Nat.shiftRight T 12)) (pigC (Nat.shiftRight T 12)))
      (pigB (Nat.shiftRight T 12))) 1)
      (Nat.shiftLeft (andn (Nat.land (pigA (Nat.shiftRight T 12)) (pigB (Nat.shiftRight T 12)))
        (pigC (Nat.shiftRight T 12))) 2))
def updG (T d : ℕ) : ℕ :=
  bif Nat.beq (andn d (nm T)) 0 then Nat.lor T d
  else bif Nat.beq (Nat.land (andn d (nm T)) (andn d (nm T) - 1)) 0 then Nat.lor T (andn d (nm T)) else T
def passX : List ℕ → ℕ → ℕ
  | [], T => T
  | d :: ds, T => passX ds (updG T d)
def pass (X : List ℕ) (T : ℕ) : ℕ := passX X (Nat.lor T (Nat.lor (holeF T) (pigF T)))
def clos (X : List ℕ) : ℕ → ℕ → ℕ
  | 0, T => T
  | f+1, T => bif Nat.beq (pass X T) T then T else clos X f (pass X T)

-- s has a consistent shield over F0 ++ X
def certT (X : List ℕ) (s T : ℕ) : Bool :=
  Nat.beq (Nat.land s T) s && Nat.beq (Nat.land T (nm T)) 0 && allOk T (nm T) F0 && allOk T (nm T) X
def cert (X : List ℕ) (s : ℕ) : Bool := certT X s (clos X 30 s)
-- the clause c is not RUP over F0 ++ X
def cnrT (X : List ℕ) (c T : ℕ) : Bool :=
  Nat.beq (Nat.land (nm c) T) (nm c) && allOk T (nm T) F0 && allOk T (nm T) X
def cnr (X : List ℕ) (c : ℕ) : Bool := cnrT X c (clos X 30 (nm c))

theorem allOk_append (T nT : ℕ) : ∀ G H : List ℕ, allOk T nT (G ++ H) = (allOk T nT G && allOk T nT H)
  | [], H => by simp [allOk]
  | d :: ds, H => by simp [allOk, allOk_append T nT ds H, Bool.and_assoc]

theorem sub_of_land {a T : ℕ} (h : Nat.beq (Nat.land a T) a = true) {i : ℕ} (hi : a.testBit i = true) :
    T.testBit i = true := by
  have h' : a &&& T = a := Nat.eq_of_beq_eq_true h
  have : (a &&& T).testBit i = true := by rw [h']; exact hi
  rw [Nat.testBit_and] at this
  simpa [hi] using this

theorem certT_sound {X : List ℕ} (hX : ∀ d ∈ X, d < 2 ^ 24) {s T : ℕ} (h : certT X s T = true) :
    ∃ U, (↑(decode s) : Set (Literal V)) ⊆ U ∧ Closed (setOf (F0 ++ X)) U ∧ Calm (setOf (F0 ++ X)) U ∧ Cons U := by
  unfold certT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hall : allOk T (nm T) (F0 ++ X) = true := by rw [allOk_append, h3, h4]; rfl
  have hlt : ∀ d ∈ F0 ++ X, d < 2 ^ 24 := by
    intro d hd; rcases List.mem_append.mp hd with hd | hd
    · exact F0_lt d hd
    · exact hX d hd
  obtain ⟨hk, hc⟩ := allOk_sound hlt hall
  refine ⟨↑(decode T), ?_, hc, hk, cons_sound h2⟩
  intro l hl
  simp only [Finset.mem_coe, mem_decode] at hl ⊢
  exact sub_of_land h1 hl

theorem cert_sound {X : List ℕ} (hX : ∀ d ∈ X, d < 2 ^ 24) {s : ℕ} (h : cert X s = true) :
    ∃ U, (↑(decode s) : Set (Literal V)) ⊆ U ∧ Closed (setOf (F0 ++ X)) U ∧ Calm (setOf (F0 ++ X)) U ∧ Cons U :=
  certT_sound hX h

theorem cnr_sound {X : List ℕ} (hX : ∀ d ∈ X, d < 2 ^ 24) {c : ℕ} (h : cnr X c = true) :
    ¬ IsRUP (setOf (F0 ++ X)) (decode c) := by
  unfold cnr cnrT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h3⟩, h4⟩ := h
  set T := clos X 30 (nm c)
  have hall : allOk T (nm T) (F0 ++ X) = true := by rw [allOk_append, h3, h4]; rfl
  have hlt : ∀ d ∈ F0 ++ X, d < 2 ^ 24 := by
    intro d hd; rcases List.mem_append.mp hd with hd | hd
    · exact F0_lt d hd
    · exact hX d hd
  obtain ⟨hk, hc⟩ := allOk_sound hlt hall
  apply not_rup hc hk
  rintro _ ⟨l, hl, rfl⟩
  simp only [Finset.mem_coe] at hl ⊢
  have : negLit l ∈ decode (nm c) := by
    have h' := (@mem_decode_nm c (negLit l)).mp
    rw [negLit_negLit] at h'
    exact h' hl
  rw [mem_decode] at this ⊢
  exact sub_of_land h1 this

-- robustness, computed
def robLoop (f : ℕ → Bool) (s : ℕ) : ℕ → Bool
  | 0 => true
  | j+1 => (f (Nat.lor s (nm (2 ^ j))) || f (Nat.lor s (2 ^ j))) && robLoop f s j

def robB (X : List ℕ) : ℕ → ℕ → Bool
  | 0, s => cert X s
  | k+1, s => robB X k s && robLoop (robB X k) s 24

theorem robLoop_mem {f : ℕ → Bool} {s : ℕ} : ∀ {n : ℕ}, robLoop f s n = true → ∀ j < n,
    (f (Nat.lor s (nm (2 ^ j))) || f (Nat.lor s (2 ^ j))) = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n+1, h, j, hj => by
    unfold robLoop at h
    simp only [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact robLoop_mem h.2 j hj
    · exact h.1

theorem decode_or_pow (s : ℕ) (l : Literal V) :
    (↑(decode (Nat.lor s (2 ^ idx l))) : Set (Literal V)) = ↑(decode s) ∪ {l} := by
  ext l'
  simp only [Finset.mem_coe, mem_decode, Set.mem_union, Set.mem_singleton_iff]
  rw [show Nat.lor s (2 ^ idx l) = s ||| 2 ^ idx l from rfl, Nat.testBit_or, Nat.testBit_two_pow]
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (idx_inj _ _ h.symm)
  · rintro (h | rfl)
    · simp [h]
    · simp

theorem decode_or_nm (s : ℕ) (l : Literal V) :
    (↑(decode (Nat.lor s (nm (2 ^ idx l)))) : Set (Literal V)) = ↑(decode s) ∪ {negLit l} := by
  ext l'
  simp only [Finset.mem_coe, mem_decode, Set.mem_union, Set.mem_singleton_iff]
  rw [show Nat.lor s (nm (2 ^ idx l)) = s ||| nm (2 ^ idx l) from rfl, Nat.testBit_or,
    testBit_nm _ _ (idx_lt l'), Nat.testBit_two_pow]
  have key : flip (idx l') = idx l ↔ l' = negLit l := by
    constructor
    · intro h
      rw [← idx_neg] at h
      have := idx_inj _ _ h
      rw [← this, negLit_negLit]
    · rintro rfl
      rw [idx_neg]
      exact flip_flip _ (idx_lt l)
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (key.mp h.symm)
  · rintro (h | h)
    · simp [h]
    · simp [key.mpr h]

theorem robB_sound {X : List ℕ} (hX : ∀ d ∈ X, d < 2 ^ 24) :
    ∀ (k s : ℕ), robB X k s = true → RobS (setOf (F0 ++ X)) k ↑(decode s)
  | 0, s, h => cert_sound hX h
  | k+1, s, h => by
    unfold robB at h
    simp only [Bool.and_eq_true] at h
    refine ⟨robB_sound hX k s h.1, fun m => ?_⟩
    have := robLoop_mem h.2 (idx m) (idx_lt m)
    simp only [Bool.or_eq_true] at this
    rcases this with h1 | h1
    · left; rw [← decode_or_nm]; exact robB_sound hX k _ h1
    · right; rw [← decode_or_pow]; exact robB_sound hX k _ h1

-- the search for the inclusion-minimal clauses not certified non-RUP over F0
def minimalB (T : ℕ) : ℕ → Bool
  | 0 => true
  | x+1 => (!(Nat.testBit T x) || cnr [] (Nat.xor T (2 ^ x))) && minimalB T x

def dfsLoop : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | _+1, _, _, 0 => []
  | f+1, S, b, c+1 =>
      (bif cnr [] (Nat.lor S (2 ^ b)) then dfsLoop f (Nat.lor S (2 ^ b)) (b+1) (23 - b)
       else bif minimalB (Nat.lor S (2 ^ b)) 24 then [Nat.lor S (2 ^ b)] else []) ++ dfsLoop f S (b+1) c

theorem dfs_eq (f S b c : ℕ) : dfsLoop (f+1) S b (c+1) =
    (bif cnr [] (Nat.lor S (2 ^ b)) then dfsLoop f (Nat.lor S (2 ^ b)) (b+1) (23 - b)
     else bif minimalB (Nat.lor S (2 ^ b)) 24 then [Nat.lor S (2 ^ b)] else []) ++ dfsLoop f S (b+1) c := rfl

def pre (t b : ℕ) : ℕ := Nat.land t (2 ^ b - 1)

theorem testBit_pre (t b i : ℕ) : (pre t b).testBit i = (t.testBit i && decide (i < b)) := by
  unfold pre
  rw [show Nat.land t (2 ^ b - 1) = t &&& (2 ^ b - 1) from rfl, Nat.testBit_and, Nat.testBit_two_pow_sub_one]

theorem pre_zero (t : ℕ) : pre t 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [testBit_pre]; simp

theorem pre_full {t : ℕ} (ht : t < 2 ^ 24) : pre t 24 = t := by
  apply Nat.eq_of_testBit_eq; intro i; rw [testBit_pre]
  by_cases hi : i < 24
  · simp [hi]
  · have : t.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

theorem pre_succ_true {t b : ℕ} (h : t.testBit b = true) : Nat.lor (pre t b) (2 ^ b) = pre t (b+1) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show Nat.lor (pre t b) (2 ^ b) = pre t b ||| 2 ^ b from rfl, Nat.testBit_or, testBit_pre, testBit_pre,
    Nat.testBit_two_pow]
  by_cases hib : i = b
  · subst hib; simp [h]
  · by_cases hi : i < b
    · simp [hi, show i < b+1 by omega, Ne.symm hib]
    · simp [hi, show ¬ i < b+1 by omega, Ne.symm hib]

theorem pre_succ_false {t b : ℕ} (h : t.testBit b = false) : pre t b = pre t (b+1) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_pre, testBit_pre]
  by_cases hib : i = b
  · subst hib; simp [h]
  · by_cases hi : i < b
    · simp [hi, show i < b+1 by omega]
    · simp [hi, show ¬ i < b+1 by omega]

theorem minimalB_true {T : ℕ} (hP : ∀ x < 24, T.testBit x = true → cnr [] (Nat.xor T (2 ^ x)) = true) :
    ∀ n ≤ 24, minimalB T n = true
  | 0, _ => rfl
  | n+1, hn => by
    unfold minimalB
    rw [Bool.and_eq_true]
    refine ⟨?_, minimalB_true hP n (by omega)⟩
    cases h : T.testBit n
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      exact hP n (by omega) h

theorem dfs_complete {t : ℕ} (ht : t < 2 ^ 24) (hnot : cnr [] t = false)
    (hmin : ∀ t', (∀ i, t'.testBit i = true → t.testBit i = true) → t' ≠ t → cnr [] t' = true) :
    ∀ n f b, b + n = 24 → n + 1 ≤ f → pre t b ≠ t → t ∈ dfsLoop f (pre t b) b n := by
  intro n
  induction n with
  | zero =>
    intro f b hb _ hne
    exact absurd (by rw [show b = 24 by omega]; exact pre_full ht) hne
  | succ c ih =>
    intro f b hb hf hne
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [dfs_eq, List.mem_append]
    have h23 : 23 - b = c := by omega
    cases htb : t.testBit b
    · right
      rw [pre_succ_false htb]
      exact ih f' (b+1) (by omega) (by omega) (by rwa [← pre_succ_false htb])
    · left
      rw [pre_succ_true htb, h23]
      by_cases hT : pre t (b+1) = t
      · have hc : cnr [] (pre t (b+1)) = false := by rw [hT]; exact hnot
        rw [hc, cond_false]
        have hm : minimalB (pre t (b+1)) 24 = true := by
          rw [hT]
          apply minimalB_true _ 24 le_rfl
          intro x _ htx
          apply hmin
          · intro i hi
            rw [show Nat.xor t (2 ^ x) = t ^^^ 2 ^ x from rfl, Nat.testBit_xor, Nat.testBit_two_pow] at hi
            by_cases hix : x = i
            · subst hix; simp [htx] at hi
            · simpa [hix] using hi
          · intro heq
            have := congrArg (fun z => Nat.testBit z x) heq
            rw [show Nat.xor t (2 ^ x) = t ^^^ 2 ^ x from rfl, Nat.testBit_xor, Nat.testBit_two_pow, htx] at this
            simp at this
        rw [hm, cond_true, hT]
        exact List.mem_singleton_self t
      · have hc : cnr [] (pre t (b+1)) = true := by
          apply hmin _ (fun i hi => by rw [testBit_pre] at hi; simp at hi; exact hi.1) hT
        rw [hc, cond_true]
        exact ih f' (b+1) (by omega) (by omega) hT

theorem encode : ∀ C : Clause V, ∃ c, c < 2 ^ 24 ∧ decode c = C := by
  intro C
  induction C using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by ext l; simp [mem_decode]⟩
  | insert l C _ ih =>
    obtain ⟨c, hc, rfl⟩ := ih
    refine ⟨Nat.lor c (2 ^ idx l), ?_, ?_⟩
    · exact Nat.or_lt_two_pow hc (Nat.pow_lt_pow_right (by norm_num) (idx_lt l))
    · ext l'
      have := congrArg (fun S : Set (Literal V) => l' ∈ S) (decode_or_pow c l)
      simp only [Finset.mem_coe, Set.mem_union, Set.mem_singleton_iff, eq_iff_iff] at this
      rw [this, Finset.mem_insert]
      tauto

theorem L1_complete {C : Clause V} (h : IsRUP (setOf F0) C) : ∃ t ∈ dfsLoop 30 0 0 24, decode t ⊆ C := by
  classical
  obtain ⟨c, hc, rfl⟩ := encode C
  have hP : ∀ x, cnr [] x = true → ¬ IsRUP (setOf F0) (decode x) := by
    intro x hx
    have := cnr_sound (X := []) (by simp) hx
    simpa using this
  have hex : ∃ t, (∀ i, t.testBit i = true → c.testBit i = true) ∧ cnr [] t = false := by
    refine ⟨c, fun i h => h, ?_⟩
    cases hcc : cnr [] c
    · rfl
    · exact absurd h (hP c hcc)
  obtain ⟨htc, htn⟩ := Nat.find_spec hex
  have hmin : ∀ t', (∀ i, t'.testBit i = true → (Nat.find hex).testBit i = true) → t' ≠ Nat.find hex →
      cnr [] t' = true := by
    intro t' hsub hne
    have hlt : t' < Nat.find hex := lt_of_le_of_ne (Nat.le_of_testBit hsub) hne
    have := Nat.find_min hex hlt
    cases hh : cnr [] t'
    · exact absurd ⟨fun i hi => htc i (hsub i hi), hh⟩ this
    · rfl
  have htlt : Nat.find hex < 2 ^ 24 := lt_of_le_of_lt (Nat.le_of_testBit htc) hc
  have h0 : cnr [] 0 = true := by decide +kernel
  have hne : pre (Nat.find hex) 0 ≠ Nat.find hex := by
    rw [pre_zero]
    intro h
    rw [← h, h0] at htn
    exact absurd htn (by decide)
  refine ⟨Nat.find hex, ?_, ?_⟩
  · have := dfs_complete htlt htn hmin 24 30 0 (by norm_num) (by norm_num) hne
    rwa [pre_zero] at this
  · intro l hl
    rw [mem_decode] at hl ⊢
    exact htc _ hl

theorem php_eq : PHP (3+1) 3 = setOf F0 := by
  ext D
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, i', j, hne, rfl⟩)
    · have : ∀ i : Fin (3+1), ∃ d ∈ F0, (Finset.univ.image fun j : Fin 3 => ((i, j), true)) = decode d := by
        decide +kernel
      obtain ⟨d, hd, he⟩ := this i
      exact ⟨d, hd, he⟩
    · have : ∀ i i' : Fin (3+1), ∀ j : Fin 3, i ≠ i' →
          ∃ d ∈ F0, ({((i, j), false), ((i', j), false)} : Clause V) = decode d := by
        decide +kernel
      obtain ⟨d, hd, he⟩ := this i i' j hne
      exact ⟨d, hd, he⟩
  · rintro ⟨d, hd, rfl⟩
    have : ∀ d ∈ F0, (∃ i : Fin (3+1), decode d = Finset.univ.image fun j : Fin 3 => ((i, j), true)) ∨
        (∃ i i' : Fin (3+1), ∃ j : Fin 3, i ≠ i' ∧ decode d = {((i, j), false), ((i', j), false)}) := by
      decide +kernel
    rcases this d hd with ⟨i, h⟩ | ⟨i, i', j, hne, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨i, i', j, hne, h⟩

-- the domination of a learned clause by a minimal one
theorem dom1 {m : ℕ} {C1 : Clause V} (hsub : decode m ⊆ C1) (L : List (Clause V)) :
    ∀ D ∈ setOf F0 ∪ {D | D ∈ L ++ [C1]}, ∃ D' ∈ setOf (F0 ++ [m]) ∪ {D | D ∈ L}, D' ⊆ D := by
  rintro D (⟨d, hd, rfl⟩ | hD)
  · exact ⟨decode d, Or.inl ⟨d, List.mem_append_left _ hd, rfl⟩, le_rfl⟩
  · simp only [Set.mem_setOf_eq, List.mem_append, List.mem_singleton] at hD
    rcases hD with hD | rfl
    · exact ⟨D, Or.inr hD, le_rfl⟩
    · exact ⟨decode m, Or.inl ⟨m, by simp, rfl⟩, hsub⟩


-- symmetry: permutations of pigeons and holes
def P4 : List (List ℕ) := [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]
def P3 : List (List ℕ) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

def psi (a b : ℕ) (l : Literal V) : Literal V :=
  ((⟨(P4.getD a []).getD l.1.1.val 0 % (3+1), Nat.mod_lt _ (by decide)⟩,
    ⟨(P3.getD b []).getD l.1.2.val 0 % 3, Nat.mod_lt _ (by decide)⟩), l.2)

theorem psi_neg (a b : ℕ) (l : Literal V) : negLit (psi a b l) = psi a b (negLit l) := rfl

theorem up_map (ψ : Literal V → Literal V) (hneg : ∀ l, negLit (ψ l) = ψ (negLit l))
    {G : Set (Clause V)} {A : Set (Literal V)} {l : Literal V} (h : UPForces G A l) :
    UPForces ((fun C => C.image ψ) '' G) (ψ '' A) (ψ l) := by
  induction h with
  | hyp h => exact UPForces.hyp ⟨_, h, rfl⟩
  | @unit D l hD hl _ ih =>
    refine UPForces.unit ⟨D, hD, rfl⟩ (Finset.mem_image_of_mem ψ hl) ?_
    intro x hx hne
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hx
    rw [hneg]
    exact ih l' hl' (fun h => hne (h ▸ rfl))

theorem rup_map (ψ : Literal V → Literal V) (hneg : ∀ l, negLit (ψ l) = ψ (negLit l))
    {G : Set (Clause V)} {C : Clause V} (h : IsRUP G C) :
    IsRUP ((fun C => C.image ψ) '' G) (C.image ψ) := by
  obtain ⟨D, hD, hall⟩ := h
  refine ⟨D.image ψ, ⟨D, hD, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
  have := up_map ψ hneg (hall l hl)
  have hA : ψ '' (negLit '' (↑C : Set (Literal V))) = negLit '' (↑(C.image ψ) : Set (Literal V)) := by
    ext y
    simp only [Set.mem_image, Finset.coe_image, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨ψ z, ⟨z, hz, rfl⟩, hneg z⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨negLit z, ⟨z, hz, rfl⟩, (hneg z).symm⟩
  rw [hA] at this
  rw [hneg]
  exact this

def Pm (M : Clause V) : Prop := ∀ C1 C2 C3 : Clause V, M ⊆ C1 →
  IsRUP (PHP (3+1) 3 ∪ {D | D ∈ [C1]}) C2 → IsRUP (PHP (3+1) 3 ∪ {D | D ∈ [C2, C1]}) C3 →
  IsRUP (PHP (3+1) 3 ∪ {D | D ∈ [C3, C2, C1]}) ∅ → False

theorem img_sub (ψ : Literal V → Literal V) (hinv : ∀ C ∈ PHP (3+1) 3, C.image ψ ∈ PHP (3+1) 3)
    (L : List (Clause V)) :
    (fun C => C.image ψ) '' (PHP (3+1) 3 ∪ {D | D ∈ L}) ⊆
      PHP (3+1) 3 ∪ {D | D ∈ L.map (fun C => C.image ψ)} := by
  rintro _ ⟨C, hC | hC, rfl⟩
  · exact Or.inl (hinv C hC)
  · exact Or.inr (List.mem_map.mpr ⟨C, hC, rfl⟩)

theorem Pm_transport (ψ : Literal V → Literal V) (hneg : ∀ l, negLit (ψ l) = ψ (negLit l))
    (hinv : ∀ C ∈ PHP (3+1) 3, C.image ψ ∈ PHP (3+1) 3) {M : Clause V} (h : Pm (M.image ψ)) : Pm M := by
  intro C1 C2 C3 hsub h2 h3 h4
  apply h (C1.image ψ) (C2.image ψ) (C3.image ψ) (Finset.image_subset_image hsub)
  · exact rup_mono (img_sub ψ hinv [C1]) le_rfl (rup_map ψ hneg h2)
  · exact rup_mono (img_sub ψ hinv [C2, C1]) le_rfl (rup_map ψ hneg h3)
  · have := rup_mono (img_sub ψ hinv [C3, C2, C1]) le_rfl (rup_map ψ hneg h4)
    rw [Finset.image_empty] at this
    exact this

theorem Pm_of_rob {r : ℕ} (hr : r < 2 ^ 24) (hrb : robB [r] 2 0 = true) : Pm (decode r) := by
  intro C1 C2 C3 hsub h2 h3 h4
  rw [php_eq] at h2 h3 h4
  have hX : ∀ d ∈ [r], d < 2 ^ 24 := by
    intro d hd; rw [List.mem_singleton.mp hd]; exact hr
  have hrob := robB_sound hX 2 0 hrb
  have r2 : IsRUP (setOf (F0 ++ [r]) ∪ {D | D ∈ ([] : List (Clause V))}) C2 := rup_dom (dom1 hsub []) h2
  have r3 : IsRUP (setOf (F0 ++ [r]) ∪ {D | D ∈ [C2]}) C3 := rup_dom (dom1 hsub [C2]) h3
  have r4 : IsRUP (setOf (F0 ++ [r]) ∪ {D | D ∈ [C3, C2]}) ∅ := rup_dom (dom1 hsub [C3, C2]) h4
  have hrun : RunOver (setOf (F0 ++ [r])) [C3, C2] := ⟨⟨trivial, r2⟩, r3⟩
  obtain ⟨U, -, hc, hk, -⟩ := robS_sound _ 2 _ hrob [C3, C2] rfl hrun
  exact not_rup hc hk (by simp) r4

-- the data: the minimal clauses, the seven representatives, the symmetries used, and for each
-- clause a symmetry taking it to a representative
def L1lit : List ℕ := [7, 11, 19, 67, 131, 515, 1027, 4099, 8195, 13, 37, 69, 261, 517, 2053, 4101, 16389, 25, 41, 193, 321, 1537, 2561, 65537, 131073, 524289, 1048577, 4194305, 8388609, 22, 38, 134, 262, 1030, 2054, 8198, 16390, 26, 50, 194, 386, 1538, 3074, 32770, 131074, 262146, 1048578, 2097154, 8388610, 44, 52, 324, 388, 2564, 3076, 32772, 65540, 262148, 524292, 2097156, 4194308, 56, 88, 152, 536, 1048, 32792, 65560, 104, 296, 552, 2088, 32808, 131112, 200, 328, 1544, 2568, 8200, 16392, 524296, 1048584, 4194312, 8388616, 176, 304, 1072, 2096, 65584, 131120, 208, 400, 1552, 3088, 4112, 16400, 262160, 1048592, 2097168, 8388624, 352, 416, 2592, 3104, 4128, 8224, 262176, 524320, 2097184, 4194336, 448, 704, 1216, 262336, 524480, 832, 2368, 262464, 1048896, 1600, 2624, 8256, 16448, 65600, 131136, 4194368, 8388672, 1408, 2432, 524672, 1048960, 1664, 3200, 4224, 16512, 32896, 131200, 2097280, 8388736, 2816, 3328, 4352, 8448, 33024, 65792, 2097408, 4194560, 3584, 2098688, 4195840, 2099712, 8391168, 8704, 16896, 66048, 131584, 524800, 1049088, 4197376, 8391680, 5120, 17408, 33792, 132096, 263168, 1049600, 6144, 10240, 34816, 67584, 264192, 526336, 12288, 20480, 36864, 69632, 135168, 266240, 528384, 1052672, 2101248, 4198400, 8392704, 24576, 40960, 73728, 139264, 270336, 532480, 1056768, 2105344, 4202496, 8396800, 49152, 81920, 147456, 278528, 540672, 1064960, 2113536, 4210688, 8404992, 98304, 163840, 294912, 557056, 1081344, 2129920, 4227072, 8421376, 196608, 327680, 589824, 1114112, 2162688, 4259840, 8454144, 393216, 655360, 1179648, 2228224, 4325376, 8519680, 786432, 1310720, 2359296, 4456448, 8650752, 1572864, 2621440, 4718592, 8912896, 3145728, 5242880, 9437184, 6291456, 10485760, 12582912]
def R7 : List ℕ := [7, 11, 4099, 4112, 12288, 36864, 40960]
def SymP : List (ℕ × ℕ × List ℕ) := [(0, 0, [7, 56, 448, 3584, 36864, 266240, 2101248, 294912, 2129920, 2359296, 73728, 532480, 4202496, 589824, 4259840, 4718592, 147456, 1064960, 8404992, 1179648, 8519680, 9437184]), (0, 1, [7, 56, 448, 3584, 36864, 266240, 2101248, 294912, 2129920, 2359296, 147456, 1064960, 8404992, 1179648, 8519680, 9437184, 73728, 532480, 4202496, 589824, 4259840, 4718592]), (0, 2, [7, 56, 448, 3584, 73728, 532480, 4202496, 589824, 4259840, 4718592, 36864, 266240, 2101248, 294912, 2129920, 2359296, 147456, 1064960, 8404992, 1179648, 8519680, 9437184]), (0, 3, [7, 56, 448, 3584, 73728, 532480, 4202496, 589824, 4259840, 4718592, 147456, 1064960, 8404992, 1179648, 8519680, 9437184, 36864, 266240, 2101248, 294912, 2129920, 2359296]), (0, 4, [7, 56, 448, 3584, 147456, 1064960, 8404992, 1179648, 8519680, 9437184, 36864, 266240, 2101248, 294912, 2129920, 2359296, 73728, 532480, 4202496, 589824, 4259840, 4718592]), (0, 5, [7, 56, 448, 3584, 147456, 1064960, 8404992, 1179648, 8519680, 9437184, 73728, 532480, 4202496, 589824, 4259840, 4718592, 36864, 266240, 2101248, 294912, 2129920, 2359296]), (2, 0, [7, 448, 56, 3584, 266240, 36864, 2101248, 294912, 2359296, 2129920, 532480, 73728, 4202496, 589824, 4718592, 4259840, 1064960, 147456, 8404992, 1179648, 9437184, 8519680]), (2, 1, [7, 448, 56, 3584, 266240, 36864, 2101248, 294912, 2359296, 2129920, 1064960, 147456, 8404992, 1179648, 9437184, 8519680, 532480, 73728, 4202496, 589824, 4718592, 4259840]), (2, 2, [7, 448, 56, 3584, 532480, 73728, 4202496, 589824, 4718592, 4259840, 266240, 36864, 2101248, 294912, 2359296, 2129920, 1064960, 147456, 8404992, 1179648, 9437184, 8519680]), (2, 3, [7, 448, 56, 3584, 532480, 73728, 4202496, 589824, 4718592, 4259840, 1064960, 147456, 8404992, 1179648, 9437184, 8519680, 266240, 36864, 2101248, 294912, 2359296, 2129920]), (2, 4, [7, 448, 56, 3584, 1064960, 147456, 8404992, 1179648, 9437184, 8519680, 266240, 36864, 2101248, 294912, 2359296, 2129920, 532480, 73728, 4202496, 589824, 4718592, 4259840]), (2, 5, [7, 448, 56, 3584, 1064960, 147456, 8404992, 1179648, 9437184, 8519680, 532480, 73728, 4202496, 589824, 4718592, 4259840, 266240, 36864, 2101248, 294912, 2359296, 2129920]), (3, 0, [7, 448, 3584, 56, 266240, 2101248, 36864, 2359296, 294912, 2129920, 532480, 4202496, 73728, 4718592, 589824, 4259840, 1064960, 8404992, 147456, 9437184, 1179648, 8519680]), (3, 1, [7, 448, 3584, 56, 266240, 2101248, 36864, 2359296, 294912, 2129920, 1064960, 8404992, 147456, 9437184, 1179648, 8519680, 532480, 4202496, 73728, 4718592, 589824, 4259840]), (3, 2, [7, 448, 3584, 56, 532480, 4202496, 73728, 4718592, 589824, 4259840, 266240, 2101248, 36864, 2359296, 294912, 2129920, 1064960, 8404992, 147456, 9437184, 1179648, 8519680]), (3, 3, [7, 448, 3584, 56, 532480, 4202496, 73728, 4718592, 589824, 4259840, 1064960, 8404992, 147456, 9437184, 1179648, 8519680, 266240, 2101248, 36864, 2359296, 294912, 2129920]), (3, 4, [7, 448, 3584, 56, 1064960, 8404992, 147456, 9437184, 1179648, 8519680, 266240, 2101248, 36864, 2359296, 294912, 2129920, 532480, 4202496, 73728, 4718592, 589824, 4259840]), (3, 5, [7, 448, 3584, 56, 1064960, 8404992, 147456, 9437184, 1179648, 8519680, 532480, 4202496, 73728, 4718592, 589824, 4259840, 266240, 2101248, 36864, 2359296, 294912, 2129920]), (6, 0, [56, 7, 448, 3584, 36864, 294912, 2129920, 266240, 2101248, 2359296, 73728, 589824, 4259840, 532480, 4202496, 4718592, 147456, 1179648, 8519680, 1064960, 8404992, 9437184]), (6, 1, [56, 7, 448, 3584, 36864, 294912, 2129920, 266240, 2101248, 2359296, 147456, 1179648, 8519680, 1064960, 8404992, 9437184, 73728, 589824, 4259840, 532480, 4202496, 4718592]), (6, 2, [56, 7, 448, 3584, 73728, 589824, 4259840, 532480, 4202496, 4718592, 36864, 294912, 2129920, 266240, 2101248, 2359296, 147456, 1179648, 8519680, 1064960, 8404992, 9437184]), (6, 3, [56, 7, 448, 3584, 73728, 589824, 4259840, 532480, 4202496, 4718592, 147456, 1179648, 8519680, 1064960, 8404992, 9437184, 36864, 294912, 2129920, 266240, 2101248, 2359296]), (6, 4, [56, 7, 448, 3584, 147456, 1179648, 8519680, 1064960, 8404992, 9437184, 36864, 294912, 2129920, 266240, 2101248, 2359296, 73728, 589824, 4259840, 532480, 4202496, 4718592]), (6, 5, [56, 7, 448, 3584, 147456, 1179648, 8519680, 1064960, 8404992, 9437184, 73728, 589824, 4259840, 532480, 4202496, 4718592, 36864, 294912, 2129920, 266240, 2101248, 2359296]), (8, 0, [56, 448, 7, 3584, 294912, 36864, 2129920, 266240, 2359296, 2101248, 589824, 73728, 4259840, 532480, 4718592, 4202496, 1179648, 147456, 8519680, 1064960, 9437184, 8404992]), (8, 1, [56, 448, 7, 3584, 294912, 36864, 2129920, 266240, 2359296, 2101248, 1179648, 147456, 8519680, 1064960, 9437184, 8404992, 589824, 73728, 4259840, 532480, 4718592, 4202496]), (8, 2, [56, 448, 7, 3584, 589824, 73728, 4259840, 532480, 4718592, 4202496, 294912, 36864, 2129920, 266240, 2359296, 2101248, 1179648, 147456, 8519680, 1064960, 9437184, 8404992]), (8, 3, [56, 448, 7, 3584, 589824, 73728, 4259840, 532480, 4718592, 4202496, 1179648, 147456, 8519680, 1064960, 9437184, 8404992, 294912, 36864, 2129920, 266240, 2359296, 2101248]), (8, 4, [56, 448, 7, 3584, 1179648, 147456, 8519680, 1064960, 9437184, 8404992, 294912, 36864, 2129920, 266240, 2359296, 2101248, 589824, 73728, 4259840, 532480, 4718592, 4202496]), (8, 5, [56, 448, 7, 3584, 1179648, 147456, 8519680, 1064960, 9437184, 8404992, 589824, 73728, 4259840, 532480, 4718592, 4202496, 294912, 36864, 2129920, 266240, 2359296, 2101248]), (9, 0, [56, 448, 3584, 7, 294912, 2129920, 36864, 2359296, 266240, 2101248, 589824, 4259840, 73728, 4718592, 532480, 4202496, 1179648, 8519680, 147456, 9437184, 1064960, 8404992]), (9, 1, [56, 448, 3584, 7, 294912, 2129920, 36864, 2359296, 266240, 2101248, 1179648, 8519680, 147456, 9437184, 1064960, 8404992, 589824, 4259840, 73728, 4718592, 532480, 4202496]), (9, 2, [56, 448, 3584, 7, 589824, 4259840, 73728, 4718592, 532480, 4202496, 294912, 2129920, 36864, 2359296, 266240, 2101248, 1179648, 8519680, 147456, 9437184, 1064960, 8404992]), (9, 3, [56, 448, 3584, 7, 589824, 4259840, 73728, 4718592, 532480, 4202496, 1179648, 8519680, 147456, 9437184, 1064960, 8404992, 294912, 2129920, 36864, 2359296, 266240, 2101248]), (9, 4, [56, 448, 3584, 7, 1179648, 8519680, 147456, 9437184, 1064960, 8404992, 294912, 2129920, 36864, 2359296, 266240, 2101248, 589824, 4259840, 73728, 4718592, 532480, 4202496]), (9, 5, [56, 448, 3584, 7, 1179648, 8519680, 147456, 9437184, 1064960, 8404992, 589824, 4259840, 73728, 4718592, 532480, 4202496, 294912, 2129920, 36864, 2359296, 266240, 2101248]), (12, 0, [448, 7, 56, 3584, 266240, 294912, 2359296, 36864, 2101248, 2129920, 532480, 589824, 4718592, 73728, 4202496, 4259840, 1064960, 1179648, 9437184, 147456, 8404992, 8519680]), (12, 1, [448, 7, 56, 3584, 266240, 294912, 2359296, 36864, 2101248, 2129920, 1064960, 1179648, 9437184, 147456, 8404992, 8519680, 532480, 589824, 4718592, 73728, 4202496, 4259840]), (12, 2, [448, 7, 56, 3584, 532480, 589824, 4718592, 73728, 4202496, 4259840, 266240, 294912, 2359296, 36864, 2101248, 2129920, 1064960, 1179648, 9437184, 147456, 8404992, 8519680]), (12, 3, [448, 7, 56, 3584, 532480, 589824, 4718592, 73728, 4202496, 4259840, 1064960, 1179648, 9437184, 147456, 8404992, 8519680, 266240, 294912, 2359296, 36864, 2101248, 2129920]), (12, 4, [448, 7, 56, 3584, 1064960, 1179648, 9437184, 147456, 8404992, 8519680, 266240, 294912, 2359296, 36864, 2101248, 2129920, 532480, 589824, 4718592, 73728, 4202496, 4259840]), (12, 5, [448, 7, 56, 3584, 1064960, 1179648, 9437184, 147456, 8404992, 8519680, 532480, 589824, 4718592, 73728, 4202496, 4259840, 266240, 294912, 2359296, 36864, 2101248, 2129920]), (13, 0, [448, 7, 3584, 56, 266240, 2359296, 294912, 2101248, 36864, 2129920, 532480, 4718592, 589824, 4202496, 73728, 4259840, 1064960, 9437184, 1179648, 8404992, 147456, 8519680]), (13, 1, [448, 7, 3584, 56, 266240, 2359296, 294912, 2101248, 36864, 2129920, 1064960, 9437184, 1179648, 8404992, 147456, 8519680, 532480, 4718592, 589824, 4202496, 73728, 4259840]), (13, 2, [448, 7, 3584, 56, 532480, 4718592, 589824, 4202496, 73728, 4259840, 266240, 2359296, 294912, 2101248, 36864, 2129920, 1064960, 9437184, 1179648, 8404992, 147456, 8519680]), (13, 3, [448, 7, 3584, 56, 532480, 4718592, 589824, 4202496, 73728, 4259840, 1064960, 9437184, 1179648, 8404992, 147456, 8519680, 266240, 2359296, 294912, 2101248, 36864, 2129920]), (13, 4, [448, 7, 3584, 56, 1064960, 9437184, 1179648, 8404992, 147456, 8519680, 266240, 2359296, 294912, 2101248, 36864, 2129920, 532480, 4718592, 589824, 4202496, 73728, 4259840]), (13, 5, [448, 7, 3584, 56, 1064960, 9437184, 1179648, 8404992, 147456, 8519680, 532480, 4718592, 589824, 4202496, 73728, 4259840, 266240, 2359296, 294912, 2101248, 36864, 2129920]), (14, 0, [448, 56, 7, 3584, 294912, 266240, 2359296, 36864, 2129920, 2101248, 589824, 532480, 4718592, 73728, 4259840, 4202496, 1179648, 1064960, 9437184, 147456, 8519680, 8404992]), (14, 1, [448, 56, 7, 3584, 294912, 266240, 2359296, 36864, 2129920, 2101248, 1179648, 1064960, 9437184, 147456, 8519680, 8404992, 589824, 532480, 4718592, 73728, 4259840, 4202496]), (14, 2, [448, 56, 7, 3584, 589824, 532480, 4718592, 73728, 4259840, 4202496, 294912, 266240, 2359296, 36864, 2129920, 2101248, 1179648, 1064960, 9437184, 147456, 8519680, 8404992]), (14, 3, [448, 56, 7, 3584, 589824, 532480, 4718592, 73728, 4259840, 4202496, 1179648, 1064960, 9437184, 147456, 8519680, 8404992, 294912, 266240, 2359296, 36864, 2129920, 2101248]), (14, 4, [448, 56, 7, 3584, 1179648, 1064960, 9437184, 147456, 8519680, 8404992, 294912, 266240, 2359296, 36864, 2129920, 2101248, 589824, 532480, 4718592, 73728, 4259840, 4202496]), (14, 5, [448, 56, 7, 3584, 1179648, 1064960, 9437184, 147456, 8519680, 8404992, 589824, 532480, 4718592, 73728, 4259840, 4202496, 294912, 266240, 2359296, 36864, 2129920, 2101248]), (15, 0, [448, 56, 3584, 7, 294912, 2359296, 266240, 2129920, 36864, 2101248, 589824, 4718592, 532480, 4259840, 73728, 4202496, 1179648, 9437184, 1064960, 8519680, 147456, 8404992]), (15, 1, [448, 56, 3584, 7, 294912, 2359296, 266240, 2129920, 36864, 2101248, 1179648, 9437184, 1064960, 8519680, 147456, 8404992, 589824, 4718592, 532480, 4259840, 73728, 4202496]), (15, 2, [448, 56, 3584, 7, 589824, 4718592, 532480, 4259840, 73728, 4202496, 294912, 2359296, 266240, 2129920, 36864, 2101248, 1179648, 9437184, 1064960, 8519680, 147456, 8404992]), (15, 3, [448, 56, 3584, 7, 589824, 4718592, 532480, 4259840, 73728, 4202496, 1179648, 9437184, 1064960, 8519680, 147456, 8404992, 294912, 2359296, 266240, 2129920, 36864, 2101248]), (15, 4, [448, 56, 3584, 7, 1179648, 9437184, 1064960, 8519680, 147456, 8404992, 294912, 2359296, 266240, 2129920, 36864, 2101248, 589824, 4718592, 532480, 4259840, 73728, 4202496]), (15, 5, [448, 56, 3584, 7, 1179648, 9437184, 1064960, 8519680, 147456, 8404992, 589824, 4718592, 532480, 4259840, 73728, 4202496, 294912, 2359296, 266240, 2129920, 36864, 2101248]), (16, 0, [448, 3584, 7, 56, 2359296, 266240, 294912, 2101248, 2129920, 36864, 4718592, 532480, 589824, 4202496, 4259840, 73728, 9437184, 1064960, 1179648, 8404992, 8519680, 147456]), (16, 1, [448, 3584, 7, 56, 2359296, 266240, 294912, 2101248, 2129920, 36864, 9437184, 1064960, 1179648, 8404992, 8519680, 147456, 4718592, 532480, 589824, 4202496, 4259840, 73728]), (16, 2, [448, 3584, 7, 56, 4718592, 532480, 589824, 4202496, 4259840, 73728, 2359296, 266240, 294912, 2101248, 2129920, 36864, 9437184, 1064960, 1179648, 8404992, 8519680, 147456]), (16, 3, [448, 3584, 7, 56, 4718592, 532480, 589824, 4202496, 4259840, 73728, 9437184, 1064960, 1179648, 8404992, 8519680, 147456, 2359296, 266240, 294912, 2101248, 2129920, 36864]), (16, 4, [448, 3584, 7, 56, 9437184, 1064960, 1179648, 8404992, 8519680, 147456, 2359296, 266240, 294912, 2101248, 2129920, 36864, 4718592, 532480, 589824, 4202496, 4259840, 73728]), (16, 5, [448, 3584, 7, 56, 9437184, 1064960, 1179648, 8404992, 8519680, 147456, 4718592, 532480, 589824, 4202496, 4259840, 73728, 2359296, 266240, 294912, 2101248, 2129920, 36864]), (17, 0, [448, 3584, 56, 7, 2359296, 294912, 266240, 2129920, 2101248, 36864, 4718592, 589824, 532480, 4259840, 4202496, 73728, 9437184, 1179648, 1064960, 8519680, 8404992, 147456]), (17, 1, [448, 3584, 56, 7, 2359296, 294912, 266240, 2129920, 2101248, 36864, 9437184, 1179648, 1064960, 8519680, 8404992, 147456, 4718592, 589824, 532480, 4259840, 4202496, 73728]), (17, 2, [448, 3584, 56, 7, 4718592, 589824, 532480, 4259840, 4202496, 73728, 2359296, 294912, 266240, 2129920, 2101248, 36864, 9437184, 1179648, 1064960, 8519680, 8404992, 147456]), (17, 3, [448, 3584, 56, 7, 4718592, 589824, 532480, 4259840, 4202496, 73728, 9437184, 1179648, 1064960, 8519680, 8404992, 147456, 2359296, 294912, 266240, 2129920, 2101248, 36864]), (17, 4, [448, 3584, 56, 7, 9437184, 1179648, 1064960, 8519680, 8404992, 147456, 2359296, 294912, 266240, 2129920, 2101248, 36864, 4718592, 589824, 532480, 4259840, 4202496, 73728]), (17, 5, [448, 3584, 56, 7, 9437184, 1179648, 1064960, 8519680, 8404992, 147456, 4718592, 589824, 532480, 4259840, 4202496, 73728, 2359296, 294912, 266240, 2129920, 2101248, 36864])]
def SymD : List (ℕ × ℕ × ℕ × ℕ) := [(7, 0, 0, 7), (11, 0, 0, 11), (19, 0, 2, 11), (67, 2, 0, 11), (131, 2, 2, 11), (515, 3, 0, 11), (1027, 3, 2, 11), (4099, 0, 0, 4099), (8195, 0, 2, 4099), (13, 0, 1, 11), (37, 0, 3, 11), (69, 2, 1, 11), (261, 2, 3, 11), (517, 3, 1, 11), (2053, 3, 3, 11), (4101, 0, 1, 4099), (16389, 0, 3, 4099), (25, 6, 0, 11), (41, 6, 1, 11), (193, 8, 0, 11), (321, 8, 1, 11), (1537, 9, 0, 11), (2561, 9, 1, 11), (65537, 6, 2, 4112), (131073, 6, 3, 4112), (524289, 8, 2, 4112), (1048577, 8, 3, 4112), (4194305, 9, 2, 4112), (8388609, 9, 3, 4112), (22, 0, 4, 11), (38, 0, 5, 11), (134, 2, 4, 11), (262, 2, 5, 11), (1030, 3, 4, 11), (2054, 3, 5, 11), (8198, 0, 4, 4099), (16390, 0, 5, 4099), (26, 6, 2, 11), (50, 6, 4, 11), (194, 8, 2, 11), (386, 8, 4, 11), (1538, 9, 2, 11), (3074, 9, 4, 11), (32770, 6, 0, 4112), (131074, 6, 5, 4112), (262146, 8, 0, 4112), (1048578, 8, 5, 4112), (2097154, 9, 0, 4112), (8388610, 9, 5, 4112), (44, 6, 3, 11), (52, 6, 5, 11), (324, 8, 3, 11), (388, 8, 5, 11), (2564, 9, 3, 11), (3076, 9, 5, 11), (32772, 6, 1, 4112), (65540, 6, 4, 4112), (262148, 8, 1, 4112), (524292, 8, 4, 4112), (2097156, 9, 1, 4112), (4194308, 9, 4, 4112), (56, 6, 0, 7), (88, 12, 0, 11), (152, 12, 2, 11), (536, 13, 0, 11), (1048, 13, 2, 11), (32792, 6, 0, 4099), (65560, 6, 2, 4099), (104, 12, 1, 11), (296, 12, 3, 11), (552, 13, 1, 11), (2088, 13, 3, 11), (32808, 6, 1, 4099), (131112, 6, 3, 4099), (200, 14, 0, 11), (328, 14, 1, 11), (1544, 15, 0, 11), (2568, 15, 1, 11), (8200, 0, 2, 4112), (16392, 0, 3, 4112), (524296, 14, 2, 4112), (1048584, 14, 3, 4112), (4194312, 15, 2, 4112), (8388616, 15, 3, 4112), (176, 12, 4, 11), (304, 12, 5, 11), (1072, 13, 4, 11), (2096, 13, 5, 11), (65584, 6, 4, 4099), (131120, 6, 5, 4099), (208, 14, 2, 11), (400, 14, 4, 11), (1552, 15, 2, 11), (3088, 15, 4, 11), (4112, 0, 0, 4112), (16400, 0, 5, 4112), (262160, 14, 0, 4112), (1048592, 14, 5, 4112), (2097168, 15, 0, 4112), (8388624, 15, 5, 4112), (352, 14, 3, 11), (416, 14, 5, 11), (2592, 15, 3, 11), (3104, 15, 5, 11), (4128, 0, 1, 4112), (8224, 0, 4, 4112), (262176, 14, 1, 4112), (524320, 14, 4, 4112), (2097184, 15, 1, 4112), (4194336, 15, 4, 4112), (448, 8, 0, 7), (704, 16, 0, 11), (1216, 16, 2, 11), (262336, 8, 0, 4099), (524480, 8, 2, 4099), (832, 16, 1, 11), (2368, 16, 3, 11), (262464, 8, 1, 4099), (1048896, 8, 3, 4099), (1600, 17, 0, 11), (2624, 17, 1, 11), (8256, 2, 2, 4112), (16448, 2, 3, 4112), (65600, 12, 2, 4112), (131136, 12, 3, 4112), (4194368, 17, 2, 4112), (8388672, 17, 3, 4112), (1408, 16, 4, 11), (2432, 16, 5, 11), (524672, 8, 4, 4099), (1048960, 8, 5, 4099), (1664, 17, 2, 11), (3200, 17, 4, 11), (4224, 2, 0, 4112), (16512, 2, 5, 4112), (32896, 12, 0, 4112), (131200, 12, 5, 4112), (2097280, 17, 0, 4112), (8388736, 17, 5, 4112), (2816, 17, 3, 11), (3328, 17, 5, 11), (4352, 2, 1, 4112), (8448, 2, 4, 4112), (33024, 12, 1, 4112), (65792, 12, 4, 4112), (2097408, 17, 1, 4112), (4194560, 17, 4, 4112), (3584, 9, 0, 7), (2098688, 9, 0, 4099), (4195840, 9, 2, 4099), (2099712, 9, 1, 4099), (8391168, 9, 3, 4099), (8704, 3, 2, 4112), (16896, 3, 3, 4112), (66048, 13, 2, 4112), (131584, 13, 3, 4112), (524800, 16, 2, 4112), (1049088, 16, 3, 4112), (4197376, 9, 4, 4099), (8391680, 9, 5, 4099), (5120, 3, 0, 4112), (17408, 3, 5, 4112), (33792, 13, 0, 4112), (132096, 13, 5, 4112), (263168, 16, 0, 4112), (1049600, 16, 5, 4112), (6144, 3, 1, 4112), (10240, 3, 4, 4112), (34816, 13, 1, 4112), (67584, 13, 4, 4112), (264192, 16, 1, 4112), (526336, 16, 4, 4112), (12288, 0, 0, 12288), (20480, 0, 1, 12288), (36864, 0, 0, 36864), (69632, 0, 2, 40960), (135168, 0, 3, 40960), (266240, 2, 0, 36864), (528384, 2, 2, 40960), (1052672, 2, 3, 40960), (2101248, 3, 0, 36864), (4198400, 3, 2, 40960), (8392704, 3, 3, 40960), (24576, 0, 4, 12288), (40960, 0, 0, 40960), (73728, 0, 2, 36864), (139264, 0, 5, 40960), (270336, 2, 0, 40960), (532480, 2, 2, 36864), (1056768, 2, 5, 40960), (2105344, 3, 0, 40960), (4202496, 3, 2, 36864), (8396800, 3, 5, 40960), (49152, 0, 1, 40960), (81920, 0, 4, 40960), (147456, 0, 3, 36864), (278528, 2, 1, 40960), (540672, 2, 4, 40960), (1064960, 2, 3, 36864), (2113536, 3, 1, 40960), (4210688, 3, 4, 40960), (8404992, 3, 3, 36864), (98304, 6, 0, 12288), (163840, 6, 1, 12288), (294912, 12, 0, 36864), (557056, 12, 2, 40960), (1081344, 12, 3, 40960), (2129920, 13, 0, 36864), (4227072, 13, 2, 40960), (8421376, 13, 3, 40960), (196608, 6, 4, 12288), (327680, 12, 0, 40960), (589824, 12, 2, 36864), (1114112, 12, 5, 40960), (2162688, 13, 0, 40960), (4259840, 13, 2, 36864), (8454144, 13, 5, 40960), (393216, 12, 1, 40960), (655360, 12, 4, 40960), (1179648, 12, 3, 36864), (2228224, 13, 1, 40960), (4325376, 13, 4, 40960), (8519680, 13, 3, 36864), (786432, 8, 0, 12288), (1310720, 8, 1, 12288), (2359296, 16, 0, 36864), (4456448, 16, 2, 40960), (8650752, 16, 3, 40960), (1572864, 8, 4, 12288), (2621440, 16, 0, 40960), (4718592, 16, 2, 36864), (8912896, 16, 5, 40960), (3145728, 16, 1, 40960), (5242880, 16, 4, 40960), (9437184, 16, 3, 36864), (6291456, 9, 0, 12288), (10485760, 9, 1, 12288), (12582912, 9, 4, 12288)]

theorem symp_ok : ∀ p ∈ SymP, p.2.2.length = 22 ∧
    ∀ q ∈ List.zip F0 p.2.2, q.2 ∈ F0 ∧ (decode q.1).image (psi p.1 p.2.1) = decode q.2 := by
  decide +kernel
theorem symd_keys : SymD.map (fun e => e.1) = L1lit := by decide +kernel
theorem symd_ok : ∀ e ∈ SymD, (∃ p ∈ SymP, p.1 = e.2.1 ∧ p.2.1 = e.2.2.1) ∧ e.2.2.2 ∈ R7 ∧
    (decode e.1).image (psi e.2.1 e.2.2.1) = decode e.2.2.2 := by decide +kernel
theorem rob_0 : robB [7] 2 0 = true := by decide +kernel
theorem rob_1 : robB [11] 2 0 = true := by decide +kernel
theorem rob_2 : robB [4099] 2 0 = true := by decide +kernel
theorem rob_3 : robB [4112] 2 0 = true := by decide +kernel
theorem rob_4 : robB [12288] 2 0 = true := by decide +kernel
theorem rob_5 : robB [36864] 2 0 = true := by decide +kernel
theorem rob_6 : robB [40960] 2 0 = true := by decide +kernel
theorem R7_ok : ∀ r ∈ R7, r < 2 ^ 24 ∧ robB [r] 2 0 = true := by
  intro r hr
  simp only [R7, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, rob_0⟩
  · exact ⟨by norm_num, rob_1⟩
  · exact ⟨by norm_num, rob_2⟩
  · exact ⟨by norm_num, rob_3⟩
  · exact ⟨by norm_num, rob_4⟩
  · exact ⟨by norm_num, rob_5⟩
  · exact ⟨by norm_num, rob_6⟩

-- the search, split into its 24 top branches
def br (f b : ℕ) : List ℕ :=
  bif cnr [] (Nat.lor 0 (2 ^ b)) then dfsLoop f (Nat.lor 0 (2 ^ b)) (b+1) (23 - b)
  else bif minimalB (Nat.lor 0 (2 ^ b)) 24 then [Nat.lor 0 (2 ^ b)] else []

theorem br_eq (f b c : ℕ) : dfsLoop (f+1) 0 b (c+1) = br f b ++ dfsLoop f 0 (b+1) c := rfl

theorem mem_loop0 {t : ℕ} : ∀ c f b, c ≤ f → t ∈ dfsLoop f 0 b c → ∃ i < c, t ∈ br (f - 1 - i) (b + i)
  | 0, f, b, _, h => by
    cases f with
    | zero => simp [dfsLoop] at h
    | succ f => simp [dfsLoop] at h
  | c+1, f, b, hc, h => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [br_eq, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, by omega, by simpa using h⟩
    · obtain ⟨i, hi, hmem⟩ := mem_loop0 c f' (b+1) (by omega) h
      refine ⟨i+1, by omega, ?_⟩
      have e1 : f' + 1 - 1 - (i+1) = f' - 1 - i := by omega
      have e2 : b + (i+1) = b + 1 + i := by omega
      rw [e1, e2]
      exact hmem
theorem br_0 : br (30 - 1 - 0) (0 + 0) = [7, 11, 19, 67, 131, 515, 1027, 4099, 8195, 13, 37, 69, 261, 517, 2053, 4101, 16389, 25, 41, 193, 321, 1537, 2561, 65537, 131073, 524289, 1048577, 4194305, 8388609] := by decide +kernel
theorem br_1 : br (30 - 1 - 1) (0 + 1) = [22, 38, 134, 262, 1030, 2054, 8198, 16390, 26, 50, 194, 386, 1538, 3074, 32770, 131074, 262146, 1048578, 2097154, 8388610] := by decide +kernel
theorem br_2 : br (30 - 1 - 2) (0 + 2) = [44, 52, 324, 388, 2564, 3076, 32772, 65540, 262148, 524292, 2097156, 4194308] := by decide +kernel
theorem br_3 : br (30 - 1 - 3) (0 + 3) = [56, 88, 152, 536, 1048, 32792, 65560, 104, 296, 552, 2088, 32808, 131112, 200, 328, 1544, 2568, 8200, 16392, 524296, 1048584, 4194312, 8388616] := by decide +kernel
theorem br_4 : br (30 - 1 - 4) (0 + 4) = [176, 304, 1072, 2096, 65584, 131120, 208, 400, 1552, 3088, 4112, 16400, 262160, 1048592, 2097168, 8388624] := by decide +kernel
theorem br_5 : br (30 - 1 - 5) (0 + 5) = [352, 416, 2592, 3104, 4128, 8224, 262176, 524320, 2097184, 4194336] := by decide +kernel
theorem br_6 : br (30 - 1 - 6) (0 + 6) = [448, 704, 1216, 262336, 524480, 832, 2368, 262464, 1048896, 1600, 2624, 8256, 16448, 65600, 131136, 4194368, 8388672] := by decide +kernel
theorem br_7 : br (30 - 1 - 7) (0 + 7) = [1408, 2432, 524672, 1048960, 1664, 3200, 4224, 16512, 32896, 131200, 2097280, 8388736] := by decide +kernel
theorem br_8 : br (30 - 1 - 8) (0 + 8) = [2816, 3328, 4352, 8448, 33024, 65792, 2097408, 4194560] := by decide +kernel
theorem br_9 : br (30 - 1 - 9) (0 + 9) = [3584, 2098688, 4195840, 2099712, 8391168, 8704, 16896, 66048, 131584, 524800, 1049088] := by decide +kernel
theorem br_10 : br (30 - 1 - 10) (0 + 10) = [4197376, 8391680, 5120, 17408, 33792, 132096, 263168, 1049600] := by decide +kernel
theorem br_11 : br (30 - 1 - 11) (0 + 11) = [6144, 10240, 34816, 67584, 264192, 526336] := by decide +kernel
theorem br_12 : br (30 - 1 - 12) (0 + 12) = [12288, 20480, 36864, 69632, 135168, 266240, 528384, 1052672, 2101248, 4198400, 8392704] := by decide +kernel
theorem br_13 : br (30 - 1 - 13) (0 + 13) = [24576, 40960, 73728, 139264, 270336, 532480, 1056768, 2105344, 4202496, 8396800] := by decide +kernel
theorem br_14 : br (30 - 1 - 14) (0 + 14) = [49152, 81920, 147456, 278528, 540672, 1064960, 2113536, 4210688, 8404992] := by decide +kernel
theorem br_15 : br (30 - 1 - 15) (0 + 15) = [98304, 163840, 294912, 557056, 1081344, 2129920, 4227072, 8421376] := by decide +kernel
theorem br_16 : br (30 - 1 - 16) (0 + 16) = [196608, 327680, 589824, 1114112, 2162688, 4259840, 8454144] := by decide +kernel
theorem br_17 : br (30 - 1 - 17) (0 + 17) = [393216, 655360, 1179648, 2228224, 4325376, 8519680] := by decide +kernel
theorem br_18 : br (30 - 1 - 18) (0 + 18) = [786432, 1310720, 2359296, 4456448, 8650752] := by decide +kernel
theorem br_19 : br (30 - 1 - 19) (0 + 19) = [1572864, 2621440, 4718592, 8912896] := by decide +kernel
theorem br_20 : br (30 - 1 - 20) (0 + 20) = [3145728, 5242880, 9437184] := by decide +kernel
theorem br_21 : br (30 - 1 - 21) (0 + 21) = [6291456, 10485760] := by decide +kernel
theorem br_22 : br (30 - 1 - 22) (0 + 22) = [12582912] := by decide +kernel
theorem br_23 : br (30 - 1 - 23) (0 + 23) = [] := by decide +kernel

theorem in_L1 : ∀ m ∈ dfsLoop 30 0 0 24, m ∈ L1lit := by
  intro m hm
  obtain ⟨i, hi, h⟩ := mem_loop0 24 30 0 (by norm_num) hm
  interval_cases i
  · rw [br_0] at h
    exact (by decide +kernel : ∀ x ∈ [7, 11, 19, 67, 131, 515, 1027, 4099, 8195, 13, 37, 69, 261, 517, 2053, 4101, 16389, 25, 41, 193, 321, 1537, 2561, 65537, 131073, 524289, 1048577, 4194305, 8388609], x ∈ L1lit) m h
  · rw [br_1] at h
    exact (by decide +kernel : ∀ x ∈ [22, 38, 134, 262, 1030, 2054, 8198, 16390, 26, 50, 194, 386, 1538, 3074, 32770, 131074, 262146, 1048578, 2097154, 8388610], x ∈ L1lit) m h
  · rw [br_2] at h
    exact (by decide +kernel : ∀ x ∈ [44, 52, 324, 388, 2564, 3076, 32772, 65540, 262148, 524292, 2097156, 4194308], x ∈ L1lit) m h
  · rw [br_3] at h
    exact (by decide +kernel : ∀ x ∈ [56, 88, 152, 536, 1048, 32792, 65560, 104, 296, 552, 2088, 32808, 131112, 200, 328, 1544, 2568, 8200, 16392, 524296, 1048584, 4194312, 8388616], x ∈ L1lit) m h
  · rw [br_4] at h
    exact (by decide +kernel : ∀ x ∈ [176, 304, 1072, 2096, 65584, 131120, 208, 400, 1552, 3088, 4112, 16400, 262160, 1048592, 2097168, 8388624], x ∈ L1lit) m h
  · rw [br_5] at h
    exact (by decide +kernel : ∀ x ∈ [352, 416, 2592, 3104, 4128, 8224, 262176, 524320, 2097184, 4194336], x ∈ L1lit) m h
  · rw [br_6] at h
    exact (by decide +kernel : ∀ x ∈ [448, 704, 1216, 262336, 524480, 832, 2368, 262464, 1048896, 1600, 2624, 8256, 16448, 65600, 131136, 4194368, 8388672], x ∈ L1lit) m h
  · rw [br_7] at h
    exact (by decide +kernel : ∀ x ∈ [1408, 2432, 524672, 1048960, 1664, 3200, 4224, 16512, 32896, 131200, 2097280, 8388736], x ∈ L1lit) m h
  · rw [br_8] at h
    exact (by decide +kernel : ∀ x ∈ [2816, 3328, 4352, 8448, 33024, 65792, 2097408, 4194560], x ∈ L1lit) m h
  · rw [br_9] at h
    exact (by decide +kernel : ∀ x ∈ [3584, 2098688, 4195840, 2099712, 8391168, 8704, 16896, 66048, 131584, 524800, 1049088], x ∈ L1lit) m h
  · rw [br_10] at h
    exact (by decide +kernel : ∀ x ∈ [4197376, 8391680, 5120, 17408, 33792, 132096, 263168, 1049600], x ∈ L1lit) m h
  · rw [br_11] at h
    exact (by decide +kernel : ∀ x ∈ [6144, 10240, 34816, 67584, 264192, 526336], x ∈ L1lit) m h
  · rw [br_12] at h
    exact (by decide +kernel : ∀ x ∈ [12288, 20480, 36864, 69632, 135168, 266240, 528384, 1052672, 2101248, 4198400, 8392704], x ∈ L1lit) m h
  · rw [br_13] at h
    exact (by decide +kernel : ∀ x ∈ [24576, 40960, 73728, 139264, 270336, 532480, 1056768, 2105344, 4202496, 8396800], x ∈ L1lit) m h
  · rw [br_14] at h
    exact (by decide +kernel : ∀ x ∈ [49152, 81920, 147456, 278528, 540672, 1064960, 2113536, 4210688, 8404992], x ∈ L1lit) m h
  · rw [br_15] at h
    exact (by decide +kernel : ∀ x ∈ [98304, 163840, 294912, 557056, 1081344, 2129920, 4227072, 8421376], x ∈ L1lit) m h
  · rw [br_16] at h
    exact (by decide +kernel : ∀ x ∈ [196608, 327680, 589824, 1114112, 2162688, 4259840, 8454144], x ∈ L1lit) m h
  · rw [br_17] at h
    exact (by decide +kernel : ∀ x ∈ [393216, 655360, 1179648, 2228224, 4325376, 8519680], x ∈ L1lit) m h
  · rw [br_18] at h
    exact (by decide +kernel : ∀ x ∈ [786432, 1310720, 2359296, 4456448, 8650752], x ∈ L1lit) m h
  · rw [br_19] at h
    exact (by decide +kernel : ∀ x ∈ [1572864, 2621440, 4718592, 8912896], x ∈ L1lit) m h
  · rw [br_20] at h
    exact (by decide +kernel : ∀ x ∈ [3145728, 5242880, 9437184], x ∈ L1lit) m h
  · rw [br_21] at h
    exact (by decide +kernel : ∀ x ∈ [6291456, 10485760], x ∈ L1lit) m h
  · rw [br_22] at h
    exact (by decide +kernel : ∀ x ∈ [12582912], x ∈ L1lit) m h
  · rw [br_23] at h
    exact absurd h (List.not_mem_nil)

theorem psi_inv {a b : ℕ} (h : ∃ p ∈ SymP, p.1 = a ∧ p.2.1 = b) :
    ∀ C ∈ PHP (3+1) 3, C.image (psi a b) ∈ PHP (3+1) 3 := by
  rw [php_eq]
  rintro C ⟨d, hd, rfl⟩
  obtain ⟨p, hp, rfl, rfl⟩ := h
  obtain ⟨hlen, hz⟩ := symp_ok p hp
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have hF : F0.length = 22 := rfl
  have hk22 : k < 22 := hF ▸ hk
  have hkz : k < (List.zip F0 p.2.2).length := by rw [List.length_zip, hlen, hF, Nat.min_self]; exact hk22
  have hq := List.getElem_mem hkz
  rw [List.getElem_zip] at hq
  obtain ⟨h1, h2⟩ := hz _ hq
  exact ⟨_, h1, h2⟩

theorem all_Pm : ∀ m ∈ dfsLoop 30 0 0 24, Pm (decode m) := by
  intro m hm
  have hm' := in_L1 m hm
  rw [← symd_keys] at hm'
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
  obtain ⟨hp, hr, himg⟩ := symd_ok e he
  obtain ⟨hlt, hrb⟩ := R7_ok _ hr
  apply Pm_transport (psi e.2.1 e.2.2.1) (psi_neg _ _) (psi_inv hp)
  rw [himg]
  exact Pm_of_rob hlt hrb

theorem main3 (C1 C2 C3 : Clause V) (h1 : IsRUP (PHP (3+1) 3 ∪ {D | D ∈ ([] : List (Clause V))}) C1)
    (h2 : IsRUP (PHP (3+1) 3 ∪ {D | D ∈ [C1]}) C2) (h3 : IsRUP (PHP (3+1) 3 ∪ {D | D ∈ [C2, C1]}) C3)
    (h4 : IsRUP (PHP (3+1) 3 ∪ {D | D ∈ [C3, C2, C1]}) ∅) : False := by
  have h1' : IsRUP (setOf F0) C1 := by
    rw [php_eq] at h1
    exact rup_mono (fun D hD => by
      rcases hD with hD | hD
      · exact hD
      · exact absurd hD (List.not_mem_nil)) le_rfl h1
  obtain ⟨m, hm, hsub⟩ := L1_complete h1'
  exact all_Pm m hm C1 C2 C3 hsub h2 h3 h4

theorem extract : ∀ ρ : List (Clause V), IsRUPRun (PHP (3+1) 3) ρ → ∅ ∈ ρ →
    ∃ σ : List (Clause V), IsRUPRun (PHP (3+1) 3) σ ∧ σ.length < ρ.length ∧
      IsRUP (PHP (3+1) 3 ∪ {D | D ∈ σ}) ∅
  | [], _, h => absurd h (List.not_mem_nil)
  | C :: ρ', hrun, hmem => by
    cases hrun with
    | learn hρ hC =>
      rcases List.mem_cons.mp hmem with h | h
      · subst h; exact ⟨ρ', hρ, by simp, hC⟩
      · obtain ⟨σ, h1, h2, h3⟩ := extract ρ' hρ h
        exact ⟨σ, h1, by simp; omega, h3⟩

theorem sub_list {L L' : List (Clause V)} (h : ∀ D ∈ L, D ∈ L') :
    PHP (3+1) 3 ∪ {D | D ∈ L} ⊆ PHP (3+1) 3 ∪ {D | D ∈ L'} := by
  rintro D (hD | hD)
  · exact Or.inl hD
  · exact Or.inr (h D hD)

theorem finish :
    ∀ σ : List (Clause V), IsRUPRun (PHP (3+1) 3) σ → σ.length ≤ 3 →
    IsRUP (PHP (3+1) 3 ∪ {D | D ∈ σ}) ∅ → False := by
  intro σ hσ hl h4
  have P0 : decode 7 ∈ PHP (3+1) 3 := by rw [php_eq]; exact ⟨7, by decide, rfl⟩
  have self : ∀ (L : List (Clause V)) (C : Clause V), C ∈ L → IsRUP (PHP (3+1) 3 ∪ {D | D ∈ L}) C :=
    fun L C h => rup_self (Or.inr h)
  match σ, hσ, hl with
  | [], _, _ =>
    exact main3 (decode 7) (decode 7) (decode 7) (rup_self (Or.inl P0)) (rup_self (Or.inl P0))
      (rup_self (Or.inl P0)) (rup_mono (sub_list (by simp)) le_rfl h4)
  | [c1], hσ, _ =>
    cases hσ with
    | learn _ h1 =>
      exact main3 c1 c1 c1 h1 (self _ _ (by simp)) (self _ _ (by simp))
        (rup_mono (sub_list (by simp)) le_rfl h4)
  | [c2, c1], hσ, _ =>
    cases hσ with
    | learn hσ' h2 =>
      cases hσ' with
      | learn _ h1 =>
        exact main3 c1 c2 c2 h1 h2 (self _ _ (by simp)) (rup_mono (sub_list (by simp)) le_rfl h4)
  | [c3, c2, c1], hσ, _ =>
    cases hσ with
    | learn hσ' h3 =>
      cases hσ' with
      | learn hσ'' h2 =>
        cases hσ'' with
        | learn _ h1 => exact main3 c1 c2 c3 h1 h2 h3 h4
  | _ :: _ :: _ :: _ :: _, _, hl => simp at hl; omega

end PEqualNP.Outside.L_meta_9208

theorem PEqualNP.Outside.L_meta_9208 : ¬ (∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (3 + 1) 3) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)) ∈ ρ ∧ ρ.length ≤ 4) := by
  rintro ⟨ρ, hrun, hmem, hlen⟩
  obtain ⟨σ, hσ, hσl, hσr⟩ := PEqualNP.Outside.L_meta_9208.extract ρ hrun hmem
  exact PEqualNP.Outside.L_meta_9208.finish σ hσ (by omega) hσr
