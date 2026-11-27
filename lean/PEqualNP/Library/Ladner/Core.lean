import PEqualNP.Library.Ladner.Defs
import PEqualNP.Library.Universal.PrimsCPT
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Machines.ReduceNP
import PEqualNP.Library.Machines.LenLE
import PEqualNP.Library.Helpers.PolyExp
import PEqualNP.Library.L016
import PEqualNP.Library.L017
import PEqualNP.Library.L018
import PEqualNP.Library.L039
import PEqualNP.Library.L055

/-!
# The delayed diagonal language works, given the properties of its stage function

Helper module (proofs only, no statement may use it). The pure-mathematics part of the proof of
the theorem of Ladner (1975), in its padding form: from the stated properties of the stage
function and of the enumeration of deciders, the language `LL cA q` is in NP, outside P and
not NP-hard when P differs from NP.
-/

namespace PEqualNP.Library.Ladner

open PEqualNP.Library PEqualNP.Library.Universal PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-- Transport of polynomial-time computability along pointwise equality. -/
theorem cptE {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- A polynomial is below a power of its argument plus two. -/
theorem poly_le_pow2 (p : Polynomial ℕ) : ∃ c : ℕ, ∀ n : ℕ, p.eval n ≤ (n + 2) ^ c := by
  obtain ⟨k, hk⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add p
  refine ⟨k + 1, fun n => ?_⟩
  have h1 : n ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have h2 : 2 ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have h3 : k < 2 ^ k := Nat.lt_two_pow_self
  have h4 : (n + 2) ^ (k + 1) = (n + 2) ^ k * (n + 2) := pow_succ _ _
  have h5 := hk n
  nlinarith

theorem stage_zero (cA : List Bool) (q : Polynomial ℕ) : stage cA q 0 = 0 := rfl

/-- The pure-mathematics core. -/
theorem core (cA : List Bool) (q : Polynomial ℕ)
    (hA : NPComplete (Acq cA q))
    (hsucc : ∀ n, stage cA q (n + 1) =
      stage cA q n + (if Wb cA q (Hs cA q n) = true then 1 else 0))
    (hsound : ∀ n, Wb cA q (Hs cA q n) = true →
      ∃ z, ¬ (Dd (stage cA q n) z = true ↔ z ∈ LL cA q))
    (hlive : ∀ i z, ¬ (Dd i z = true ↔ z ∈ LL cA q) → ∀ n₀, ∃ n, n₀ ≤ n ∧
      (stage cA q n = i → Wb cA q (Hs cA q n) = true))
    (hcover : ∀ L ∈ P, ∃ i, ∀ z, Dd i z = true ↔ z ∈ L)
    (hdec : ∀ i, {z : List Bool | Dd i z = true} ∈ P)
    (hpad : {y : List Bool | Gp cA q y} ∈ P)
    (hbrute : ∀ n₁ : ℕ, ∃ B ∈ P, (∀ x ∈ B, x ∈ Acq cA q) ∧
      ∀ x ∈ Acq cA q, x.length < n₁ → x ∈ B)
    (hne : P ≠ NP) :
    LL cA q ∈ NP ∧ LL cA q ∉ P ∧ ¬ NPHard (LL cA q) := by
  -- outside P
  have hLP : LL cA q ∉ P := by
    intro hL
    obtain ⟨i, hi⟩ := hcover _ hL
    have hb : ∀ n, stage cA q n ≤ i := by
      intro n
      induction n with
      | zero => rw [stage_zero]; omega
      | succ n ih =>
        rw [hsucc]
        by_cases hw : Wb cA q (Hs cA q n) = true
        · obtain ⟨z, hz⟩ := hsound n hw
          have hne' : stage cA q n ≠ i := by
            intro e
            rw [e] at hz
            exact hz (hi z)
          rw [ite_eq_left hw]
          omega
        · rw [ite_eq_right hw]
          exact ih
    have hred : PolyTimeReducible (Acq cA q) (LL cA q) := by
      refine ⟨fun x => pairB x (un ((x.length + 2) ^ i)), ?_, fun x => ?_⟩
      · have h := L055 ((Polynomial.X + Polynomial.C 2) ^ i)
        simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_C] at h
        exact cpt_pairB2 cpt_id h
      · have hG : Gp cA q (pairB x (un ((x.length + 2) ^ i))) := by
          simp only [Gp, psi, unpairB_pairB, pairB_length, un_length]
          have := Nat.pow_le_pow_right (show 0 < x.length + 2 by omega) (hb x.length)
          omega
        constructor
        · intro hx
          refine ⟨?_, hG⟩
          simpa only [psi, unpairB_pairB] using hx
        · intro h
          simpa only [psi, unpairB_pairB] using h.1
    exact hne ((L018 _ hA).1 (L016 _ _ hred hL))
  -- in NP
  have hNP : LL cA q ∈ NP := by
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∉ Acq cA q := by
      by_contra hall
      push Not at hall
      have e : Acq cA q = (Set.univ : Set (List Bool)) := Set.eq_univ_of_forall hall
      have h39 : Acq cA q ∈ P := by rw [e]; exact L039
      exact hne ((L018 _ hA).1 h39)
    obtain ⟨fG, hfG, hcG⟩ := hpad
    refine L017 _ _ ⟨fun y => sel (if fG y then [true] else []) x0 (psi y), ?_, fun y => ?_⟩ hA.1
    · exact cpt_sel (cpt_bitFlag hcG) (cpt_const x0) cpt_unpairB1
    · have hG : Gp cA q y ↔ fG y = true := hfG y
      show y ∈ LL cA q ↔ sel (if fG y = true then [true] else []) x0 (psi y) ∈ Acq cA q
      cases hb : fG y
      · have hn : ¬ Gp cA q y := by rw [hG, hb]; simp
        have e : sel (if false = true then [true] else []) x0 (psi y) = x0 := by simp [sel]
        rw [e]
        exact ⟨fun h => absurd h.2 hn, fun h => absurd h hx0⟩
      · have hy : Gp cA q y := hG.2 hb
        have e : sel (if true = true then [true] else []) x0 (psi y) = psi y := by simp [sel]
        rw [e]
        exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  refine ⟨hNP, hLP, ?_⟩
  -- not NP-hard
  intro hh
  obtain ⟨f, hfc, hf⟩ := hh _ hA.1
  have hmono : Monotone (stage cA q) :=
    monotone_nat_of_le_succ (fun n => by rw [hsucc]; omega)
  have hunb : ∀ c, ∃ n, c < stage cA q n := by
    intro c
    by_contra hc
    push Not at hc
    have hev : ∀ c, (∀ n, stage cA q n ≤ c) →
        ∃ n₀, ∀ n, n₀ ≤ n → stage cA q n = stage cA q n₀ := by
      intro c
      induction c with
      | zero =>
        intro h
        exact ⟨0, fun n _ => by have h1 := h n; have h2 := h 0; omega⟩
      | succ c ih =>
        intro h
        by_cases hex : ∃ n₀, stage cA q n₀ = c + 1
        · obtain ⟨n₀, hn₀⟩ := hex
          exact ⟨n₀, fun n hn => by have h1 := hmono hn; have h2 := h n; omega⟩
        · push Not at hex
          exact ih (fun n => by have h1 := h n; have h2 := hex n; omega)
    obtain ⟨n₀, hn₀⟩ := hev c hc
    have heq : ∀ z, Dd (stage cA q n₀) z = true ↔ z ∈ LL cA q := by
      intro z
      by_contra hz
      obtain ⟨n, hn, hw⟩ := hlive _ z hz n₀
      have h1 := hw (hn₀ n hn)
      have h2 := hsucc n
      rw [ite_eq_left h1, hn₀ n hn, hn₀ (n + 1) (by omega)] at h2
      omega
    apply hLP
    have e : LL cA q = {z : List Bool | Dd (stage cA q n₀) z = true} :=
      Set.ext (fun z => (heq z).symm)
    rw [e]
    exact hdec _
  obtain ⟨q', hq'⟩ := output_length_poly f hfc
  obtain ⟨c, hc⟩ := poly_le_pow2 q'
  obtain ⟨n₁, hn₁⟩ := hunb c
  obtain ⟨B, hBP, hBsub, hBsup⟩ := hbrute n₁
  obtain ⟨fG, hfG, hcG⟩ := hpad
  obtain ⟨Sh, hSh⟩ : ∃ Sh : List Bool → Prop,
      ∀ x, Sh x ↔ (Gp cA q (f x) ∧ (psi (f x)).length < x.length) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : List Bool → List Bool, ∀ x, g x =
      sel (if fG (f x) then [true] else []) x
        (sel (if decide ((true :: psi (f x)).length ≤ x.length) then [true] else []) x
          (psi (f x))) := ⟨_, fun _ => rfl⟩
  have hgT : ∀ x, Sh x → g x = psi (f x) := by
    intro x hx
    rw [hSh] at hx
    have h1 : fG (f x) = true := (hfG (f x)).1 hx.1
    have h2 : (psi (f x)).length < x.length := hx.2
    rw [hg, h1]
    simp [sel, h2]
  have hgF : ∀ x, ¬ Sh x → g x = x := by
    intro x hx
    rw [hSh] at hx
    rw [hg]
    cases hb : fG (f x)
    · simp [sel]
    · have hG : Gp cA q (f x) := (hfG (f x)).2 hb
      have h2 : ¬ (psi (f x)).length < x.length := fun h => hx ⟨hG, h⟩
      simp [sel, h2]
  have hgcpt : CPT g := by
    have hpf : CPT (fun x => psi (f x)) := cpt_comp hfc cpt_unpairB1
    have h1 : CPT (fun x => if fG (f x) then [true] else []) :=
      cpt_bitFlag (cpt_comp hfc hcG)
    have h2 : CPT (fun x =>
        if decide ((true :: psi (f x)).length ≤ x.length) then [true] else []) :=
      cpt_bitFlag (cpt_comp (cpt_pair cpt_id (cpt_cons1 true hpf)) LenCmp.lenLE_polyTime)
    exact cptE (cpt_sel h1 cpt_id (cpt_sel h2 cpt_id hpf)) (fun x => (hg x).symm)
  have hglen : ∀ x, (g x).length ≤ x.length := by
    intro x
    by_cases h : Sh x
    · rw [hgT x h]; exact ((hSh x).1 h).2.le
    · rw [hgF x h]
  have hgA : ∀ x, x ∈ Acq cA q ↔ g x ∈ Acq cA q := by
    intro x
    by_cases h : Sh x
    · rw [hgT x h, hf x]
      exact ⟨fun h' => h'.1, fun h' => ⟨h', ((hSh x).1 h).1⟩⟩
    · rw [hgF x h]
  have hshort : ∀ x, ¬ Sh x → x ∈ Acq cA q → x.length < n₁ := by
    intro x hS hx
    have hL : f x ∈ LL cA q := (hf x).1 hx
    have hG : ((psi (f x)).length + 2) ^ stage cA q (psi (f x)).length ≤ (f x).length := hL.2
    have hm : x.length ≤ (psi (f x)).length := by
      by_contra h'
      exact hS ((hSh x).2 ⟨hL.2, by omega⟩)
    by_contra hlt
    have hst : c < stage cA q (psi (f x)).length :=
      lt_of_lt_of_le hn₁ (hmono (by omega))
    have h1 : ((psi (f x)).length + 2) ^ (c + 1) ≤
        ((psi (f x)).length + 2) ^ stage cA q (psi (f x)).length :=
      Nat.pow_le_pow_right (by omega) hst
    have h2 : (f x).length ≤ (x.length + 2) ^ c := (hq' x).trans (hc _)
    have h3 : (x.length + 2) ^ c ≤ ((psi (f x)).length + 2) ^ c :=
      Nat.pow_le_pow_left (by omega) c
    have h4 : ((psi (f x)).length + 2) ^ c < ((psi (f x)).length + 2) ^ (c + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hfix : ∀ k x, x.length ≤ k → ¬ Sh (g^[k] x) := by
    intro k
    induction k with
    | zero =>
      intro x hx hS
      have h1 := ((hSh _).1 hS).2
      simp only [Function.iterate_zero, id_eq] at h1
      omega
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      by_cases h : Sh x
      · refine ih _ ?_
        rw [hgT x h]
        have h1 := ((hSh x).1 h).2
        omega
      · rw [hgF x h, Function.iterate_fixed (hgF x h)]
        exact h
  have hiterA : ∀ k x, x ∈ Acq cA q ↔ g^[k] x ∈ Acq cA q := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, ← ih, ← hgA]
  have hred : PolyTimeReducible (Acq cA q) B := by
    refine ⟨fun x => g^[x.length] x, cpt_iterLen hgcpt hglen cpt_id cpt_id, fun x => ?_⟩
    constructor
    · intro hx
      have h1 := (hiterA x.length x).1 hx
      exact hBsup _ h1 (hshort _ (hfix _ x le_rfl) h1)
    · intro hx
      exact (hiterA x.length x).2 (hBsub _ hx)
  exact hne ((L018 _ hA).1 (L016 _ _ hred hBP))

end PEqualNP.Library.Ladner
