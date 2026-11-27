import PEqualNP.Library.Universal.LazyDefs
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.L055

/-!
# Upward padding: an exponential-time language, padded in front, is in P

Helper module (proofs only, no statement may use it).

A string `s` is a padded string `replicate (2 ^ (x.length ^ k) + k) true ++ false :: x` exactly
when a flag string `padF k s` is empty, and then `x = dropN s`. The flag is built from three
polynomial-time tests: `s` contains a `false`; the leading run, less `k` symbols, does not
vanish under `(dropN s).length ^ k` halvings; the same string less one more symbol does vanish.
The decider of the padded language runs the format test, extracts `dropN s` (or a fixed
non-member on a malformed input) and runs the given decider, whose time is at most the length
of the padding.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

local notation "CPT" =>
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

private theorem cptP {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### The format test -/

/-- The clock of the format test: `(dropN s).length ^ k` ones. -/
def padE (k : ℕ) (s : List Bool) : List Bool := List.replicate ((dropN s).length ^ k) true

/-- Nonempty exactly when `s` contains a `false`. -/
def padA (s : List Bool) : List Bool := dropN (s ++ [false])

/-- Nonempty exactly when the leading run has at least `2 ^ e + k` symbols. -/
def padB (k : ℕ) (s : List Bool) : List Bool := half^[(padE k s).length] ((hd s).drop k)

/-- Empty exactly when the leading run has at most `2 ^ e + k` symbols. -/
def padC (k : ℕ) (s : List Bool) : List Bool := half^[(padE k s).length] ((hd s).drop k).tail

/-- The format flag: empty exactly on padded strings. -/
def padF (k : ℕ) (s : List Bool) : List Bool :=
  sel (padA s) [true] (sel (padB k s) [true] (padC k s))

theorem half_length_le (s : List Bool) : (half s).length ≤ s.length := by
  rw [half_eq, un_length]; exact Nat.div_le_self _ _

theorem half_iter_length (e : ℕ) (w : List Bool) : (half^[e] w).length = w.length / 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', half_eq, un_length, ih, Nat.div_div_eq_div_mul, pow_succ]

theorem padB_length (k : ℕ) (s : List Bool) :
    (padB k s).length = ((hd s).length - k) / 2 ^ ((dropN s).length ^ k) := by
  simp [padB, padE, half_iter_length]

theorem padC_length (k : ℕ) (s : List Bool) :
    (padC k s).length = ((hd s).length - k - 1) / 2 ^ ((dropN s).length ^ k) := by
  simp [padC, padE, half_iter_length, Nat.sub_sub]

theorem hd_split (s : List Bool) : padA s = [] ∨ s = hd s ++ false :: dropN s := by
  induction s with
  | nil => left; simp [padA, dropN]
  | cons b r ih =>
    cases b
    · right; simp [hd, dropN]
    · have h1 : hd (true :: r) = true :: hd r := by simp [hd]
      have h2 : dropN (true :: r) = dropN r := by simp [dropN]
      rcases ih with h | h
      · left
        have h3 : padA (true :: r) = padA r := by simp [padA, dropN]
        rw [h3]; exact h
      · right
        rw [h1, h2]
        exact congrArg (List.cons true) h

theorem hd_eq_un (s : List Bool) : hd s = un (hd s).length :=
  un_length_eq _ (fun b hb => by
    have hall : ∀ l : List Bool, ∀ b ∈ l.takeWhile id, b = true := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        cases a
        · simp
        · intro b hb
          simp only [List.takeWhile_cons, id, ite_true, List.mem_cons] at hb
          rcases hb with hb | hb
          · exact hb
          · exact ih b hb
    exact hall s b hb)

theorem padF_pad (k : ℕ) (x : List Bool) :
    padF k (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = [] := by
  have h1 : hd (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) =
      un (2 ^ (x.length ^ k) + k) := hd_un _ _
  have h2 : dropN (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = x :=
    dropN_un _ _
  have hA : padA (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = x ++ [false] := by
    have e : (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) ++ [false] =
        un (2 ^ (x.length ^ k) + k) ++ false :: (x ++ [false]) := by simp [un]
    rw [padA, e, dropN_un]
  have hpos : 0 < 2 ^ (x.length ^ k) := Nat.pos_of_ne_zero (by positivity)
  have hB : padB k (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) ≠ [] := by
    intro hh
    have := congrArg List.length hh
    rw [padB_length, h1, h2, un_length, Nat.add_sub_cancel, Nat.div_self hpos] at this
    simp at this
  have hC : padC k (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [padC_length, h1, h2, un_length, Nat.add_sub_cancel]
    exact Nat.div_eq_of_lt (by omega)
  have hA' : padA (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) ≠ [] := by
    rw [hA]; simp
  simp [padF, sel, hA', hB, hC]

theorem padF_nil_iff (k : ℕ) (s : List Bool) :
    padF k s = [] ↔
      s = List.replicate (2 ^ ((dropN s).length ^ k) + k) true ++ false :: dropN s := by
  constructor
  · intro h
    by_cases hA : padA s = []
    · simp [padF, sel, hA] at h
    by_cases hB : padB k s = []
    · simp [padF, sel, hA, hB] at h
    have hC : padC k s = [] := by simpa [padF, sel, hA, hB] using h
    have hs := (hd_split s).resolve_left hA
    have hpos : 0 < 2 ^ ((dropN s).length ^ k) := Nat.pos_of_ne_zero (by positivity)
    have hB' : (padB k s).length ≠ 0 := fun hh => hB (List.eq_nil_of_length_eq_zero hh)
    have hC' : (padC k s).length = 0 := by rw [hC]; rfl
    rw [padB_length] at hB'
    rw [padC_length] at hC'
    have b1 : ¬ ((hd s).length - k < 2 ^ ((dropN s).length ^ k)) := fun hh =>
      hB' (Nat.div_eq_of_lt hh)
    have b2 : (hd s).length - k - 1 < 2 ^ ((dropN s).length ^ k) := by
      rcases (Nat.div_eq_zero_iff).1 hC' with h0 | h0
      · omega
      · exact h0
    have hlen : (hd s).length = 2 ^ ((dropN s).length ^ k) + k := by omega
    have hh : hd s = List.replicate (2 ^ ((dropN s).length ^ k) + k) true := by
      rw [hd_eq_un s, hlen]; rfl
    rw [hh] at hs
    exact hs
  · intro h
    have := padF_pad k (dropN s)
    rw [← h] at this
    exact this

/-! ### Polynomial time -/

theorem cpt_half' : CPT half :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

theorem cpt_drop (k : ℕ) {f : List Bool → List Bool} (hf : CPT f) :
    CPT (fun s => (f s).drop k) := by
  induction k with
  | zero => exact cptP hf (fun _ => rfl)
  | succ k ih => exact cptP (cpt_tail1 ih) (fun s => by simp)

theorem cpt_padE (k : ℕ) : CPT (padE k) :=
  cptP (cpt_comp cpt_dropN (PEqualNP.Library.L055 (Polynomial.X ^ k)))
    (fun s => by simp [padE])

theorem cpt_padA : CPT padA :=
  cptP (cpt_comp (cpt_app2 cpt_id (cpt_const [false])) cpt_dropN) (fun _ => rfl)

theorem cpt_padB (k : ℕ) : CPT (padB k) :=
  cptP (cpt_iterLen cpt_half' half_length_le (cpt_padE k) (cpt_drop k cpt_hd)) (fun _ => rfl)

theorem cpt_padC (k : ℕ) : CPT (padC k) :=
  cptP (cpt_iterLen cpt_half' half_length_le (cpt_padE k) (cpt_tail1 (cpt_drop k cpt_hd)))
    (fun _ => rfl)

theorem cpt_padF (k : ℕ) : CPT (padF k) :=
  cptP (cpt_sel cpt_padA (cpt_const [true])
    (cpt_sel (cpt_padB k) (cpt_const [true]) (cpt_padC k))) (fun _ => rfl)

private theorem isEmpty_run (q : Bool) (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool))) (fun q => some q) q l =
      [q && l.isEmpty] := by
  induction l generalizing q with
  | nil => simp [fstRun]
  | cons b l ih => simp [fstRun, ih]

theorem cpt_isEmpty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (false, (none : Option Bool)))
    (fun q => some q) true (fun l => by
      rw [isEmpty_run]; simp [Computability.encodeBool])

/-! ### The padded language -/

theorem padTime_mono (k : ℕ) : Monotone (fun n : ℕ => 2 ^ (n ^ k) + k) := by
  intro a b hab
  exact Nat.add_le_add_right
    (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hab k)) k

theorem padding_in_P (L : Language Bool) (k : ℕ)
    (h : L ∈ DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) :
    ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
      s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈ P := by
  obtain ⟨f, hf, hc⟩ := h
  by_cases hL : ∃ x₀ : List Bool, x₀ ∉ L
  · obtain ⟨x₀, hx₀⟩ := hL
    have hfx₀ : f x₀ ≠ true := fun hh => hx₀ ((hf x₀).2 hh)
    refine ⟨fun s => f (sel (padF k s) (dropN s) x₀), ?_, ?_⟩
    · intro s
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h2 : dropN (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = x :=
          dropN_un _ _
        show f (sel _ _ x₀) = true
        rw [padF_pad, sel_nil, h2]
        exact (hf x).1 hx
      · intro hs
        have hs' : f (sel (padF k s) (dropN s) x₀) = true := hs
        by_cases hp : padF k s = []
        · rw [hp, sel_nil] at hs'
          exact ⟨dropN s, (hf _).2 hs', (padF_nil_iff k s).1 hp⟩
        · have e : sel (padF k s) (dropN s) x₀ = x₀ := by simp [sel, hp]
          rw [e] at hs'
          exact absurd hs' hfx₀
    · have hg : CPT (fun s => sel (padF k s) (dropN s) x₀) :=
        cptP (cpt_sel (cpt_padF k) cpt_dropN (cpt_const x₀)) (fun _ => rfl)
      obtain ⟨p, hp⟩ := time_of_polyTime hg
      let len : ℕ → ℕ := fun n =>
        max x₀.length (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n)
      have hlen : ∀ s : List Bool,
          (sel (padF k s) (dropN s) x₀).length ≤ len s.length := by
        intro s
        by_cases hpf : padF k s = []
        · rw [hpf, sel_nil]
          have hs := congrArg List.length ((padF_nil_iff k s).1 hpf)
          simp only [List.length_append, List.length_replicate, List.length_cons] at hs
          refine le_trans ?_ (le_max_right _ _)
          have hm : (dropN s).length ≤ s.length := dropN_length s
          refine Nat.le_findGreatest hm ?_
          show 2 ^ ((dropN s).length ^ k) + k ≤ s.length
          generalize 2 ^ ((dropN s).length ^ k) = A at hs ⊢
          omega
        · have e : sel (padF k s) (dropN s) x₀ = x₀ := by simp [sel, hpf]
          rw [e]
          exact le_max_left _ _
      obtain ⟨c, hcb⟩ := comp_time (fun x : List Bool => x) (fun x : List Bool => x)
        Computability.encodeBool (fun s => sel (padF k s) (dropN s) x₀) f
        (fun n => p.eval n) (fun n : ℕ => 2 ^ (n ^ k) + k) len hp hc (padTime_mono k) hlen
      refine ⟨⟨c.toTM2ComputableAux,
        p + Polynomial.C 3 * Polynomial.X +
          Polynomial.C (2 * x₀.length + 2 ^ (x₀.length ^ k) + 2 * k + 5), fun a => ?_⟩⟩
      refine ⟨(c.outputsFun a).toEvalsTo, (c.outputsFun a).steps_le_m.trans ((hcb _).trans ?_)⟩
      generalize (a : List Bool).length = n
      have l1 : Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n ≤ n := Nat.findGreatest_le n
      have l2 : 2 ^ (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n ^ k) + k ≤ n + k + 2 := by
        rcases Nat.eq_zero_or_pos (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n) with h0 | h0
        · rw [h0]
          have : 2 ^ (0 ^ k) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by omega) (by
              rcases Nat.eq_zero_or_pos k with hk | hk
              · subst hk; simp
              · rw [Nat.zero_pow hk]; omega)
          omega
        · have := Nat.findGreatest_of_ne_zero (P := fun m => 2 ^ (m ^ k) + k ≤ n) rfl
            (by omega : Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n ≠ 0)
          omega
      have l3 : 2 ^ (len n ^ k) + k ≤ 2 ^ (x₀.length ^ k) + k + (n + k + 2) := by
        show 2 ^ ((max x₀.length (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n)) ^ k) + k ≤ _
        rcases max_cases x₀.length (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n) with
          ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [hm]; omega
        · rw [hm]
          generalize 2 ^ (x₀.length ^ k) = A
          generalize 2 ^ (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n ^ k) = B at l2 ⊢
          omega
      have l4 : len n ≤ x₀.length + n := by
        show max x₀.length (Nat.findGreatest (fun m => 2 ^ (m ^ k) + k ≤ n) n) ≤ _
        exact max_le (by omega) (by omega)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      show Polynomial.eval n p + (2 * len n + 2) + (2 ^ (len n ^ k) + k) ≤ _
      omega
  · have hall : ∀ x : List Bool, x ∈ L := fun x => by
      by_contra hx
      exact hL ⟨x, hx⟩
    refine ⟨fun s => (padF k s).isEmpty, ?_, cpt_comp (cpt_padF k) cpt_isEmpty⟩
    intro s
    constructor
    · rintro ⟨x, -, rfl⟩
      show (padF k _).isEmpty = true
      rw [padF_pad]; rfl
    · intro hs
      have hs' : (padF k s).isEmpty = true := hs
      have hp : padF k s = [] := List.isEmpty_iff.1 hs'
      exact ⟨dropN s, hall _, (padF_nil_iff k s).1 hp⟩

end PEqualNP.Library.Universal
