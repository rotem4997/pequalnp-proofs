import PEqualNP.MetaComplexity.Helpers.RowCode
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.IterRun

/-!
# Helper module (proofs only): symbol strings written in bits

Helper for "MCSP is in NP". A string over the alphabet `Sym` is written in bits, four bits per
symbol (`enc4`), and read back by a finite-state transducer (`dec4`). Both directions are
polynomial-time computable, so a finite-state transducer on symbol strings lifts to a
polynomial-time function on bit strings, and so does its bounded iteration.

* `symBits`, `enc4`, `dec4`, `dec4_enc4`, `length_enc4`, `length_dec4_le`, `enc4_injective`.
* `cpt_dec4`, `cpt_enc4`: the two polynomial-time lemmas.
* `cpt_fstRun2`, `cpt_fstRun`, `cpt_fstRun2_comp`, `cpt_fstRun_comp`: a transducer run is
  polynomial-time computable, for any alphabets.
* `lift_sym_sym`, `lift_sym_bool`, `lift_bool_bool`, `lift_bool_sym`: transducers on bit codes.
* `dec4_iterate`, `iter_sym`: bounded iteration of a symbol transducer that never lengthens.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.Library PEqualNP.Library.Machines

/-! ## The codec -/

/-- The four bits of a symbol. -/
def symBits : Sym → List Bool
  | Sym.A => [false, false, false, false]
  | Sym.O => [false, false, false, true]
  | Sym.N => [false, false, true, false]
  | Sym.R => [false, false, true, true]
  | Sym.t => [false, true, false, false]
  | Sym.V0 => [false, true, false, true]
  | Sym.V1 => [false, true, true, false]
  | Sym.Z => [false, true, true, true]
  | Sym.E0 => [true, false, false, false]
  | Sym.E1 => [true, false, false, true]
  | Sym.En => [true, false, true, false]

/-- The symbol of four bits. A group of four bits that is not the code of a symbol reads as
`Sym.V0`. -/
def bitsSym : Bool → Bool → Bool → Bool → Sym
  | false, false, false, false => Sym.A
  | false, false, false, true => Sym.O
  | false, false, true, false => Sym.N
  | false, false, true, true => Sym.R
  | false, true, false, false => Sym.t
  | false, true, false, true => Sym.V0
  | false, true, true, false => Sym.V1
  | false, true, true, true => Sym.Z
  | true, false, false, false => Sym.E0
  | true, false, false, true => Sym.E1
  | true, false, true, false => Sym.En
  | _, _, _, _ => Sym.V0

/-- A symbol string in bits: four bits per symbol. -/
def enc4 (u : List Sym) : List Bool := u.flatMap symBits

/-- The state of the decoder: the bits of the current group read so far (none, one, two or
three of them). -/
abbrev Pend : Type := Option (Bool ⊕ (Bool × Bool) ⊕ (Bool × Bool × Bool))

/-- The decoder: collect four bits, then write their symbol. -/
def δdec : Pend → Bool → Pend × Option Sym
  | none, a => (some (Sum.inl a), none)
  | some (Sum.inl a), b => (some (Sum.inr (Sum.inl (a, b))), none)
  | some (Sum.inr (Sum.inl (a, b))), c => (some (Sum.inr (Sum.inr (a, b, c))), none)
  | some (Sum.inr (Sum.inr (a, b, c))), d => (none, some (bitsSym a b c d))

/-- A bit string read as a symbol string, four bits at a time. A group that is not the code of
a symbol reads as `Sym.V0`; a last group of fewer than four bits is dropped. -/
def dec4 (w : List Bool) : List Sym := fstRun δdec (fun _ => none) none w

theorem dec4_nil : dec4 [] = [] := rfl

theorem dec4_cons4 (a b c d : Bool) (w : List Bool) :
    dec4 (a :: b :: c :: d :: w) = bitsSym a b c d :: dec4 w := rfl

theorem dec4_symBits_append (s : Sym) (w : List Bool) :
    dec4 (symBits s ++ w) = s :: dec4 w := by
  cases s <;> rfl

theorem enc4_nil : enc4 [] = [] := rfl

theorem enc4_cons (s : Sym) (u : List Sym) : enc4 (s :: u) = symBits s ++ enc4 u := by
  simp [enc4]

theorem enc4_append (u v : List Sym) : enc4 (u ++ v) = enc4 u ++ enc4 v := by
  simp [enc4]

/-- Decoding undoes encoding. -/
theorem dec4_enc4 (u : List Sym) : dec4 (enc4 u) = u := by
  induction u with
  | nil => rfl
  | cons s u ih => rw [enc4_cons, dec4_symBits_append, ih]

theorem enc4_injective : Function.Injective enc4 :=
  Function.LeftInverse.injective dec4_enc4

theorem length_symBits (s : Sym) : (symBits s).length = 4 := by
  cases s <;> rfl

theorem length_enc4 (u : List Sym) : (enc4 u).length = 4 * u.length := by
  induction u with
  | nil => rfl
  | cons s u ih =>
    rw [enc4_cons, List.length_append, length_symBits, ih, List.length_cons]
    omega

/-- The number of bits a decoder state holds. -/
def pendN : Pend → ℕ
  | none => 0
  | some (Sum.inl _) => 1
  | some (Sum.inr (Sum.inl _)) => 2
  | some (Sum.inr (Sum.inr _)) => 3

theorem length_decRun_le (q : Pend) (w : List Bool) :
    4 * (fstRun δdec (fun _ => none) q w).length ≤ w.length + pendN q := by
  induction w generalizing q with
  | nil => simp [fstRun]
  | cons x w ih =>
    rcases q with _ | a | ⟨a, b⟩ | ⟨a, b, c⟩
    · have h := ih (some (Sum.inl x))
      simp only [fstRun, δdec, pendN, Option.toList_none, List.nil_append,
        List.length_cons] at h ⊢
      omega
    · have h := ih (some (Sum.inr (Sum.inl (a, x))))
      simp only [fstRun, δdec, pendN, Option.toList_none, List.nil_append,
        List.length_cons] at h ⊢
      omega
    · have h := ih (some (Sum.inr (Sum.inr (a, b, x))))
      simp only [fstRun, δdec, pendN, Option.toList_none, List.nil_append,
        List.length_cons] at h ⊢
      omega
    · have h := ih none
      simp only [fstRun, δdec, pendN, Option.toList_some, List.singleton_append,
        List.length_cons] at h ⊢
      omega

/-- A decoded string has at most a quarter of the bits. -/
theorem length_dec4_le (w : List Bool) : 4 * (dec4 w).length ≤ w.length :=
  length_decRun_le none w

theorem length_dec4_le' (w : List Bool) : (dec4 w).length ≤ w.length := by
  have := length_dec4_le w
  omega

/-! ## Transducer runs are polynomial-time computable -/

/-- A two-output transducer run, for strings encoded as themselves. -/
theorem cpt_fstRun2 {A B Q : Type} [Fintype A] [Fintype Q]
    (δ : Q → A → Q × Option B × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime (fun l : List A => l) (fun l : List B => l) (fstRun2 δ fin q₀) :=
  fst2_polyTime _ _ _ δ fin q₀ (fun _ => rfl)

/-- A one-output transducer run, for strings encoded as themselves. -/
theorem cpt_fstRun {A B Q : Type} [Fintype A] [Fintype Q]
    (δ : Q → A → Q × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime (fun l : List A => l) (fun l : List B => l) (fstRun δ fin q₀) :=
  fst_polyTime _ _ _ δ fin q₀ (fun _ => rfl)

/-- A two-output transducer applied to a polynomial-time computable string. -/
theorem cpt_fstRun2_comp {α αΓ A B Q : Type} [Fintype A] [Fintype Q] {ea : α → List αΓ}
    {f : α → List A} (hf : ComputableInPolyTime ea (fun l : List A => l) f)
    (δ : Q → A → Q × Option B × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime ea (fun l : List B => l) (fun a => fstRun2 δ fin q₀ (f a)) :=
  cpt_comp hf (cpt_fstRun2 δ fin q₀)

/-- A one-output transducer applied to a polynomial-time computable string. -/
theorem cpt_fstRun_comp {α αΓ A B Q : Type} [Fintype A] [Fintype Q] {ea : α → List αΓ}
    {f : α → List A} (hf : ComputableInPolyTime ea (fun l : List A => l) f)
    (δ : Q → A → Q × Option B) (fin : Q → Option B) (q₀ : Q) :
    ComputableInPolyTime ea (fun l : List B => l) (fun a => fstRun δ fin q₀ (f a)) :=
  cpt_comp hf (cpt_fstRun δ fin q₀)

/-- The run of a transducer without state that writes two symbols for each symbol read. -/
theorem fstRun2_stateless {A B : Type} (x y : A → B) (l : List A) :
    fstRun2 (fun (_ : Unit) a => ((), some (x a), some (y a))) (fun _ => none) () l =
      l.flatMap (fun a => [x a, y a]) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fstRun2, ih]

/-- Replacing each symbol by two is polynomial-time computable. -/
theorem cpt_double {A B : Type} [Fintype A] (x y : A → B) :
    ComputableInPolyTime (fun l : List A => l) (fun l : List B => l)
      (fun l : List A => l.flatMap (fun a => [x a, y a])) :=
  fst2_polyTime _ _ _ (fun (_ : Unit) a => ((), some (x a), some (y a))) (fun _ => none) ()
    (fun l => (fstRun2_stateless x y l).symm)

/-! ## The codec is polynomial-time computable -/

/-- Decoding is polynomial-time computable. -/
theorem cpt_dec4 :
    ComputableInPolyTime (fun w : List Bool => w) (fun u : List Sym => u) dec4 :=
  cpt_fstRun δdec (fun _ => none) none

/-- The first two bits of a symbol. -/
def symHi (s : Sym) : Bool × Bool := ((symBits s).getD 0 false, (symBits s).getD 1 false)

/-- The last two bits of a symbol. -/
def symLo (s : Sym) : Bool × Bool := ((symBits s).getD 2 false, (symBits s).getD 3 false)

theorem enc4_eq_double (u : List Sym) :
    enc4 u = (u.flatMap (fun s => [symHi s, symLo s])).flatMap
      (fun p : Bool × Bool => [p.1, p.2]) := by
  induction u with
  | nil => rfl
  | cons s u ih =>
    have h : symBits s = [(symHi s).1, (symHi s).2, (symLo s).1, (symLo s).2] := by
      cases s <;> rfl
    rw [enc4_cons, ih, h]
    simp

/-- Encoding is polynomial-time computable. -/
theorem cpt_enc4 :
    ComputableInPolyTime (fun u : List Sym => u) (fun w : List Bool => w) enc4 := by
  have h := cpt_comp (cpt_double symHi symLo)
    (cpt_double (fun p : Bool × Bool => p.1) (fun p : Bool × Bool => p.2))
  have e : enc4 = (fun u : List Sym => (u.flatMap (fun s => [symHi s, symLo s])).flatMap
      (fun p : Bool × Bool => [p.1, p.2])) := funext enc4_eq_double
  rw [e]; exact h

/-! ## Transducers on bit codes -/

/-- A symbol transducer on bit codes, output in bit codes. -/
theorem lift_sym_sym {Q : Type} [Fintype Q] (δ : Q → Sym → Q × Option Sym × Option Sym)
    (fin : Q → Option Sym) (q₀ : Q) :
    ComputableInPolyTime (fun w : List Bool => w) (fun w : List Bool => w)
      (fun w : List Bool => enc4 (fstRun2 δ fin q₀ (dec4 w))) :=
  cpt_comp (cpt_fstRun2_comp cpt_dec4 δ fin q₀) cpt_enc4

/-- A transducer from symbols to bits, on bit codes. -/
theorem lift_sym_bool {Q : Type} [Fintype Q] (δ : Q → Sym → Q × Option Bool × Option Bool)
    (fin : Q → Option Bool) (q₀ : Q) :
    ComputableInPolyTime (fun w : List Bool => w) (fun w : List Bool => w)
      (fun w : List Bool => fstRun2 δ fin q₀ (dec4 w)) :=
  cpt_fstRun2_comp cpt_dec4 δ fin q₀

/-- A transducer from bits to bits. -/
theorem lift_bool_bool {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Bool × Option Bool)
    (fin : Q → Option Bool) (q₀ : Q) :
    ComputableInPolyTime (fun w : List Bool => w) (fun w : List Bool => w)
      (fun w : List Bool => fstRun2 δ fin q₀ w) :=
  cpt_fstRun2 δ fin q₀

/-- A transducer from bits to symbols, output in bit codes. -/
theorem lift_bool_sym {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Sym × Option Sym)
    (fin : Q → Option Sym) (q₀ : Q) :
    ComputableInPolyTime (fun w : List Bool => w) (fun w : List Bool => w)
      (fun w : List Bool => enc4 (fstRun2 δ fin q₀ w)) :=
  cpt_comp (cpt_fstRun2 δ fin q₀) cpt_enc4

/-! ## Bounded iteration -/

/-- Iterating a function on bit codes is iterating it on symbol strings. -/
theorem dec4_iterate (T : List Sym → List Sym) (k : ℕ) (w : List Bool) :
    dec4 ((fun w : List Bool => enc4 (T (dec4 w)))^[k] w) = T^[k] (dec4 w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dec4_enc4, ih]

/-- Bounded iteration of a symbol transducer that never lengthens its input: the first
component is the bit code of the start string, the length of the second is the number of
rounds. -/
theorem iter_sym {Q : Type} [Fintype Q] (δ : Q → Sym → Q × Option Sym × Option Sym)
    (fin : Q → Option Sym) (q₀ : Q)
    (hlen : ∀ l : List Sym, (fstRun2 δ fin q₀ l).length ≤ l.length) :
    ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => (fstRun2 δ fin q₀)^[p.2.length] (dec4 p.1)) := by
  obtain ⟨c⟩ := lift_sym_sym δ fin q₀
  have hk : ∀ y : List Bool,
      ((fun w : List Bool => enc4 (fstRun2 δ fin q₀ (dec4 w))) y).length ≤ y.length + 0 := by
    intro y
    have h1 := hlen (dec4 y)
    have h2 := length_dec4_le y
    simp only [length_enc4]
    omega
  have h : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool =>
        (fun w : List Bool => enc4 (fstRun2 δ fin q₀ (dec4 w)))^[p.2.length] p.1) :=
    Iter.iter_polyTime _ c 0 hk
  have h' := cpt_comp h cpt_dec4
  have e : (fun p : List Bool × List Bool => (fstRun2 δ fin q₀)^[p.2.length] (dec4 p.1)) =
      (fun p : List Bool × List Bool => dec4
        ((fun w : List Bool => enc4 (fstRun2 δ fin q₀ (dec4 w)))^[p.2.length] p.1)) := by
    funext p; rw [dec4_iterate]
  rw [e]; exact h'

end PEqualNP.MetaComplexity.Helpers.Machines
