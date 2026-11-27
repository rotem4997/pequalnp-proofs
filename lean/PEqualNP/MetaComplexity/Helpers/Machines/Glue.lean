import PEqualNP.MetaComplexity.Helpers.Machines.Codec
import PEqualNP.MetaComplexity.Helpers.Machines.StrEq
import PEqualNP.Library.Machines.NormalForm
import PEqualNP.Library.Machines.ConstList

/-!
# Helper module (proofs only): decisions on a pair, assembled from string functions

Helper for "MCSP is in NP". Functions of a pair `(x, w)` of bit strings whose value is a bit
string, a symbol string or a bit are combined here: pairing, equality, length comparison,
"all bits true", concatenation, conjunction, transducers, bounded iteration. The last two
lemmas turn a polynomial-time verifier into membership in NP.

The pairing of two functions of the pair goes through a bit string: `packRaw` writes a raw
list over `Bool ⊕ Bool` with two bits per symbol, `unpack` reads the two strings back, so a
function of the pair becomes a function of one bit string, where `cpt_pair` applies.

* `pair_prod`, `pair_eq`, `pair_lenLE`, `pair_allTrue`, `pair_append`, `pair_and`,
  `pair_comp`, `pair_const`: bit-string valued functions of the pair.
* `sym_enc`, `sym_dec`, `sym_dec4_fst`, `sym_dec4_snd`, `sym_eq`, `sym_lenLE`, `sym_append`,
  `sym_iter`, `sym_eq_append_run`: symbol-string valued functions of the pair.
* `np_of_verifier`, `np_of_sym_verifier`: the packaging.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.Library PEqualNP.Library.Machines

/-! ## General helpers -/

/-- A function equal everywhere to a polynomial-time computable one is polynomial-time
computable. -/
theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f g : α → β}
    (hf : ComputableInPolyTime ea eb f) (e : ∀ a, f a = g a) :
    ComputableInPolyTime ea eb g := by
  have h : f = g := funext e
  rw [← h]; exact hf

/-- A decision, seen as a one-bit string. -/
theorem cpt_bit_of_dec {α αΓ : Type} {ea : α → List αΓ} {a : α → Bool}
    (h : ComputableInPolyTime ea Computability.encodeBool a) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun p => [a p]) := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun q => c.outputsFun q⟩⟩

/-- A one-bit string, seen as a decision. -/
theorem cpt_dec_of_bit {α αΓ : Type} {ea : α → List αΓ} {a : α → Bool}
    (h : ComputableInPolyTime ea (fun x : List Bool => x) (fun p => [a p])) :
    ComputableInPolyTime ea Computability.encodeBool a := by
  obtain ⟨c⟩ := h
  exact ⟨⟨c.toTM2ComputableAux, c.time, fun q => c.outputsFun q⟩⟩

/-- Whether every bit of a string is true. -/
theorem cpt_allTrue :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => x.all id) :=
  cpt_congr (cpt_comp cpt_dup allTrue_polyTime) (fun x => by simp)

/-! ## A raw list over `Bool ⊕ Bool` as a bit string -/

/-- Two bits per symbol: the side, then the bit. -/
def packRaw (l : List (Bool ⊕ Bool)) : List Bool :=
  fstRun2
    (fun (_ : Unit) (s : Bool ⊕ Bool) => ((), some (Sum.isRight s), some (Sum.elim id id s)))
    (fun _ => none) () l

/-- The reader of one side `t`: remember the side bit, then keep the next bit when the side is
`t`. -/
def δun (t : Bool) : Option Bool → Bool → Option Bool × Option Bool
  | none, a => (some a, none)
  | some a, b => (none, if a = t then some b else none)

/-- The two strings of a packed raw list. -/
def unpack (l : List Bool) : List Bool × List Bool :=
  (fstRun (δun false) (fun _ => none) none l, fstRun (δun true) (fun _ => none) none l)

theorem unpack_packRaw (l : List (Bool ⊕ Bool)) : unpack (packRaw l) = nfDec l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s with
    | inl b =>
      have h1 : unpack (packRaw (Sum.inl b :: l)) =
          (b :: (unpack (packRaw l)).1, (unpack (packRaw l)).2) := rfl
      have h2 : nfDec (Sum.inl b :: l) = (b :: (nfDec l).1, (nfDec l).2) := rfl
      rw [h1, h2, ih]
    | inr b =>
      have h1 : unpack (packRaw (Sum.inr b :: l)) =
          ((unpack (packRaw l)).1, b :: (unpack (packRaw l)).2) := rfl
      have h2 : nfDec (Sum.inr b :: l) = ((nfDec l).1, b :: (nfDec l).2) := rfl
      rw [h1, h2, ih]

theorem unpack_pack (p : List Bool × List Bool) : unpack (packRaw (encodePair p)) = p := by
  rw [unpack_packRaw, nfDec_encodePair]

theorem cpt_pack :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => packRaw (encodePair p)) :=
  fst2_polyTime _ _ _
    (fun (_ : Unit) (s : Bool ⊕ Bool) => ((), some (Sum.isRight s), some (Sum.elim id id s)))
    (fun _ => none) () (fun _ => rfl)

theorem cpt_unpack :
    ComputableInPolyTime (fun x : List Bool => x) encodePair unpack :=
  cpt_pair (cpt_fstRun (δun false) (fun _ => none) none)
    (cpt_fstRun (δun true) (fun _ => none) none)

/-! ## Bit-string valued functions of the pair -/

/-- Pairing two functions of the pair. -/
theorem pair_prod {f g : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) g) :
    ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p, g p)) :=
  cpt_congr
    (cpt_comp cpt_pack (cpt_pair (cpt_comp cpt_unpack hf) (cpt_comp cpt_unpack hg)))
    (fun p => by simp only [unpack_pack])

/-- Applying a function of one string to a function of the pair. -/
theorem pair_comp {β βΓ : Type} {eb : β → List βΓ} {f : List Bool × List Bool → List Bool}
    {h : List Bool → β}
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f)
    (hh : ComputableInPolyTime (fun x : List Bool => x) eb h) :
    ComputableInPolyTime encodePair eb (fun p : List Bool × List Bool => h (f p)) :=
  cpt_comp hf hh

/-- A constant string. -/
theorem pair_const (l : List Bool) :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun _ : List Bool × List Bool => l) :=
  cpt_comp cpt_fst (constList_polyTime l)

/-- Equality of two functions of the pair. -/
theorem pair_eq {f g : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) g) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (f p = g p)) := by
  have s : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) := strEq_polyTime (A := Bool)
  exact cpt_comp (pair_prod hf hg) s

/-- Length comparison of two functions of the pair. -/
theorem pair_lenLE {f g : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) g) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide ((g p).length ≤ (f p).length)) :=
  cpt_comp (pair_prod hf hg) LenCmp.lenLE_polyTime

/-- Whether every bit of a function of the pair is true. -/
theorem pair_allTrue {f : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => (f p).all id) :=
  cpt_comp hf cpt_allTrue

/-- Concatenation of two functions of the pair. -/
theorem pair_append {f g : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun x : List Bool => x) f)
    (hg : ComputableInPolyTime encodePair (fun x : List Bool => x) g) :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => f p ++ g p) :=
  cpt_comp (pair_prod hf hg) cpt_append

/-- Conjunction of two decisions on the pair. -/
theorem pair_and {a b : List Bool × List Bool → Bool}
    (ha : ComputableInPolyTime encodePair Computability.encodeBool a)
    (hb : ComputableInPolyTime encodePair Computability.encodeBool b) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => a p && b p) :=
  cpt_congr (pair_allTrue (pair_append (cpt_bit_of_dec ha) (cpt_bit_of_dec hb)))
    (fun p => by simp)

/-! ## Symbol-string valued functions of the pair -/

/-- The bit code of a symbol-string valued function. -/
theorem sym_enc {α αΓ : Type} {ea : α → List αΓ} {f : α → List Sym}
    (hf : ComputableInPolyTime ea (fun u : List Sym => u) f) :
    ComputableInPolyTime ea (fun x : List Bool => x) (fun p => enc4 (f p)) :=
  cpt_comp hf cpt_enc4

/-- The symbol string of a bit-string valued function. -/
theorem sym_dec {α αΓ : Type} {ea : α → List αΓ} {f : α → List Bool}
    (hf : ComputableInPolyTime ea (fun x : List Bool => x) f) :
    ComputableInPolyTime ea (fun u : List Sym => u) (fun p => dec4 (f p)) :=
  cpt_comp hf cpt_dec4

/-- The first component, decoded. -/
theorem sym_dec4_fst :
    ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => dec4 p.1) :=
  sym_dec cpt_fst

/-- The second component, decoded. -/
theorem sym_dec4_snd :
    ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => dec4 p.2) :=
  sym_dec cpt_snd

/-- Equality of two symbol-string valued functions of the pair. -/
theorem sym_eq {f g : List Bool × List Bool → List Sym}
    (hf : ComputableInPolyTime encodePair (fun u : List Sym => u) f)
    (hg : ComputableInPolyTime encodePair (fun u : List Sym => u) g) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (f p = g p)) :=
  cpt_congr (pair_eq (sym_enc hf) (sym_enc hg))
    (fun p => by simp only [enc4_injective.eq_iff])

/-- Length comparison of two symbol-string valued functions of the pair. -/
theorem sym_lenLE {f g : List Bool × List Bool → List Sym}
    (hf : ComputableInPolyTime encodePair (fun u : List Sym => u) f)
    (hg : ComputableInPolyTime encodePair (fun u : List Sym => u) g) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide ((g p).length ≤ (f p).length)) :=
  cpt_congr (pair_lenLE (sym_enc hf) (sym_enc hg))
    (fun p => by simp [length_enc4])

/-- Concatenation of two symbol-string valued functions of the pair. -/
theorem sym_append {f g : List Bool × List Bool → List Sym}
    (hf : ComputableInPolyTime encodePair (fun u : List Sym => u) f)
    (hg : ComputableInPolyTime encodePair (fun u : List Sym => u) g) :
    ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => f p ++ g p) :=
  cpt_congr (sym_dec (pair_append (sym_enc hf) (sym_enc hg)))
    (fun p => by rw [← enc4_append, dec4_enc4])

/-- Bounded iteration of a symbol transducer that never lengthens its input: the start string
is `f p`, the number of rounds is the length of `c p`. -/
theorem sym_iter {Q : Type} [Fintype Q] (δ : Q → Sym → Q × Option Sym × Option Sym)
    (fin : Q → Option Sym) (q₀ : Q)
    (hlen : ∀ l : List Sym, (fstRun2 δ fin q₀ l).length ≤ l.length)
    {f : List Bool × List Bool → List Sym} {c : List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime encodePair (fun u : List Sym => u) f)
    (hc : ComputableInPolyTime encodePair (fun x : List Bool => x) c) :
    ComputableInPolyTime encodePair (fun u : List Sym => u)
      (fun p : List Bool × List Bool => (fstRun2 δ fin q₀)^[(c p).length] (f p)) :=
  cpt_congr (cpt_comp (pair_prod (sym_enc hf) hc) (iter_sym δ fin q₀ hlen))
    (fun p => by simp only [dec4_enc4])

/-- The run of one symbol transducer on the decoded witness equals the concatenation of the
runs of two others. -/
theorem sym_eq_append_run {Q₁ Q₂ Q₃ : Type} [Fintype Q₁] [Fintype Q₂] [Fintype Q₃]
    (δ₁ : Q₁ → Sym → Q₁ × Option Sym × Option Sym) (fin₁ : Q₁ → Option Sym) (q₁ : Q₁)
    (δ₂ : Q₂ → Sym → Q₂ × Option Sym × Option Sym) (fin₂ : Q₂ → Option Sym) (q₂ : Q₂)
    (δ₃ : Q₃ → Sym → Q₃ × Option Sym × Option Sym) (fin₃ : Q₃ → Option Sym) (q₃ : Q₃) :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (fstRun2 δ₁ fin₁ q₁ (dec4 p.2) =
        fstRun2 δ₂ fin₂ q₂ (dec4 p.2) ++ fstRun2 δ₃ fin₃ q₃ (dec4 p.2))) :=
  sym_eq (cpt_fstRun2_comp sym_dec4_snd δ₁ fin₁ q₁)
    (sym_append (cpt_fstRun2_comp sym_dec4_snd δ₂ fin₂ q₂)
      (cpt_fstRun2_comp sym_dec4_snd δ₃ fin₃ q₃))

/-! ## Packaging -/

/-- A polynomial-time verifier with polynomially bounded witnesses puts the language in NP. -/
theorem np_of_verifier (L : Language Bool) (fR : List Bool × List Bool → Bool)
    (q : Polynomial ℕ)
    (hR : ComputableInPolyTime encodePair Computability.encodeBool fR)
    (h : ∀ x : List Bool, x ∈ L ↔
      ∃ w : List Bool, w.length ≤ q.eval x.length ∧ fR (x, w) = true) :
    L ∈ NP :=
  ⟨{p | fR p = true}, q, ⟨fR, fun _ => Iff.rfl, hR⟩, h⟩

/-- The same when the witness is a symbol string, handed to the verifier in bits. -/
theorem np_of_sym_verifier (L : Language Bool) (V : List Bool → List Sym → Bool)
    (q : Polynomial ℕ)
    (hV : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => V p.1 (dec4 p.2)))
    (h : ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Sym, u.length ≤ q.eval x.length ∧ V x u = true) :
    L ∈ NP := by
  refine np_of_verifier L _ (Polynomial.C 4 * q) hV (fun x => ?_)
  rw [h x]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  constructor
  · rintro ⟨u, hu, hv⟩
    refine ⟨enc4 u, ?_, ?_⟩
    · rw [length_enc4]; omega
    · show V x (dec4 (enc4 u)) = true
      rw [dec4_enc4]; exact hv
  · rintro ⟨w, hw, hv⟩
    refine ⟨dec4 w, ?_, hv⟩
    have := length_dec4_le w
    omega

end PEqualNP.MetaComplexity.Helpers.Machines
