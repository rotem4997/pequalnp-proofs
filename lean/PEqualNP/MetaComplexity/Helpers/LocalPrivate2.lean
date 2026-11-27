import PEqualNP.MetaComplexity.Helpers.LocalCore
import PEqualNP.MetaComplexity.Helpers.LocalFormat
import PEqualNP.MetaComplexity.Helpers.Coding
import PEqualNP.MetaComplexity.Helpers.Hardwire

/-!
# Private witnesses, sharpened

Sharpenings of `L-meta-038` (private witnesses in a 1-local reduction of parity to partial
MCSP of fixed format).

* `private_var`: the format may vary with the input. Every odd input has a small function
  consistent with its own table and with the table of no other input of the same format.
  `private_witness` (the statement of `L-meta-038`) is the case of a constant format.
* `count`, `count_explicit`: a 1-local reduction of parity on `n` bits of fixed format needs
  `2 ^ (n - 1)` functions of circuit size at most `s` on `n'` inputs.
* `not_private_two`: the statement of `L-meta-038` with locality 2 in place of 1 is false.
* `local_one_iff`: a map is 1-local exactly when every output position is a function of one
  fixed input position.
* `var_format`: a constant format is not forced. Any local reduction of parity of fixed format
  on at least one bit gives one, of the same locality, whose format depends on the input.

This file does not import `LocalPrivate` (its imports clash with those of `LocalCore`): the
proof of `L-meta-038` is redone here, in the more general form `private_var`.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalPrivate2

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

/-! ## Words of the instance format -/

theorem split_unique : ∀ (s s' : ℕ) (A B : List Bool),
    List.replicate s true ++ false :: A = List.replicate s' true ++ false :: B →
      s = s' ∧ A = B
  | 0, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.nil_append] at h
    exact ⟨rfl, (List.cons.inj h).2⟩
  | 0, s' + 1, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, s' + 1, A, B, h => by
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h
    obtain ⟨h1, h2⟩ := split_unique s s' A B (List.cons.inj h).2
    exact ⟨by rw [h1], h2⟩

theorem encodePartial_injective : ∀ (T T' : List (Option Bool)),
    encodePartial T = encodePartial T' → T = T'
  | [], [], _ => rfl
  | [], o :: T', h => by
    have hl := congrArg List.length h
    rw [LocalFormat.length_encodePartial, LocalFormat.length_encodePartial] at hl
    simp at hl
  | o :: T, [], h => by
    have hl := congrArg List.length h
    rw [LocalFormat.length_encodePartial, LocalFormat.length_encodePartial] at hl
    simp at hl
  | o :: T, o' :: T', h => by
    have ih := encodePartial_injective T T'
    rw [LocalFormat.encodePartial_cons, LocalFormat.encodePartial_cons] at h
    rcases o with _ | b <;> rcases o' with _ | b' <;> simp at h
    · rw [ih h]
    · rw [h.1, ih h.2]

/-- Membership of a word of the instance format, unpacked. -/
theorem mem_iff (s k : ℕ) (T : List (Option Bool)) (hT : T.length = 2 ^ k) :
    List.replicate s true ++ false :: encodePartial T ∈ PartialMCSP ↔
      ∃ f : (Fin k → Bool) → Bool, Consistent k T f ∧ HasCircuitSize k f s := by
  constructor
  · rintro ⟨m, s', T', hw, hlen, f, hc, hs⟩
    obtain ⟨e1, e2⟩ := split_unique s s' _ _ hw
    have e3 := encodePartial_injective _ _ e2
    subst e1
    subst e3
    have e4 : m = k := Nat.pow_right_injective (Nat.le_refl 2) (hlen.symm.trans hT)
    subst e4
    exact ⟨f, hc, hs⟩
  · rintro ⟨f, hc, hs⟩
    exact ⟨k, s, T, rfl, hT, f, hc, hs⟩

/-- The two symbols of entry `k` of a code. -/
theorem enc_pair : ∀ (T : List (Option Bool)) (k : ℕ), k < T.length →
    (encodePartial T)[2 * k]? = some (T.getD k none).isSome ∧
      (encodePartial T)[2 * k + 1]? = some ((T.getD k none).getD false)
  | [], k, h => by simp at h
  | o :: T, 0, _ => by
    rw [LocalFormat.encodePartial_cons]
    cases o <;> simp
  | o :: T, k + 1, h => by
    have ih := enc_pair T k (by simpa using h)
    rw [LocalFormat.encodePartial_cons]
    have e1 : 2 * (k + 1) = 2 * k + 2 := by ring
    have e2 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [e2, e1]
    cases o <;> simpa using ih

/-- The two symbols of entry `k` of an instance. -/
theorem word_pair (s : ℕ) (T : List (Option Bool)) (u : List Bool)
    (h : u = List.replicate s true ++ false :: encodePartial T) (k : ℕ) (hk : k < T.length) :
    u[s + 1 + 2 * k]? = some (T.getD k none).isSome ∧
      u[s + 1 + 2 * k + 1]? = some ((T.getD k none).getD false) := by
  obtain ⟨p1, p2⟩ := enc_pair T k hk
  have a1 := LocalFormat.getElem?_replicate_append_add s (2 * k + 1) (false :: encodePartial T)
  have a2 := LocalFormat.getElem?_replicate_append_add s (2 * k + 1 + 1)
    (false :: encodePartial T)
  rw [List.getElem?_cons_succ] at a1 a2
  have e1 : s + 1 + 2 * k = s + (2 * k + 1) := by ring
  have e2 : s + 1 + 2 * k + 1 = s + (2 * k + 1 + 1) := by ring
  rw [h, e2, e1, a1, a2]
  exact ⟨p1, p2⟩

/-- Flipping one position of an input of odd weight gives an input that is not of odd weight. -/
theorem flip_even {n : ℕ} (x : Fin n → Bool) (i : Fin n) (c : Bool) (hc : c ≠ x i)
    (hx : (Finset.univ.filter fun k : Fin n => x k = true).card % 2 = 1) :
    ¬ (Finset.univ.filter fun k : Fin n => Function.update x i c k = true).card % 2 = 1 := by
  cases hxi : x i with
  | false =>
    have hct : c = true := by cases c <;> simp_all
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i c k = true) =
        insert i (Finset.univ.filter fun k : Fin n => x k = true) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [hct]
      · simp [hk]
    rw [hset, Finset.card_insert_of_notMem (by simp [hxi])]
    omega
  | true =>
    have hcf : c = false := by cases c <;> simp_all
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i c k = true) =
        (Finset.univ.filter fun k : Fin n => x k = true).erase i := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [hcf]
      · simp [hk]
    rw [hset, Finset.card_erase_of_mem (by simp [hxi])]
    omega

/-! ## Certificates of size one, on a set of inputs -/

/-- On the inputs in `A`, every value of `g` is fixed by at most one input position. -/
def Cert1On {n : ℕ} {α : Type} (A : (Fin n → Bool) → Prop) (g : (Fin n → Bool) → α) : Prop :=
  ∀ x : Fin n → Bool, A x → ∃ S : Finset (Fin n), S.card ≤ 1 ∧
    ∀ y : Fin n → Bool, A y → (∀ i ∈ S, y i = x i) → g y = g x

/-- If `g` changes between two points of `A` that differ at position `i` only, the value at one
of them is fixed, on `A`, by position `i`. -/
theorem dep {n : ℕ} {α : Type} (A : (Fin n → Bool) → Prop) (g : (Fin n → Bool) → α)
    (h : Cert1On A g) (x z : Fin n → Bool) (i : Fin n) (hAx : A x) (hAz : A z)
    (hzx : ∀ k : Fin n, k ≠ i → z k = x k) (hne : g z ≠ g x) :
    ∀ u : Fin n → Bool, A u → u i = z i → g u = g z := by
  obtain ⟨S, c, hS⟩ := h z hAz
  by_cases hi : i ∈ S
  · have hall : ∀ k ∈ S, k = i := fun k hk => Finset.card_le_one.1 c k hk i hi
    intro u hAu hu
    apply hS u hAu
    intro k hk
    rw [hall k hk]
    exact hu
  · exfalso
    apply hne
    exact (hS x hAx (fun k hk => (hzx k (fun e => hi (e ▸ hk))).symm)).symm

/-- The entry at a point between `x` and `y`, when defined, is the entry at `x` or at `y`. The
four points of the square spanned by `x` and `y` at position `i` are in `A`. -/
theorem entry_step {n : ℕ} (A : (Fin n → Bool) → Prop) (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1On A fun u => (E u).isSome) (hV : Cert1On A fun u => (E u).getD false)
    (x y z : Fin n → Bool) (i : Fin n) (hAx : A x) (hAy : A y) (hAz : A z)
    (hAu : A (Function.update y i (x i))) (hzx : ∀ k : Fin n, k ≠ i → z k = x k)
    (hzy : z i = y i) (b : Bool) (hz : E z = some b) : E x = some b ∨ E y = some b := by
  have hxz : ∀ k : Fin n, k ≠ i → x k = z k := fun k hk => (hzx k hk).symm
  have hui : Function.update y i (x i) i = x i := Function.update_self i (x i) y
  have huy : ∀ k : Fin n, k ≠ i → y k = Function.update y i (x i) k :=
    fun k hk => (Function.update_of_ne hk (x i) y).symm
  by_cases hd : (E z).isSome = (E x).isSome
  · by_cases hv : (E z).getD false = (E x).getD false
    · left
      rw [hz] at hd hv
      cases hx : E x with
      | none => rw [hx] at hd; simp at hd
      | some c => rw [hx] at hv; simp at hv; rw [hv]
    · have hVy : (E y).getD false = (E z).getD false :=
        dep A (fun u => (E u).getD false) hV x z i hAx hAz hzx hv y hAy hzy.symm
      have hVx : ∀ u : Fin n → Bool, A u → u i = x i → (E u).getD false = (E x).getD false :=
        dep A (fun u => (E u).getD false) hV z x i hAz hAx hxz (fun e => hv e.symm)
      cases hy : E y with
      | some c =>
        right
        rw [hy, hz] at hVy
        simp at hVy
        rw [hVy]
      | none =>
        exfalso
        have hVu := hVx _ hAu hui
        cases hu : E (Function.update y i (x i)) with
        | none =>
          rw [hu] at hVu
          rw [hy] at hVy
          apply hv
          rw [← hVy, ← hVu]
        | some c =>
          have hne : (E y).isSome ≠ (E (Function.update y i (x i))).isSome := by
            rw [hy, hu]; simp
          have h2 := dep A (fun u => (E u).isSome) hD (Function.update y i (x i)) y i hAu hAy
            huy hne z hAz hzy
          rw [hz, hy] at h2
          simp at h2
  · have hDy : (E y).isSome = (E z).isSome :=
      dep A (fun u => (E u).isSome) hD x z i hAx hAz hzx hd y hAy hzy.symm
    have hDx : ∀ u : Fin n → Bool, A u → u i = x i → (E u).isSome = (E x).isSome :=
      dep A (fun u => (E u).isSome) hD z x i hAz hAx hxz (fun e => hd e.symm)
    have hx : E x = none := by
      cases hx : E x with
      | none => rfl
      | some c => rw [hz, hx] at hd; simp at hd
    have hu : E (Function.update y i (x i)) = none := by
      have h := hDx _ hAu hui
      rw [hx] at h
      cases hu : E (Function.update y i (x i)) with
      | none => rfl
      | some c => rw [hu] at h; simp at h
    right
    cases hy : E y with
    | none => rw [hy, hz] at hDy; simp at hDy
    | some c =>
      by_cases hVuy : (E y).getD false = (E (Function.update y i (x i))).getD false
      · by_cases hv : (E z).getD false = (E x).getD false
        · rw [hy, hu] at hVuy
          rw [hz, hx] at hv
          simp at hVuy hv
          rw [hVuy, hv]
        · have hVy : (E y).getD false = (E z).getD false :=
            dep A (fun u => (E u).getD false) hV x z i hAx hAz hzx hv y hAy hzy.symm
          rw [hy, hz] at hVy
          simp at hVy
          rw [hVy]
      · have h2 := dep A (fun u => (E u).getD false) hV (Function.update y i (x i)) y i hAu hAy
          huy hVuy z hAz hzy
        rw [hz, hy] at h2
        simp at h2
        rw [h2]

/-! ## The format at a point between two inputs of the same format -/

/-- Whatever is read off position `j` and is the same at `x` and at `y` is the same at a point
between them. -/
theorem mid {n : ℕ} {α : Type} (w : (Fin n → Bool) → List Bool) (hq : QueryLocal n 1 w)
    (φ : Option Bool → α) (x y z : Fin n → Bool) (i : Fin n)
    (hzx : ∀ k : Fin n, k ≠ i → z k = x k) (hzy : z i = y i) (j : ℕ)
    (h : φ (w x)[j]? = φ (w y)[j]?) : φ (w z)[j]? = φ (w x)[j]? := by
  obtain ⟨S, c, hS⟩ := hq j z
  by_cases hi : i ∈ S
  · have hall : ∀ k ∈ S, k = i := fun k hk => Finset.card_le_one.1 c k hk i hi
    rw [h]
    exact (congrArg φ (hS y (fun k hk => by rw [hall k hk]; exact hzy.symm))).symm
  · exact (congrArg φ (hS x (fun k hk => (hzx k (fun e => hi (e ▸ hk))).symm))).symm

/-- A point between two inputs of one format has that format. -/
theorem fmt_mid {n : ℕ} (w : (Fin n → Bool) → List Bool) (hq : QueryLocal n 1 w)
    (x y z : Fin n → Bool) (i : Fin n) (hzx : ∀ k : Fin n, k ≠ i → z k = x k)
    (hzy : z i = y i) (s k sz kz : ℕ) (Tx Ty Tz : List (Option Bool))
    (hx : w x = List.replicate s true ++ false :: encodePartial Tx) (hTx : Tx.length = 2 ^ k)
    (hy : w y = List.replicate s true ++ false :: encodePartial Ty) (hTy : Ty.length = 2 ^ k)
    (hz : w z = List.replicate sz true ++ false :: encodePartial Tz)
    (hTz : Tz.length = 2 ^ kz) : sz = s ∧ kz = k := by
  have key : ∀ j : ℕ, (w x)[j]? = (w y)[j]? → (w z)[j]? = (w x)[j]? :=
    fun j h => mid w hq id x y z i hzx hzy j h
  have keyS : ∀ j : ℕ, ((w x)[j]? = none) = ((w y)[j]? = none) →
      ((w z)[j]? = none) = ((w x)[j]? = none) :=
    fun j h => mid w hq (fun o : Option Bool => o = none) x y z i hzx hzy j h
  have hlx := LocalFormat.length_of_eq s Tx _ hx
  have hly := LocalFormat.length_of_eq s Ty _ hy
  have hlz := LocalFormat.length_of_eq sz Tz _ hz
  have sep : ∀ (r : ℕ) (l : List Bool),
      (List.replicate r true ++ false :: l)[r]? = some false := by
    intro r l
    simp
  have hs : sz = s := by
    rcases Nat.lt_trichotomy sz s with h | h | h
    · exfalso
      have h1 : (w x)[sz]? = some true := by
        rw [hx]; exact LocalFormat.getElem?_replicate_append_lt s sz _ h
      have h1y : (w y)[sz]? = some true := by
        rw [hy]; exact LocalFormat.getElem?_replicate_append_lt s sz _ h
      have h2 : (w z)[sz]? = some false := by rw [hz]; exact sep sz _
      have h3 := key sz (h1.trans h1y.symm)
      rw [h1, h2] at h3
      simp at h3
    · exact h
    · exfalso
      have h1 : (w x)[s]? = some false := by rw [hx]; exact sep s _
      have h1y : (w y)[s]? = some false := by rw [hy]; exact sep s _
      have h2 : (w z)[s]? = some true := by
        rw [hz]; exact LocalFormat.getElem?_replicate_append_lt sz s _ h
      have h3 := key s (h1.trans h1y.symm)
      rw [h1, h2] at h3
      simp at h3
  subst hs
  refine ⟨rfl, ?_⟩
  have hxy : (w y).length = (w x).length := by rw [hly, hlx, hTy, hTx]
  have a1 : (w z)[(w x).length]? = (w x)[(w x).length]? :=
    key _ (by rw [List.getElem?_eq_none (le_refl _), List.getElem?_eq_none (le_of_eq hxy)])
  rw [List.getElem?_eq_none (le_refl _), List.getElem?_eq_none_iff] at a1
  have a2 : ((w z)[(w x).length - 1]? = none) = ((w x)[(w x).length - 1]? = none) :=
    keyS _ (propext (by
      rw [List.getElem?_eq_none_iff, List.getElem?_eq_none_iff]
      omega))
  rw [List.getElem?_eq_none_iff, List.getElem?_eq_none_iff] at a2
  have a3 : ¬ (w z).length ≤ (w x).length - 1 := by
    rw [a2]
    omega
  have hpow : 2 ^ kz = 2 ^ k := by omega
  exact Nat.pow_right_injective (Nat.le_refl 2) hpow

/-! ## Private witnesses, the format free to vary -/

/-- Private witnesses in a 1-local reduction of parity to partial MCSP whose format may depend
on the input: every odd input has a function of circuit size within its own bound, consistent
with its own table and with the table of no other input of the same format. -/
theorem private_var (n : ℕ) (w : (Fin n → Bool) → List Bool) (s n' : (Fin n → Bool) → ℕ)
    (T : (Fin n → Bool) → List (Option Bool)) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate (s x) true ++ false :: encodePartial (T x) ∧
        (T x).length = 2 ^ n' x)
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) (hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1) :
    ∃ f : (Fin (n' x) → Bool) → Bool, Consistent (n' x) (T x) f ∧
      HasCircuitSize (n' x) f (s x) ∧
      ∀ y : Fin n → Bool, s y = s x → n' y = n' x → Consistent (n' x) (T y) f → y = x := by
  have hm := (hred x).1 hx
  rw [(hfmt x).1, mem_iff _ _ _ (hfmt x).2] at hm
  obtain ⟨f, hc, hs⟩ := hm
  refine ⟨f, hc, hs, fun y hsy hny hy => ?_⟩
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hAz : s (Function.update x i (y i)) = s x ∧ n' (Function.update x i (y i)) = n' x :=
    fmt_mid w hq x y _ i (fun k hk' => Function.update_of_ne hk' (y i) x)
      (Function.update_self i (y i) x) (s x) (n' x) _ _ (T x) (T y) _ (hfmt x).1 (hfmt x).2
      (by rw [← hsy]; exact (hfmt y).1) (by rw [← hny]; exact (hfmt y).2) (hfmt _).1 (hfmt _).2
  have hAu : s (Function.update y i (x i)) = s x ∧ n' (Function.update y i (x i)) = n' x :=
    fmt_mid w hq y x _ i (fun k hk' => Function.update_of_ne hk' (x i) y)
      (Function.update_self i (x i) y) (s x) (n' x) _ _ (T y) (T x) _
      (by rw [← hsy]; exact (hfmt y).1) (by rw [← hny]; exact (hfmt y).2) (hfmt x).1 (hfmt x).2
      (hfmt _).1 (hfmt _).2
  have hword : ∀ v : Fin n → Bool, (s v = s x ∧ n' v = n' x) →
      w v = List.replicate (s x) true ++ false :: encodePartial (T v) ∧
        (T v).length = 2 ^ n' x := by
    intro v hv
    rw [← hv.1, ← hv.2]
    exact hfmt v
  apply flip_even x i (y i) hi hx
  rw [hred, (hword _ hAz).1, mem_iff _ _ _ (hword _ hAz).2]
  refine ⟨f, ?_, hs⟩
  intro e b he
  by_cases hk : tableIndex e < 2 ^ n' x
  · have hD : Cert1On (fun v : Fin n → Bool => s v = s x ∧ n' v = n' x)
        fun u : Fin n → Bool => ((T u).getD (tableIndex e) none).isSome := by
      intro u hu
      obtain ⟨S, c, hS⟩ := hq (s x + 1 + 2 * tableIndex e) u
      refine ⟨S, c, fun v hv hag => ?_⟩
      have h := hS v hag
      rw [(word_pair (s x) (T v) (w v) (hword v hv).1 _ (by rw [(hword v hv).2]; exact hk)).1,
        (word_pair (s x) (T u) (w u) (hword u hu).1 _ (by rw [(hword u hu).2]; exact hk)).1]
        at h
      exact Option.some.inj h
    have hV : Cert1On (fun v : Fin n → Bool => s v = s x ∧ n' v = n' x)
        fun u : Fin n → Bool => ((T u).getD (tableIndex e) none).getD false := by
      intro u hu
      obtain ⟨S, c, hS⟩ := hq (s x + 1 + 2 * tableIndex e + 1) u
      refine ⟨S, c, fun v hv hag => ?_⟩
      have h := hS v hag
      rw [(word_pair (s x) (T v) (w v) (hword v hv).1 _ (by rw [(hword v hv).2]; exact hk)).2,
        (word_pair (s x) (T u) (w u) (hword u hu).1 _ (by rw [(hword u hu).2]; exact hk)).2]
        at h
      exact Option.some.inj h
    rcases entry_step (fun v : Fin n → Bool => s v = s x ∧ n' v = n' x)
      (fun u => (T u).getD (tableIndex e) none) hD hV x y
      (Function.update x i (y i)) i ⟨rfl, rfl⟩ ⟨hsy, hny⟩ hAz hAu
      (fun k hk' => Function.update_of_ne hk' (y i) x)
      (Function.update_self i (y i) x) b he with h | h
    · exact hc e b h
    · exact hy e b h
  · exfalso
    have hl : (T (Function.update x i (y i))).length ≤ tableIndex e := by
      rw [(hword _ hAz).2]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at he
    simp at he

/-- Private witnesses: the statement of `L-meta-038`, reproved as the case of `private_var`
with a constant format. -/
theorem private_witness (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) (hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧ HasCircuitSize n' f s ∧
      ∀ y : Fin n → Bool, Consistent n' (T y) f → y = x := by
  obtain ⟨f, hc, hs, hp⟩ := private_var n w (fun _ => s) (fun _ => n') T hq hfmt hred x hx
  exact ⟨f, hc, hs, fun y hy => hp y rfl rfl hy⟩

/-! ## The count -/

/-- A 1-local reduction of parity on `n` bits to partial MCSP of fixed format needs `2 ^ (n - 1)`
functions of circuit size at most `s` on `n'` inputs: the private witnesses of the odd inputs
are distinct. -/
theorem count (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hn : 0 < n) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) :
    2 ^ (n - 1) ≤ {f : (Fin n' → Bool) → Bool | HasCircuitSize n' f s}.ncard := by
  have hpw := private_witness n n' s w T hq hfmt hred
  have hfin : {f : (Fin n' → Bool) → Bool | HasCircuitSize n' f s}.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hodd := Coding.two_pow_le_odd hn
  have hcard : (Finset.univ.filter fun x : Fin n → Bool =>
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1).card
        ≤ hfin.toFinset.card := by
    refine Finset.card_le_card_of_injOn
      (fun x => if h : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1
        then Classical.choose (hpw x h) else fun _ => false) ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      simp only [hx', ↓reduceDIte]
      exact Finset.mem_coe.2
        ((Set.Finite.mem_toFinset _).2 (Classical.choose_spec (hpw x hx')).2.1)
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      simp only [hx', hy', ↓reduceDIte] at hxy
      exact (Classical.choose_spec (hpw y hy')).2.2 x
        (by rw [← hxy]; exact (Classical.choose_spec (hpw x hx')).1)
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm]
  omega

/-- The count, with the checked bound on the number of functions of small circuit size. -/
theorem count_explicit (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hn : 0 < n) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) :
    2 ^ (n - 1) ≤ (s + 1) * ((3 * ((n' + s + 2) * (n' + s + 2))) ^ s * (n' + s + 1)) :=
  (count n n' s w T hn hq hfmt hred).trans (LocalCore.count_le n' s)

/-! ## Locality two: private witnesses fail -/

/-- A member of partial MCSP: bound `0`, no variable, the table `[some false]`. -/
theorem mem_some_false :
    List.replicate 0 true ++ false :: encodePartial [some false] ∈ PartialMCSP := by
  rw [mem_iff 0 0 [some false] rfl]
  refine ⟨fun _ => false, ?_, ⟨[], 0⟩, ?_, ?_, ?_⟩
  · intro e b h
    have h0 : tableIndex e = 0 := by simp [tableIndex]
    rw [h0] at h
    simpa using h
  · intro g hg
    simp at hg
  · simp [Circuit.size]
  · intro x
    simp [Circuit.eval, Circuit.wires]

/-- A non-member of the same format: bound `0`, no variable, the table `[some true]`. A circuit
without gates on no inputs evaluates to `false`. -/
theorem not_mem_some_true :
    List.replicate 0 true ++ false :: encodePartial [some true] ∉ PartialMCSP := by
  rw [mem_iff 0 0 [some true] rfl]
  rintro ⟨f, hc, C, -, hsz, hev⟩
  have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hsz)
  have h1 : f (fun _ => false) = true := hc _ true (by simp [tableIndex])
  have h2 := hev (fun _ => false)
  rw [h1] at h2
  simp [Circuit.eval, Circuit.wires, hg] at h2

/-- The statement of `L-meta-038` with locality 2 in place of locality 1 is false. On two bits,
send the odd inputs to one member and the even inputs to one non-member of the same format:
the two odd inputs share their table, so no witness is private. -/
theorem not_private_two :
    ¬ ∀ (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
      (T : (Fin n → Bool) → List (Option Bool)),
      QueryLocal n 2 w →
      (∀ x : Fin n → Bool,
        w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n') →
      (∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) →
      ∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 →
        ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧ HasCircuitSize n' f s ∧
          ∀ y : Fin n → Bool, Consistent n' (T y) f → y = x := by
  intro H
  have hex : ∃ T : (Fin 2 → Bool) → List (Option Bool),
      (∀ x : Fin 2 → Bool, (Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1 →
        T x = [some false]) ∧
      (∀ x : Fin 2 → Bool, ¬ (Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1 →
        T x = [some true]) :=
    ⟨fun x => [some (!decide ((Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1))],
      fun x h => by simp [h], fun x h => by simp [h]⟩
  obtain ⟨T, hT1, hT0⟩ := hex
  have hq : QueryLocal 2 2
      (fun x : Fin 2 → Bool => List.replicate 0 true ++ false :: encodePartial (T x)) := by
    intro j x
    refine ⟨Finset.univ, by simp, fun y hy => ?_⟩
    have e : y = x := funext fun i => hy i (Finset.mem_univ i)
    rw [e]
  have hlen : ∀ x : Fin 2 → Bool, (T x).length = 2 ^ 0 := by
    intro x
    by_cases h : (Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1
    · rw [hT1 x h]; rfl
    · rw [hT0 x h]; rfl
  have hred : ∀ x : Fin 2 → Bool,
      (Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1 ↔
        List.replicate 0 true ++ false :: encodePartial (T x) ∈ PartialMCSP := by
    intro x
    by_cases h : (Finset.univ.filter fun i : Fin 2 => x i = true).card % 2 = 1
    · rw [hT1 x h]
      exact ⟨fun _ => mem_some_false, fun _ => h⟩
    · rw [hT0 x h]
      exact ⟨fun h' => absurd h' h, fun h' => absurd h' not_mem_some_true⟩
  have o0 : (Finset.univ.filter fun i : Fin 2 =>
      (fun i : Fin 2 => decide (i = 0)) i = true).card % 2 = 1 := by decide
  have o1 : (Finset.univ.filter fun i : Fin 2 =>
      (fun i : Fin 2 => decide (i = 1)) i = true).card % 2 = 1 := by decide
  obtain ⟨f, hc, -, hp⟩ := H 2 0 0 _ T hq (fun x => ⟨rfl, hlen x⟩) hred
    (fun i : Fin 2 => decide (i = 0)) o0
  rw [hT1 _ o0] at hc
  have hy := hp (fun i : Fin 2 => decide (i = 1)) (by rw [hT1 _ o1]; exact hc)
  have h0 := congrFun hy 0
  simp at h0

/-! ## Locality one is one input position per output position -/

/-- A function on the cube each value of which is fixed by at most one position is a function
of one position. -/
theorem dictator_gen {n : ℕ} {α : Type} (g : (Fin n → Bool) → α)
    (h : ∀ x : Fin n → Bool, ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → g y = g x) :
    ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → g x = g y := by
  by_cases hconst : ∀ x y : Fin n → Bool, g x = g y
  · exact ⟨∅, by simp, fun x y _ => hconst x y⟩
  · simp only [not_forall] at hconst
    obtain ⟨x, y, hxy⟩ := hconst
    obtain ⟨Sx, cx, hSx⟩ := h x
    obtain ⟨Sy, cy, hSy⟩ := h y
    have hxne : Sx.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      subst he
      exact hxy (hSx y (by simp)).symm
    have hyne : Sy.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      subst he
      exact hxy (hSy x (by simp))
    obtain ⟨a, ha⟩ := hxne
    obtain ⟨b, hb⟩ := hyne
    have hax : ∀ k ∈ Sx, k = a := fun k hk => Finset.card_le_one.1 cx k hk a ha
    have hby : ∀ k ∈ Sy, k = b := fun k hk => Finset.card_le_one.1 cy k hk b hb
    have hgx : ∀ u : Fin n → Bool, u a = x a → g u = g x :=
      fun u hu => hSx u (fun k hk => by rw [hax k hk]; exact hu)
    have hgy : ∀ u : Fin n → Bool, u b = y b → g u = g y :=
      fun u hu => hSy u (fun k hk => by rw [hby k hk]; exact hu)
    have hab : a = b := by
      by_contra hne
      apply hxy
      rw [← hgx (Function.update x b (y b)) (Function.update_of_ne hne _ _),
        hgy (Function.update x b (y b)) (Function.update_self _ _ _)]
    subst hab
    have hval : x a ≠ y a := fun e => hxy (hgy x e)
    refine ⟨{a}, by simp, fun u v huv => ?_⟩
    have huv' : u a = v a := huv a (by simp)
    by_cases hu : u a = x a
    · rw [hgx u hu, hgx v (huv'.symm.trans hu)]
    · have hu' : u a = y a := by
        revert hu hval
        cases u a <;> cases x a <;> cases y a <;> simp
      rw [hgy u hu', hgy v (huv'.symm.trans hu')]

/-- A map is 1-local exactly when every output position is a function of one fixed input
position (or of none): the certificate does not depend on the input. -/
theorem local_one_iff (n : ℕ) (w : (Fin n → Bool) → List Bool) :
    QueryLocal n 1 w ↔ ∀ j : ℕ, ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → (w x)[j]? = (w y)[j]? := by
  constructor
  · intro hq j
    exact dictator_gen (fun u => (w u)[j]?) (fun x => hq j x)
  · intro h j x
    obtain ⟨S, c, hS⟩ := h j
    exact ⟨S, c, fun y hy => hS y x hy⟩

/-! ## A dummy variable: the same instance in another format -/

theorem tableIndex_snoc (K : ℕ) (y : Fin K → Bool) (b : Bool) :
    tableIndex (Fin.snoc (α := fun _ => Bool) y b : Fin (K + 1) → Bool)
      = tableIndex y + (if b = true then 2 ^ K else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

theorem tableIndex_lt : ∀ (K : ℕ) (x : Fin K → Bool), tableIndex x < 2 ^ K
  | 0, x => by simp [tableIndex]
  | K + 1, x => by
    have h := tableIndex_snoc K (Fin.init x) (x (Fin.last K))
    rw [Fin.snoc_init_self] at h
    have ih := tableIndex_lt K (Fin.init x)
    rw [h, pow_succ]
    split_ifs <;> omega

theorem enc_replicate_none : ∀ m : ℕ,
    encodePartial (List.replicate m none) = List.replicate (2 * m) false
  | 0 => by simp [encodePartial]
  | m + 1 => by
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [List.replicate_succ, LocalFormat.encodePartial_cons, enc_replicate_none m, e,
      List.replicate_succ, List.replicate_succ]
    rfl

theorem enc_append (T T' : List (Option Bool)) :
    encodePartial (T ++ T') = encodePartial T ++ encodePartial T' := by
  unfold encodePartial
  rw [List.flatMap_append]

theorem ofFn_snoc (K : ℕ) (y : Fin K → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (α := fun _ => Bool) y b : Fin (K + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- The renumbering of wires when an input is added after the first `K` inputs. -/
def sh (K i : ℕ) : ℕ := if i < K then i else i + 1

/-- The gate with its wires renumbered. -/
def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh K)⟩

theorem getD_sh (u t : List Bool) (b : Bool) (i : ℕ) :
    (u ++ b :: t).getD (sh u.length i) false = (u ++ t).getD i false := by
  unfold sh
  split_ifs with h
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · have e : i + 1 - u.length = (i - u.length) + 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), e,
      List.getElem?_cons_succ]

theorem wires_sh (K : ℕ) (b : Bool) (gs : List Gate) : ∀ u t : List Bool, u.length = K →
    ∃ t' : List Bool, wiresFrom gs (u ++ t) = u ++ t' ∧
      wiresFrom (gs.map (shGate K)) (u ++ b :: t) = u ++ b :: t' := by
  induction gs with
  | nil => intro u t _; exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    intro u t hu
    have hval :
        (shGate K g).op.eval ((shGate K g).inputs.map fun i => (u ++ b :: t).getD i false)
          = g.op.eval (g.inputs.map fun i => (u ++ t).getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      subst hu
      exact getD_sh u t b i
    obtain ⟨t', h1, h2⟩ :=
      ih u (t ++ [g.op.eval (g.inputs.map fun i => (u ++ t).getD i false)]) hu
    refine ⟨t', ?_, ?_⟩
    · rw [← List.append_assoc] at h1
      exact h1
    · have h3 : wiresFrom ((g :: gs).map (shGate K)) (u ++ b :: t)
          = wiresFrom (gs.map (shGate K)) ((u ++ b :: t) ++
            [(shGate K g).op.eval
              ((shGate K g).inputs.map fun i => (u ++ b :: t).getD i false)]) :=
        rfl
      rw [h3, hval, List.append_assoc, List.cons_append]
      exact h2

/-- A function that ignores an added last input has the circuit size of the function on the
other inputs. -/
theorem add_dummy (K s : ℕ) (g : (Fin K → Bool) → Bool) (h : HasCircuitSize K g s) :
    HasCircuitSize (K + 1) (fun x : Fin (K + 1) → Bool => g (Fin.init x)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  refine ⟨⟨C.gates.map (shGate K), sh K C.output⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
    refine ⟨(ok g0 hg0).1, ?_⟩
    simp only [shGate, List.length_map]
    exact (ok g0 hg0).2
  · simpa [Circuit.size] using hsz
  · intro x
    have hx : List.ofFn x = List.ofFn (Fin.init x) ++ [x (Fin.last K)] := by
      have h := ofFn_snoc K (Fin.init x) (x (Fin.last K))
      rw [Fin.snoc_init_self] at h
      exact h
    have hl : (List.ofFn (Fin.init x)).length = K := by simp
    obtain ⟨t', h1, h2⟩ := wires_sh K (x (Fin.last K)) C.gates (List.ofFn (Fin.init x)) [] hl
    rw [List.append_nil] at h1
    have h3 := getD_sh (List.ofFn (Fin.init x)) t' (x (Fin.last K)) C.output
    rw [hl] at h3
    show _ = g (Fin.init x)
    rw [← hev (Fin.init x)]
    show (wiresFrom (C.gates.map (shGate K)) (List.ofFn x)).getD (sh K C.output) false
      = (wiresFrom C.gates (List.ofFn (Fin.init x))).getD C.output false
    rw [hx, h2, h1]
    exact h3

/-- Fixing the last input to `false` does not increase the circuit size. -/
theorem fix_false (K s : ℕ) (f : (Fin (K + 1) → Bool) → Bool) (h : HasCircuitSize (K + 1) f s) :
    HasCircuitSize K (fun y : Fin K → Bool => f (Fin.snoc y false)) s := by
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · subst h0
    obtain ⟨C, ok, hsz, hev⟩ := h
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hsz)
    refine ⟨C, ok, hsz, fun y => ?_⟩
    show C.eval (List.ofFn y) = f (Fin.snoc y false)
    rw [← hev (Fin.snoc y false), ofFn_snoc]
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl_nil]
    by_cases hj : C.output = (List.ofFn y).length
    · rw [hj, getD_snoc_eq, List.getD_eq_default _ _ (le_refl _)]
    · rw [getD_snoc_ne _ _ _ _ hj]
  · have h1 := fix_last K f false s h
    rw [max_eq_left hpos] at h1
    exact h1

/-- Adding a variable on which the table is undefined changes neither the bound nor
membership. -/
theorem pad_iff (s K : ℕ) (T : List (Option Bool)) (hT : T.length = 2 ^ K) :
    (∃ g : (Fin K → Bool) → Bool, Consistent K T g ∧ HasCircuitSize K g s) ↔
      ∃ f : (Fin (K + 1) → Bool) → Bool,
        Consistent (K + 1) (T ++ List.replicate (2 ^ K) none) f ∧ HasCircuitSize (K + 1) f s := by
  constructor
  · rintro ⟨g, hc, hs⟩
    refine ⟨fun x => g (Fin.init x), ?_, add_dummy K s g hs⟩
    intro x b h
    have hx := tableIndex_snoc K (Fin.init x) (x (Fin.last K))
    rw [Fin.snoc_init_self] at hx
    have hlt := tableIndex_lt K (Fin.init x)
    rw [hx] at h
    cases hl : x (Fin.last K) with
    | false =>
      rw [hl] at h
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at h
      rw [List.getD_append _ _ _ _ (by rw [hT]; exact hlt)] at h
      exact hc _ b h
    | true =>
      exfalso
      rw [hl] at h
      simp only [ite_true] at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hT]; omega),
        List.getElem?_replicate] at h
      split_ifs at h <;> simp at h
  · rintro ⟨f, hc, hs⟩
    refine ⟨fun y => f (Fin.snoc y false), ?_, fix_false K s f hs⟩
    intro y b h
    apply hc
    rw [tableIndex_snoc]
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    rw [List.getD_append _ _ _ _ (by rw [hT]; exact tableIndex_lt K y)]
    exact h

/-- The same, for words. -/
theorem pad_mem_iff (s K : ℕ) (T : List (Option Bool)) (hT : T.length = 2 ^ K) :
    List.replicate s true ++ false :: encodePartial T ∈ PartialMCSP ↔
      List.replicate s true ++ false :: encodePartial (T ++ List.replicate (2 ^ K) none)
        ∈ PartialMCSP := by
  have hT' : (T ++ List.replicate (2 ^ K) none).length = 2 ^ (K + 1) := by
    rw [List.length_append, List.length_replicate, hT, pow_succ]
    ring
  rw [mem_iff s K T hT, mem_iff s (K + 1) _ hT']
  exact pad_iff s K T hT

/-! ## A constant format is not forced -/

/-- From a `q`-local reduction of parity on `n ≥ 1` bits to partial MCSP of fixed format, a
`q`-local reduction whose format depends on the input: the inputs with first bit `true` get a
dummy variable. Every output is still an instance, and the number of variables is not
constant. -/
theorem var_format (n q n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hn : 0 < n) (hq1 : 0 < q)
    (hq : QueryLocal n q w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP) :
    ∃ (w2 : (Fin n → Bool) → List Bool) (s2 n2 : (Fin n → Bool) → ℕ)
      (T2 : (Fin n → Bool) → List (Option Bool)),
      QueryLocal n q w2 ∧
      (∀ x : Fin n → Bool,
        w2 x = List.replicate (s2 x) true ++ false :: encodePartial (T2 x) ∧
          (T2 x).length = 2 ^ n2 x) ∧
      (∀ x : Fin n → Bool,
        (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w2 x ∈ PartialMCSP) ∧
      ∃ x y : Fin n → Bool, n2 x ≠ n2 y := by
  have hlen : ∀ y : Fin n → Bool, (w y).length = s + (2 * 2 ^ n' + 1) := by
    intro y
    rw [LocalFormat.length_of_eq s (T y) _ (hfmt y).1, (hfmt y).2]
  have hpad : ∀ y : Fin n → Bool,
      List.replicate s true ++ false :: encodePartial (T y ++ List.replicate (2 ^ n') none)
        = w y ++ List.replicate (2 * 2 ^ n') false := by
    intro y
    rw [enc_append, enc_replicate_none, (hfmt y).1, List.append_assoc, List.cons_append]
  refine ⟨fun x => List.replicate s true ++ false ::
      encodePartial (if x ⟨0, hn⟩ = true then T x ++ List.replicate (2 ^ n') none else T x),
    fun _ => s, fun x => if x ⟨0, hn⟩ = true then n' + 1 else n',
    fun x => if x ⟨0, hn⟩ = true then T x ++ List.replicate (2 ^ n') none else T x,
    ?_, ?_, ?_, ?_⟩
  · intro j x
    have key : ∀ v : Fin n → Bool, j < s + (2 * 2 ^ n' + 1) →
        (List.replicate s true ++ false :: encodePartial
          (if v ⟨0, hn⟩ = true then T v ++ List.replicate (2 ^ n') none else T v))[j]?
          = (w v)[j]? := by
      intro v hj
      by_cases hv : v ⟨0, hn⟩ = true
      · simp only [hv, ↓reduceIte]
        rw [hpad v, List.getElem?_append_left (by rw [hlen v]; exact hj)]
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        rw [← (hfmt v).1]
    by_cases hj : j < s + (2 * 2 ^ n' + 1)
    · obtain ⟨S, c, hS⟩ := hq j x
      refine ⟨S, c, fun y hy => ?_⟩
      show (List.replicate s true ++ false :: encodePartial
          (if y ⟨0, hn⟩ = true then T y ++ List.replicate (2 ^ n') none else T y))[j]?
        = (List.replicate s true ++ false :: encodePartial
          (if x ⟨0, hn⟩ = true then T x ++ List.replicate (2 ^ n') none else T x))[j]?
      rw [key y hj, key x hj]
      exact hS y hy
    · refine ⟨{⟨0, hn⟩}, by rw [Finset.card_singleton]; exact hq1, fun y hy => ?_⟩
      have hy0 : y ⟨0, hn⟩ = x ⟨0, hn⟩ := hy _ (by simp)
      show (List.replicate s true ++ false :: encodePartial
          (if y ⟨0, hn⟩ = true then T y ++ List.replicate (2 ^ n') none else T y))[j]?
        = (List.replicate s true ++ false :: encodePartial
          (if x ⟨0, hn⟩ = true then T x ++ List.replicate (2 ^ n') none else T x))[j]?
      rw [hy0]
      by_cases hv : x ⟨0, hn⟩ = true
      · simp only [hv, ↓reduceIte]
        rw [hpad y, hpad x,
          List.getElem?_append_right (by rw [hlen y]; omega),
          List.getElem?_append_right (by rw [hlen x]; omega), hlen y, hlen x]
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        rw [← (hfmt y).1, ← (hfmt x).1,
          List.getElem?_eq_none (by rw [hlen y]; omega),
          List.getElem?_eq_none (by rw [hlen x]; omega)]
  · intro x
    refine ⟨rfl, ?_⟩
    show (if x ⟨0, hn⟩ = true then T x ++ List.replicate (2 ^ n') none else T x).length
      = 2 ^ (if x ⟨0, hn⟩ = true then n' + 1 else n')
    by_cases hv : x ⟨0, hn⟩ = true
    · simp only [hv, ↓reduceIte]
      rw [List.length_append, List.length_replicate, (hfmt x).2, pow_succ]
      ring
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      exact (hfmt x).2
  · intro x
    show _ ↔ List.replicate s true ++ false :: encodePartial
      (if x ⟨0, hn⟩ = true then T x ++ List.replicate (2 ^ n') none else T x) ∈ PartialMCSP
    rw [hred x]
    by_cases hv : x ⟨0, hn⟩ = true
    · simp only [hv, ↓reduceIte]
      rw [(hfmt x).1]
      exact pad_mem_iff s n' (T x) (hfmt x).2
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      rw [← (hfmt x).1]
  · refine ⟨fun _ => false, fun _ => true, ?_⟩
    simp

end PEqualNP.MetaComplexity.Helpers.LocalPrivate2
