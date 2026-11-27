import PEqualNP.MetaComplexity.Helpers.HittingSet
import PEqualNP.MetaComplexity.Helpers.Columns
import PEqualNP.MetaComplexity.Helpers.LocalFormat

/-!
# A local reduction of parity to partial MCSP

Helper for `L-meta-035`. With `m + 1` blocks of at most `q` input bits each and `y i` the parity
of block `i`, the reduction writes a hitting set instance on `2 * (m + 1)` points. The point
`pt m i b` reads "the parity of `y 0, ..., y i` is `b`". The family `fam m y` has

* the pair `{pt m i false, pt m i true}` for every `i ≤ m`;
* the singleton `{pt m m true}`;
* the singleton `{pt m 0 (y 0)}`;
* for `i < m` and a bit `b`, the pair `{pt m i b, pt m (i + 1) (xor (!b) (y (i + 1)))}`.

A hitting set with at most `m + 1` points takes one point of each pair of the first kind, so it
is a string `p`; the other sets say `p 0 = y 0`, `p (i + 1) = xor (p i) (y (i + 1))` and
`p m = true` (`gadget`). Whether a set is in the family is read off ONE bit of `y`, the one of
index `idx S`, by the definition of `fam`: this is what makes the map local.

The partial table is `false` at the zero input, `true` at the indicator of every set of the
family and undefined elsewhere; with the bound `m`, `L-meta-015` (`hitting_iff`) turns
membership in partial MCSP into the existence of a hitting set with `m + 1` points.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalConstruct

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-! ## The points and the family -/

/-- The point `(i, b)` of the universe of `2 * (m + 1)` points; meant for `i ≤ m`. -/
def pt (m i : ℕ) (b : Bool) : Fin (2 * (m + 1)) :=
  ⟨(2 * i + b.toNat) % (2 * (m + 1)), Nat.mod_lt _ (by omega)⟩

theorem pt_val (m i : ℕ) (b : Bool) (hi : i ≤ m) : ((pt m i b : Fin (2 * (m + 1))) : ℕ)
    = 2 * i + b.toNat := by
  show (2 * i + b.toNat) % (2 * (m + 1)) = 2 * i + b.toNat
  apply Nat.mod_eq_of_lt
  cases b
  · simp
    omega
  · simp
    omega

theorem pt_inj (m i i' : ℕ) (b b' : Bool) (hi : i ≤ m) (hi' : i' ≤ m)
    (h : pt m i b = pt m i' b') : i = i' ∧ b = b' := by
  have hv := congrArg (fun a : Fin (2 * (m + 1)) => (a : ℕ)) h
  simp only [pt_val m i b hi, pt_val m i' b' hi'] at hv
  cases b <;> cases b' <;> simp at hv ⊢ <;> omega

theorem pt_half (m i : ℕ) (b : Bool) (hi : i ≤ m) :
    ((pt m i b : Fin (2 * (m + 1))) : ℕ) / 2 = i := by
  rw [pt_val m i b hi]
  cases b <;> simp
  omega

/-- The index of the bit of `y` that decides whether `S` is in the family: half the largest
point of `S`. -/
def idx {N : ℕ} (S : Finset (Fin N)) : ℕ := (S.sup fun a : Fin N => (a : ℕ)) / 2

/-- "The set `S` is in the family", as a condition on the single bit `c` of `y` it reads. -/
def P (m : ℕ) (S : Finset (Fin (2 * (m + 1)))) (c : Bool) : Prop :=
  (∃ i : ℕ, i ≤ m ∧ S = {pt m i false, pt m i true}) ∨ S = {pt m m true} ∨ S = {pt m 0 c} ∨
    ∃ (i : ℕ) (b : Bool), i < m ∧ S = {pt m i b, pt m (i + 1) (xor (!b) c)}

theorem P_nonempty (m : ℕ) (S : Finset (Fin (2 * (m + 1)))) (c : Bool) (h : P m S c) :
    S.Nonempty := by
  rcases h with ⟨i, _, rfl⟩ | rfl | rfl | ⟨i, b, _, rfl⟩ <;> simp

/-- The family of sets of the hitting set instance for the bits `y`. -/
noncomputable def fam (m : ℕ) (y : ℕ → Bool) : Finset (Finset (Fin (2 * (m + 1)))) :=
  letI : DecidablePred fun S : Finset (Fin (2 * (m + 1))) => P m S (y (idx S)) :=
    Classical.decPred _
  Finset.univ.filter fun S : Finset (Fin (2 * (m + 1))) => P m S (y (idx S))

theorem mem_fam (m : ℕ) (y : ℕ → Bool) (S : Finset (Fin (2 * (m + 1)))) :
    S ∈ fam m y ↔ P m S (y (idx S)) := by
  unfold fam
  simp

theorem idx_single (m : ℕ) (c : Bool) : idx ({pt m 0 c} : Finset (Fin (2 * (m + 1)))) = 0 := by
  unfold idx
  rw [Finset.sup_singleton, pt_val m 0 c (Nat.zero_le m)]
  cases c <;> simp

theorem idx_edge (m i : ℕ) (b d : Bool) (hi : i < m) :
    idx ({pt m i b, pt m (i + 1) d} : Finset (Fin (2 * (m + 1)))) = i + 1 := by
  unfold idx
  rw [Finset.sup_insert, Finset.sup_singleton, pt_val m i b (by omega),
    pt_val m (i + 1) d (by omega)]
  have hle : 2 * i + b.toNat ≤ 2 * (i + 1) + d.toNat := by
    cases b <;> simp <;> omega
  rw [sup_eq_right.2 hle]
  cases d <;> simp
  omega

/-- The parity of `y 0, ..., y k`. -/
def par (y : ℕ → Bool) : ℕ → Bool
  | 0 => y 0
  | k + 1 => xor (par y k) (y (k + 1))

theorem mem_of_hit {α : Type} [DecidableEq α] (H : Finset α) (a : α)
    (h : (H ∩ {a}).Nonempty) : a ∈ H := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hc
  rw [Finset.mem_singleton] at h2
  rw [← h2]
  exact h1

theorem mem_of_hit_pair {α : Type} [DecidableEq α] (H : Finset α) (a b : α)
    (h : (H ∩ {a, b}).Nonempty) : a ∈ H ∨ b ∈ H := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hc
  rw [Finset.mem_insert, Finset.mem_singleton] at h2
  rcases h2 with h2 | h2
  · left; rw [← h2]; exact h1
  · right; rw [← h2]; exact h1

/-- The gadget: the family has a hitting set with at most `m + 1` points exactly when the
parity of `y 0, ..., y m` is odd. -/
theorem gadget (m : ℕ) (y : ℕ → Bool) :
    (∃ H : Finset (Fin (2 * (m + 1))), (∀ S ∈ fam m y, (H ∩ S).Nonempty) ∧ H.card ≤ m + 1) ↔
      par y m = true := by
  constructor
  · rintro ⟨H, hhit, hcard⟩
    have pairs : ∀ i : ℕ, i ≤ m → pt m i false ∈ H ∨ pt m i true ∈ H := by
      intro i hi
      exact mem_of_hit_pair H _ _ (hhit _ ((mem_fam m y _).2 (Or.inl ⟨i, hi, rfl⟩)))
    have inj : Set.InjOn (fun a : Fin (2 * (m + 1)) => (a : ℕ) / 2) (H : Set (Fin (2 * (m + 1)))) := by
      apply Finset.injOn_of_surjOn_of_card_le (t := Finset.range (m + 1))
      · intro a _
        have := a.isLt
        simp only [Finset.coe_range, Set.mem_Iio]
        omega
      · intro i hi
        simp only [Finset.coe_range, Set.mem_Iio] at hi
        rcases pairs i (by omega) with h | h
        · exact ⟨_, h, pt_half m i false (by omega)⟩
        · exact ⟨_, h, pt_half m i true (by omega)⟩
      · rw [Finset.card_range]
        exact hcard
    have notboth : ∀ (i : ℕ) (b b' : Bool), i ≤ m → pt m i b ∈ H → pt m i b' ∈ H → b = b' := by
      intro i b b' hi h1 h2
      have e := inj h1 h2 (by
        show ((pt m i b : Fin (2 * (m + 1))) : ℕ) / 2 = ((pt m i b' : Fin (2 * (m + 1))) : ℕ) / 2
        rw [pt_half m i b hi, pt_half m i b' hi])
      exact (pt_inj m i i b b' hi hi e).2
    have key : ∀ i : ℕ, i ≤ m → ∀ b : Bool, pt m i b ∈ H ↔ b = par y i := by
      intro i
      induction i with
      | zero =>
        intro hi b
        have hS : ({pt m 0 (y 0)} : Finset (Fin (2 * (m + 1)))) ∈ fam m y := by
          rw [mem_fam, idx_single]
          exact Or.inr (Or.inr (Or.inl rfl))
        have h0 : pt m 0 (y 0) ∈ H := mem_of_hit H _ (hhit _ hS)
        constructor
        · intro hb
          exact notboth 0 b (y 0) hi hb h0
        · intro hb
          rw [hb]
          exact h0
      | succ i ih =>
        intro hi b
        have ih' := ih (by omega)
        have hS : ({pt m i (!par y i), pt m (i + 1) (xor (par y i) (y (i + 1)))} :
            Finset (Fin (2 * (m + 1)))) ∈ fam m y := by
          rw [mem_fam, idx_edge m i _ _ (by omega)]
          refine Or.inr (Or.inr (Or.inr ⟨i, !par y i, by omega, ?_⟩))
          rw [Bool.not_not]
        have h1 : pt m (i + 1) (par y (i + 1)) ∈ H := by
          rcases mem_of_hit_pair H _ _ (hhit _ hS) with h | h
          · have := (ih' (!par y i)).1 h
            cases hp : par y i <;> rw [hp] at this <;> simp at this
          · exact h
        constructor
        · intro hb
          exact notboth (i + 1) b _ hi hb h1
        · intro hb
          rw [hb]
          exact h1
    have hS : ({pt m m true} : Finset (Fin (2 * (m + 1)))) ∈ fam m y := by
      rw [mem_fam]
      exact Or.inr (Or.inl rfl)
    exact ((key m (Nat.le_refl m) true).1 (mem_of_hit H _ (hhit _ hS))).symm
  · intro hodd
    refine ⟨(Finset.range (m + 1)).image fun i : ℕ => pt m i (par y i), ?_, ?_⟩
    · have hin : ∀ i : ℕ, i ≤ m →
          pt m i (par y i) ∈ (Finset.range (m + 1)).image fun i : ℕ => pt m i (par y i) :=
        fun i hi => Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩
      intro S hS
      rw [mem_fam] at hS
      rcases hS with ⟨i, hi, hS⟩ | hS | hS | ⟨i, b, hi, hS⟩
      · refine ⟨pt m i (par y i), Finset.mem_inter.2 ⟨hin i hi, ?_⟩⟩
        rw [hS]
        cases par y i <;> simp
      · refine ⟨pt m m true, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
        · have := hin m (Nat.le_refl m)
          rw [hodd] at this
          exact this
        · rw [hS]
          simp
      · have h0 : idx S = 0 := by
          rw [hS]
          exact idx_single m _
        rw [h0] at hS
        refine ⟨pt m 0 (y 0), Finset.mem_inter.2 ⟨hin 0 (Nat.zero_le m), ?_⟩⟩
        rw [hS]
        simp
      · have h0 : idx S = i + 1 := by
          rw [hS]
          exact idx_edge m i _ _ hi
        rw [h0] at hS
        by_cases hb : par y i = b
        · refine ⟨pt m i (par y i), Finset.mem_inter.2 ⟨hin i (by omega), ?_⟩⟩
          rw [hS, hb]
          simp
        · refine ⟨pt m (i + 1) (par y (i + 1)), Finset.mem_inter.2 ⟨hin (i + 1) (by omega), ?_⟩⟩
          have hb' : par y i = !b := by
            cases hp : par y i <;> cases b <;> simp_all
          have e : par y (i + 1) = xor (!b) (y (i + 1)) := by
            show xor (par y i) (y (i + 1)) = xor (!b) (y (i + 1))
            rw [hb']
          rw [hS, e]
          simp
    · exact le_trans Finset.card_image_le (by rw [Finset.card_range])

/-! ## The table and the word -/

/-- The set of inputs on which `z` is true. -/
def supp {N : ℕ} (z : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N => z i = true

open Classical in
/-- The entry of the partial table at the input `z`: `false` at the zero input, `true` at the
indicator of a set of the family, undefined elsewhere. It reads one bit of `y`. -/
noncomputable def entry (m : ℕ) (y : ℕ → Bool) (z : Fin (2 * (m + 1)) → Bool) : Option Bool :=
  if z = (fun _ : Fin (2 * (m + 1)) => false) then some false
  else if P m (supp z) (y (idx (supp z))) then some true else none

/-- The partial table, on `2 * (m + 1)` variables. -/
noncomputable def table (m : ℕ) (y : ℕ → Bool) : List (Option Bool) :=
  (List.range (2 ^ (2 * (m + 1)))).map fun k : ℕ => entry m y (bitsOf (2 * (m + 1)) k)

/-- The instance: the bound `m` in unary, the separator, the code of the table. -/
noncomputable def word (m : ℕ) (y : ℕ → Bool) : List Bool :=
  List.replicate m true ++ false :: encodePartial (table m y)

theorem length_table (m : ℕ) (y : ℕ → Bool) : (table m y).length = 2 ^ (2 * (m + 1)) := by
  simp [table]

theorem length_word (m : ℕ) (y : ℕ → Bool) :
    (word m y).length = 2 ^ (2 * (m + 1) + 1) + (m + 1) := by
  unfold word
  rw [List.length_append, List.length_replicate, List.length_cons,
    LocalFormat.length_encodePartial, length_table, pow_succ]
  omega

theorem getD_table (m : ℕ) (y : ℕ → Bool) (z : Fin (2 * (m + 1)) → Bool) :
    (table m y).getD (tableIndex z) none = entry m y z := by
  unfold table
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (tableIndex_lt z),
    Option.map_some, Option.getD_some, bitsOf_tableIndex]

theorem consistent_iff (m : ℕ) (y : ℕ → Bool) (f : (Fin (2 * (m + 1)) → Bool) → Bool) :
    Consistent (2 * (m + 1)) (table m y) f ↔
      f (fun _ : Fin (2 * (m + 1)) => false) = false ∧
        ∀ S ∈ fam m y, f (fun i : Fin (2 * (m + 1)) => decide (i ∈ S)) = true := by
  constructor
  · intro h
    refine ⟨h _ false (by rw [getD_table]; simp [entry]), fun S hS => h _ true ?_⟩
    rw [mem_fam] at hS
    obtain ⟨a, ha⟩ := P_nonempty m S _ hS
    have hz : (fun i : Fin (2 * (m + 1)) => decide (i ∈ S))
        ≠ (fun _ : Fin (2 * (m + 1)) => false) := by
      intro e
      have := congrFun e a
      simp [ha] at this
    have hs : supp (fun i : Fin (2 * (m + 1)) => decide (i ∈ S)) = S := by
      ext i
      simp [supp]
    rw [getD_table]
    unfold entry
    rw [hs]
    split_ifs with h1
    · exact absurd h1 hz
    · rfl
  · rintro ⟨h0, h1⟩ z b hb
    rw [getD_table] at hb
    unfold entry at hb
    split_ifs at hb with hz hP
    · rw [hz, h0]
      exact Option.some.inj hb
    · have e : z = fun i : Fin (2 * (m + 1)) => decide (i ∈ supp z) := by
        funext i
        simp [supp]
      rw [e, h1 (supp z) ((mem_fam m y _).2 hP)]
      exact Option.some.inj hb

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

/-- Membership of the word in partial MCSP is the existence of a function as in `L-meta-015`. -/
theorem word_mem_iff (m : ℕ) (y : ℕ → Bool) :
    word m y ∈ PartialMCSP ↔ par y m = true := by
  rw [← gadget m y, ← hitting_iff (2 * (m + 1)) (fam m y) m]
  constructor
  · rintro ⟨n', s, T, hw, hlen, f, hc, hs⟩
    obtain ⟨e1, e2⟩ := split_unique m s _ _ hw
    have e3 := encodePartial_injective _ _ e2
    subst e1
    subst e3
    rw [length_table] at hlen
    have e4 : 2 * (m + 1) = n' := Nat.pow_right_injective (Nat.le_refl 2) hlen
    subst e4
    obtain ⟨h0, h1⟩ := (consistent_iff m y f).1 hc
    exact ⟨f, h0, h1, hs⟩
  · rintro ⟨f, h0, h1, hs⟩
    exact ⟨2 * (m + 1), m, table m y, rfl, length_table m y, f,
      (consistent_iff m y f).2 ⟨h0, h1⟩, hs⟩

/-! ## Locality -/

/-- The index of the bit of `y` read by entry `k` of the table. -/
def ix (m k : ℕ) : ℕ := idx (supp (bitsOf (2 * (m + 1)) k))

theorem table_get (m : ℕ) (y y' : ℕ → Bool) (k : ℕ) (h : y (ix m k) = y' (ix m k)) :
    (table m y)[k]? = (table m y')[k]? := by
  rcases Nat.lt_or_ge k (2 ^ (2 * (m + 1))) with hk | hk
  · unfold table
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hk, Option.map_some,
      Option.map_some]
    unfold entry
    unfold ix at h
    rw [h]
  · rw [List.getElem?_eq_none_iff.2 (by rw [length_table]; exact hk),
      List.getElem?_eq_none_iff.2 (by rw [length_table]; exact hk)]

/-- A symbol of the code of a partial table is fixed by one entry of the table. -/
theorem enc_congr : ∀ (T T' : List (Option Bool)) (j : ℕ), T[j / 2]? = T'[j / 2]? →
    (encodePartial T)[j]? = (encodePartial T')[j]?
  | [], T', j, h => by
    have hl : T'.length ≤ j / 2 := List.getElem?_eq_none_iff.1 (by rw [← h]; simp)
    have h2 : (encodePartial T')[j]? = none :=
      List.getElem?_eq_none_iff.2 (by rw [LocalFormat.length_encodePartial]; omega)
    rw [h2]
    simp [encodePartial]
  | o :: T, [], j, h => by
    have hl : (o :: T).length ≤ j / 2 := List.getElem?_eq_none_iff.1 (by rw [h]; simp)
    have h2 : (encodePartial (o :: T))[j]? = none :=
      List.getElem?_eq_none_iff.2 (by rw [LocalFormat.length_encodePartial]; omega)
    rw [h2]
    simp [encodePartial]
  | o :: T, o' :: T', 0, h => by
    simp at h
    subst h
    rw [LocalFormat.encodePartial_cons, LocalFormat.encodePartial_cons]
    cases o <;> simp
  | o :: T, o' :: T', 1, h => by
    simp at h
    subst h
    rw [LocalFormat.encodePartial_cons, LocalFormat.encodePartial_cons]
    cases o <;> simp
  | o :: T, o' :: T', j + 2, h => by
    have ih := enc_congr T T' j (by simpa using h)
    rw [LocalFormat.encodePartial_cons, LocalFormat.encodePartial_cons]
    cases o <;> cases o' <;> simpa using ih

theorem word_get (m : ℕ) (y y' : ℕ → Bool) (j : ℕ)
    (h : y (ix m ((j - (m + 1)) / 2)) = y' (ix m ((j - (m + 1)) / 2))) :
    (word m y)[j]? = (word m y')[j]? := by
  unfold word
  rcases Nat.lt_or_ge j m with hj | hj
  · rw [LocalFormat.getElem?_replicate_append_lt m j _ hj,
      LocalFormat.getElem?_replicate_append_lt m j _ hj]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = m + k := ⟨j - m, by omega⟩
    rw [LocalFormat.getElem?_replicate_append_add, LocalFormat.getElem?_replicate_append_add]
    cases k with
    | zero => rfl
    | succ k =>
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
      have hk : m + (k + 1) - (m + 1) = k := by omega
      rw [hk] at h
      exact enc_congr _ _ _ (table_get m y y' _ h)

/-! ## Blocks -/

/-- The parity of the bits of `x` in block `i`: the positions `j` with `j / q = i`. -/
def blockPar (n q : ℕ) (x : Fin n → Bool) : ℕ → Bool := fun i =>
  decide ((Finset.univ.filter fun j : Fin n => (j : ℕ) / q = i ∧ x j = true).card % 2 = 1)

theorem xor_decide_odd (a b : ℕ) :
    xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) = decide ((a + b) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [Nat.add_mod, ha, hb]

theorem par_blockPar (n q : ℕ) (x : Fin n → Bool) : ∀ k : ℕ, par (blockPar n q x) k =
    decide ((Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ k ∧ x j = true).card % 2 = 1)
  | 0 => by
    show blockPar n q x 0 = _
    unfold blockPar
    simp only [Nat.le_zero]
  | k + 1 => by
    show xor (par (blockPar n q x) k) (blockPar n q x (k + 1)) = _
    rw [par_blockPar n q x k]
    unfold blockPar
    have hd : Disjoint (Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ k ∧ x j = true)
        (Finset.univ.filter fun j : Fin n => (j : ℕ) / q = k + 1 ∧ x j = true) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      omega
    have e : (Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ k ∧ x j = true) ∪
        (Finset.univ.filter fun j : Fin n => (j : ℕ) / q = k + 1 ∧ x j = true)
        = Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ k + 1 ∧ x j = true := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge ((j : ℕ) / q) (k + 1) with h | h
        · exact Or.inl ⟨by omega, h2⟩
        · exact Or.inr ⟨by omega, h2⟩
    rw [xor_decide_odd, ← Finset.card_union_of_disjoint hd, e]

theorem block_card (n q i : ℕ) (hq : 0 < q) :
    (Finset.univ.filter fun j : Fin n => (j : ℕ) / q = i).card ≤ q := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun j : Fin n => (j : ℕ) / q = i)
    (t := Finset.Ico (q * i) (q * i + q)) (fun j : Fin n => (j : ℕ)) (by
      intro j hj
      have hj' : (j : ℕ) / q = i := by simpa using hj
      have h1 := Nat.div_add_mod (j : ℕ) q
      have h2 := Nat.mod_lt (j : ℕ) hq
      rw [hj'] at h1
      simp only [Finset.coe_Ico, Set.mem_Ico]
      omega) (Fin.val_injective.injOn)
  rw [Nat.card_Ico] at h
  omega

theorem blockPar_congr (n q i : ℕ) (x x' : Fin n → Bool)
    (h : ∀ j : Fin n, (j : ℕ) / q = i → x' j = x j) : blockPar n q x' i = blockPar n q x i := by
  unfold blockPar
  have e : (Finset.univ.filter fun j : Fin n => (j : ℕ) / q = i ∧ x' j = true)
      = (Finset.univ.filter fun j : Fin n => (j : ℕ) / q = i ∧ x j = true) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h j h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h j h1]; exact h2⟩
  rw [e]

/-- A `q`-local reduction of parity on `n` bits to partial MCSP, with `⌈n / q⌉` blocks. -/
theorem main : ∀ n q : ℕ, 0 < n → 0 < q → ∃ w : (Fin n → Bool) → List Bool,
    QueryLocal n q w ∧
    (∀ x : Fin n → Bool,
      (w x).length = 2 ^ (2 * ((n + q - 1) / q) + 1) + (n + q - 1) / q) ∧
    ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP := by
  intro n q hn hq
  have hpos : 0 < (n + q - 1) / q := Nat.div_pos (by omega) hq
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n + q - 1) / q = m + 1 := ⟨(n + q - 1) / q - 1, by omega⟩
  have hcover : ∀ j : Fin n, (j : ℕ) / q ≤ m := by
    intro j
    have h1 := Nat.div_add_mod (n + q - 1) q
    have h2 := Nat.mod_lt (n + q - 1) hq
    rw [hm] at h1
    have h3 : (j : ℕ) < q * (m + 1) := by
      have := j.isLt
      omega
    have h4 : (j : ℕ) / q < m + 1 := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm]; exact h3)
    omega
  refine ⟨fun x => word m (blockPar n q x), ?_, ?_, ?_⟩
  · intro j x
    refine ⟨Finset.univ.filter fun i : Fin n => (i : ℕ) / q = ix m ((j - (m + 1)) / 2),
      block_card n q _ hq, fun x' hx' => ?_⟩
    apply word_get
    apply blockPar_congr
    intro i hi
    exact hx' i (by simp [hi])
  · intro x
    rw [hm]
    exact length_word m _
  · intro x
    rw [word_mem_iff, par_blockPar]
    have e : (Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ m ∧ x j = true)
        = Finset.univ.filter fun i : Fin n => x i = true := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hcover j, h⟩⟩
    rw [e]
    simp

end PEqualNP.MetaComplexity.Helpers.LocalConstruct
