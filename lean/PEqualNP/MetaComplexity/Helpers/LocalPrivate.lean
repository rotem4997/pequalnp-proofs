import PEqualNP.MetaComplexity.Helpers.LocalConstruct

/-!
# Private witnesses in a 1-local reduction of parity to partial MCSP

Helper for `L-meta-038`. A map of fixed format every output position of which has certificate
complexity at most one, and which reduces parity to partial MCSP, gives every odd input a
function of small circuit size consistent with its own table and with the table of no other
input.

The point that needs care: a table entry is written with two output positions (a "defined"
bit and a value bit), and the two could follow different input bits. Because every output is a
code, the pair `false, true` occurs at no input, and with certificates of size one this forces
the entry at a point `z` between `x` and `y` (equal to `x` off one position, to `y` on it) to be,
when defined, the entry at `x` or the entry at `y` (`entry_step`).
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalPrivate

open PEqualNP.MetaComplexity

/-- Every value of `g` is fixed by at most one input position. -/
def Cert1 {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) : Prop :=
  ∀ x : Fin n → Bool, ∃ S : Finset (Fin n), S.card ≤ 1 ∧
    ∀ y : Fin n → Bool, (∀ i ∈ S, y i = x i) → g y = g x

/-- If `g` changes between two points that differ at position `i` only, the value at one of
them is fixed by position `i`. -/
theorem dep {n : ℕ} {α : Type} (g : (Fin n → Bool) → α) (h : Cert1 g) (x z : Fin n → Bool)
    (i : Fin n) (hzx : ∀ k : Fin n, k ≠ i → z k = x k) (hne : g z ≠ g x) :
    ∀ u : Fin n → Bool, u i = z i → g u = g z := by
  obtain ⟨S, c, hS⟩ := h z
  by_cases hi : i ∈ S
  · have hall : ∀ k ∈ S, k = i := fun k hk => Finset.card_le_one.1 c k hk i hi
    intro u hu
    apply hS
    intro k hk
    rw [hall k hk]
    exact hu
  · exfalso
    apply hne
    exact (hS x (fun k hk => (hzx k (fun e => hi (e ▸ hk))).symm)).symm

/-- The entry at a point between `x` and `y`, when defined, is the entry at `x` or at `y`. -/
theorem entry_step {n : ℕ} (E : (Fin n → Bool) → Option Bool)
    (hD : Cert1 fun u => (E u).isSome) (hV : Cert1 fun u => (E u).getD false)
    (x y z : Fin n → Bool) (i : Fin n) (hzx : ∀ k : Fin n, k ≠ i → z k = x k)
    (hzy : z i = y i) (b : Bool) (hz : E z = some b) : E x = some b ∨ E y = some b := by
  have hxz : ∀ k : Fin n, k ≠ i → x k = z k := fun k hk => (hzx k hk).symm
  -- the point equal to `y` off `i` and to `x` on `i`
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
        dep (fun u => (E u).getD false) hV x z i hzx hv y hzy.symm
      have hVx : ∀ u : Fin n → Bool, u i = x i → (E u).getD false = (E x).getD false :=
        dep (fun u => (E u).getD false) hV z x i hxz (fun e => hv e.symm)
      cases hy : E y with
      | some c =>
        right
        rw [hy, hz] at hVy
        simp at hVy
        rw [hVy]
      | none =>
        exfalso
        have hVu := hVx _ hui
        cases hu : E (Function.update y i (x i)) with
        | none =>
          rw [hu] at hVu
          rw [hy] at hVy
          apply hv
          rw [← hVy, ← hVu]
        | some c =>
          have hne : (E y).isSome ≠ (E (Function.update y i (x i))).isSome := by
            rw [hy, hu]; simp
          have h2 := dep (fun u => (E u).isSome) hD (Function.update y i (x i)) y i huy hne
            z hzy
          rw [hz, hy] at h2
          simp at h2
  · have hDy : (E y).isSome = (E z).isSome :=
      dep (fun u => (E u).isSome) hD x z i hzx hd y hzy.symm
    have hDx : ∀ u : Fin n → Bool, u i = x i → (E u).isSome = (E x).isSome :=
      dep (fun u => (E u).isSome) hD z x i hxz (fun e => hd e.symm)
    have hx : E x = none := by
      cases hx : E x with
      | none => rfl
      | some c => rw [hz, hx] at hd; simp at hd
    have hu : E (Function.update y i (x i)) = none := by
      have h := hDx _ hui
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
            dep (fun u => (E u).getD false) hV x z i hzx hv y hzy.symm
          rw [hy, hz] at hVy
          simp at hVy
          rw [hVy]
      · have h2 := dep (fun u => (E u).getD false) hV (Function.update y i (x i)) y i huy hVuy
          z hzy
        rw [hz, hy] at h2
        simp at h2
        rw [h2]

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

/-- Private witnesses: the statement of `L-meta-038`. -/
theorem private_witness (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hq : QueryLocal n 1 w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) (hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧ HasCircuitSize n' f s ∧
      ∀ y : Fin n → Bool, Consistent n' (T y) f → y = x := by
  obtain ⟨m, s', T', hw, hlen, f, hc, hs⟩ := (hred x).1 hx
  rw [(hfmt x).1] at hw
  obtain ⟨e1, e2⟩ := LocalConstruct.split_unique s s' _ _ hw
  have e3 := LocalConstruct.encodePartial_injective _ _ e2
  subst e1
  subst e3
  have e4 : m = n' := Nat.pow_right_injective (Nat.le_refl 2) (hlen.symm.trans (hfmt x).2)
  subst e4
  refine ⟨f, hc, hs, fun y hy => ?_⟩
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  apply flip_even x i (y i) hi hx
  rw [hred]
  refine ⟨m, s, T (Function.update x i (y i)), (hfmt _).1, (hfmt _).2, f, ?_, hs⟩
  intro e b he
  by_cases hk : tableIndex e < 2 ^ m
  · have hD : Cert1 fun u : Fin n → Bool => ((T u).getD (tableIndex e) none).isSome := by
      intro u
      obtain ⟨S, c, hS⟩ := hq (s + 1 + 2 * tableIndex e) u
      refine ⟨S, c, fun v hv => ?_⟩
      have h := hS v hv
      rw [(word_pair s (T v) (w v) (hfmt v).1 _ (by rw [(hfmt v).2]; exact hk)).1,
        (word_pair s (T u) (w u) (hfmt u).1 _ (by rw [(hfmt u).2]; exact hk)).1] at h
      exact Option.some.inj h
    have hV : Cert1 fun u : Fin n → Bool => ((T u).getD (tableIndex e) none).getD false := by
      intro u
      obtain ⟨S, c, hS⟩ := hq (s + 1 + 2 * tableIndex e + 1) u
      refine ⟨S, c, fun v hv => ?_⟩
      have h := hS v hv
      rw [(word_pair s (T v) (w v) (hfmt v).1 _ (by rw [(hfmt v).2]; exact hk)).2,
        (word_pair s (T u) (w u) (hfmt u).1 _ (by rw [(hfmt u).2]; exact hk)).2] at h
      exact Option.some.inj h
    rcases entry_step (fun u => (T u).getD (tableIndex e) none) hD hV x y
      (Function.update x i (y i)) i (fun k hk' => Function.update_of_ne hk' (y i) x)
      (Function.update_self i (y i) x) b he with h | h
    · exact hc e b h
    · exact hy e b h
  · exfalso
    have hl : (T (Function.update x i (y i))).length ≤ tableIndex e := by
      rw [(hfmt _).2]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at he
    simp at he

end PEqualNP.MetaComplexity.Helpers.LocalPrivate
