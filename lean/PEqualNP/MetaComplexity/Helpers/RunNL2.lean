import PEqualNP.MetaComplexity.Helpers.RunNL

/-!
# Theorem NL, part 2: removing the NOT state at `x_e := 1`

A gate list `gs` on `n + 1` inputs with the NOT state at input `e`: gate `pn` a NOT reading `e`,
gate `pm` an AND listing `pn`, gate `pS` an OR listing `pm`, with the reader conditions. A set
`R` of gates is removed (`pn`, `pm`, `pS` and possibly a gate read only by `pm`). Each kept gate
`p` keeps its operation; a listed wire `a` is mapped by `nlRho p a`:
* an input to itself;
* a kept earlier gate to its new place `n + 1 + nlCnt R j`;
* the wire of `pS` to the image of its other operand `s` when `s` is an earlier wire other than
  `pm` (an alias at `x_e = 1`), and otherwise to the gate's own new wire (which reads `false`);
* anything else (a later wire, a removed gate) to the gate's own new wire.
The new list computes the function with `x_e` set to `1`, at every point.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A default gate. -/
def nlG0 : Gate := ⟨GateOp.and, []⟩

/-- The number of gates below `p` outside `R`. -/
def nlCnt (R : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => if p ∈ R then nlCnt R p else nlCnt R p + 1

theorem nlCnt_le (R : Finset ℕ) (p : ℕ) : nlCnt R p ≤ p := by
  induction p with
  | zero => simp [nlCnt]
  | succ p ih => simp only [nlCnt]; split_ifs <;> omega

theorem nlCnt_mono (R : Finset ℕ) {p q : ℕ} (h : p ≤ q) : nlCnt R p ≤ nlCnt R q := by
  induction q with
  | zero => simp at h; subst h; exact le_rfl
  | succ q ih =>
    rcases Nat.lt_or_ge p (q + 1) with h' | h'
    · have := ih (by omega)
      simp only [nlCnt]; split_ifs <;> omega
    · have : p = q + 1 := by omega
      subst this; exact le_rfl

theorem nlCnt_keep (R : Finset ℕ) {p : ℕ} (h : p ∉ R) : nlCnt R (p + 1) = nlCnt R p + 1 := by
  simp [nlCnt, h]

theorem nlCnt_lt (R : Finset ℕ) {p q : ℕ} (hp : p ∉ R) (h : p < q) : nlCnt R p < nlCnt R q := by
  have h1 := nlCnt_keep R hp
  have h2 := nlCnt_mono R (show p + 1 ≤ q by omega)
  omega

theorem nlCnt_inj (R : Finset ℕ) {p q : ℕ} (hp : p ∉ R) (hq : q ∉ R)
    (h : nlCnt R p = nlCnt R q) : p = q := by
  rcases lt_trichotomy p q with h' | h' | h'
  · have := nlCnt_lt R hp h'; omega
  · exact h'
  · have := nlCnt_lt R hq h'; omega

theorem nlCnt_card (R : Finset ℕ) (p : ℕ) :
    nlCnt R p + ((Finset.range p).filter (· ∈ R)).card = p := by
  induction p with
  | zero => simp [nlCnt]
  | succ p ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p ∈ R
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp)]
      simp only [nlCnt, if_pos hp]; omega
    · rw [if_neg hp]
      simp only [nlCnt, if_neg hp]; omega

/-- The kept gates below `p`, in order, each given by `f`. -/
def nlB (R : Finset ℕ) (f : ℕ → Gate) : ℕ → List Gate
  | 0 => []
  | p + 1 => if p ∈ R then nlB R f p else nlB R f p ++ [f p]

theorem nlB_len (R : Finset ℕ) (f : ℕ → Gate) (p : ℕ) : (nlB R f p).length = nlCnt R p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [nlB, nlCnt]
    split_ifs <;> simp [ih]

theorem nlB_prefix (R : Finset ℕ) (f : ℕ → Gate) (p : ℕ) :
    ∀ d, ∃ t, nlB R f (p + d) = nlB R f p ++ t := by
  intro d
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    rw [← Nat.add_assoc]
    simp only [nlB]
    split_ifs
    · exact ⟨t, ht⟩
    · exact ⟨t ++ _, by rw [ht, List.append_assoc]⟩

theorem nlB_get (R : Finset ℕ) (f : ℕ → Gate) {p q : ℕ} (hp : p ∉ R) (hq : p < q) :
    (nlB R f q)[nlCnt R p]? = some (f p) := by
  obtain ⟨t, ht⟩ := nlB_prefix R f (p + 1) (q - (p + 1))
  rw [show p + 1 + (q - (p + 1)) = q by omega] at ht
  rw [ht]
  have h1 : nlB R f (p + 1) = nlB R f p ++ [f p] := by
    simp [nlB, hp]
  rw [h1, List.append_assoc, List.getElem?_append_right (by rw [nlB_len]), nlB_len]
  simp

theorem nlB_mem (R : Finset ℕ) (f : ℕ → Gate) (p : ℕ) : ∀ (k : ℕ) (g : Gate),
    (nlB R f p)[k]? = some g → ∃ q, q < p ∧ q ∉ R ∧ nlCnt R q = k ∧ g = f q := by
  induction p with
  | zero => intro k g h; simp [nlB] at h
  | succ p ih =>
    intro k g h
    simp only [nlB] at h
    split_ifs at h with hp
    · obtain ⟨q, h1, h2, h3, h4⟩ := ih k g h
      exact ⟨q, by omega, h2, h3, h4⟩
    · by_cases hk : k < (nlB R f p).length
      · rw [List.getElem?_append_left hk] at h
        obtain ⟨q, h1, h2, h3, h4⟩ := ih k g h
        exact ⟨q, by omega, h2, h3, h4⟩
      · rw [List.getElem?_append_right (by omega)] at h
        have hk' : k - (nlB R f p).length = 0 := by
          by_contra hne
          rw [List.getElem?_eq_none (by simp; omega)] at h
          cases h
        rw [hk'] at h
        simp at h
        refine ⟨p, by omega, hp, ?_, h.symm⟩
        rw [nlB_len] at hk hk'
        omega

/-! ## The wire map -/

section Map
variable (n : ℕ) (gs : List Gate) (R : Finset ℕ) (pm pS : ℕ)

/-- The other operand of the OR gate `pS`: a listed earlier wire other than `pm`. -/
def nlSo : Option ℕ :=
  (gs.getD pS nlG0).inputs.find? (fun a => decide (a ≠ n + 1 + pm ∧ a < n + 1 + pS))

/-- The new place of an input or a kept gate. -/
def nlIota (a : ℕ) : ℕ := if a < n + 1 then a else n + 1 + nlCnt R (a - (n + 1))

/-- The wire map of kept gate `p`. -/
def nlRho (p a : ℕ) : ℕ :=
  if a < n + 1 then a
  else if a < n + 1 + p then
    (if a - (n + 1) ∈ R then
      (if a = n + 1 + pS then
        (match nlSo n gs pm pS with
          | some s => nlIota n R s
          | none => n + 1 + nlCnt R p)
       else n + 1 + nlCnt R p)
     else n + 1 + nlCnt R (a - (n + 1)))
  else n + 1 + nlCnt R p

/-- Gate `p` with its listed wires mapped. -/
def nlMk (p : ℕ) : Gate :=
  ⟨(gs.getD p nlG0).op, (gs.getD p nlG0).inputs.map (nlRho n gs R pm pS p)⟩

/-- The circuit with the gates of `R` removed, output `o` mapped as if read after the last gate. -/
def nlL (o : ℕ) : Circuit :=
  ⟨nlB R (nlMk n gs R pm pS) gs.length, nlRho n gs R pm pS gs.length o⟩

end Map

theorem nl_getD {gs : List Gate} {p : ℕ} (hp : p < gs.length) : gs.getD p nlG0 = gs[p] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

theorem nlL_len (n : ℕ) (gs : List Gate) (R : Finset ℕ) (pm pS o : ℕ)
    (hR : ∀ j ∈ R, j < gs.length) :
    (nlL n gs R pm pS o).gates.length = gs.length - R.card := by
  show (nlB R _ gs.length).length = _
  rw [nlB_len]
  have h1 := nlCnt_card R gs.length
  have h2 : (Finset.range gs.length).filter (· ∈ R) = R := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hR p h, h⟩⟩
  rw [h2] at h1
  omega

theorem nlL_fan (n : ℕ) (gs : List Gate) (R : Finset ℕ) (pm pS o : ℕ)
    (hfan : FanInTwo ⟨gs, o⟩) : FanInTwo (nlL n gs R pm pS o) := by
  intro g hg
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
  obtain ⟨q, hq, _, _, rfl⟩ := nlB_mem R _ gs.length k g hk
  have := hfan (gs.getD q nlG0) (by rw [nl_getD hq]; exact List.getElem_mem hq)
  refine ⟨this.1, ?_⟩
  show ((gs.getD q nlG0).inputs.map _).length ≤ 2
  rw [List.length_map]; exact this.2

/-- Two listed wires of a list of at most two that both differ from a listed `b` are equal. -/
theorem nl_two (l : List ℕ) (hl : l.length ≤ 2) (b a a' : ℕ) (hb : b ∈ l) (ha : a ∈ l)
    (ha' : a' ∈ l) (hab : a ≠ b) (hab' : a' ≠ b) : a = a' := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ => simp at ha hb; omega
  | [u, v], _ => simp at ha ha' hb; omega
  | _ :: _ :: _ :: _, h => simp at h

theorem nlSo_spec (n : ℕ) (gs : List Gate) (pm pS s : ℕ) (h : nlSo n gs pm pS = some s) :
    s ∈ (gs.getD pS nlG0).inputs ∧ s ≠ n + 1 + pm ∧ s < n + 1 + pS := by
  unfold nlSo at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2.1, h2.2⟩

theorem nlSo_of (n : ℕ) (gs : List Gate) (pm pS : ℕ) (hl : (gs.getD pS nlG0).inputs.length ≤ 2)
    (hm : n + 1 + pm ∈ (gs.getD pS nlG0).inputs) (a : ℕ) (ha : a ∈ (gs.getD pS nlG0).inputs)
    (h1 : a ≠ n + 1 + pm) (h2 : a < n + 1 + pS) : nlSo n gs pm pS = some a := by
  have hs : (nlSo n gs pm pS).isSome := by
    unfold nlSo
    rw [List.find?_isSome]
    exact ⟨a, ha, by simp [h1, h2]⟩
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨k1, k2, _⟩ := nlSo_spec n gs pm pS s hs'
  rw [hs', nl_two _ hl _ s a hm k1 ha k2 h1]

end PEqualNP.MetaComplexity.Helpers.RunNL
