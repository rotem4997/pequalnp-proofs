import PEqualNP.MetaComplexity.Helpers.LocPlan

/-!
# Local class: the removal lemma and its two consequences

Pieces `ToolRemoval`, `ToolNoAlias` and `ToolLive` of `LocPlan.lean` (row `L-meta-115`).

The removal of a set `S` of aliases and orphans is done in one pass. The wire map `rmap` sends
an input to itself, an alias to the image of its target, and a kept gate `p` to `m + cnt p`,
where `cnt p` is the number of kept gates below `p`. The new list `build` holds the kept gates
in order, each with its inputs mapped by `rmap`. Every kept gate reads only wires that are not
orphans (an orphan is read only inside `S`), and the target of an alias is never an orphan, so
an induction on the wire gives the values.
-/

namespace PEqualNP.MetaComplexity.Loc.Removal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Loc

/-- The number of gates below `p` outside `S`. -/
def cnt (S : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => if p ∈ S then cnt S p else cnt S p + 1

/-- The wire map of the removal. -/
def rmap (m : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  if j < m then j
  else if j - m ∈ S then
    match tgt (j - m) with
    | some i => if _h : i < j then rmap m S tgt i else 0
    | none => 0
  else m + cnt S (j - m)
termination_by j

/-- The gate `g` with its inputs mapped by `r`. -/
def rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

/-- A default gate. -/
def g0 : Gate := ⟨GateOp.and, []⟩

/-- The kept gates below `p`, in order, inputs mapped by `r`. -/
def build (S : Finset ℕ) (r : ℕ → ℕ) (gs : List Gate) : ℕ → List Gate
  | 0 => []
  | p + 1 => if p ∈ S then build S r gs p else build S r gs p ++ [rg r (gs.getD p g0)]

section
variable (m : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ)

theorem rmap_lt {j : ℕ} (h : j < m) : rmap m S tgt j = j := by
  rw [rmap]; simp [h]

theorem rmap_keep {p : ℕ} (h : p ∉ S) : rmap m S tgt (m + p) = m + cnt S p := by
  rw [rmap]; simp [h]

theorem rmap_alias {p i : ℕ} (h : p ∈ S) (ht : tgt p = some i) (hi : i < m + p) :
    rmap m S tgt (m + p) = rmap m S tgt i := by
  rw [rmap]; simp [h, ht, hi]

theorem cnt_succ_keep {p : ℕ} (h : p ∉ S) : cnt S (p + 1) = cnt S p + 1 := by
  simp [cnt, h]

theorem cnt_mono {p q : ℕ} (h : p ≤ q) : cnt S p ≤ cnt S q := by
  induction q with
  | zero => simp at h; subst h; exact le_rfl
  | succ q ih =>
    rcases Nat.lt_or_ge p (q + 1) with h' | h'
    · have := ih (by omega)
      simp only [cnt]; split_ifs <;> omega
    · have : p = q + 1 := by omega
      subst this; exact le_rfl

theorem cnt_card (p : ℕ) : cnt S p + ((Finset.range p).filter (· ∈ S)).card = p := by
  induction p with
  | zero => simp [cnt]
  | succ p ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p ∈ S
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp)]
      simp only [cnt, if_pos hp]; omega
    · rw [if_neg hp]
      simp only [cnt, if_neg hp]; omega

variable (r : ℕ → ℕ) (gs : List Gate)

theorem len_build (p : ℕ) : (build S r gs p).length = cnt S p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [build, cnt]
    split_ifs <;> simp [ih]

theorem build_prefix (p : ℕ) : ∀ d, ∃ t, build S r gs (p + d) = build S r gs p ++ t := by
  intro d
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    rw [← Nat.add_assoc]
    simp only [build]
    split_ifs
    · exact ⟨t, ht⟩
    · exact ⟨t ++ _, by rw [ht, List.append_assoc]⟩

theorem get_build {p q : ℕ} (hp : p ∉ S) (hq : p < q) :
    (build S r gs q)[cnt S p]? = some (rg r (gs.getD p g0)) := by
  obtain ⟨t, ht⟩ := build_prefix S r gs (p + 1) (q - (p + 1))
  rw [show p + 1 + (q - (p + 1)) = q by omega] at ht
  rw [ht]
  have h1 : build S r gs (p + 1) = build S r gs p ++ [rg r (gs.getD p g0)] := by
    simp [build, hp]
  rw [h1, List.append_assoc, List.getElem?_append_right (by rw [len_build]),
    len_build]
  simp

theorem mem_build (p : ℕ) : ∀ (k : ℕ) (g' : Gate), (build S r gs p)[k]? = some g' →
    ∃ q, q < p ∧ q ∉ S ∧ cnt S q = k ∧ g' = rg r (gs.getD q g0) := by
  induction p with
  | zero => intro k g' h; simp [build] at h
  | succ p ih =>
    intro k g' h
    simp only [build] at h
    split_ifs at h with hp
    · obtain ⟨q, h1, h2, h3, h4⟩ := ih k g' h
      exact ⟨q, by omega, h2, h3, h4⟩
    · by_cases hk : k < (build S r gs p).length
      · rw [List.getElem?_append_left hk] at h
        obtain ⟨q, h1, h2, h3, h4⟩ := ih k g' h
        exact ⟨q, by omega, h2, h3, h4⟩
      · rw [List.getElem?_append_right (by omega)] at h
        have hk' : k - (build S r gs p).length = 0 := by
          by_contra hne
          rw [List.getElem?_eq_none (by simp; omega)] at h
          cases h
        rw [hk'] at h
        simp at h
        refine ⟨p, by omega, hp, ?_, h.symm⟩
        rw [len_build] at hk hk'
        omega

end

/-- Wire `j` is not an orphan of `S` under `tgt`. -/
def NO (m : ℕ) (S : Finset ℕ) (tgt : ℕ → Option ℕ) (j : ℕ) : Prop :=
  ∀ p ∈ S, tgt p = none → j ≠ m + p

section
variable {m : ℕ} {gs : List Gate} {o : ℕ} {P : Set (Fin m → Bool)} {S : Finset ℕ}
  {tgt : ℕ → Option ℕ}

theorem no_tgt (hR : Removable m gs o P S tgt) {p i : ℕ} (hp : p ∈ S) (ht : tgt p = some i) :
    NO m S tgt i := by
  intro q hq hqn heq
  rcases (hR q hq).2 with ⟨j, hj, _⟩ | ⟨_, _, _, hno⟩
  · rw [hqn] at hj; cases hj
  · exact hno p hp (heq ▸ ht)

theorem no_read (hR : Removable m gs o P S tgt) {p : ℕ} (hp : p ∉ S) {g : Gate}
    (hg : gs[p]? = some g) {a : ℕ} (ha : a ∈ g.inputs) : NO m S tgt a := by
  intro q hq hqn heq
  rcases (hR q hq).2 with ⟨j, hj, _⟩ | ⟨_, _, hrd, _⟩
  · rw [hqn] at hj; cases hj
  · exact hp (hrd p ⟨g, hg, heq ▸ ha⟩)

theorem rmap_bound (hR : Removable m gs o P S tgt) :
    ∀ a, NO m S tgt a → ∀ q, a < m + q → rmap m S tgt a < m + cnt S q := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro hno q haq
    by_cases ham : a < m
    · rw [rmap_lt m S tgt ham]; omega
    · obtain ⟨p, rfl⟩ : ∃ p, a = m + p := ⟨a - m, by omega⟩
      by_cases hp : p ∈ S
      · rcases (hR p hp).2 with ⟨i, hi, hil, _⟩ | ⟨hn, _⟩
        · rw [rmap_alias m S tgt hp hi hil]
          exact ih i hil (no_tgt hR hp hi) q (by omega)
        · exact absurd rfl (hno p hp hn)
      · rw [rmap_keep m S tgt hp]
        have h1 := cnt_succ_keep S hp
        have h2 := cnt_mono S (show p + 1 ≤ q by omega)
        omega

theorem getD_eq {gs : List Gate} {p : ℕ} (hp : p < gs.length) :
    gs[p]? = some (gs.getD p g0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  rfl

theorem clean_build (hcl : CleanL m gs) (hR : Removable m gs o P S tgt) :
    CleanL m (build S (rmap m S tgt) gs gs.length) := by
  intro k g' hk
  obtain ⟨q, hq, hqS, rfl, rfl⟩ := mem_build S (rmap m S tgt) gs _ k g' hk
  have hg := getD_eq hq
  have hc := hcl q _ hg
  have hb : ∀ a ∈ (gs.getD q g0).inputs, rmap m S tgt a < m + cnt S q := fun a ha =>
    rmap_bound hR a (no_read hR hqS hg ha) q (hc.lt a ha)
  rcases hc with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, _, _, h2⟩
  · refine Or.inl ⟨h1, rmap m S tgt j, hb j (by rw [h2]; simp), ?_⟩
    show (gs.getD q g0).inputs.map _ = _
    rw [h2]; rfl
  · refine Or.inr ⟨h1, rmap m S tgt j, rmap m S tgt k, hb j (by rw [h2]; simp),
      hb k (by rw [h2]; simp), ?_⟩
    show (gs.getD q g0).inputs.map _ = _
    rw [h2]; rfl

theorem val_build (hcl : CleanL m gs) (hR : Removable m gs o P S tgt) :
    ∀ j, j < m + gs.length → NO m S tgt j → ∀ x ∈ P,
      vl (build S (rmap m S tgt) gs gs.length) x (rmap m S tgt j) = vl gs x j := by
  have hcl' := clean_build hcl hR
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjl hno x hx
    by_cases hjm : j < m
    · rw [rmap_lt m S tgt hjm, vl_input _ x j hjm, vl_input _ x j hjm]
    · obtain ⟨p, rfl⟩ : ∃ p, j = m + p := ⟨j - m, by omega⟩
      by_cases hp : p ∈ S
      · rcases (hR p hp).2 with ⟨i, hi, hil, hv⟩ | ⟨hn, _⟩
        · rw [rmap_alias m S tgt hp hi hil, hv x hx]
          exact ih i hil (by omega) (no_tgt hR hp hi) x hx
        · exact absurd rfl (hno p hp hn)
      · have hpl : p < gs.length := by omega
        have hg := getD_eq hpl
        rw [rmap_keep m S tgt hp,
          vl_gate _ hcl' x (cnt S p) _ (get_build S (rmap m S tgt) gs hp hpl),
          vl_gate gs hcl x p _ hg]
        show (gs.getD p g0).op.eval (((gs.getD p g0).inputs.map (rmap m S tgt)).map _) = _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have hal := (hcl p _ hg).lt a ha
        exact ih a hal (by omega) (no_read hR hp hg ha) x hx

end

theorem ToolRemoval_proof : ToolRemoval := by
  intro m gs o P S tgt hcl hR
  refine ⟨build S (rmap m S tgt) gs gs.length, rmap m S tgt, clean_build hcl hR, ?_, ?_,
    fun j hj => rmap_lt m S tgt hj, ?_⟩
  · intro hnf g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨q, hq, _, _, rfl⟩ := mem_build S (rmap m S tgt) gs _ k g hk
    show (gs.getD q g0).op ≠ _
    exact hnf _ (List.mem_of_getElem? (getD_eq hq))
  · have h1 := cnt_card S gs.length
    have h2 : (Finset.range gs.length).filter (· ∈ S) = S := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨(hR p h).1, h⟩⟩
    rw [h2] at h1
    rw [len_build]
    omega
  · intro j hj hno
    refine ⟨?_, val_build hcl hR j hj hno⟩
    rw [len_build]
    exact rmap_bound hR j hno gs.length hj

/-- A wire past the end of the list is false. -/
theorem vl_past {m : ℕ} (gs : List Gate) (x : Fin m → Bool) {j : ℕ} (h : m + gs.length ≤ j) :
    vl gs x j = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

/-- The output of a list computing a function that is not constant is a wire of the list. -/
theorem out_lt {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hc : Computes m gs o f) (hf : ∃ x y : Fin m → Bool, f x ≠ f y) : o < m + gs.length := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := hf
  apply hxy
  rw [← hc x, ← hc y, vl_past gs x (by omega), vl_past gs y (by omega)]

/-- Removing one gate of a least circuit, keeping the output, is impossible. -/
theorem least_no_drop {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hM : MLeast m f gs o) (hf : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (tgt : ℕ → Option ℕ) (hR : Removable m gs o Set.univ {p} tgt) (ho : o ≠ m + p ∨ tgt p ≠ none) :
    False := by
  obtain ⟨gs', r, hcl', hnf', hlen, _, hv⟩ :=
    ToolRemoval_proof m gs o Set.univ {p} tgt hM.1 hR
  have hol := out_lt hM.2.2.1 hf
  have hno : ∀ q ∈ ({p} : Finset ℕ), tgt q = none → o ≠ m + q := by
    intro q hq hqn
    rw [Finset.mem_singleton] at hq
    subst hq
    rcases ho with h | h
    · exact h
    · exact absurd hqn h
  obtain ⟨_, hv'⟩ := hv o hol hno
  have hle := hM.2.2.2 gs' (r o) hcl' (hnf' hM.2.1) (fun x => by
    rw [hv' x (Set.mem_univ x)]; exact hM.2.2.1 x)
  simp at hlen
  omega

theorem ToolNoAlias_proof : ToolNoAlias := by
  intro m f gs o hM hf p hp j hj heq
  refine least_no_drop hM hf p (fun _ => some j) ?_ (Or.inr (by simp))
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst q
  exact ⟨hp, Or.inl ⟨j, rfl, hj, fun x _ => heq x⟩⟩

theorem ToolLive_proof : ToolLive := by
  intro m f gs o hM hf
  refine ⟨out_lt hM.2.2.1 hf, ?_⟩
  intro p hp hop
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  refine least_no_drop hM hf p (fun _ => none) ?_ (Or.inl hop)
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst q
  refine ⟨hp, Or.inr ⟨rfl, hop, ?_, fun _ _ h => by cases h⟩⟩
  intro q hrd
  have : q ∈ RdSet gs (m + p) := mem_rdSet.2 hrd
  rw [hne] at this
  simp at this

end PEqualNP.MetaComplexity.Loc.Removal
