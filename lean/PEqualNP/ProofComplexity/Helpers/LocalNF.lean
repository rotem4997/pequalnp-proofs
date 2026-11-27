import PEqualNP.ProofComplexity.Helpers.EchelonNF
import PEqualNP.ProofComplexity.Helpers.ExpanderSupp
import PEqualNP.ProofComplexity.Helpers.LocalSat

/-!
# Helpers: the local normal form facts on a pigeonhole graph (helper module, proofs only)

Helper H5 of the route to L-pcx-046 (`notes/pcx-046-route.md`, section 1.5). With
`nf (locIdeal G S)` the echelon normal form modulo the polynomials vanishing on the points that
respect every hole and seat every pigeon of `S`:

* `nf_locIdeal_holes` (locality): the monomials of the normal form of a monomial `a` have their
  holes among the holes of `a` and the neighbours of `S`;
* `nf_locIdeal_insert` (peel one pigeon): adding a pigeon `p` with a neighbour `j` that is
  neither a neighbour of `S` nor a hole of `a` does not change the normal form of `a`;
* `nf_locIdeal_ext` (extension): if `S` is closed for `K`, the normal form of a monomial with
  holes in `K` is the same for every `T` between `S` and size `s`.

The two substitutions are `bind₁` maps: `localNF_zeroOut` sets to zero every variable whose hole
is outside a set of holes, and `localNF_override` rewrites one hole `j` (the edge from `p` is
set to one, the other edges at `j` to zero).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)

/-- Evaluating a substituted polynomial is evaluating at the substituted point. -/
theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]

/-- A polynomial is the sum of its terms; the image of a sum of terms under a linear map. -/
theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]

/-! ### Zeroing the variables whose hole is outside `K` -/

/-- The substitution that sets to zero every variable whose hole is outside `K`. -/
noncomputable def localNF_zeroOut (K : Finset (Fin N)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 ∈ K then X e else 0

theorem localNF_zeroOut_monomial (K : Finset (Fin N)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (localNF_zeroOut G K) (monomial b c)
      = if monoHoles G b ⊆ K then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, localNF_zeroOut G K e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [localNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxK⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [localNF_zeroOut, ite_eq_right hxK, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem localNF_zeroOut_mem {S : Finset (Fin m)} {K : Finset (Fin N)} (hK : S.biUnion G ⊆ K)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) :
    bind₁ (localNF_zeroOut G K) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_zeroOut G K e) * eval α (localNF_zeroOut G K e') = 0
    by_cases h : e.1.2 ∈ K
    · by_cases h' : e'.1.2 ∈ K
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact hα.1 e e' h1 h2
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [localNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.2 i hi
    have hmem : e.1.2 ∈ K := by
      refine hK (Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩)
      rw [← he]
      exact e.2
    refine ⟨e, he, ?_⟩
    show eval α (localNF_zeroOut G K e) = 1
    rw [localNF_zeroOut, ite_eq_left hmem, eval_X, h1]

theorem localNF_zeroOut_eq (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (localNF_zeroOut G K) r
      = ∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => localNF_zeroOut_monomial G K b _

theorem localNF_support_sum_filter (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoHoles G b ⊆ K) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc

/-- Locality: the monomials of the normal form of `a` modulo `locIdeal G S` have their holes
among the holes of `a` and the neighbours of `S`. -/
theorem nf_locIdeal_holes (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (locIdeal G S) (monomial a 1)).support,
      monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G := by
  have hsub := localNF_support_sum_filter G (monoHoles G a ∪ S.biUnion G)
    (nf (locIdeal G S) (monomial a 1))
  have heq : nf (locIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
          (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
          monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (locIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (locIdeal G S) (monomial a 1) b (Finset.mem_filter.mp (hsub hb)).1
    · have h := localNF_zeroOut_mem G (S := S) (K := monoHoles G a ∪ S.biUnion G)
        Finset.subset_union_right (nf_sub_mem (locIdeal G S) (monomial a 1))
      rw [map_sub, localNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        localNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
      (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
      monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2

/-! ### Overriding one hole -/

/-- The substitution at hole `j`: the edge from `p` becomes one, the other edges at `j` become
zero, every other variable is kept. -/
noncomputable def localNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 = j then (if e.1.1 = p then 1 else 0) else X e

/-- A monomial with the edges at hole `j` dropped. -/
noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)

theorem localNF_override_monomial_of_notMem (p : Fin m) {j : Fin N} {b : GEdge G →₀ ℕ}
    (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (localNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, localNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [localNF_override, ite_eq_right hne]
  rw [hprod, monomial_eq]
  rfl

theorem localNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hj : j ∈ G p)
    (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ locIdeal G (insert p S)) :
    bind₁ (localNF_override G p j) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_override G p j e) * eval α (localNF_override G p j e') = 0
    by_cases h : e.1.2 = j
    · have h' : e'.1.2 = j := h1 ▸ h
      by_cases hp : e.1.1 = p
      · have hp' : ¬ e'.1.1 = p := fun h3 => h2 (hp.trans h3.symm)
        rw [localNF_override, localNF_override, ite_eq_left h', ite_eq_right hp', map_zero,
          mul_zero]
      · rw [localNF_override, ite_eq_left h, ite_eq_right hp, map_zero, zero_mul]
    · have h' : ¬ e'.1.2 = j := fun h3 => h (h1.trans h3)
      rw [localNF_override, localNF_override, ite_eq_right h, ite_eq_right h', eval_X, eval_X]
      exact hα.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (localNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [localNF_override, ite_eq_left rfl, ite_eq_left rfl, map_one]
    · obtain ⟨e, he, h1⟩ := hα.2 i h
      have hne : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (localNF_override G p j e) = 1
      rw [localNF_override, ite_eq_right hne, eval_X, h1]

/-- The image of a monomial under the override is zero or the monomial with the edges at `j`
dropped. -/
theorem localNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (localNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (localNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, e.1.2 = j ∧ ¬ e.1.1 = p
  · obtain ⟨e, he, h1, h2⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rw [localNF_override, ite_eq_left h1, ite_eq_right h2, zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz' : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, h, h2⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), localNF_override, ite_eq_left h,
        ite_eq_left (hz' e he h), one_pow]
    · rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        localNF_override, ite_eq_right h]

/-- Dropping the edges at a hole gives the same monomial or one of smaller degree. -/
theorem localNF_drop_eq_or_degree_lt (j : Fin N) (c : GEdge G →₀ ℕ) :
    localNF_drop G j c = c ∨ (localNF_drop G j c).degree < c.degree := by
  have hsplit : localNF_drop G j c + c.filter (fun e => ¬ e.1.2 ≠ j) = c :=
    Finsupp.filter_add_filter_not c _
  by_cases h0 : c.filter (fun e => ¬ e.1.2 ≠ j) = 0
  · left
    rw [h0, add_zero] at hsplit
    exact hsplit
  · right
    have hdeg : (localNF_drop G j c).degree + (c.filter (fun e => ¬ e.1.2 ≠ j)).degree
        = c.degree := by
      rw [← map_add, hsplit]
    have hpos : 0 < (c.filter (fun e => ¬ e.1.2 ≠ j)).degree :=
      Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    omega

/-- The override maps the span of the monomials below `b` into itself. -/
theorem localNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (localNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b := 
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases localNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))

/-- Peel one pigeon: adding a pigeon `p` with a neighbour `j` that is neither a neighbour of `S`
nor a hole of `a` does not change the normal form of `a`. -/
theorem nf_locIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoHoles G a) :
    nf (locIdeal G (insert p S)) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have _ := hp
  refine nf_unique (locIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (locIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hbj : j ∉ monoHoles G b := by
      intro h
      rcases Finset.mem_union.mp (nf_locIdeal_holes G S a b hb h) with h' | h'
      · exact ha h'
      · exact hjS h'
    have himg := congrArg (bind₁ (localNF_override G p j)) huw
    rw [map_add, localNF_override_monomial_of_notMem G p hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (localNF_override_mem G hj hjS hu)
      (localNF_override_mem_restrictSupport G p j hw)
  · exact locIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (locIdeal G S) (monomial a 1))

/-- Extension: if `S` is closed for `K`, the normal form of a monomial with holes in `K` is the
same modulo `locIdeal G T` for every `T` with `S ⊆ T` and `T.card ≤ s`. -/
theorem nf_locIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoHoles G a ⊆ K) :
    nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_locIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

end PEqualNP.ProofComplexity.Helpers
