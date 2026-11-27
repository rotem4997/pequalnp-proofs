import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkB

/-!
# The owner link, clause (a): building blocks (conjecture until checked)

The heads of one `innerF E k u v b` block are exactly the thread indices
`3(E+1) + 2k(u * 3(E+1) + v) + i`, `i < 2k`, of parity `i % 2 = 1 ↔ b`, without repeats
(`innerF_heads`, `innerF_heads_nodup`), and blocks of distinct pairs `(u, v)` below `3(E+1)` have
disjoint heads (`innerF_heads_disjoint`). This is the thread half of `F` in G-OWN, with `b` in the
role of `u ∈ T`. The vertex half and the identification of the pairs with `H` are the open part,
stated as `PlacedEdges` below.
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

theorem innerF_heads (E k u v : ℕ) (b : Bool) (x : ℕ) :
    x ∈ (innerF E k u v b).map (fun l : List ℕ => l.headD 0) ↔
      ∃ i, i < 2 * k ∧ x = 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + i ∧
        (i % 2 = 1 ↔ b = true) := by
  unfold innerF
  simp only [List.map_map, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Function.comp_apply, List.headD_cons, Xf]
  constructor
  · rintro ⟨s, ⟨hs, hp⟩, rfl⟩
    refine ⟨s, hs, by omega, ?_⟩
    rw [← hp]; omega
  · rintro ⟨i, hi, rfl, hp⟩
    refine ⟨i, ⟨hi, ?_⟩, by omega⟩
    rw [← hp]; omega

theorem innerF_heads_nodup (E k u v : ℕ) (b : Bool) :
    ((innerF E k u v b).map (fun l : List ℕ => l.headD 0)).Nodup := by
  unfold innerF
  simp only [List.map_map]
  refine List.Nodup.map ?_ ((List.nodup_range).filter _)
  intro s t h
  simp only [Function.comp_apply, List.headD_cons, Xf] at h
  omega

theorem innerF_heads_disjoint {E k u v u' v' : ℕ} {b b' : Bool} (hv : v < 3 * (E + 1))
    (hv' : v' < 3 * (E + 1)) (hne : (u, v) ≠ (u', v')) (x : ℕ)
    (hx : x ∈ (innerF E k u v b).map (fun l : List ℕ => l.headD 0))
    (hx' : x ∈ (innerF E k u' v' b').map (fun l : List ℕ => l.headD 0)) : False := by
  rw [innerF_heads] at hx hx'
  obtain ⟨i, hi, rfl, -⟩ := hx
  obtain ⟨i', hi', he, -⟩ := hx'
  generalize hN : 3 * (E + 1) = N at *
  have hk : 0 < k := by omega
  -- the base index u * N + v determines (u, v)
  have hb : 2 * k * (u * N + v) + i = 2 * k * (u' * N + v') + i' := by omega
  have hq : u * N + v = u' * N + v' := by
    have h1 : (2 * k * (u * N + v) + i) / (2 * k) = u * N + v := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
    have h2 : (2 * k * (u' * N + v') + i') / (2 * k) = u' * N + v' := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi', Nat.zero_add]
    rw [← h1, ← h2, hb]
  have hu : u = u' := by
    have h1 : (u * N + v) / N = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
    have h2 : (u' * N + v') / N = u' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv', Nat.zero_add]
    rw [← h1, ← h2, hq]
  subst hu
  exact hne (by simp only [Prod.mk.injEq, true_and]; omega)

/-- The `innerF` calls of `OWN'`, as (u, v, inT) triples, in order. -/
def callsF (E : ℕ) (ψ : CNF) : List (ℕ × ℕ × Bool) :=
  (List.range ψ.length).flatMap (fun i : ℕ => (List.range (wF ψ i + 1)).flatMap (fun j : ℕ =>
    (if j < wF ψ i then
        [(2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0), posF E ψ i j, (litF ψ i j).2)]
      else [(2 * E + 1, posF E ψ i j, true)]) ++
    ((List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l))).map
        (fun l : ℕ => (posF E ψ i j, posF E ψ i l, decide (j ≠ fF ψ i))) ++
    (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then
        [(2 * (litF ψ i j).1, 2 * (litF ψ i j).1 + 1, false)] else []))) ++
  [(2 * E, 2 * E + 1, false), (2 * E, 3 * E + 2, false)]

/-- FIRST GAP (open, conjecture by the script attack): under the G-OWN prefix, the calls are
exactly the edges of the placed graph `H`, each once, smaller end first, and the flag is
membership of the smaller end in `T`. With `innerF_heads`, `innerF_heads_nodup`,
`innerF_heads_disjoint` this gives the thread half of clause (a) and drives clause (c). -/
def PlacedEdges : Prop :=
  ∀ (φ : PEqualNP.Search.CNF) (E k : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), 1 ≤ k → E = (PEqualNP.Search.encodeCNF φ).length → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z, e z = (φ.flatMap (fun c => c.map some ++ [none])).findIdx (fun o => o.any (fun l => l.1 == z))) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin (3 * (E + 1))), (∀ a b : Fin (3 * (E + 1)), H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ T : Finset (Fin (3 * (E + 1))), (∀ a : Fin (3 * (E + 1)), a ∈ T ↔ ∃ u ∈ PEqualNP.MetaComplexity.CoverPromise.cvcCover φ, num u = a.val) →
    ((callsF E (REN φ)).map (fun c : ℕ × ℕ × Bool => (c.1, c.2.1))).Nodup ∧
    (∀ c ∈ callsF E (REN φ), c.1 < c.2.1 ∧ c.2.1 < 3 * (E + 1)) ∧
    (∀ a b : Fin (3 * (E + 1)), a < b → (H.Adj a b ↔ ∃ t : Bool, (a.val, b.val, t) ∈ callsF E (REN φ))) ∧
    (∀ c ∈ callsF E (REN φ), ∀ a : Fin (3 * (E + 1)), a.val = c.1 → (a ∈ T ↔ c.2.2 = true))

/-- The second conjunct of `PlacedEdges`, proved: every call has its smaller end first and both
ends below `3(E+1)`, for `REN φ` at the code length. -/
theorem calls_bounds (φ : CNF) (E : ℕ) (hE : E = (encodeCNF φ).length) :
    ∀ c ∈ callsF E (REN φ), c.1 < c.2.1 ∧ c.2.1 < 3 * (E + 1) := by
  have hI : itemsF φ ≤ E := hE ▸ items_le_encode φ
  have hP : ∀ i, i < (REN φ).length → ∀ j, j ≤ wF (REN φ) i → offF (REN φ) i + j ≤ E := by
    intro i hi j hj
    rw [ren_length] at hi
    have := off_add_le φ i hi
    have hw : wF (REN φ) i = wF φ i := ren_getD_length φ i
    rw [ren_off]; omega
  have hV : ∀ i j, (litF (REN φ) i j).1 ≤ E := fun i j => (ren_var_le φ i j).trans hI
  intro c hc
  simp only [callsF, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨i, hi, j, hj, hc⟩ | rfl | rfl
  · have hpj := hP i hi j (by omega)
    have hz := hV i j
    rcases hc with (hc | hc) | hc
    · split_ifs at hc <;> simp only [List.mem_singleton] at hc <;> subst hc <;>
        simp only [posF] <;> (try split_ifs) <;> omega
    · simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
      obtain ⟨l, ⟨hl, hjl⟩, rfl⟩ := hc
      have := hP i hi l (by omega)
      simp only [posF]; omega
    · split_ifs at hc
      · simp only [List.mem_singleton] at hc; subst hc
        simp only; omega
      · simp at hc
  · simp only; omega
  · simp only; omega

end PEqualNP.MetaComplexity.Helpers.OwnerLink
