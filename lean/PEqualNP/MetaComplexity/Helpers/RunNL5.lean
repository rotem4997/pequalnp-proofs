import PEqualNP.MetaComplexity.Helpers.RunNL4

/-!
# Theorem NL, part 5: the wire map backwards, and paths through it

`nl_pre`: the only wires a kept gate `p` sends to the new place of an input or kept gate `b` are
`b` itself and the OR gate `pS` (when `b` is its other operand). `nl_path`: a path of reads from
the OR gate to a wire maps to a path of reads in the new list from the image of the other
operand. `nlFR` is the read relation of the free-input-chain statement.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The read relation of the free-input-chain statement on circuit `C` with `n + 1` inputs. -/
def nlFR (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
    ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨
      (C.gates.get j).op ≠ GateOp.not ∧ a ∈ (C.gates.get j).inputs)

theorem nlIota_lt (n : ℕ) (R : Finset ℕ) (p b : ℕ) (hb : b < n + 1 + p)
    (hbR : n + 1 ≤ b → b - (n + 1) ∉ R) : nlIota n R b < n + 1 + nlCnt R p := by
  unfold nlIota
  split_ifs with h
  · omega
  · have := nlCnt_lt R (hbR (by omega)) (show b - (n + 1) < p by omega); omega

theorem nlIota_inj (n : ℕ) (R : Finset ℕ) (b b' : ℕ) (hbR : n + 1 ≤ b → b - (n + 1) ∉ R)
    (hbR' : n + 1 ≤ b' → b' - (n + 1) ∉ R) (h : nlIota n R b = nlIota n R b') : b = b' := by
  unfold nlIota at h
  split_ifs at h with h1 h2 h2
  · exact h
  · omega
  · omega
  · have := nlCnt_inj R (hbR (by omega)) (hbR' (by omega)) (by omega)
    omega

theorem nlRho_iota (n : ℕ) (gs : List Gate) (R : Finset ℕ) (pm pS p a : ℕ) (ha : a < n + 1 + p)
    (haR : n + 1 ≤ a → a - (n + 1) ∉ R) : nlRho n gs R pm pS p a = nlIota n R a := by
  unfold nlRho nlIota
  by_cases h1 : a < n + 1
  · rw [if_pos h1, if_pos h1]
  · have h3 := haR (by omega)
    rw [if_neg h1, if_pos ha, if_neg h3, if_neg h1]

theorem nlRho_S (n : ℕ) (gs : List Gate) (R : Finset ℕ) (pm pS p s : ℕ) (hp : pS < p)
    (hR : pS ∈ R) (hs : nlSo n gs pm pS = some s) :
    nlRho n gs R pm pS p (n + 1 + pS) = nlIota n R s := by
  unfold nlRho
  rw [if_neg (by omega), if_pos (by omega), if_pos (by simpa using hR), if_pos rfl, hs]

/-- A gate keeps its reads through a wire map. -/
theorem nlRel_map (g : Gate) (r : ℕ → ℕ) (a : ℕ) (h : nlRel g a) :
    nlRel ⟨g.op, g.inputs.map r⟩ (r a) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨h1, ?_⟩
    show (g.inputs.map r).head? = some (r a)
    rw [List.head?_map, h2]; rfl
  · right
    exact ⟨h1, List.mem_map_of_mem h2⟩

theorem nl_two' (l : List ℕ) (hl : l.length ≤ 2) (u v z : ℕ) (hu : u ∈ l) (hv : v ∈ l)
    (huv : u ≠ v) (hz : z ∈ l) : z = u ∨ z = v := by
  by_cases h : z = u
  · exact Or.inl h
  · exact Or.inr (nl_two l hl u z v hu hz hv h (fun h' => huv h'.symm))

section
variable {n : ℕ} {gs : List Gate} {ev pn pm pS : ℕ} {R : Finset ℕ}
  (hN : nlState n gs ev pn pm pS) (hR : nlRSpec n gs pn pm pS R)
include hN hR

/-- The wires sent to the new place of an input or kept gate `b`. -/
theorem nl_pre (p a b : ℕ) (hb : b < n + 1 + p) (hbR : n + 1 ≤ b → b - (n + 1) ∉ R)
    (h : nlRho n gs R pm pS p a = nlIota n R b) :
    a = b ∨ (a = n + 1 + pS ∧ pS < p ∧ nlSo n gs pm pS = some b) := by
  have hlt := nlIota_lt n R p b hb hbR
  unfold nlRho at h
  by_cases h1 : a < n + 1
  · rw [if_pos h1] at h
    left
    apply nlIota_inj n R a b (by omega) hbR
    unfold nlIota; rw [if_pos h1]; exact h
  · rw [if_neg h1] at h
    by_cases h2 : a < n + 1 + p
    · rw [if_pos h2] at h
      by_cases h3 : a - (n + 1) ∈ R
      · rw [if_pos h3] at h
        by_cases h4 : a = n + 1 + pS
        · rw [if_pos h4] at h
          cases hso : nlSo n gs pm pS with
          | none => rw [hso] at h; simp only at h; omega
          | some s =>
            rw [hso] at h
            simp only at h
            obtain ⟨_, s2, s3⟩ := hN.s_facts hR hso
            have := nlIota_inj n R s b s3 hbR h
            subst this
            exact Or.inr ⟨h4, by omega, rfl⟩
        · rw [if_neg h4] at h; omega
      · rw [if_neg h3] at h
        left
        apply nlIota_inj n R a b (fun _ => h3) hbR
        unfold nlIota; rw [if_neg h1]; exact h
    · rw [if_neg h2] at h; omega

/-- A path of reads from the OR gate maps to a path in the new list. -/
theorem nl_path (o : ℕ) (hRin : pS ∈ R) (hRle : ∀ j ∈ R, j ≤ pS) {s : ℕ}
    (hso : nlSo n gs pm pS = some s) {w : ℕ}
    (h : Relation.TransGen (nlE gs (n + 1)) (n + 1 + pS) w) :
    n + 1 + pS < w ∧ w < n + 1 + gs.length ∧ w - (n + 1) ∉ R ∧
      Relation.TransGen (nlFR n (nlL n gs R pm pS o)) (nlIota n R s) (nlIota n R w) := by
  have key : ∀ j, j < gs.length → pS < j → ∀ u, nlRel (gs.getD j nlG0) u →
      nlFR n (nlL n gs R pm pS o) (nlRho n gs R pm pS j u) (nlIota n R (n + 1 + j)) := by
    intro j hj hjS u hu
    have hjR : j ∉ R := fun h' => by have := hRle j h'; omega
    have hget : (nlL n gs R pm pS o).gates[nlCnt R j]? = some (nlMk n gs R pm pS j) :=
      nlB_get R _ hjR hj
    obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.1 hget
    refine ⟨⟨nlCnt R j, hlt⟩, ?_, ?_⟩
    · unfold nlIota; rw [if_neg (by omega)]; simp
    · have := nlRel_map (gs.getD j nlG0) (nlRho n gs R pm pS j) u hu
      simp only [List.get_eq_getElem]
      rw [hg]
      exact this
  induction h with
  | single h =>
    obtain ⟨j, hj, rfl, hlt, hr⟩ := h
    have hjS : pS < j := by omega
    refine ⟨hlt, by omega, fun h' => by have := hRle _ h'; omega, ?_⟩
    have := key j hj hjS _ hr
    rw [nlRho_S n gs R pm pS j s hjS hRin hso] at this
    exact Relation.TransGen.single this
  | tail _ h ih =>
    obtain ⟨j, hj, rfl, hlt, hr⟩ := h
    obtain ⟨i1, _, i3, i4⟩ := ih
    have hjS : pS < j := by omega
    refine ⟨by omega, by omega, fun h' => by have := hRle _ h'; omega, ?_⟩
    have := key j hj hjS _ hr
    rw [nlRho_iota n gs R pm pS j _ hlt (fun _ => i3)] at this
    exact Relation.TransGen.tail i4 this

end

end PEqualNP.MetaComplexity.Helpers.RunNL
