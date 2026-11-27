import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.FoldProg
import PEqualNP.MetaComplexity.Helpers.LiftFix

/-!
# Redirecting or zeroing operands of an `IsAO2` circuit

`ρ i b` is the new source of operand `b` of gate `i` (`srcOf n w` keeps wire `w`, `none` is the constant
false). The gates outside `K` are dropped. `redirect_lt`: if at every input where `F` is false some
super-solution of the rewired gate equations is false at the output, and at every edge some sub-solution is
true there, and some gate is dropped or zeroed, then `F` has a strictly smaller `IsAO2` circuit.
`super_of_le`: the old gate values are a super-solution where every new operand is at most the old one.
`adj_of_AO`: a circuit computing `F` with a gate in the output cone has an edge.
-/

namespace PEqualNP.MetaComplexity.FoldProg

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

/-- Wire `w` as a source. -/
def srcOf (n w : ℕ) : Src n ℕ := if h : w < n then some (Sum.inl ⟨w, h⟩) else some (Sum.inr (w - n))

theorem srcOf_inr (w j : ℕ) (h : srcOf n w = some (Sum.inr j)) : w = n + j := by
  unfold srcOf at h
  split_ifs at h with hw
  · simp at h
  · simp only [Option.some.injEq, Sum.inr.injEq] at h
    omega

/-- Is the operation AND? -/
def isA : GateOp → Bool
  | GateOp.and => true
  | _ => false

/-- The program of `C` with operands rewired by `ρ`. -/
def progOf (C : Circuit) (ρ : ℕ → Fin 2 → Src n ℕ) : Prog n ℕ :=
  ⟨fun i => isA (gateAt C i).op, ρ⟩

theorem wireVal_lt (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem srcAt_srcOf (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun j => gateVal n C j x) (srcOf n w) = wireVal n C w x := by
  unfold srcOf
  split_ifs with hw
  · exact (wireVal_lt C w hw x).symm
  · show gateVal n C (w - n) x = _
    have : n + (w - n) = w := by omega
    unfold gateVal wireVal
    rw [this]

/-- The gate equation of an `IsAO2` circuit. -/
theorem gate_eq (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n C k x = opv (isA (gateAt C k).op) (wireVal n C (opnd C k 0) x)
      (wireVal n C (opnd C k 1) x) := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hmem : gateAt C k ∈ C.gates := List.mem_of_getElem? hg
  have hlen := hC.2.2 _ hmem
  have hop := hC.1 _ hmem
  have hback := hC.2.1 k hk
  have hsplit : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    have h := List.take_append_drop k C.gates
    rw [List.drop_eq_getElem_cons hk] at h
    have e : C.gates[k] = gateAt C k := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    rw [e] at h
    exact h.symm
  have htake : (C.gates.take k).length = k := by simp; omega
  have hold : ∀ w < n + k, wireVal n C w x = wireVal n ⟨C.gates.take k, 0⟩ w x := by
    intro w hw
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [wires_prefix]
    rw [wires_length, htake]
    simpa using hw
  have hnew : gateVal n C k x = (gateAt C k).op.eval
      ((gateAt C k).inputs.map fun i => wireVal n ⟨C.gates.take k, 0⟩ i x) := by
    rw [← wireVal_new, htake]
    unfold gateVal wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [wires_prefix]
    · simp [List.foldl_append]
    · rw [List.length_append, wires_length, htake, List.length_ofFn]; simp
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := List.length_eq_two.1 hlen
  have hp : p < n + k := hback p (by rw [hpq]; simp)
  have hq : q < n + k := hback q (by rw [hpq]; simp)
  rw [hnew]
  simp only [opnd, hpq, List.map_cons, List.map_nil, ← hold p hp, ← hold q hq]
  rcases hop with h | h <;> simp [h, GateOp.eval, opv, isA]

theorem super_of_le (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ) (hK : ∀ k ∈ K, k < C.gates.length)
    (ρ : ℕ → Fin 2 → Src n ℕ) (x : Fin n → Bool)
    (h : ∀ k ∈ K, ∀ b, srcAt x (fun j => gateVal n C j x) (ρ k b) = true → wireVal n C (opnd C k b) x = true) :
    ∀ k ∈ K, opv ((progOf C ρ).isAnd k) (srcAt x (fun j => gateVal n C j x) (ρ k 0))
      (srcAt x (fun j => gateVal n C j x) (ρ k 1)) = true → gateVal n C k x = true := by
  intro k hk hv
  rw [gate_eq C hC k (hK k hk) x]
  exact opv_mono _ _ _ _ _ (h k hk 0) (h k hk 1) hv

/-- Redirect or zero operands, drop the gates outside `K`: a strictly smaller circuit. -/
theorem redirect_lt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < C.gates.length) (ρ : ℕ → Fin 2 → Src n ℕ)
    (hcl : ∀ k ∈ K, ∀ b : Fin 2, ∀ j : ℕ, ρ k b = some (Sum.inr j) → j ∈ K ∧ j < k)
    (o : Src n ℕ) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K) (hne : ∃ u w, G.Adj u w)
    (hup : ∀ x : Fin n → Bool, graphFun G ∅ x = false → ∃ u : ℕ → Bool,
      (∀ k ∈ K, opv ((progOf C ρ).isAnd k) (srcAt x u (ρ k 0)) (srcAt x u (ρ k 1)) = true → u k = true) ∧
      srcAt x u o = false)
    (hedge : ∀ p q, G.Adj p q → ∃ u : ℕ → Bool,
      (∀ k ∈ K, u k = true → opv ((progOf C ρ).isAnd k) (srcAt (pairInput p q) u (ρ k 0))
        (srcAt (pairInput p q) u (ρ k 1)) = true) ∧ srcAt (pairInput p q) u o = true)
    (hlt : ∃ k < C.gates.length, k ∉ K ∨ ∃ b, ρ k b = none) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hcl' : Closed (progOf C ρ) id K := hcl
  obtain ⟨v, hv⟩ := sol_exists (progOf C ρ) id K hcl'
  have hle' : ∀ x : Fin n → Bool, srcAt x (fun j => v j x) o = true → graphFun G ∅ x = true := by
    intro x hx
    by_contra hF
    obtain ⟨u, hu, huo⟩ := hup x (by simpa using hF)
    have hle := sol_le (progOf C ρ) id K hcl' x (fun i => v i x) u (hv x) hu
    rcases o with _ | (c | j)
    · exact Bool.false_ne_true hx
    · rw [show srcAt x u (some (Sum.inl c)) = x c from rfl] at huo
      rw [show srcAt x (fun j => v j x) (some (Sum.inl c)) = x c from rfl, huo] at hx
      exact absurd hx (by decide)
    · have h := hle j (ho j rfl) hx
      rw [show srcAt x u (some (Sum.inr j)) = u j from rfl, h] at huo
      exact absurd huo (by decide)
  have hedge' : ∀ p q, G.Adj p q → srcAt (pairInput p q) (fun j => v j (pairInput p q)) o = true := by
    intro p q hpq
    obtain ⟨u, hu, huo⟩ := hedge p q hpq
    have hle := le_sol (progOf C ρ) id K hcl' (pairInput p q) (fun i => v i (pairInput p q)) u (hv _) hu
    rcases o with _ | (c | j)
    · exact huo
    · exact huo
    · exact hle j (ho j rfl) huo
  obtain ⟨D, hD, hs, hf⟩ := fold_computes G (progOf C ρ) id v K hcl' hv o ho hne hle' hedge'
  refine ⟨D, hD, lt_of_le_of_lt hs ?_, hf⟩
  obtain ⟨k, hk, hkk⟩ := hlt
  have hsub : kept (progOf C ρ) v K ⊆ (Finset.range C.gates.length).erase k := by
    intro i hi
    obtain ⟨hiK, h0, h1⟩ := Finset.mem_filter.1 hi
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 (hK i hiK)⟩
    rintro rfl
    rcases hkk with h | ⟨b, h⟩
    · exact h hiK
    · have hb : srcAt (fun _ => true) (fun j => v j fun _ => true) (ρ i b) = true := by
        fin_cases b
        · exact h0
        · exact h1
      rw [h] at hb
      exact Bool.false_ne_true hb
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.2 hk), Finset.card_range] at h2
  show _ < C.gates.length
  omega

/-- A circuit for the edge function with an output that exists has an edge to accept. -/
theorem adj_of_AO (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (ho : C.output < n + C.gates.length) : ∃ u w, G.Adj u w := by
  have hall : ∀ m < n + C.gates.length, wireVal n C m (fun _ => true) = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases hmn : m < n
      · rw [wireVal_lt C m hmn]
      · have hk : m - n < C.gates.length := by omega
        have hback := hC.2.1 (m - n) hk
        have hg : C.gates[m - n]? = some (gateAt C (m - n)) := by
          simp [gateAt, List.getD_eq_getElem?_getD, hk]
        have hlen := hC.2.2 _ (List.mem_of_getElem? hg)
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hlen
        have hp := hback p (by rw [hpq]; simp)
        have hq := hback q (by rw [hpq]; simp)
        have e := gate_eq C hC (m - n) hk (fun _ => true)
        have e2 : wireVal n C m (fun _ => true) = gateVal n C (m - n) (fun _ => true) := by
          unfold gateVal wireVal
          rw [show n + (m - n) = m by omega]
        rw [e2, e]
        simp only [opnd, hpq]
        have h0 : wireVal n C p (fun _ => true) = true := ih p (by omega) (by omega)
        have h1 : wireVal n C q (fun _ => true) = true := ih q (by omega) (by omega)
        simp [h0, h1, opv]
  have h := hall C.output ho
  have h' : circuitFun n C (fun _ => true) = true := h
  rw [hF, graphFun_empty] at h'
  obtain ⟨u, w, huw, _⟩ := h'
  exact ⟨u, w, huw⟩

end PEqualNP.MetaComplexity.FoldProg
