import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.TableSearch

/-!
# DRAFT: the exchange lemma for any Boolean function, on the root names

DRAFT statements for builders and readers. Nothing here is a result: the statements `Stmt*`
are `Prop`s, NOT proved. Only the sanity lemmas at the end are proved. The statements use root
names only (`Circuit`, `Gate`, `GateOp`, `Circuit.wires`, `Circuit.size`, `FanInTwo`,
`circuitFun`, `IsMinimalCircuit`); the helper import serves the sanity lemmas only.

Paper source: FULL-PROOF Lemma 4.3 and Corollary 4.4 (lgp assembly). Design notes, with the
tests and the build plan: `notes/exchange/design.md`.

The reader count, written inline. Gate number `q` of `C` (on `n` inputs) READS wire `h` when
`h` is one of its effective inputs (the head only, for a NOT gate: `GateOp.eval` ignores the
rest) and `h < n + q` (the wire exists when the gate is evaluated: a forward index reads
`false`, not `h`). Gates are counted, not occurrences: `AND [h, h]` is one reader.
`C.gates.zipIdx` lists each gate with its position.

The hypothesis `NOT h <= F` is written `(C.wires (List.ofFn x)).getD h false = false →
circuitFun n C x = true`: the value of wire `h` (false if the wire does not exist) is the same
lookup `Circuit.eval` makes for the output.
-/

namespace PEqualNP.MetaComplexity.Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- DRAFT STATEMENT (E1, the exchange as a size statement). For a fan-in-two circuit `C` on
`n` inputs and ANY wire index `h` with `NOT h <= F` (`F` the function of `C`), some fan-in-two
circuit computes `F` with at most `C.size + 2 - r` gates, `r` the number of gates reading `h`,
written without subtraction. No hypothesis that `h` is a gate, exists, or is not the output,
and none that `F` is non-constant: the proof (delete every reader, re-point its reads to the
wire it equals on `{h = 1}`, add `NOT h` and `OR(out, NOT h)`) gives size exactly
`C.size + 2 - r` in every case and never builds a constant. -/
def StmtExchange : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), FanInTwo C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) ≤ C.size + 2

/-- DRAFT STATEMENT (E2, at most two readers). In a minimal circuit, a wire `h` with
`NOT h <= F` is read by at most two gates. Follows from E1 and minimality in two lines. -/
def StmtTwoReaders : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) ≤ 2

/-- DRAFT STATEMENT (E3, the exchange with its shape: what the round rule of the lgp proof
uses in the size-neutral branch). The circuit `D` of E1 can be taken to be: the gates of `C`
that do not read `h`, in order and with their operations (picked by a strictly increasing
`σ`), each with the same value as in `C` wherever `h` is true; then `NOT [h]`; then the output
`OR [o, w]` with `w` the `NOT` gate; and its size is exactly `C.size + 2 - r`. With E1 this
gives the size-neutral branch at `r = 2` in a minimal circuit: `D` is again minimal. -/
def StmtExchangeShape : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), FanInTwo C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    ∃ (D : Circuit) (k : ℕ) (σ : ℕ → ℕ) (o : ℕ),
      FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      k + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) = C.size ∧
      D.gates.length = k + 2 ∧ D.output = n + k + 1 ∧
      D.gates[k]? = some ⟨GateOp.not, [h]⟩ ∧
      D.gates[k + 1]? = some ⟨GateOp.or, [o, n + k]⟩ ∧
      StrictMono σ ∧
      (∀ i, i < k → ∃ g gD, C.gates[σ i]? = some g ∧ D.gates[i]? = some gD ∧
        gD.op = g.op ∧
        ¬ (decide (h < n + σ i) &&
          (match g.op with
           | GateOp.not => g.inputs.take 1
           | _ => g.inputs).contains h) = true ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
          (D.wires (List.ofFn x)).getD (n + i) false =
            (C.wires (List.ofFn x)).getD (n + σ i) false)

/-! ## Sanity lemmas (proved) -/

/-- E1 and E2 are related as claimed: E2 follows from E1 by minimality. -/
theorem twoReaders_of_exchange (hE : StmtExchange) : StmtTwoReaders := by
  intro n C h hmin hcov
  obtain ⟨D, hD, hfun, hsize⟩ := hE n C h hmin.1 hcov
  have := hmin.2 D hD hfun
  omega

/-- NAND of three inputs as AND(AND(x0, x1), x2) and a NOT: wire `3` is `AND(x0, x1)`. -/
def nand3C : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩

/-- The hypothesis is met non-trivially: wire `3` is a gate, not the output, the function is
not constant and is not `NOT h`, and `h` has one reader, an AND gate that is not the output. -/
theorem nand3C_hyp :
    FanInTwo nand3C ∧
    (∀ x : Fin 3 → Bool, (nand3C.wires (List.ofFn x)).getD 3 false = false →
      circuitFun 3 nand3C x = true) ∧
    nand3C.gates.zipIdx.countP (fun p => decide (3 < 3 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 3) = 1 ∧
    3 ≠ nand3C.output ∧
    (∃ x y : Fin 3 → Bool, circuitFun 3 nand3C x ≠ circuitFun 3 nand3C y) ∧
    (∃ x : Fin 3 → Bool, circuitFun 3 nand3C x ≠ !(nand3C.wires (List.ofFn x)).getD 3 false) := by
  refine ⟨?_, by decide, by decide, by decide, ⟨fun _ => true, fun _ => false, by decide⟩,
    ⟨fun i => decide (i ≠ 2), by decide⟩⟩
  intro g hg
  simp only [nand3C, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

open PEqualNP.MetaComplexity.Helpers.TableSearch in
/-- `nand3C` is minimal: the table search of depth two from the input tables `170, 204, 240`
never meets the table `127` of NAND. -/
theorem nand3C_minimal : IsMinimalCircuit 3 nand3C := by
  have hlow : ¬ HasCircuitSize 3 (circuitFun 3 nand3C) 2 := by
    apply lower_of_search 3 8 _ [170, 204, 240] 127 2 (by norm_num) _ (by decide +kernel)
    have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
        = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
        circuitFun 3 nand3C (fun i => p.testBit i) = Nat.testBit 127 p := by decide
    exact fun p hp => ⟨_, key p hp⟩
  refine ⟨nand3C_hyp.1, fun D hD hfun => ?_⟩
  by_contra hlt
  exact hlow ⟨D, hD, by simp [nand3C, Circuit.size] at hlt ⊢; omega,
    fun x => congrFun hfun x⟩

/-- The 7-gate circuit of FULL-PROOF N4 (`neutral-branch.md` 1) on inputs `p, q, r, s, x`
(wires `0` to `4`): `AND(p, x)`, `AND(q, x)`, two NOTs, `OR(NOT(p x), r)`, `OR(NOT(q x), s)`,
their AND. Wire `h = 4` (the input `x`) has two readers. Its minimality (cc = 7) is NOT proved
here: it is the cold read's exhaustive search, see the design notes. -/
def n4C : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [6]⟩,
    ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [9, 10]⟩], 11⟩

/-- On `n4C` the hypothesis holds at `h = 4` and the reader count is two. -/
theorem n4C_hyp :
    (∀ x : Fin 5 → Bool, (n4C.wires (List.ofFn x)).getD 4 false = false →
      circuitFun 5 n4C x = true) ∧
    n4C.gates.zipIdx.countP (fun p => decide (4 < 5 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 4) = 2 := by
  refine ⟨?_, by decide⟩
  decide +kernel

/-- The REJECTED syntactic form of E2: every gate listing `h` is counted (forward listings and
the ignored entries of NOT gates included). It is false: `synC` below. -/
def StmtTwoReadersSyntactic : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    (C.gates.filter fun g => g.inputs.contains h).length ≤ 2

/-- `NOT x1` (listing `x2` second, ignored), `OR(x0, .)`, `AND(x2, .)`, `NOT .` (listing `x2`
second, ignored): a minimal 4-gate circuit of `NOT (x2 AND (x0 OR NOT x1))` where wire `2` has
one reader but is listed by three gates. Found by the exhaustive script (n = 3, 4 gates). -/
def synC : Circuit :=
  ⟨[⟨GateOp.not, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5, 2]⟩], 6⟩

open PEqualNP.MetaComplexity.Helpers.TableSearch in
theorem synC_minimal : IsMinimalCircuit 3 synC := by
  have hlow : ¬ HasCircuitSize 3 (circuitFun 3 synC) 3 := by
    apply lower_of_search 3 8 _ [170, 204, 240] 79 3 (by norm_num) _ (by decide +kernel)
    have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
        = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
        circuitFun 3 synC (fun i => p.testBit i) = Nat.testBit 79 p := by decide
    exact fun p hp => ⟨_, key p hp⟩
  refine ⟨?_, fun D hD hfun => ?_⟩
  · intro g hg
    simp only [synC, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · by_contra hlt
    exact hlow ⟨D, hD, by simp [synC, Circuit.size] at hlt ⊢; omega,
      fun x => congrFun hfun x⟩

/-- The syntactic count is refuted. -/
theorem not_twoReadersSyntactic : ¬ StmtTwoReadersSyntactic := by
  intro hS
  have := hS 3 synC 2 synC_minimal (by decide)
  revert this
  decide

/-- On `synC` the semantic count (E2's) of wire `2` is one. -/
theorem synC_semantic :
    synC.gates.zipIdx.countP (fun p => decide (2 < 3 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 2) = 1 := by
  decide

end PEqualNP.MetaComplexity.Exchange
