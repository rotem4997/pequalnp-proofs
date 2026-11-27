import Mathlib
import PEqualNP.Defs

-- A cut of the 21-gate monotone-circuit step into the two things its proof does:
-- SEARCHING for the straight-line program, and PACKAGING a program into the
-- Fin-indexed witness the statement asks for.
--
-- What the eleven constants are.  Read as 40-bit masks they are the 40 rows of an
-- 11-input truth table.  Rows 0 to 15 are the ones the output wire must accept and
-- rows 16 to 39 the ones it must reject, because the output must equal 65535 exactly.
-- Each of rows 0 to 15 has exactly TWO inputs set, so they are 16 two-element sets,
-- an edge set E on 11 vertices:
--   0-9  0-10  1-4  1-8  2-5  2-10  3-6  3-7  4-8  4-10  5-8  5-9  6-7  6-10  7-9  8-9.
-- Each of rows 16 to 39 is independent for E, and in fact those 24 rows are EXACTLY
-- the 24 maximal independent sets of E.  So the function the output wire computes is
-- forced on the nose: it is the edge-detection function of this graph, and every
-- minterm is an edge.  The graph has no four-cycle (no two vertices share two
-- neighbours) and its minimum vertex cover has size 7.
--
-- Why that makes the program hard to find.  A product of two OR-groups is clean (no
-- bit above 15) exactly when every pair it crosses is an edge, so by four-cycle
-- freeness every clean product is a STAR: one centre against a set of its
-- neighbours.  A cover of the 16 edges by k stars costs 16 - k leaf unions, k ANDs
-- and k - 1 final ORs, that is 15 + k gates, and the centres must be a vertex cover,
-- so k >= 7 and the cost is at least 22.  Nor does sharing help: two stars with
-- different centres have leaf sets meeting in at most one vertex, so no union of two
-- or more leaves is ever reusable.  Exhaustive search over every depth-3 form whose
-- products have two or three factors, inner ANDs allowed to be dirty, enumerating
-- the terms by which rows they fire on and covering the 16 rows by an exact DP,
-- gives the same 22; the four-factor forms were not searched.  A 21-gate program
-- therefore has to share sub-ORs across products of three or more groups, or be
-- deeper still, and that is the content of hProgram.
--
-- hProgram is the search half.  It hands over a straight-line program as plain
-- functions on naturals: a length n at most 21, an operation bit, two operand
-- indices that read strictly back, a value table, an output index, and three
-- distinct AND gates whose value exceeds 65535.  It builds nothing Fin-indexed and
-- says nothing about where in 16..39 the surviving bits of those three gates sit.
--
-- hPackage is the half that owes no search.  Given ANY such program over ANY input
-- valuation bounded by 2^40 it must produce the witness: bundle n into Fin 22 and
-- the operands into Fin 33, carry the output index into Fin 33 with 11 + n in range,
-- and - the part that is not bookkeeping - prove by induction along the program that
-- every wire value stays below 2^40, since the inputs do and both bitwise AND and
-- bitwise OR preserve that.  Only then does a wire value above 65535 have a set bit
-- at some position 16 + j with j < 24, which is what Fin 24 demands.  It knows
-- nothing about this graph: drop the three-dirty-AND clause from hProgram and
-- hPackage still cannot be used, and on its own it produces no program at all.
--
-- Neither half gives the step.  hProgram's program is not a witness: it has no
-- Fin 22, no Fin 33, no Fin 24 and no bit index at all.  hPackage applied to
-- nothing gives nothing.

theorem PEqualNP.Outside.R_meta_8610_1
    (hProgram :
      ∀ (c : ℕ → ℕ), (∀ (i : ℕ), i < (11 : ℕ) → c i = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD i (0 : ℕ)) →
      ∃ (n : ℕ) (f : ℕ → Bool) (p : ℕ → ℕ) (q : ℕ → ℕ) (v : ℕ → ℕ) (o : ℕ) (d : Fin (3 : ℕ) → ℕ),
        n ≤ (21 : ℕ) ∧ o < (11 : ℕ) + n ∧ v o = (65535 : ℕ) ∧ (∀ (i : ℕ), i < (11 : ℕ) → v i = c i) ∧ (∀ (g : ℕ), g < n → p g < (11 : ℕ) + g ∧ q g < (11 : ℕ) + g ∧ v ((11 : ℕ) + g) = if f g = Bool.true then v (p g) &&& v (q g) else v (p g) ||| v (q g)) ∧ Function.Injective d ∧ ∀ (j : Fin (3 : ℕ)), d j < n ∧ f (d j) = Bool.true ∧ (65535 : ℕ) < v ((11 : ℕ) + d j))
    (hPackage :
      ∀ (c : ℕ → ℕ) (n : ℕ) (f : ℕ → Bool) (p : ℕ → ℕ) (q : ℕ → ℕ) (v : ℕ → ℕ) (o : ℕ) (d : Fin (3 : ℕ) → ℕ),
      (∀ (i : ℕ), i < (11 : ℕ) → c i < (1099511627776 : ℕ)) →
        (n ≤ (21 : ℕ) ∧ o < (11 : ℕ) + n ∧ v o = (65535 : ℕ) ∧ (∀ (i : ℕ), i < (11 : ℕ) → v i = c i) ∧ (∀ (g : ℕ), g < n → p g < (11 : ℕ) + g ∧ q g < (11 : ℕ) + g ∧ v ((11 : ℕ) + g) = if f g = Bool.true then v (p g) &&& v (q g) else v (p g) ||| v (q g)) ∧ Function.Injective d ∧ ∀ (j : Fin (3 : ℕ)), d j < n ∧ f (d j) = Bool.true ∧ (65535 : ℕ) < v ((11 : ℕ) + d j)) →
      ∃ (x1 : Fin (22 : ℕ)) (x2 : Fin ↑x1 → Bool) (x3 : Fin ↑x1 → Fin (33 : ℕ)) (x4 : Fin ↑x1 → Fin (33 : ℕ)) (x5 : Fin (33 : ℕ)) (x6 : ℕ → ℕ) (x7 : Fin (3 : ℕ) → Fin ↑x1) (x8 : Fin (3 : ℕ) → Fin (24 : ℕ)), ↑x5 < (11 : ℕ) + ↑x1 ∧ x6 ↑x5 = (65535 : ℕ) ∧ (∀ (x9 : Fin (11 : ℕ)), x6 ↑x9 = c ↑x9) ∧ (∀ (x9 : Fin ↑x1), ↑(x3 x9) < (11 : ℕ) + ↑x9 ∧ ↑(x4 x9) < (11 : ℕ) + ↑x9 ∧ x6 ((11 : ℕ) + ↑x9) = if x2 x9 = Bool.true then x6 ↑(x3 x9) &&& x6 ↑(x4 x9) else x6 ↑(x3 x9) ||| x6 ↑(x4 x9)) ∧ Function.Injective x7 ∧ ∀ (x9 : Fin (3 : ℕ)), x2 (x7 x9) = Bool.true ∧ (x6 ((11 : ℕ) + ↑(x7 x9))).testBit ((16 : ℕ) + ↑(x8 x9)) = Bool.true) :
    ∃ (x1 : Fin (22 : ℕ)) (x2 : Fin ↑x1 → Bool) (x3 : Fin ↑x1 → Fin (33 : ℕ)) (x4 : Fin ↑x1 → Fin (33 : ℕ)) (x5 : Fin (33 : ℕ)) (x6 : ℕ → ℕ) (x7 : Fin (3 : ℕ) → Fin ↑x1) (x8 : Fin (3 : ℕ) → Fin (24 : ℕ)), ↑x5 < (11 : ℕ) + ↑x1 ∧ x6 ↑x5 = (65535 : ℕ) ∧ (∀ (x9 : Fin (11 : ℕ)), x6 ↑x9 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x9 (0 : ℕ)) ∧ (∀ (x9 : Fin ↑x1), ↑(x3 x9) < (11 : ℕ) + ↑x9 ∧ ↑(x4 x9) < (11 : ℕ) + ↑x9 ∧ x6 ((11 : ℕ) + ↑x9) = if x2 x9 = Bool.true then x6 ↑(x3 x9) &&& x6 ↑(x4 x9) else x6 ↑(x3 x9) ||| x6 ↑(x4 x9)) ∧ Function.Injective x7 ∧ ∀ (x9 : Fin (3 : ℕ)), x2 (x7 x9) = Bool.true ∧ (x6 ((11 : ℕ) + ↑(x7 x9))).testBit ((16 : ℕ) + ↑(x8 x9)) = Bool.true := by
  have hbnd : ∀ (i : ℕ), i < (11 : ℕ) →
      [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD i (0 : ℕ) < (1099511627776 : ℕ) := by decide
  obtain ⟨n, f, p, q, v, o, d, hn, ho, hout, hin, hgate, hinj, hdirty⟩ :=
    hProgram (fun (i : ℕ) => [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD i (0 : ℕ)) (fun (_ : ℕ) (_ : _) => rfl)
  exact hPackage (fun (i : ℕ) => [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD i (0 : ℕ)) n f p q v o d hbnd
    ⟨hn, ho, hout, hin, hgate, hinj, hdirty⟩
