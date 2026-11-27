import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- The tree child follows from the rectangle rigidity argument in L-meta-2225.
-- At the first marked AND, both parents change when line input 7 is added to
-- the singleton point. Each parent has degree at least one in that variable:
-- at a leaf this is immediate, and at any gate a changed output has a changed
-- parent. The marked AND adds the two degrees. Both sum and maximum propagate
-- this bound along its path to the output. The second marked AND gives degree
-- at least two in point input 0 by the same argument. A tree with at most 27
-- gates has at most 28 leaves. The incidence flag (0,0) in L-meta-2225
-- forces degree at most one at one endpoint, a contradiction.
--
-- For the primitive child, cut the one reusable gate out as an additional
-- literal z. Unfold the output cone backwards, stopping at z. Every other
-- gate has at most one reader, so at most 26 binary nodes remain, or 27
-- leaves. With at most one occurrence of z, substituting its two inputs
-- gives at most 28 leaves and preserves the original two marked degrees.
-- The same rectangle rigidity contradiction applies even if some of the
-- repeated reads of z are outside the output cone.
--
-- For two or more occurrences, the signed certificates below exclude the
-- compressed formula. Each of the first 21 boundary assignments is an
-- incidence and each of the last 37 is a maximal independent set. Rows and
-- columns are indexed from zero. The following 14 decimal words describe
-- the chart: bit t of word i is the value of input i on assignment t.
-- 95229015649943559 63038587666488 256462815680 4292497062759936
-- 8521481482240 14003410187812864 55389823207997440 189297016294081033
-- 288160007407550752 270286071508633728 229736628138025984 183565875465490436
-- 218994303132270608 155696362464477250
--
-- For each test matrix, let r be the cap for a raw literal, and r-d the cap
-- for z. For a literal v and any subset A of rows where v is true, sum
-- max(0, sum over i in A of W[i,j]) over the columns j where v is false.
-- The largest such sum bounds the mass of every rectangle for that literal.
-- At an OR node partition the positive rows by an accepting child. At an
-- AND node partition the negative columns by a rejecting child. The leaf
-- rectangles partition the full matrix. Its mass is therefore at most
-- 27r-2d. Each matrix has mass strictly exceeding that bound. Incidence
-- symmetry, including point-line duality, leaves three unordered pair
-- types represented by input 0 paired with 1, 7, or 12.
--
-- The following sparse matrices are given row by row. Each pair is
-- column=weight, with all omitted entries zero.
--
-- Input 0 AND input 1. Raw cap 3, seed cap 0, total mass 84.
-- 0 | 2=-1 3=1 8=1 23=1 24=-1 28=1 31=1 32=1
-- 1 | 2=1 3=1 8=-1 10=-1 14=1 24=1 25=1 35=1
-- 2 | 3=-1 8=1 10=1 17=1 24=1 31=2 32=-1
-- 3 | 1=1 2=1 21=1 23=1 24=1 27=-1 28=-1 34=1
-- 4 | 1=-1 2=1 4=1 15=1 21=1 22=1 28=1 34=-1
-- 5 | 4=-1 7=1 17=1 21=-1 24=1 27=1 28=1 34=1
-- 6 | 2=1 8=1 10=1 14=1 24=1 25=-1 30=1 34=-1
-- 7 | 1=1 2=-1 4=1 16=1 17=1 24=1 30=-1 34=1
-- 8 | 4=1 7=1 16=1 17=-1 24=-1 25=1 30=1 34=1
-- 9 | 1=1 2=1 23=-1 27=1 28=1 31=-1 32=1 34=1
-- 10 | 6=1 17=-1 23=1 25=1 30=1 31=1 32=1 34=-1
-- 11 | 1=-1 2=1 4=1 17=1 23=1 30=1 32=-1 34=1
-- 12 | 3=1 7=1 16=1 17=1 21=1 30=1 31=-2
-- 13 | 6=1 16=1 17=1 21=1 25=-1 30=-1 31=2
-- 14 | 4=1 7=-1 16=-1 17=1 21=1 25=1 30=1 31=1
-- 15 | 1=1 2=1 4=1 15=-1 16=1 21=1 22=-1 32=1
-- 16 | 3=1 15=1 16=1 17=-1 21=-1 22=1 31=1 32=1
-- 17 | 1=1 2=1 4=-1 16=-1 17=1 21=1 22=1 32=1
-- 18 | 2=1 8=1 14=-1 21=1 25=1 32=1 34=1 35=-1
-- 19 | 1=1 2=-1 6=1 14=1 21=1 22=1 32=-1 34=1
-- 20 | 6=-1 14=1 17=1 21=-1 25=1 32=1 34=1 35=1
--
-- Input 0 OR input 1. Raw cap 84, seed cap 0, total mass 2184.
-- 0 | 2=-21 4=1 17=21 33=40
-- 1 | 2=30 7=-48 11=28 14=8 19=54 33=48
-- 2 | 2=-30 7=48 11=24 19=-6 20=12 24=36 28=12 35=36
-- 3 | 2=21 4=-1 17=20 24=43 33=-40
-- 4 | 4=52 13=56 14=32 22=28 25=-19 33=-14
-- 5 | 4=-51 11=18 19=33 24=33 25=19 33=65
-- 6 | 2=20 7=36 11=28 14=20 19=33 27=31 33=-64
-- 7 | 2=-20 7=12 12=41 14=1 16=30 19=51 27=-31 28=-2 33=33
-- 8 | 4=51 10=15 11=18 19=-51 27=31 28=2 33=51
-- 9 | 1=16 2=21 4=1 12=41 17=-21 18=2 21=23 24=-43 27=42 32=2
-- 10 | 1=-16 4=25 12=41 17=-20 18=-2 21=-23 24=43 25=18 29=18 30=23
-- 11 | 2=10 7=12 12=-41 17=41 21=23 24=20 27=31 28=31 32=-2
-- 12 | 2=30 7=6 10=15 11=-24 19=6 20=12 21=18 24=33 29=30 31=-30 35=-6
-- 13 | 0=3 4=25 5=3 11=36 17=20 18=2 21=28 24=18 25=-18 29=-30 31=30
-- 14 | 4=33 10=-15 11=-18 19=51 24=-33 25=18 29=30 31=30 35=6
-- 15 | 13=28 14=1 16=12 22=-28 25=19 28=41 34=-14 35=30
-- 16 | 2=30 7=12 11=24 16=30 20=-12 22=28 28=-12 31=30 34=14 35=-30
-- 17 | 2=20 7=-12 12=41 14=-1 16=-30 20=12 22=28 27=21 28=-29 32=2 34=14 35=30
-- 18 | 7=48 11=-28 13=56 14=-28 21=5 30=23 33=36
-- 19 | 4=25 5=3 13=-56 14=28 21=5 22=5 25=51 30=23 33=14 34=14
-- 20 | 1=16 4=-25 5=-3 11=28 13=28 14=28 17=20 21=-5 25=18 29=30 30=-23
--
-- Input 0 AND input 7. Raw cap 4, seed cap 0, total mass 108.
-- 1 | 2=2 4=1 7=-2 11=1 23=1 24=2 25=1
-- 2 | 2=-2 7=2 24=2 31=2 33=2
-- 3 | 1=1 5=1 9=2 18=1 24=2 28=-2 32=1
-- 4 | 1=-1 2=1 5=1 10=1 22=2 24=1 28=2 32=-1 33=-1
-- 5 | 5=-1 10=-1 15=1 18=-1 19=2 24=1 28=2 32=1 33=1
-- 6 | 2=1 4=1 7=2 16=1 19=2 23=-1 25=-1 30=1 34=-1
-- 7 | 2=-1 10=2 11=1 12=1 19=2 23=1 26=-1 30=-1 34=1
-- 8 | 5=1 10=1 12=1 15=1 19=-2 25=1 26=1 30=1 34=1
-- 9 | 5=1 7=2 12=1 24=-2 26=1 28=2 34=1
-- 10 | 5=-1 6=2 11=1 12=1 17=-1 24=2 29=1 30=1 34=-1
-- 11 | 2=1 10=2 11=-1 12=-1 17=1 24=2 26=-1 30=1 34=1
-- 12 | 2=2 15=1 20=2 24=1 29=1 30=1 31=-2
-- 13 | 5=1 6=2 12=1 17=1 24=1 29=-1 30=-1 31=2 33=-1
-- 14 | 5=1 12=-1 15=-1 18=1 19=2 24=-1 29=1 31=2 33=1
-- 15 | 1=1 2=1 10=2 20=2 22=-2 31=1 32=1
-- 16 | 2=2 10=2 20=-2 22=2 31=2 33=-2
-- 17 | 2=1 10=-2 11=1 22=2 26=2 33=2
-- 18 | 2=1 4=-1 6=2 7=2 11=-1 16=-1 24=1 25=1 34=1
-- 19 | 1=1 2=-1 4=1 6=2 16=1 22=2 24=-1 31=-1 33=1
-- 20 | 6=-2 11=1 16=1 17=1 24=1 29=1 31=1 33=1 34=1
--
-- Input 0 OR input 7. Raw cap 4, seed cap 0, total mass 110.
-- 0 | 0=-2 1=2 8=2 20=2 23=2 36=-2
-- 1 | 3=2 8=-2 14=1 17=1 33=1 35=1 36=2
-- 2 | 1=-2 3=-2 8=2 20=2 31=2 36=2
-- 3 | 0=2 5=2 20=-2 23=2 26=2 28=-2
-- 4 | 5=2 13=2 20=2 24=2 26=-2
-- 5 | 5=-2 11=1 19=1 23=1 24=1 26=2 28=2
-- 6 | 6=1 8=2 14=1 16=1 17=-1 19=1 27=2 33=-1 34=-1
-- 7 | 10=2 15=2 17=1 19=1 23=1 27=-2 34=1
-- 8 | 5=2 6=-1 10=1 11=1 19=-1 23=-1 27=2 33=1 34=1
-- 9 | 0=2 18=2 23=-2 26=2 28=2
-- 10 | 2=1 7=1 15=2 18=-2 23=2 30=2
-- 11 | 10=2 15=-2 18=2 23=2 26=-2 27=2
-- 12 | 3=2 7=1 10=1 20=2 24=1 30=1 31=-2
-- 13 | 2=1 5=1 7=-1 11=1 18=2 24=1 25=-1 30=-1 31=2
-- 14 | 5=2 6=1 10=-1 11=-1 19=1 24=-1 25=1 30=1 31=2
-- 15 | 10=2 13=2 20=2 24=-2 26=2 33=-2
-- 16 | 1=2 10=2 20=-2 24=2 31=2
-- 17 | 10=-2 20=2 26=2 27=2 33=2
-- 18 | 2=1 8=2 13=2 14=-1 16=-1 30=1 33=1 34=1 35=-1
-- 19 | 5=1 13=-2 14=1 26=2 30=1 33=2 35=1
-- 20 | 2=-1 5=-1 7=1 13=2 16=1 18=2 25=1 30=-1 35=1
--
-- Input 0 AND input 12. Raw cap 3, seed cap 0, total mass 84.
-- 0 | 2=-1 3=1 8=1 23=1 24=-1 28=1 31=1 32=1
-- 1 | 2=1 3=1 8=-1 10=-1 14=1 24=1 25=1 35=1
-- 2 | 3=-1 8=1 10=1 17=1 24=1 31=2 32=-1
-- 3 | 1=1 2=1 21=1 23=1 24=1 27=-1 28=-1 34=1
-- 4 | 1=-1 2=1 4=1 15=1 21=1 22=1 28=1 34=-1
-- 5 | 4=-1 7=1 17=1 21=-1 24=1 27=1 28=1 34=1
-- 6 | 2=1 8=1 10=1 14=1 24=1 25=-1 30=1 34=-1
-- 7 | 1=1 2=-1 4=1 16=1 17=1 24=1 30=-1 34=1
-- 8 | 4=1 7=1 16=1 17=-1 24=-1 25=1 30=1 34=1
-- 9 | 1=1 2=1 23=-1 27=1 28=1 31=-1 32=1 34=1
-- 10 | 6=1 17=-1 23=1 25=1 30=1 31=1 32=1 34=-1
-- 11 | 1=-1 2=1 4=1 17=1 23=1 30=1 32=-1 34=1
-- 12 | 3=1 7=1 16=1 17=1 21=1 30=1 31=-2
-- 13 | 6=1 16=1 17=1 21=1 25=-1 30=-1 31=2
-- 14 | 4=1 7=-1 16=-1 17=1 21=1 25=1 30=1 31=1
-- 15 | 1=1 2=1 4=1 15=-1 16=1 21=1 22=-1 32=1
-- 16 | 3=1 15=1 16=1 17=-1 21=-1 22=1 31=1 32=1
-- 17 | 1=1 2=1 4=-1 16=-1 17=1 21=1 22=1 32=1
-- 18 | 2=1 8=1 14=-1 21=1 25=1 32=1 34=1 35=-1
-- 19 | 1=1 2=-1 6=1 14=1 21=1 22=1 32=-1 34=1
-- 20 | 6=-1 14=1 17=1 21=-1 25=1 32=1 34=1 35=1
--
-- Input 0 OR input 12. Raw cap 24, seed cap 4, total mass 654.
-- 0 | 2=-2 6=-4 7=-1 8=2 16=8 20=4 21=12 22=-1 23=10 24=-4 28=10 30=-8 32=2
-- 1 | 6=4 7=-1 8=-4 14=10 16=-12 21=8 22=-1 24=2 26=-2 30=8 32=2 33=10 35=4
-- 2 | 2=-2 8=2 16=12 20=14 21=-12 24=2 26=-2 30=8 31=10 32=-4
-- 3 | 1=2 2=2 5=10 7=1 8=2 11=2 20=-4 22=1 23=10 24=6 26=4 28=-10 32=4
-- 4 | 2=2 5=10 7=1 8=-2 11=8 17=8 20=4 22=1 23=4 25=-8 26=-4 28=10 32=-2 33=-4
-- 5 | 1=-2 5=-10 15=12 22=12 25=8 28=10 32=2 33=4
-- 6 | 3=12 8=2 14=10 16=12 27=12 33=-12
-- 7 | 8=12 10=12 22=12 27=-12 33=12
-- 8 | 1=2 3=-12 5=10 15=12 22=-12 27=12 33=12
-- 9 | 2=1 6=4 7=1 8=12 18=12 23=-10 24=-2 28=10 30=8
-- 10 | 2=2 6=10 13=12 18=-12 23=10 24=2 25=12
-- 11 | 8=-12 10=12 13=-12 18=12 23=10 24=2 27=12
-- 12 | 2=2 7=12 15=12 20=10 21=12 31=-12
-- 13 | 2=2 6=10 7=-12 15=12 18=12 25=-12 31=12
-- 14 | 1=2 3=12 5=10 15=-12 25=12 31=12
-- 15 | 2=2 7=-2 8=-2 10=10 11=8 17=-8 20=14 22=-2 23=-4 24=-2 25=8 26=2 31=4
-- 16 | 2=2 7=2 8=2 10=12 16=2 20=-14 22=2 24=2 26=4 31=12 32=4
-- 17 | 10=-12 13=12 17=8 20=10 22=2 23=4 27=12
-- 18 | 2=6 6=10 7=1 8=4 9=2 14=-10 18=2 22=1 24=2 26=2 32=2 33=12 35=-4
-- 19 | 2=-4 6=10 7=1 11=-8 14=10 17=8 22=1 24=-2 25=8 26=2 31=-4 32=-2 33=4 35=4
-- 20 | 2=-2 6=-10 7=12 11=8 14=10 18=12 31=4 32=2

theorem PEqualNP.Outside.R_meta_1969_744
  (tree : ∀ C : Circuit,
    let R := (C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))
    let W := fun (j : Nat) (u : Fin 14) =>
      (gateAt C j).op = .and ∧ (14+j = C.output ∨ InCone 14 C j (C.output-14)) ∧
      gateVal 14 C j (pairInput 0 7) = true ∧
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput u u) = false
    C.size ≤ 27 →
    (∀ j (g : Gate), C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    R.Nodup → ∀ j k : Nat, j ≠ k → ¬ InCone 14 C j k → ¬ InCone 14 C k j → W j 0 → W k 7 → False)
  (primitive : ∀ C : Circuit,
    let R := (C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))
    let P := fun j : Nat => j < C.gates.length ∧ (∀ u ∈ (gateAt C j).inputs, u < 14) ∧ (R.filter (fun w => w != 14+j)).Nodup
    let W := fun (j : Nat) (u : Fin 14) =>
      (gateAt C j).op = .and ∧ (14+j = C.output ∨ InCone 14 C j (C.output-14)) ∧
      gateVal 14 C j (pairInput 0 7) = true ∧
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput u u) = false
    C.size ≤ 27 →
    (∀ j (g : Gate), C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    ¬ R.Nodup → (∃ j, P j) → ∀ j k : Nat, j ≠ k → ¬ InCone 14 C j k → ¬ InCone 14 C k j → W j 0 → W k 7 → False)
  (residual : ∀ C : Circuit,
    let R := (C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))
    let P := fun j : Nat => j < C.gates.length ∧ (∀ u ∈ (gateAt C j).inputs, u < 14) ∧ (R.filter (fun w => w != 14+j)).Nodup
    let W := fun (j : Nat) (u : Fin 14) =>
      (gateAt C j).op = .and ∧ (14+j = C.output ∨ InCone 14 C j (C.output-14)) ∧
      gateVal 14 C j (pairInput 0 7) = true ∧
      ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput u u) = false
    C.size ≤ 27 →
    (∀ j (g : Gate), C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    ¬ R.Nodup → (¬ ∃ j, P j) → ∀ j k : Nat, j ≠ k → ¬ InCone 14 C j k → ¬ InCone 14 C k j → W j 0 → W k 7 → False) :
  ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 ≠ x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  rintro ⟨C,size,shape,correct,j,k,diff,notjk,notkj,ja,jl,jv,jo,ka,kl,kv,ko⟩
  let R := (C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))
  let P := fun j : Nat => j < C.gates.length ∧ (∀ u ∈ (gateAt C j).inputs, u < 14) ∧ (R.filter (fun w => w != 14+j)).Nodup
  by_cases ht : R.Nodup
  · exact tree C size shape correct ht j k diff notjk notkj ⟨ja,jl,jv,jo⟩ ⟨ka,kl,kv,ko⟩
  by_cases hp : ∃ j, P j
  · exact primitive C size shape correct ht hp j k diff notjk notkj ⟨ja,jl,jv,jo⟩ ⟨ka,kl,kv,ko⟩
  · exact residual C size shape correct ht hp j k diff notjk notkj ⟨ja,jl,jv,jo⟩ ⟨ka,kl,kv,ko⟩
