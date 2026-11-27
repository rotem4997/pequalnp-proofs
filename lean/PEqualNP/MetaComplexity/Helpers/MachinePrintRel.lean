import PEqualNP.Defs.MetaComplexityCoverCircuit
import PEqualNP.Defs.MetaComplexityLgp

/-!
# The cover circuit as a list of relative gates

Helper module (proofs only, no statement may use it).

A relative gate is a bit (OR if true, AND if false) and two references, each an absolute wire
`inl a` or a backward distance `inr d`. Every block of `coverCircuitB` reads only inputs and
backward distances: the OR chain reads the previous gate (distance 1), the AND reads the owner
and the previous gate (or the first entry when the list has one entry), the joining OR reads
the last gate of the blocks before (distance: the number of gates of the block plus one, which
is the number of entries of the tuple) and the AND (distance 1). `relGates` lists them;
`relocL` resolves them; `relocL_relGates` says the result is `coverGatesB`.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev RG : Type := Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)

/-- The code of the input of D02. -/
def d02enc (p : ℕ × List RG) : List Bool :=
  (List.replicate p.1 true ++ [false]) ++ PEqualNP.CircuitLowerBounds.encodeList (fun g : Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) => g.1 :: (Sum.elim (fun a : ℕ => false :: (List.replicate a true ++ [false])) (fun d : ℕ => true :: (List.replicate d true ++ [false])) g.2.1 ++ Sum.elim (fun a : ℕ => false :: (List.replicate a true ++ [false])) (fun d : ℕ => true :: (List.replicate d true ++ [false])) g.2.2)) p.2

/-- The function of D02. -/
def d02f (p : ℕ × List RG) : ℕ × Circuit :=
  (p.1, PEqualNP.CircuitLowerBounds.Circuit.mk ((List.range p.2.length).map (fun j : ℕ => PEqualNP.CircuitLowerBounds.Gate.mk (if (p.2.getD j (false, Sum.inl 0, Sum.inl 0)).1 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and) [Sum.elim (fun a : ℕ => a) (fun d : ℕ => p.1 + j - d) (p.2.getD j (false, Sum.inl 0, Sum.inl 0)).2.1, Sum.elim (fun a : ℕ => a) (fun d : ℕ => p.1 + j - d) (p.2.getD j (false, Sum.inl 0, Sum.inl 0)).2.2])) (p.1 + p.2.length - 1))

/-- One relative gate resolved at absolute index `B`. -/
def relocG (B : ℕ) (g : RG) : Gate :=
  ⟨if g.1 then GateOp.or else GateOp.and,
    [Sum.elim (fun a : ℕ => a) (fun d : ℕ => B - d) g.2.1,
      Sum.elim (fun a : ℕ => a) (fun d : ℕ => B - d) g.2.2]⟩

/-- A list of relative gates resolved from absolute index `B` on. -/
def relocL : ℕ → List RG → List Gate
  | _, [] => []
  | B, g :: L => relocG B g :: relocL (B + 1) L

theorem relocL_length : ∀ (B : ℕ) (L : List RG), (relocL B L).length = L.length
  | _, [] => rfl
  | B, _ :: L => by simp [relocL, relocL_length (B + 1) L]

theorem relocL_append : ∀ (B : ℕ) (A C : List RG),
    relocL B (A ++ C) = relocL B A ++ relocL (B + A.length) C
  | _, [], C => by simp [relocL]
  | B, g :: A, C => by
    simp only [List.cons_append, relocL, List.length_cons]
    rw [relocL_append (B + 1) A C]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem relocL_getElem : ∀ (B : ℕ) (L : List RG) (i : ℕ) (h : i < (relocL B L).length),
    (relocL B L)[i] = relocG (B + i) (L[i]'(by rw [relocL_length] at h; exact h))
  | _, [], i, h => by simp [relocL] at h
  | B, g :: L, 0, _ => by simp [relocL]
  | B, g :: L, i + 1, h => by
    simp only [relocL, List.getElem_cons_succ]
    rw [relocL_getElem (B + 1) L i]
    congr 1; omega

theorem range_eq_relocL (B : ℕ) (L : List RG) :
    (List.range L.length).map (fun j : ℕ => relocG (B + j) (L.getD j (false, Sum.inl 0, Sum.inl 0)))
      = relocL B L := by
  apply List.ext_getElem
  · simp [relocL_length]
  · intro i h1 h2
    rw [relocL_getElem]
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < L.length := by simpa using h1
    rw [List.getD_eq_getElem _ _ hi]

theorem d02f_eq (p : ℕ × List RG) : d02f p = (p.1, ⟨relocL p.1 p.2, p.1 + p.2.length - 1⟩) := by
  rw [← range_eq_relocL]
  rfl

/-! ## The relative gates of the blocks -/

/-- The OR chain of a block with first entry `v1` and further entries `rest`. -/
def chainG (v1 : ℕ) : List ℕ → List RG
  | [] => []
  | x :: xs => (true, Sum.inl v1, Sum.inl x) :: xs.map (fun y => (true, Sum.inr 1, Sum.inl y))

/-- The relative gates of the block of one tuple (owner, then its list). -/
def relBlock (lead : Bool) : List ℕ → List RG
  | t :: v1 :: rest =>
      chainG v1 rest ++ (false, Sum.inl t, if rest = [] then Sum.inl v1 else Sum.inr 1) ::
        (if lead then [] else [(true, Sum.inr (rest.length + 2), Sum.inr 1)])
  | _ => []

/-- The relative gates of all blocks. -/
def relGates : Bool → List (List ℕ) → List RG
  | _, [] => []
  | lead, l :: ls => relBlock lead l ++ relGates (lead && decide (l.length < 2)) ls

theorem chainG_length (v1 : ℕ) (rest : List ℕ) : (chainG v1 rest).length = rest.length := by
  cases rest <;> simp [chainG]

theorem chainG_getElem (v1 : ℕ) (rest : List ℕ) (i : ℕ) (h : i < (chainG v1 rest).length) :
    (chainG v1 rest)[i] = (true, (if i = 0 then Sum.inl v1 else Sum.inr 1),
      Sum.inl (rest[i]'(by rw [chainG_length] at h; exact h))) := by
  cases rest with
  | nil => simp [chainG] at h
  | cons x xs =>
    cases i with
    | zero => simp [chainG]
    | succ i => simp [chainG]

theorem relocL_chainG (B v1 : ℕ) (rest : List ℕ) :
    relocL B (chainG v1 rest) = (List.range rest.length).map (fun i =>
      (⟨GateOp.or, [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0,
        rest.getD i 0]⟩ : Gate)) := by
  apply List.ext_getElem
  · simp [relocL_length, chainG_length]
  · intro i h1 h2
    rw [relocL_getElem, List.getElem_map, List.getElem_range]
    have hi : i < rest.length := by simpa using h2
    simp only [chainG_getElem, relocG, if_true]
    rw [List.getD_eq_getElem _ _ hi]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.succ_ne_zero, if_false, Sum.elim_inr, Sum.elim_inl, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range]
      congr 2

theorem relocL_relBlock (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : lead = false → a + 1 = B) :
    relocL B (relBlock lead (t :: v1 :: rest)) = blockGates B a t v1 rest lead := by
  simp only [relBlock, blockGates]
  rw [relocL_append, relocL_chainG, chainG_length]
  congr 1
  simp only [relocL]
  congr 1
  · simp only [relocG, Bool.false_eq_true, if_false, Sum.elim_inl]
    congr 2
    cases rest with
    | nil => simp
    | cons x xs =>
      simp only [reduceCtorEq, if_false, Sum.elim_inr, List.length_cons, List.getD_cons_succ]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp only [List.getElem_map, List.getElem_range]
      simp only [Nat.add_succ_sub_one]
  · cases lead with
    | true => rfl
    | false =>
      have := ha rfl
      simp only [Bool.false_eq_true, if_false, relocL, relocG, if_true, Sum.elim_inr]
      congr 3 <;> omega

theorem relBlock_ne (t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    0 < (relBlock lead (t :: v1 :: rest)).length := by
  simp [relBlock]

theorem relocL_relGates : ∀ (ls : List (List ℕ)) (B a : ℕ) (lead : Bool),
    (lead = false → a + 1 = B) →
      relocL B (relGates lead ls) = coverGatesB B lead a (ls.map (fun l => (l.headD 0, l.tail)))
  | [], _, _, _, _ => rfl
  | [] :: ls, B, a, lead, ha => by
    simp only [relGates, relBlock, List.nil_append, List.length_nil, Nat.ofNat_pos,
      decide_true, Bool.and_true, List.map_cons, List.headD_nil, List.tail_nil, coverGatesB]
    exact relocL_relGates ls B a lead ha
  | [t] :: ls, B, a, lead, ha => by
    simp only [relGates, relBlock, List.nil_append, List.length_singleton, Nat.one_lt_ofNat,
      decide_true, Bool.and_true, List.map_cons, List.headD_cons, List.tail_cons, coverGatesB]
    exact relocL_relGates ls B a lead ha
  | (t :: v1 :: rest) :: ls, B, a, lead, ha => by
    simp only [relGates, List.map_cons, List.headD_cons, List.tail_cons, coverGatesB]
    rw [relocL_append, relocL_relBlock B a t v1 rest lead ha]
    have hl : (relBlock lead (t :: v1 :: rest)).length = (blockGates B a t v1 rest lead).length := by
      rw [← relocL_relBlock B a t v1 rest lead ha, relocL_length]
    have hpos := relBlock_ne t v1 rest lead
    have hd : (lead && decide ((t :: v1 :: rest).length < 2)) = false := by simp
    rw [hd, relocL_relGates ls _ (B + (blockGates B a t v1 rest lead).length - 1) false
      (fun _ => by omega), hl]

/-! ## The empty case -/

/-- The repair of the output wire when there is no gate: `n - 1` becomes `n`. -/
def fixf (q : ℕ × Circuit) : ℕ × Circuit :=
  if q.2.gates = [] ∧ 0 < q.1 then (q.1, ⟨[], q.2.output + 1⟩) else q

theorem fixf_d02f (n : ℕ) (ls : List (List ℕ)) :
    fixf (d02f (n, relGates true ls)) =
      (n, coverCircuitB n (ls.map (fun l => (l.headD 0, l.tail)))) := by
  rw [d02f_eq]
  have hG := relocL_relGates ls n 0 true (fun h => absurd h (by simp))
  simp only at hG ⊢
  rw [hG]
  have hlen : (relGates true ls).length = (coverGatesB n true 0
      (ls.map (fun l => (l.headD 0, l.tail)))).length := by
    rw [← hG, relocL_length]
  rw [hlen]
  unfold coverCircuitB fixf
  by_cases he : coverGatesB n true 0 (ls.map (fun l => (l.headD 0, l.tail))) = []
  · rw [if_pos he]
    simp only [he, List.length_nil, Nat.add_zero, true_and]
    by_cases hn : 0 < n
    · rw [if_pos hn]; congr 2; omega
    · rw [if_neg hn]; congr 2; omega
  · rw [if_neg he, if_neg (fun h => he h.1)]

end PEqualNP.MetaComplexity.Helpers.MachinePrint
