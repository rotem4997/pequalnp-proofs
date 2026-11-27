import PEqualNP.Library.SearchHelpers.TableauDefs
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.L055

/-!
# Helpers: the initial and final clauses of the tableau formula in polynomial time

Helper module (proofs only, no statement may use it). The encoded initial clauses and the
encoded final clauses of the tableau formula of a fixed micro-instruction code are computable
in polynomial time from the input string, and so is the whole encoded formula once the encoded
step clauses are.

The variable `uvar l` has binary digits `false^a ++ [true]` for each index `a` of `l`, so an
encoded literal is a constant prefix, a unary block `U i` for the one growing index `i`, and a
constant suffix. A family of clauses indexed by `j < N` is written by one loop (`cpt_loop`)
whose state carries the environment, a countdown and the output so far.
-/

namespace PEqualNP.Library.SearchHelpers.Tab

namespace Edge

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

theorem cptE {f f' : List Bool → List Bool} (h : CPTs f) (e : ∀ a, f a = f' a) : CPTs f' := by
  obtain rfl : f = f' := funext e
  exact h

/-! ### The unary block and the digits of a variable -/

/-- The encoded digits `false^a`: `a` times the pair `true, false`. -/
def U (a : ℕ) : List Bool := (List.replicate a true).flatMap fun _ => [true, false]

theorem U_zero : U 0 = [] := rfl

theorem U_succ (a : ℕ) : U (a + 1) = true :: false :: U a := by
  simp [U, List.replicate_succ]

theorem U_add (a b : ℕ) : U (a + b) = U a ++ U b := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, U_succ, U_succ, ih]
    rfl

theorem U_length (a : ℕ) : (U a).length = 2 * a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [U_succ]; simp only [List.length_cons, ih]; omega

theorem bits_pow_mul (a n : ℕ) (hn : n ≠ 0) :
    (2 ^ a * n).bits = List.replicate a false ++ n.bits := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 2 ^ (a + 1) * n = 2 * (2 ^ a * n) := by ring
    have h0 : 2 ^ a * n ≠ 0 := Nat.mul_ne_zero (by positivity) hn
    rw [e, Nat.bit0_bits _ h0, ih, List.replicate_succ, List.cons_append]

/-- The binary digits of a variable: `false^a ++ [true]` for each index `a`. -/
theorem bits_uvar (l : List ℕ) :
    (uvar l).bits = l.flatMap fun a => List.replicate a false ++ [true] := by
  induction l with
  | nil => simp [uvar]
  | cons a r ih =>
    rw [uvar, bits_pow_mul _ _ (by omega), Nat.bit1_bits, ih]
    simp

theorem digits_block (a : ℕ) :
    ((List.replicate a false ++ [true]).flatMap fun d => [true, d]) = U a ++ [true, true] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, List.flatMap_cons, ih, U_succ]
    rfl

theorem encodeLiteral_uvar (l : List ℕ) (pol : Bool) :
    encodeLiteral (uvar l, pol) =
      [true, pol] ++ (l.flatMap fun a => U a ++ [true, true]) ++ [false, true] := by
  have h : ((uvar l).bits.flatMap fun d => [true, d]) = l.flatMap fun a => U a ++ [true, true] := by
    rw [bits_uvar]
    induction l with
    | nil => rfl
    | cons a r ih =>
      rw [List.flatMap_cons, List.flatMap_append, digits_block, ih, List.flatMap_cons]
  simp only [encodeLiteral]
  rw [h]

/-- The constant prefix of an encoded literal: polarity and the indices before the growing one. -/
def lpre (pol : Bool) (pre : List ℕ) : List Bool :=
  [true, pol] ++ pre.flatMap fun a => U a ++ [true, true]

/-- The constant suffix of an encoded literal: the indices after the growing one. -/
def lpost (post : List ℕ) : List Bool :=
  [true, true] ++ (post.flatMap fun a => U a ++ [true, true]) ++ [false, true]

theorem encodeLiteral_split (pol : Bool) (pre : List ℕ) (i : ℕ) (post : List ℕ) :
    encodeLiteral (uvar (pre ++ i :: post), pol) = lpre pol pre ++ (U i ++ lpost post) := by
  rw [encodeLiteral_uvar]
  simp [lpre, lpost, List.flatMap_append, List.flatMap_cons]

theorem encodeClause_single (pol : Bool) (pre : List ℕ) (i : ℕ) (post : List ℕ) :
    encodeClause [(uvar (pre ++ i :: post), pol)] =
      lpre pol pre ++ (U i ++ (lpost post ++ [false, false])) := by
  simp only [encodeClause, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeLiteral_split]
  simp only [List.append_assoc]

theorem encodeCNF_append (a b : CNF) : encodeCNF (a ++ b) = encodeCNF a ++ encodeCNF b := by
  simp [encodeCNF]

theorem encodeCNF_map {ι : Type} (l : List ι) (f : ι → Clause) :
    encodeCNF (l.map f) = l.flatMap fun i => encodeClause (f i) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.flatMap_cons] at ih ⊢
    rw [← ih]
    rfl

theorem flatMap_congr_mem {ι β : Type} (l : List ι) (f g : ι → List β)
    (h : ∀ i ∈ l, f i = g i) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
      ih (fun i hi => h i (by simp [hi]))]

/-! ### Basic polynomial-time pieces -/

/-- The length of a string in unary. -/
theorem cpt_unary {f : List Bool → List Bool} (hf : CPTs f) :
    CPTs (fun x => un (f x).length) := by
  have h : CPTs (fun x : List Bool => un x.length) := by
    refine filterMap_polyTime _ _ _ (fun _ : Bool => some true) ?_
    intro x
    induction x with
    | nil => rfl
    | cons a l ih =>
      simp only [un, List.length_cons, List.replicate_succ, List.filterMap_cons] at ih ⊢
      exact congrArg (List.cons true) ih
  exact cpt_comp (g := fun x : List Bool => un x.length) hf h

/-- The unary block of the length of a string. -/
theorem cpt_U {f : List Bool → List Bool} (hf : CPTs f) : CPTs (fun x => U (f x).length) := by
  have h : CPTs (fun x : List Bool => U x.length) := by
    refine fst2_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true, some false))
      (fun _ => none) () ?_
    intro x
    induction x with
    | nil => rfl
    | cons a l ih =>
      show U (l.length + 1) = _
      rw [U_succ]
      exact congrArg (fun r => true :: false :: r) ih
  exact cpt_comp (g := fun x : List Bool => U x.length) hf h

/-- A constant family of polynomial-time strings, concatenated. -/
theorem cpt_flatMap_const {ι : Type} (l : List ι) (f : ι → List Bool → List Bool)
    (h : ∀ i, CPTs (f i)) : CPTs (fun x => l.flatMap fun i => f i x) := by
  induction l with
  | nil => exact cpt_const []
  | cons a l ih => exact cptE (cpt_app2 (h a) ih) (fun x => by simp)

/-- A constant family of polynomial-time formulas, concatenated. -/
theorem cpt_encFlatMap_const {ι : Type} (l : List ι) (f : ι → List Bool → CNF)
    (h : ∀ i, CPTs (fun x => encodeCNF (f i x))) :
    CPTs (fun x => encodeCNF (l.flatMap fun i => f i x)) := by
  refine cptE (cpt_flatMap_const l (fun i x => encodeCNF (f i x)) h) (fun x => ?_)
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, encodeCNF_append, ih]

/-- A constant family of polynomial-time clauses. -/
theorem cpt_encMap_const {ι : Type} (l : List ι) (f : ι → List Bool → Clause)
    (h : ∀ i, CPTs (fun x => encodeCNF [f i x])) :
    CPTs (fun x => encodeCNF (l.map fun i => f i x)) := by
  refine cptE (cpt_encFlatMap_const l (fun i x => [f i x]) h) (fun x => ?_)
  congr 1
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl

/-! ### The loop -/

/-- One round of the loop. The state is `pairB (pairB e C) (pairB r out)`: the environment `e`,
the full count `C`, the remaining count `r` and the output so far. The round appends the block
of the index `|C| - |r|`. -/
def loopG (blk : List Bool → List Bool) (y : List Bool) : List Bool :=
  pairB (unpairB y).1
    (pairB (unpairB (unpairB y).2).1.tail
      ((unpairB (unpairB y).2).2 ++
        blk (pairB (unpairB (unpairB y).1).1
          ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
            (unpairB (unpairB y).1).2))))

theorem tail_iter (k : ℕ) (l : List Bool) : (fun s : List Bool => s.tail)^[k] l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases l <;> simp

theorem cpt_loopG {blk : List Bool → List Bool} (hblk : CPTs blk) : CPTs (loopG blk) := by
  have h1 : CPTs (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have h21 := cpt_unpairB1_1 h2
  have h22 := cpt_unpairB2_1 h2
  have h11 := cpt_unpairB1_1 h1
  have h12 := cpt_unpairB2_1 h1
  have hJ := cpt_iterLen cpt_tail (fun s => by simp) h21 h12
  exact cpt_pairB2 h1 (cpt_pairB2 (cpt_tail1 h21)
    (cpt_app2 h22 (cpt_comp (cpt_pairB2 h11 hJ) hblk)))

theorem loopG_pair (blk : List Bool → List Bool) (e C r out : List Bool) :
    loopG blk (pairB (pairB e C) (pairB r out)) =
      pairB (pairB e C) (pairB r.tail (out ++ blk (pairB e (C.drop r.length)))) := by
  simp only [loopG, unpairB_pairB, tail_iter]

theorem loopG_iter (blk : List Bool → List Bool) (e : List Bool) (N : ℕ) :
    ∀ i, i ≤ N → (loopG blk)^[i] (pairB (pairB e (un N)) (pairB (un N) [])) =
      pairB (pairB e (un N))
        (pairB (un (N - i)) ((List.range i).flatMap fun j => blk (pairB e (un j)))) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), loopG_pair]
    have e1 : (un (N - i)).tail = un (N - (i + 1)) := by
      simp only [un, List.tail_replicate]
      congr 1
    have e2 : (un N).drop (un (N - i)).length = un i := by
      simp only [un, List.length_replicate, List.drop_replicate]
      congr 1
      omega
    rw [e1, e2, List.range_succ, List.flatMap_append]
    simp

/-- The loop: the blocks of the indices below the length of `cnt x`, in order. The block of the
index `j` is computed from `pairB (env x) (un j)` and must be at most linearly long. -/
theorem cpt_loop {blk : List Bool → List Bool} (hblk : CPTs blk) (a : ℕ)
    (hlen : ∀ s, (blk s).length ≤ a * s.length + a) {env cnt : List Bool → List Bool}
    (henv : CPTs env) (hcnt : CPTs cnt) :
    CPTs (fun x => (List.range (cnt x).length).flatMap fun j => blk (pairB (env x) (un j))) := by
  have hI := cpt_iterB (loopG blk) (cpt_loopG hblk)
    (fun y => a * ((unpairB y).1.length + 1) + a + 2) (2 * a + 2)
    (fun y => by simp only [loopG, unpairB_pairB]; exact le_rfl)
    (fun y => by
      have h1 := unpairB_length y
      have h2 := unpairB_length (unpairB y).2
      have h3 := unpairB_length (unpairB y).1
      have hJ : ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
          (unpairB (unpairB y).1).2).length ≤ (unpairB (unpairB y).1).2.length :=
        iter_length _ (fun s => by simp) _ _
      have hb := hlen (pairB (unpairB (unpairB y).1).1
        ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
          (unpairB (unpairB y).1).2))
      rw [pairB_length] at hb
      have hb' := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left a
        (show 2 * (unpairB (unpairB y).1).1.length +
          ((fun s : List Bool => s.tail)^[(unpairB (unpairB y).2).1.length]
            (unpairB (unpairB y).1).2).length + 1 ≤ (unpairB y).1.length + 1 by omega)) a)
      simp only [loopG, pairB_length, List.length_append, List.length_tail]
      omega)
    (fun y => by
      have h1 := unpairB_length y
      have h4 : a * ((unpairB y).1.length + 1) ≤ a * (y.length + 1) :=
        Nat.mul_le_mul_left a (by omega)
      have h5 : (2 * a + 2) * y.length = 2 * (a * y.length) + 2 * y.length := by ring
      have h6 : a * (y.length + 1) = a * y.length + a := by ring
      omega)
  have hC := cpt_unary hcnt
  have hin : CPTs (fun x => pairB (pairB (pairB (env x) (un (cnt x).length))
      (pairB (un (cnt x).length) [])) (un (cnt x).length)) :=
    cpt_pairB2 (cpt_pairB2 (cpt_pairB2 henv hC) (cpt_pairB2 hC (cpt_const []))) hC
  have hout := cpt_unpairB2_1 (cpt_unpairB2_1 (cpt_comp hin hI))
  refine cptE hout (fun x => ?_)
  simp only [unpairB_pairB]
  rw [show (un (cnt x).length).length = (cnt x).length by simp [un],
    loopG_iter blk (env x) (cnt x).length _ le_rfl]
  simp only [unpairB_pairB]

/-! ### Clause templates -/

/-- A literal template: polarity, the indices before the growing one, a constant added to the
growing index, and the indices after it. -/
structure LitT where
  pol : Bool
  pre : List ℕ
  ex : ℕ
  post : List ℕ

/-- The literal of a template at the growing index `i`. -/
def LitT.lit (lt : LitT) (i : ℕ) : Literal := (uvar (lt.pre ++ (i + lt.ex) :: lt.post), lt.pol)

/-- The encoded literal of a template, the growing index given by two strings. -/
def lblk (lt : LitT) (s : List Bool) : List Bool :=
  lpre lt.pol lt.pre ++ (U (unpairB s).1.length ++ (U (unpairB s).2.length ++
    (U lt.ex ++ lpost lt.post)))

/-- The encoded clause of a clause template. -/
def tblk (tm : List LitT) (s : List Bool) : List Bool :=
  (tm.flatMap fun lt => lblk lt s) ++ [false, false]

theorem cpt_tblk (tm : List LitT) : CPTs (tblk tm) := by
  have h : ∀ lt : LitT, CPTs (lblk lt) := fun lt =>
    cpt_app2 (cpt_const _) (cpt_app2 (cpt_U cpt_unpairB1)
      (cpt_app2 (cpt_U cpt_unpairB2) (cpt_const _)))
  exact cpt_app2 (cpt_flatMap_const tm lblk h) (cpt_const _)

theorem tblk_length (tm : List LitT) : ∃ a, ∀ s, (tblk tm s).length ≤ a * s.length + a := by
  have h : ∃ a, ∀ s, (tm.flatMap fun lt => lblk lt s).length ≤ a * s.length + a := by
    induction tm with
    | nil => exact ⟨0, fun s => by simp⟩
    | cons lt tm ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + ((lpre lt.pol lt.pre).length + 2 * lt.ex + (lpost lt.post).length + 2),
        fun s => ?_⟩
      have h1 := ha s
      have h2 := unpairB_length s
      have h3 : 2 * s.length ≤
          ((lpre lt.pol lt.pre).length + 2 * lt.ex + (lpost lt.post).length + 2) * s.length :=
        Nat.mul_le_mul_right _ (by omega)
      have h4 : (lblk lt s).length = (lpre lt.pol lt.pre).length +
          (2 * (unpairB s).1.length + (2 * (unpairB s).2.length +
            (2 * lt.ex + (lpost lt.post).length))) := by
        simp only [lblk, List.length_append, U_length]
      simp only [List.flatMap_cons, List.length_append]
      rw [Nat.add_mul]
      omega
  obtain ⟨a, ha⟩ := h
  refine ⟨a + 2, fun s => ?_⟩
  have h1 := ha s
  simp only [tblk, List.length_append, List.length_cons, List.length_nil]
  rw [Nat.add_mul]
  omega

theorem tblk_spec (tm : List LitT) (e : List Bool) (j : ℕ) :
    tblk tm (pairB e (un j)) = encodeClause (tm.map fun lt => lt.lit (e.length + j)) := by
  have h : ∀ lt : LitT, lblk lt (pairB e (un j)) = encodeLiteral (lt.lit (e.length + j)) := by
    intro lt
    simp only [lblk, LitT.lit, unpairB_pairB, encodeLiteral_split, U_add, un,
      List.length_replicate, List.append_assoc]
  simp only [tblk, encodeClause]
  congr 1
  induction tm with
  | nil => rfl
  | cons lt tm ih => rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih, h]

/-- A family of clauses from one template, the growing index running from the length of `off x`
over the length of `cnt x` values. -/
theorem cpt_tmplLoop (tm : List LitT) {off cnt : List Bool → List Bool} (hoff : CPTs off)
    (hcnt : CPTs cnt) :
    CPTs (fun x => encodeCNF ((List.range (cnt x).length).map fun j =>
      tm.map fun lt => lt.lit ((off x).length + j))) := by
  obtain ⟨a, ha⟩ := tblk_length tm
  refine cptE (cpt_loop (cpt_tblk tm) a ha hoff hcnt) (fun x => ?_)
  rw [encodeCNF_map]
  exact flatMap_congr_mem _ _ _ (fun j _ => tblk_spec tm (off x) j)

/-! ### The clauses of the input symbols -/

/-- The encoded clause "cell `j` holds the symbol of the bit `j` of the input". -/
def iblk (A0 A1 Bc : List Bool) (s : List Bool) : List Bool :=
  sel (hd ((fun l : List Bool => l.tail)^[(unpairB s).2.length] (unpairB s).1)) A0 A1 ++
    (U (unpairB s).2.length ++ Bc)

theorem cpt_iblk (A0 A1 Bc : List Bool) : CPTs (iblk A0 A1 Bc) := by
  have h1 : CPTs (fun y => (unpairB y).1) := cpt_unpairB1
  have h2 : CPTs (fun y => (unpairB y).2) := cpt_unpairB2
  have hJ := cpt_iterLen cpt_tail (fun s => by simp) h2 h1
  exact cpt_app2 (cpt_sel (cpt_hd1 hJ) (cpt_const A0) (cpt_const A1))
    (cpt_app2 (cpt_U h2) (cpt_const Bc))

theorem iblk_length (A0 A1 Bc : List Bool) (s : List Bool) :
    (iblk A0 A1 Bc s).length ≤
      (A0.length + A1.length + Bc.length + 2) * s.length +
        (A0.length + A1.length + Bc.length + 2) := by
  have h1 := unpairB_length s
  have h2 := sel_length (hd ((fun l : List Bool => l.tail)^[(unpairB s).2.length] (unpairB s).1))
    A0 A1 (A0.length + A1.length) (by omega) (by omega)
  have h3 : 2 * s.length ≤ (A0.length + A1.length + Bc.length + 2) * s.length :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [iblk, List.length_append, U_length]
  omega

theorem sel_hd_drop (A0 A1 : List Bool) (x : List Bool) :
    ∀ j, j < x.length → sel (hd (x.drop j)) A0 A1 = if x.getD j false then A1 else A0 := by
  induction x with
  | nil => intro j hj; simp at hj
  | cons b x ih =>
    intro j hj
    cases j with
    | zero => cases b <;> simp [hd, sel]
    | succ j =>
      have := ih j (by simpa using hj)
      simpa using this

theorem getD_map_sym (x : List Bool) :
    ∀ j, (x.map fun b => cond b 1 0).getD j 0 = cond (x.getD j false) 1 0 := by
  induction x with
  | nil => intro j; simp
  | cons b x ih =>
    intro j
    cases j with
    | zero => simp
    | succ j => simpa using ih j

theorem iblk_spec (k : ℕ) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    iblk (lpre true [2, k, 1]) (lpre true [2, k, 2]) (lpost [0] ++ [false, false])
        (pairB x (un j)) =
      encodeClause (imp [] (vC 0 k j ((x.map fun b => cond b 1 0).getD j 0 + 1))) := by
  have h : ∀ v, encodeClause (imp [] (vC 0 k j v)) =
      lpre true [2, k, v] ++ (U j ++ (lpost [0] ++ [false, false])) :=
    fun v => encodeClause_single true [2, k, v] j [0]
  rw [h, getD_map_sym]
  simp only [iblk, unpairB_pairB, tail_iter, un, List.length_replicate]
  rw [sel_hd_drop _ _ x j hj]
  cases x.getD j false <;> rfl

/-- The clauses of the input symbols. -/
theorem cpt_inputLoop (k : ℕ) :
    CPTs (fun x => encodeCNF ((List.range x.length).map fun j =>
      imp [] (vC 0 k j ((x.map fun b => cond b 1 0).getD j 0 + 1)))) := by
  refine cptE (cpt_loop (cpt_iblk _ _ _) _ (iblk_length (lpre true [2, k, 1])
    (lpre true [2, k, 2]) (lpost [0] ++ [false, false])) cpt_id cpt_id) (fun x => ?_)
  rw [encodeCNF_map]
  exact flatMap_congr_mem _ _ _ (fun j hj => iblk_spec k x j (List.mem_range.1 hj))

/-! ### One clause with the growing index last -/

/-- A unit clause whose variable ends with a growing index. -/
theorem cpt_unitLast (pol : Bool) (pre : List ℕ) {t : List Bool → List Bool} (ht : CPTs t) :
    CPTs (fun x => encodeCNF [[(uvar (pre ++ [(t x).length]), pol)]]) := by
  refine cptE (cpt_app2 (cpt_const (lpre pol pre))
    (cpt_app2 (cpt_U ht) (cpt_const (lpost [] ++ [false, false])))) (fun x => ?_)
  have h := encodeClause_single pol pre (t x).length []
  simp only [encodeCNF, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact h.symm

end Edge

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search in
theorem cpt_initPart (c : PEqualNP.Library.Universal.Code) (p q : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        (initClauses c (x.map (fun b => cond b 1 0)) (p.eval x.length)
          (cellsOf x.length (p.eval x.length) (q.eval x.length)))) := by
  -- strings of the growing lengths
  have hm : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) := L055 p
  have hH : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate
        (cellsOf x.length (p.eval x.length) (q.eval x.length)) true) :=
    Edge.cptE (L055 (Polynomial.X + p + q + Polynomial.C 2)) (fun x => by simp [cellsOf])
  have hnil : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => ([] : List Bool)) := cpt_const []
  -- the blank cells of a stack, from a growing offset
  have hblank : ∀ (k : ℕ) {off : List Bool → List Bool},
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) off →
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => encodeCNF
          ((List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
            imp [] (vC 0 k ((off x).length + j) 0))) := by
    intro k off hoff
    refine Edge.cptE (Edge.cpt_tmplLoop [⟨true, [2, k, 0], 0, [0]⟩] hoff hH) (fun x => ?_)
    simp only [List.length_replicate]
    rfl
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun _ : List Bool => encodeCNF [imp [] (vP 0 (c.pc₀ + 1)), imp [] (vQ 0 c.state₀)]) :=
    cpt_const _
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF ((List.range c.nstk).flatMap fun k =>
        if k = c.kin then []
        else (List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
          imp [] (vC 0 k j 0))) := by
    refine Edge.cpt_encFlatMap_const (List.range c.nstk) _ (fun k => ?_)
    by_cases hk : k = c.kin
    · simp only [eq_true hk, ↓reduceIte]
      exact cpt_const _
    · simp only [eq_false hk, ↓reduceIte]
      exact Edge.cptE (hblank k hnil) (fun x => by simp)
  have hC : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF (if c.kin < c.nstk then
        ((List.range x.length).map fun j =>
          imp [] (vC 0 c.kin j ((x.map fun b => cond b 1 0).getD j 0 + 1)))
        ++ ((List.range (p.eval x.length)).map fun j =>
          [(vC 0 c.kin (x.length + j) 0, true), (vC 0 c.kin (x.length + j) 3, true),
            (vC 0 c.kin (x.length + j) 4, true)])
        ++ ((List.range (p.eval x.length - 1)).map fun j =>
          imp [vC 0 c.kin (x.length + j) 0] (vC 0 c.kin (x.length + (j + 1)) 0))
        ++ ((List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
          imp [] (vC 0 c.kin (x.length + p.eval x.length + j) 0))
      else [])) := by
    by_cases hk : c.kin < c.nstk
    · simp only [eq_true hk, ↓reduceIte, Edge.encodeCNF_append]
      have h1 := Edge.cpt_inputLoop c.kin
      have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (p.eval x.length)).map fun j =>
            [(vC 0 c.kin (x.length + j) 0, true), (vC 0 c.kin (x.length + j) 3, true),
              (vC 0 c.kin (x.length + j) 4, true)])) := by
        refine Edge.cptE (Edge.cpt_tmplLoop [⟨true, [2, c.kin, 0], 0, [0]⟩,
          ⟨true, [2, c.kin, 3], 0, [0]⟩, ⟨true, [2, c.kin, 4], 0, [0]⟩] cpt_id hm) (fun x => ?_)
        simp only [List.length_replicate]
        rfl
      have h3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (p.eval x.length - 1)).map fun j =>
            imp [vC 0 c.kin (x.length + j) 0] (vC 0 c.kin (x.length + (j + 1)) 0))) := by
        refine Edge.cptE (Edge.cpt_tmplLoop [⟨false, [2, c.kin, 0], 0, [0]⟩,
          ⟨true, [2, c.kin, 0], 1, [0]⟩] cpt_id (cpt_tail1 hm)) (fun x => ?_)
        simp only [List.length_tail, List.length_replicate]
        rfl
      have h4 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF
            ((List.range (cellsOf x.length (p.eval x.length) (q.eval x.length))).map fun j =>
              imp [] (vC 0 c.kin (x.length + p.eval x.length + j) 0))) :=
        Edge.cptE (hblank c.kin (cpt_app2 cpt_id hm)) (fun x => by simp)
      exact cpt_app2 (cpt_app2 (cpt_app2 h1 h2) h3) h4
    · simp only [eq_false hk, ↓reduceIte]
      exact cpt_const _
  refine Edge.cptE (cpt_app2 (cpt_app2 hA hB) hC) (fun x => ?_)
  simp only [initClauses, Edge.encodeCNF_append, List.length_map]

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search in
theorem cpt_finalPart (c : PEqualNP.Library.Universal.Code) (q : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF (finalClauses c (bound c) (q.eval x.length))) := by
  have hT : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (q.eval x.length) true) := L055 q
  have hunit : ∀ (pol : Bool) (pre : List ℕ),
      ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => encodeCNF [[(uvar (pre ++ [q.eval x.length]), pol)]]) :=
    fun pol pre => Edge.cptE (Edge.cpt_unitLast pol pre hT) (fun x => by simp)
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF
        ((List.range (bound c)).map fun p => [(vP (q.eval x.length) (p + 1), false)])) :=
    Edge.cpt_encMap_const _ _ (fun p => hunit false [0, p + 1])
  have hB : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => encodeCNF (if c.kout < c.nstk then
        [[(vC (q.eval x.length) c.kout 0 0, false)]]
        ++ ((List.range (bound c)).flatMap fun v =>
          if v = 1 then [] else [[(vC (q.eval x.length) c.kout 0 (v + 1), false)]])
        ++ ((List.range (bound c)).map fun v => [(vC (q.eval x.length) c.kout 1 (v + 1), false)])
      else [[]])) := by
    by_cases hk : c.kout < c.nstk
    · simp only [eq_true hk, ↓reduceIte, Edge.encodeCNF_append]
      have h1 := hunit false [2, c.kout, 0, 0]
      have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (bound c)).flatMap fun v =>
            if v = 1 then [] else [[(vC (q.eval x.length) c.kout 0 (v + 1), false)]])) := by
        refine Edge.cpt_encFlatMap_const _ _ (fun v => ?_)
        by_cases hv : v = 1
        · simp only [eq_true hv, ↓reduceIte]
          exact cpt_const _
        · simp only [eq_false hv, ↓reduceIte]
          exact hunit false [2, c.kout, v + 1, 0]
      have h3 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => encodeCNF ((List.range (bound c)).map fun v =>
            [(vC (q.eval x.length) c.kout 1 (v + 1), false)])) :=
        Edge.cpt_encMap_const _ _ (fun v => hunit false [2, c.kout, v + 1, 1])
      exact cpt_app2 (cpt_app2 h1 h2) h3
    · simp only [eq_false hk, ↓reduceIte]
      exact cpt_const _
  refine Edge.cptE (cpt_app2 hA hB) (fun x => ?_)
  simp only [finalClauses, Edge.encodeCNF_append]

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search in
theorem cpt_tableau_of (c : PEqualNP.Library.Universal.Code) (p q : Polynomial ℕ)
    (hstep : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        ((List.range (q.eval x.length)).flatMap fun t =>
          stepClauses c.nstk (cellsOf x.length (p.eval x.length) (q.eval x.length))
            (bound c) c.prog t))) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        (tableau c (x.map (fun b => cond b 1 0)) (p.eval x.length) (q.eval x.length))) := by
  refine Edge.cptE (cpt_app2 (cpt_app2 (cpt_initPart c p q) hstep) (cpt_finalPart c q))
    (fun x => ?_)
  simp only [tableau, Edge.encodeCNF_append, List.length_map]

end PEqualNP.Library.SearchHelpers.Tab
