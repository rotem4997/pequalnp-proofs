import PEqualNP.Library.SearchHelpers.TableauDefs
import PEqualNP.Library.SearchHelpers.TableauStepWLoop

/-!
# Helpers: the encoded step clauses of the tableau are polynomial-time computable

Helper module (proofs only, no statement may use it).

The main result is `cpt_stepPart`: for a fixed code `c` and polynomials `p`, `q`, the binary
encoding of the step clauses of all times `t < q |x|` of the tableau is a polynomial-time
function of `x`.

The code is fixed, so the step clauses of one time are a constant number of clauses and of
families of clauses over the cell index. The proof is by structure: a number, a variable, a
clause or a formula that depends on a string is "computable" when its unary string or its
encoding is a polynomial-time function of the string (`NatC`, `VarC`, `ClC`, `CnfC`), and each
constructor of the step clauses keeps computability. A family over a growing range is the loop
of `TableauStepWLoop.lean`. The digits of a variable `uvar l` are unary blocks (`bits_uvar`), so
its encoding needs no binary arithmetic.
-/

namespace PEqualNP.Library.SearchHelpers.Tab.StepW

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal PEqualNP.Search

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### The digits of a variable -/

theorem bits_pow_mul (a m : ℕ) (hm : m ≠ 0) :
    (2 ^ a * m).bits = List.replicate a false ++ m.bits := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by ring
    rw [e, Nat.bit0_bits _ (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hm), ih]
    rfl

/-- The binary digits of `uvar l`, least significant first: `false^a ++ [true]` for each index
`a` of `l` in order. -/
theorem bits_uvar (l : List ℕ) :
    (uvar l).bits = l.flatMap fun a => List.replicate a false ++ [true] := by
  induction l with
  | nil => simp [uvar]
  | cons a r ih =>
    simp only [uvar]
    rw [bits_pow_mul _ _ (by omega), Nat.bit1_bits, ih]
    simp

/-- The digits of `uvar l` as they stand in the encoding of a literal: every digit after a
`true`. -/
def digs : List ℕ → List Bool
  | [] => []
  | a :: r => spread (un a) ++ true :: true :: digs r

theorem spread_un (a : ℕ) :
    spread (un a) = (List.replicate a false).flatMap fun d => [true, d] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [un_succ, List.replicate_succ, List.flatMap_cons, ← ih]
    rfl

theorem digs_eq (l : List ℕ) : ((uvar l).bits.flatMap fun d => [true, d]) = digs l := by
  rw [bits_uvar]
  induction l with
  | nil => rfl
  | cons a r ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.flatMap_append, ih, digs, spread_un]
    simp

theorem encodeLiteral_uvar (l : List ℕ) (b : Bool) :
    encodeLiteral (uvar l, b) = true :: b :: (digs l ++ [false, true]) := by
  simp [encodeLiteral, digs_eq]

theorem encodeCNF_append (φ ψ : CNF) : encodeCNF (φ ++ ψ) = encodeCNF φ ++ encodeCNF ψ := by
  simp [encodeCNF]

theorem encodeCNF_flatMap {α : Type} (l : List α) (φ : α → CNF) :
    encodeCNF (l.flatMap φ) = l.flatMap fun a => encodeCNF (φ a) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, encodeCNF_append, ih, List.flatMap_cons]

/-! ### Computable numbers, variables, clauses and formulas -/

/-- A number that depends on a string, written in unary in polynomial time. -/
def NatC (n : List Bool → ℕ) : Prop := CPTs (fun s => un (n s))

/-- A list of indices whose digit string is written in polynomial time. -/
def DigC (l : List Bool → List ℕ) : Prop := CPTs (fun s => digs (l s))

/-- A variable whose two literals are encoded in polynomial time. -/
def VarC (v : List Bool → ℕ) : Prop := ∀ b : Bool, CPTs (fun s => encodeLiteral (v s, b))

/-- A clause encoded in polynomial time. -/
def ClC (c : List Bool → Clause) : Prop := CPTs (fun s => encodeClause (c s))

/-- A formula encoded in polynomial time. -/
def CnfC (φ : List Bool → CNF) : Prop := CPTs (fun s => encodeCNF (φ s))

theorem natC_const (k : ℕ) : NatC (fun _ => k) := cpt_const (un k)

theorem natC_succ {n : List Bool → ℕ} (h : NatC n) : NatC (fun s => n s + 1) :=
  cptE (cpt_cons1 true h) (fun _ => rfl)

theorem natC_pred {n : List Bool → ℕ} (h : NatC n) : NatC (fun s => n s - 1) :=
  cptE (cpt_tail1 h) (fun s => by
    show (un (n s)).tail = un (n s - 1)
    cases n s <;> rfl)

theorem natC_len {u : List Bool → List Bool} (hu : CPTs u) : NatC (fun s => (u s).length) :=
  cptE (cpt_mulU2 hu (cpt_const [true])) (fun s => by simp [mulU])

/-- The loop index: the length of the first component of the packed argument. -/
theorem natC_fst : NatC (fun y => (unpairB y).1.length) := natC_len cpt_unpairB1

/-- A number of the outer string, read inside a loop. -/
theorem natC_snd {n : List Bool → ℕ} (h : NatC n) : NatC (fun y => n (unpairB y).2) :=
  cptE (cpt_comp cpt_unpairB2 (show CPTs (fun s => un (n s)) from h)) (fun _ => rfl)

theorem digC_nil : DigC (fun _ => []) := cpt_const []

theorem digC_cons {a : List Bool → ℕ} {l : List Bool → List ℕ} (ha : NatC a) (hl : DigC l) :
    DigC (fun s => a s :: l s) :=
  cptE (cpt_app2 (cpt_comp ha cpt_spread) (cpt_cons1 true (cpt_cons1 true hl))) (fun _ => rfl)

theorem varC_of_dig {l : List Bool → List ℕ} (hl : DigC l) : VarC (fun s => uvar (l s)) :=
  fun b => cptE (cpt_cons1 true (cpt_cons1 b (cpt_app2 hl (cpt_const [false, true]))))
    (fun _ => (encodeLiteral_uvar _ _).symm)

theorem varC_vP {t q : List Bool → ℕ} (ht : NatC t) (hq : NatC q) :
    VarC (fun s => vP (t s) (q s)) :=
  varC_of_dig (digC_cons (natC_const 0) (digC_cons hq (digC_cons ht digC_nil)))

theorem varC_vQ {t v : List Bool → ℕ} (ht : NatC t) (hv : NatC v) :
    VarC (fun s => vQ (t s) (v s)) :=
  varC_of_dig (digC_cons (natC_const 1) (digC_cons hv (digC_cons ht digC_nil)))

theorem varC_vC {t k j x : List Bool → ℕ} (ht : NatC t) (hk : NatC k) (hj : NatC j)
    (hx : NatC x) : VarC (fun s => vC (t s) (k s) (j s) (x s)) :=
  varC_of_dig (digC_cons (natC_const 2) (digC_cons hk (digC_cons hx (digC_cons hj
    (digC_cons ht digC_nil)))))

theorem clC_nil : ClC (fun _ => []) := cptE (cpt_const [false, false]) (fun _ => rfl)

theorem clC_cons {v : List Bool → ℕ} {c : List Bool → Clause} (hv : VarC v) (b : Bool)
    (hc : ClC c) : ClC (fun s => (v s, b) :: c s) :=
  cptE (cpt_app2 (hv b) hc) (fun _ => by simp [encodeClause])

theorem clC_imp_nil {c : List Bool → ℕ} (hc : VarC c) : ClC (fun s => imp [] (c s)) :=
  cptE (clC_cons hc true clC_nil) (fun _ => rfl)

theorem clC_imp_cons {a c : List Bool → ℕ} {p : List Bool → List ℕ} (ha : VarC a)
    (h : ClC (fun s => imp (p s) (c s))) : ClC (fun s => imp (a s :: p s) (c s)) :=
  cptE (clC_cons ha false h) (fun _ => rfl)

theorem cnfC_nil : CnfC (fun _ => []) := cpt_const []

theorem cnfC_append {φ ψ : List Bool → CNF} (h1 : CnfC φ) (h2 : CnfC ψ) :
    CnfC (fun s => φ s ++ ψ s) :=
  cptE (cpt_app2 h1 h2) (fun _ => (encodeCNF_append _ _).symm)

theorem cnfC_cons {c : List Bool → Clause} {φ : List Bool → CNF} (h1 : ClC c) (h2 : CnfC φ) :
    CnfC (fun s => c s :: φ s) :=
  cptE (cpt_app2 h1 h2) (fun _ => by simp [encodeCNF])

/-- A family over a constant list. -/
theorem cnfC_flatMap_const {α : Type} (l : List α) {φ : α → List Bool → CNF}
    (h : ∀ a, CnfC (φ a)) : CnfC (fun s => l.flatMap fun a => φ a s) := by
  induction l with
  | nil => exact cnfC_nil
  | cons a l ih => exact cnfC_append (h a) ih

/-- A family of clauses over a constant list. -/
theorem cnfC_map_const {α : Type} (l : List α) {c : α → List Bool → Clause}
    (h : ∀ a, ClC (c a)) : CnfC (fun s => l.map fun a => c a s) := by
  induction l with
  | nil => exact cnfC_nil
  | cons a l ih => exact cnfC_cons (h a) ih

/-- A family over a growing range: the body is computable as a function of the packed string
`pairB (un j) s`. -/
theorem cnfC_flatMap_range {n : List Bool → ℕ} (hn : NatC n) {φ : ℕ → List Bool → CNF}
    (h : CnfC (fun y => φ (unpairB y).1.length (unpairB y).2)) :
    CnfC (fun s => (List.range (n s)).flatMap fun j => φ j s) := by
  have h' := cpt_flatMapRange h hn cpt_id
  refine cptE h' (fun s => ?_)
  simp only [unpairB_pairB, un_length]
  exact (encodeCNF_flatMap _ _).symm

/-! ### The step clauses -/

theorem pcC (B q : ℕ) (i : Instr) {t : List Bool → ℕ} (ht : NatC t) :
    CnfC (fun s => pcClauses B (t s) q i) := by
  refine cnfC_map_const (List.range B)
    (c := fun v s => imp [vP (t s) q, vQ (t s) v] (vP (t s + 1) (nextCode i v))) (fun v => ?_)
  exact clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons (varC_vQ ht (natC_const v))
    (clC_imp_nil (varC_vP (natC_succ ht) (natC_const _))))

theorem readsC (K B q v : ℕ) (o : Option ℕ) (g : ℕ → ℕ) {t : List Bool → ℕ} (ht : NatC t) :
    CnfC (fun s => (reads K B (t s) o).map fun r =>
      imp (vP (t s) q :: vQ (t s) v :: r.1) (vQ (t s + 1) (g r.2))) := by
  have hnone : CnfC (fun s => [imp [vP (t s) q, vQ (t s) v] (vQ (t s + 1) (g 0))]) :=
    cnfC_cons (clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
      (varC_vQ ht (natC_const v)) (clC_imp_nil (varC_vQ (natC_succ ht) (natC_const _)))))
      cnfC_nil
  cases o with
  | none => exact hnone
  | some k =>
    by_cases hk : k < K
    · have h : CnfC (fun s => (List.range (B + 1)).map fun x =>
          imp [vP (t s) q, vQ (t s) v, vC (t s) k 0 x] (vQ (t s + 1) (g x))) :=
        cnfC_map_const _ (fun x => clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
          (varC_vQ ht (natC_const v)) (clC_imp_cons
            (varC_vC ht (natC_const k) (natC_const 0) (natC_const x))
            (clC_imp_nil (varC_vQ (natC_succ ht) (natC_const _))))))
      refine cptE h (fun s => ?_)
      simp only [reads, hk, ↓reduceIte, List.map_map]
      rfl
    · refine cptE hnone (fun s => ?_)
      simp [reads, hk]

theorem stateC (K B q : ℕ) (i : Instr) {t : List Bool → ℕ} (ht : NatC t) :
    CnfC (fun s => stateClauses K B (t s) q i) :=
  cnfC_flatMap_const (List.range B) (fun v => readsC K B q v (rdStack i) (newState i v) ht)

/-- One row of the copy clauses: the cell `j` at time `t` goes to the cell `j'` at time
`t + 1`. -/
theorem rowC (B q k : ℕ) {t j j' : List Bool → ℕ} (ht : NatC t) (hj : NatC j)
    (hj' : NatC j') :
    CnfC (fun s => (List.range (B + 1)).map fun x =>
      imp [vP (t s) q, vC (t s) k (j s) x] (vC (t s + 1) k (j' s) x)) :=
  cnfC_map_const _ (fun x => clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
    (varC_vC ht (natC_const k) hj (natC_const x))
    (clC_imp_nil (varC_vC (natC_succ ht) (natC_const k) hj' (natC_const x)))))

theorem cellC (B q k : ℕ) (op : Op) {H t : List Bool → ℕ} (hH : NatC H) (ht : NatC t) :
    CnfC (fun s => cellClauses (H s) B (t s) q k op) := by
  cases op with
  | keep =>
    exact cnfC_flatMap_range hH
      (φ := fun j s => (List.range (B + 1)).map fun x =>
        imp [vP (t s) q, vC (t s) k j x] (vC (t s + 1) k j x))
      (rowC B q k (natC_snd ht) natC_fst natC_fst)
  | push tbl =>
    refine cnfC_append ?_ ?_
    · exact cnfC_map_const (List.range B)
        (c := fun v s => imp [vP (t s) q, vQ (t s) v] (vC (t s + 1) k 0 (tbl.getD v 0 + 1)))
        (fun v => clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_cons
          (varC_vQ ht (natC_const v)) (clC_imp_nil
            (varC_vC (natC_succ ht) (natC_const k) (natC_const 0) (natC_const _)))))
    · exact cnfC_flatMap_range (natC_pred hH)
        (φ := fun j s => (List.range (B + 1)).map fun x =>
          imp [vP (t s) q, vC (t s) k j x] (vC (t s + 1) k (j + 1) x))
        (rowC B q k (natC_snd ht) natC_fst (natC_succ natC_fst))
  | pop =>
    refine cnfC_append ?_ ?_
    · exact cnfC_flatMap_range (natC_pred hH)
        (φ := fun j s => (List.range (B + 1)).map fun x =>
          imp [vP (t s) q, vC (t s) k (j + 1) x] (vC (t s + 1) k j x))
        (rowC B q k (natC_snd ht) (natC_succ natC_fst) natC_fst)
    · exact cnfC_cons (clC_imp_cons (varC_vP ht (natC_const q)) (clC_imp_nil
        (varC_vC (natC_succ ht) (natC_const k) (natC_pred hH) (natC_const 0)))) cnfC_nil

theorem stepC (K B : ℕ) (P : List Instr) {H t : List Bool → ℕ} (hH : NatC H) (ht : NatC t) :
    CnfC (fun s => stepClauses K (H s) B P (t s)) :=
  cnfC_flatMap_const (List.range (B + 1)) (fun q =>
    cnfC_append (cnfC_append (pcC B q (instrAt P q) ht) (stateC K B q (instrAt P q) ht))
      (cnfC_flatMap_const (List.range K)
        (fun k => cellC B q k (stackOp (instrAt P q) k) hH ht)))

end PEqualNP.Library.SearchHelpers.Tab.StepW

namespace PEqualNP.Library.SearchHelpers.Tab

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal StepW

/-- The encoded step clauses of the tableau, over all times below `q |x|`, are a
polynomial-time function of `x`. -/
theorem cpt_stepPart (c : PEqualNP.Library.Universal.Code) (p q : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => PEqualNP.Search.encodeCNF
        ((List.range (q.eval x.length)).flatMap fun t =>
          stepClauses c.nstk (cellsOf x.length (p.eval x.length) (q.eval x.length))
            (bound c) c.prog t)) := by
  have hT : NatC (fun x => q.eval x.length) := PEqualNP.Library.L055 q
  have hH : NatC (fun x => cellsOf x.length (p.eval x.length) (q.eval x.length)) := by
    refine cptE (natC_len (cpt_app2 cpt_id (cpt_app2 (PEqualNP.Library.L055 p)
      (cpt_app2 (PEqualNP.Library.L055 q) (cpt_const [true, true]))))) (fun x => ?_)
    congr 1
    simp only [cellsOf, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  exact cnfC_flatMap_range hT
    (φ := fun t x => stepClauses c.nstk (cellsOf x.length (p.eval x.length) (q.eval x.length))
      (bound c) c.prog t)
    (stepC c.nstk (bound c) c.prog (natC_snd hH) natC_fst)

end PEqualNP.Library.SearchHelpers.Tab
