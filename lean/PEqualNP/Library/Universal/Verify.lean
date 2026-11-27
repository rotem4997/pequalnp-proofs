import PEqualNP.Library.Universal.SStep

/-!
# The verification function on bit strings

Helper module (proofs only, no statement may use it). `V (z, w)` splits `z` into a code string,
an input and a budget, builds the initial configuration string with the symbols of the input
and of the witness `w`, iterates the string-level step budget-many times, and tests that the
result is halted with output stack exactly `[1]`.

## Primitives and the toolbox item that computes each

* `hNst`, `hPc`, `hSt`, `hKin`, `hKout`: compositions of `hd`, `dropN` and `List.tail`.
* `insK kf new sk`: the iteration `splitK` (see `SStep.lean`), two `unpairB` components, append
  and one `sel`.
* `inSyms x w`: append of `bump (spread x)` and `bump (bump (bump (spread w)))`.
* `initS cs x w`: `unpairB`, the header fields, `blank`, `insK`, three `pairB`.
* `haltedS`: emptiness of a component (a transducer writing a flag at the end).
* `stkS`: three `unpairB` components.
* `outOne kout sk`: the iteration `dropL^[kout.length] sk`, then a transducer that compares the
  first four symbols with a constant and writes a flag at the end.
* `V`: length comparison, the iteration `sstep^[budget.length]` with the measure `smeasure`,
  and the two tests.
-/

namespace PEqualNP.Library.Universal

/-- The number of stacks, in unary. -/
def hNst (h : List Bool) : List Bool := (hd h).tail

/-- The initial program counter string. -/
def hPc (h : List Bool) : List Bool := hd (dropN h)

/-- The initial state, in unary. -/
def hSt (h : List Bool) : List Bool := (hd (dropN (dropN h))).tail

/-- The input stack, in unary. -/
def hKin (h : List Bool) : List Bool := (hd (dropN (dropN (dropN h)))).tail

/-- The output stack, in unary. -/
def hKout (h : List Bool) : List Bool := (hd (dropN (dropN (dropN (dropN h))))).tail

/-- Insert numbers on top of the stack `kf.length`; nothing happens outside the range. -/
def insK (kf new sk : List Bool) : List Bool :=
  sel (unpairB (splitK kf sk)).1 (unpairB (splitK kf sk)).2
    ((unpairB (splitK kf sk)).2 ++ (new ++ (unpairB (splitK kf sk)).1))

/-- The input symbols: the bits of `x` numbered `0` and `1`, then those of `w` numbered `2`
and `3`. -/
def inSyms (x w : List Bool) : List Bool := bump (spread x) ++ bump (bump (bump (spread w)))

/-- The initial configuration string, from the code string, the input and the witness. -/
def initS (cs x w : List Bool) : List Bool :=
  pairB (unpairB cs).1 (pairB (hPc (unpairB cs).2) (pairB (hSt (unpairB cs).2)
    (insK (hKin (unpairB cs).2) (inSyms x w) (blank (hNst (unpairB cs).2)))))

/-- The configuration string is halted. -/
def haltedS (y : List Bool) : Bool := (unpairB (unpairB y).2).1.isEmpty

/-- The stacks part of a configuration string. -/
def stkS (y : List Bool) : List Bool := (unpairB (unpairB (unpairB y).2).2).2

/-- The stack `kout.length` is exactly `[1]`. -/
def outOne (kout sk : List Bool) : Bool :=
  decide ((dropL^[kout.length] sk).take 4 = [true, true, false, false])

/-- The verification function: `p = (z, w)` where `z` is the pair of a code string and the pair
of an input and a budget. -/
def V (p : List Bool × List Bool) : Bool :=
  decide (p.2.length ≤ (unpairB (unpairB p.1).2).2.length) &&
    (haltedS (sstep^[(unpairB (unpairB p.1).2).2.length]
      (initS (unpairB p.1).1 (unpairB (unpairB p.1).2).1 p.2)) &&
    outOne (hKout (unpairB (unpairB p.1).1).2)
      (stkS (sstep^[(unpairB (unpairB p.1).2).2.length]
        (initS (unpairB p.1).1 (unpairB (unpairB p.1).2).1 p.2))))

theorem getD_replicate_nil (n k : ℕ) : (List.replicate n ([] : List ℕ)).getD k [] = [] := by
  induction n generalizing k with
  | zero => simp
  | succ n ih => cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simpa [List.replicate_succ] using ih k

theorem insK_spec (k : ℕ) (l : List ℕ) (S : List (List ℕ)) :
    insK (un k) (encNs l) (encLL S) = encLL (S.set k (l ++ S.getD k [])) := by
  rw [insK, splitK_encLL, ins_spec]

theorem inSyms_spec (x w : List Bool) :
    inSyms x w = encNs ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2) := by
  rw [inSyms, inX_spec, inW_spec, encNs_append]

theorem initS_spec (c : Code) (x w : List Bool) :
    initS (encCode c) x w =
      encCfg c.prog (c.init ((x.map fun b => cond b 1 0) ++ w.map fun b => cond b 3 2)) := by
  have h1 : hNst (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.nstk := by
    simp [hNst, un_succ]
  have h2 : hPc (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un (c.pc₀ + 1) := by
    simp [hPc]
  have h3 : hSt (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.state₀ := by
    simp [hSt, un_succ]
  have h4 : hKin (encNs [c.nstk, c.pc₀, c.state₀, c.kin, c.kout]) = un c.kin := by
    simp [hKin, un_succ]
  simp only [initS, encCode, unpairB_pairB, h1, h2, h3, h4, blank_un, inSyms_spec, insK_spec,
    getD_replicate_nil, List.append_nil, encCfg, Code.init, encPc]

theorem haltedS_encCfg (P : List Instr) (cfg : Cfg) :
    haltedS (encCfg P cfg) = true ↔ cfg.pc = none := by
  obtain ⟨pc, v, S⟩ := cfg
  cases pc <;> simp [haltedS, encCfg, unpairB_pairB, encPc, un_succ]

theorem stkS_encCfg (P : List Instr) (cfg : Cfg) : stkS (encCfg P cfg) = encLL cfg.stk := by
  simp [stkS, encCfg, unpairB_pairB]

theorem outOne_spec (k : ℕ) (S : List (List ℕ)) :
    outOne (un k) (encLL S) = true ↔ S.getD k [] = [1] := by
  rw [outOne, un_length, dropL_iter_encLL, decide_eq_true_eq]
  induction S generalizing k with
  | nil => simp
  | cons a S ih =>
    cases k with
    | zero =>
      rcases a with _ | ⟨s, a⟩
      · simp [encLL_cons]
      · rcases s with _ | _ | s
        · simp [encLL_cons, encNs_cons, encN, un_succ]
        · rcases a with _ | ⟨s', a⟩
          · simp [encLL_cons, encNs_cons, encN, un_succ]
          · simp [encLL_cons, encNs_cons, encN, un_succ]
        · simp [encLL_cons, encNs_cons, encN, un_succ]
    | succ k => simpa using ih k

/-- Correctness of the verification function. -/
theorem V_spec (c : Code) (x w : List Bool) (t : ℕ) :
    V (pairB (encCode c) (pairB x (un t)), w) = true ↔
      (w.length ≤ t ∧ c.outputsWithin
        (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2)) t [1]) := by
  have h5 : hKout (unpairB (encCode c)).2 = un c.kout := by
    simp [hKout, encCode, unpairB_pairB, un_succ]
  simp only [V, unpairB_pairB, un_length, initS_spec, sstep_iter, h5, Bool.and_eq_true,
    decide_eq_true_eq, haltedS_encCfg, stkS_encCfg, outOne_spec, Code.outputsWithin, Code.run]

end PEqualNP.Library.Universal
