import PEqualNP.Library.SearchHelpers.TableauStepWLoop
import PEqualNP.Library.Universal.Padding
import PEqualNP.MetaComplexity.Helpers.MachinePair
import PEqualNP.Defs.MetaComplexityLgp

/-!
# Writing the circuit code of a gate list with relative wire references

Helper module (proofs only, no statement may use it).

The input is `n` in unary, then a list of relative gates: an operation bit and two references,
each a tag bit (`false`: absolute wire `a`, `true`: backward distance `d`) and the number in
unary. The output is the code `encodeLgp` of the instance with `n` inputs whose gate `j` reads
wire `a` or wire `n + j - d`, and whose output is wire `n + (number of gates) - 1`.

The machine is a composition of string functions (`Universal` toolbox):

* `rlBin u = encodeNat u.length`: the binary code of a unary number, by iterating `rlBStep`
  (one bit per round: the parity, then half of the length), which lengthens by a constant.
* `rlDropG` skips one relative gate (`tail` and `dropN` only); iterated `j` times from the
  start of the list it reaches gate `j`.
* `rlBody` writes the code of gate `j` from `pairB (un j) s`; the loop `cpt_flatMapRange`
  concatenates it over `j` below the number of gates, which is itself written in unary by the
  same loop (`rlCount`).
-/

namespace PEqualNP.MetaComplexity.Helpers.MachineReloc

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Library.SearchHelpers.Tab.StepW
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Polynomial-time computability of a function on plain bit strings. -/
local notation "CPTs" => ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)

/-! ### Iterated tail -/

theorem rl_tail_iter (k : ℕ) (x : List Bool) : List.tail^[k] x = x.drop k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    cases x <;> simp

/-- Dropping as many symbols as the length of `v`. -/
def rlDropU (v x : List Bool) : List Bool := List.tail^[v.length] x

theorem rlDropU_eq (v x : List Bool) : rlDropU v x = x.drop v.length := rl_tail_iter _ _

theorem cpt_rlDropU {v x : List Bool → List Bool} (hv : CPTs v) (hx : CPTs x) :
    CPTs (fun s => rlDropU (v s) (x s)) :=
  cpt_iterLen cpt_tail (fun s => by simp) hv hx

/-! ### Parity and binary code of a unary number -/

/-- The parity transducer. -/
def rlParD (q : Bool) (_ : Bool) : Bool × Option Bool := (!q, none)

/-- The parity of the length, as a one-symbol string. -/
def rlPar (u : List Bool) : List Bool := fstRun rlParD (fun q => some q) false u

theorem rlParD_run (q : Bool) (u : List Bool) :
    fstRun rlParD (fun q => some q) q u = [Bool.xor (Nat.bodd u.length) q] := by
  induction u generalizing q with
  | nil => simp [fstRun]
  | cons b l ih =>
    simp only [fstRun, rlParD, Option.toList_none, List.nil_append, ih, List.length_cons,
      Nat.bodd_succ]
    cases q <;> cases Nat.bodd l.length <;> rfl

theorem rlPar_eq (u : List Bool) : rlPar u = [Nat.bodd u.length] := by
  simp [rlPar, rlParD_run]

theorem cpt_rlPar : CPTs rlPar :=
  fst_polyTime _ _ _ rlParD (fun q => some q) false (fun _ => rfl)

/-- One round of the binary conversion on `pairB acc u`: when `u` is nonempty, write `true`
and the parity of `|u|` after `acc`, and halve `u`. -/
def rlBStep (y : List Bool) : List Bool :=
  sel (unpairB y).2 y
    (pairB ((unpairB y).1 ++ true :: rlPar (unpairB y).2) (half (unpairB y).2))

theorem cpt_rlBStep : CPTs rlBStep :=
  cptE (cpt_sel cpt_unpairB2 cpt_id
    (cpt_pairB2 (cpt_app2 cpt_unpairB1 (cpt_cons1 true (cpt_comp cpt_unpairB2 cpt_rlPar)))
      (cpt_comp cpt_unpairB2 cpt_half'))) (fun _ => rfl)

theorem rlBStep_length (y : List Bool) : (rlBStep y).length ≤ y.length + 5 := by
  have h1 := unpairB_length y
  have h2 := half_length_le (unpairB y).2
  unfold rlBStep sel
  split
  · omega
  · rw [pairB_length, List.length_append, List.length_cons, rlPar_eq]
    simp only [List.length_singleton]
    omega

theorem rlBStep_nil (acc : List Bool) : rlBStep (pairB acc []) = pairB acc [] := by
  simp [rlBStep, unpairB_pairB]

theorem rlBStep_succ (acc : List Bool) (m : ℕ) :
    rlBStep (pairB acc (un (m + 1))) =
      pairB (acc ++ [true, Nat.bodd (m + 1)]) (un ((m + 1) / 2)) := by
  simp [rlBStep, unpairB_pairB, un_succ, rlPar_eq, half_eq]

theorem rl_bits_succ (m : ℕ) :
    Nat.bits (m + 1) = Nat.bodd (m + 1) :: Nat.bits ((m + 1) / 2) := by
  have hd : Nat.div2 (m + 1) = (m + 1) / 2 := Nat.div2_val _
  have e := Nat.bit_bodd_div2 (m + 1)
  rw [← hd]
  conv_lhs => rw [← e]
  apply Nat.bits_append_bit
  intro h0
  rw [h0] at e
  cases hb : Nat.bodd (m + 1)
  · rw [hb] at e
    simp [Nat.bit] at e
  · rfl

/-- The binary digits, each preceded by `true`. -/
def rlDig (l : List Bool) : List Bool := l.flatMap (fun b => [true, b])

theorem rlBStep_iter (k : ℕ) : ∀ (m : ℕ) (acc : List Bool), m ≤ k →
    rlBStep^[k] (pairB acc (un m)) = pairB (acc ++ rlDig (Nat.bits m)) [] := by
  induction k with
  | zero =>
    intro m acc hm
    obtain rfl : m = 0 := by omega
    simp [rlDig]
  | succ k ih =>
    intro m acc hm
    rw [Function.iterate_succ_apply]
    cases m with
    | zero =>
      rw [un_zero, rlBStep_nil, ← un_zero, ih 0 acc (Nat.zero_le _)]
      rfl
    | succ m =>
      rw [rlBStep_succ, ih _ _ (by omega), rl_bits_succ m]
      simp [rlDig]

/-- The binary code of the length of a string. -/
def rlBin (u : List Bool) : List Bool :=
  (unpairB (rlBStep^[u.length] (pairB [] u))).1 ++ [false]

theorem rlBin_un (m : ℕ) : rlBin (un m) = encodeNat m := by
  rw [rlBin, un_length, rlBStep_iter m m [] le_rfl, unpairB_pairB]
  simp [rlDig, encodeNat]

theorem cpt_rlBin : CPTs rlBin :=
  cptE (cpt_app2 (cpt_unpairB1_1 (cpt_iterGrow cpt_rlBStep 5 rlBStep_length cpt_id
    (cpt_pairB2 (cpt_const []) cpt_id))) (cpt_const [false])) (fun _ => rfl)

/-! ### The relative gate list -/

/-- The code of a reference: a tag bit, then the number in unary. -/
def rlRef (r : ℕ ⊕ ℕ) : List Bool :=
  Sum.elim (fun a : ℕ => false :: (List.replicate a true ++ [false]))
    (fun d : ℕ => true :: (List.replicate d true ++ [false])) r

/-- The code of a relative gate. -/
def rlGate (g : Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) : List Bool := g.1 :: (rlRef g.2.1 ++ rlRef g.2.2)

/-- The input string. -/
def rlIn (p : ℕ × List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) : List Bool :=
  (List.replicate p.1 true ++ [false]) ++ encodeList rlGate p.2

theorem rlIn_eq (n : ℕ) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    rlIn (n, l) = un n ++ false :: encodeList rlGate l := by
  simp [rlIn, un]

theorem rlRef_app (r : ℕ ⊕ ℕ) (t : List Bool) :
    rlRef r ++ t = Sum.elim (fun _ => false) (fun _ => true) r ::
      (un (Sum.elim (fun a : ℕ => a) (fun d : ℕ => d) r) ++ false :: t) := by
  cases r <;> simp [rlRef, un]

theorem rl_enc_cons (g : Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    encodeList rlGate (g :: l) =
      true :: g.1 :: (rlRef g.2.1 ++ (rlRef g.2.2 ++ encodeList rlGate l)) := by
  simp [encodeList, rlGate]

theorem rl_enc_length (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    l.length ≤ (encodeList rlGate l).length := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [rl_enc_cons]
    simp only [List.length_cons, List.length_append]
    omega

theorem rl_dropN_ref (r : ℕ ⊕ ℕ) (t : List Bool) : dropN (rlRef r ++ t).tail = t := by
  rw [rlRef_app, List.tail_cons, dropN_un]

/-- Skip one relative gate. -/
def rlDropG (s : List Bool) : List Bool := dropN (dropN s.tail.tail.tail).tail

theorem rlDropG_length (s : List Bool) : (rlDropG s).length ≤ s.length := by
  unfold rlDropG
  have h1 := dropN_length (dropN s.tail.tail.tail).tail
  have h2 := dropN_length s.tail.tail.tail
  simp only [List.length_tail] at h1 h2 ⊢
  omega

theorem cpt_rlDropG : CPTs rlDropG :=
  cptE (cpt_dropN1 (cpt_tail1 (cpt_dropN1 (cpt_tail1 (cpt_tail1 cpt_tail))))) (fun _ => rfl)

theorem rlDropG_cons (g : Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    rlDropG (encodeList rlGate (g :: l)) = encodeList rlGate l := by
  rw [rl_enc_cons, rlDropG]
  simp only [List.tail_cons]
  rw [rl_dropN_ref, rl_dropN_ref]

theorem rlDropG_iter (j : ℕ) : ∀ l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)), j ≤ l.length →
    rlDropG^[j] (encodeList rlGate l) = encodeList rlGate (l.drop j) := by
  induction j with
  | zero => intro l _; rfl
  | succ j ih =>
    intro l hj
    cases l with
    | nil => simp at hj
    | cons g l =>
      rw [Function.iterate_succ_apply, rlDropG_cons, ih l (by simp at hj; omega)]
      rfl

theorem rlDropG_nil : rlDropG [] = [] := rfl

theorem rlDropG_false (k : ℕ) : hd (rlDropG^[k] [false]) = [] := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Function.iterate_succ_apply]
    have e : rlDropG [false] = [] := rfl
    rw [e, Function.iterate_fixed rlDropG_nil]
    rfl

theorem rlDropG_past (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) (k : ℕ) :
    hd (rlDropG^[l.length + k] (encodeList rlGate l)) = [] := by
  rw [Nat.add_comm, Function.iterate_add_apply, rlDropG_iter l.length l le_rfl, List.drop_length]
  exact rlDropG_false k

/-! ### One gate -/

/-- The wire a reference reads (`t` starts at the tag), with `base = un n ++ un j`. -/
def rlWire (t base : List Bool) : List Bool := sel (hd t) (hd t.tail) (rlDropU (hd t.tail) base)

theorem cpt_rlWire {t base : List Bool → List Bool} (ht : CPTs t) (hb : CPTs base) :
    CPTs (fun s => rlWire (t s) (base s)) :=
  cptE (cpt_sel (cpt_hd1 ht) (cpt_hd1 (cpt_tail1 ht)) (cpt_rlDropU (cpt_hd1 (cpt_tail1 ht)) hb))
    (fun _ => rfl)

theorem rlWire_ref (r : ℕ ⊕ ℕ) (t : List Bool) (n j : ℕ) :
    rlWire (rlRef r ++ t) (un n ++ un j) =
      un (Sum.elim (fun a : ℕ => a) (fun d : ℕ => n + j - d) r) := by
  rw [rlWire, rlRef_app, List.tail_cons, hd_un]
  cases r with
  | inl a => simp [hd]
  | inr d =>
    simp only [Sum.elim_inr]
    have e : hd (true :: (un d ++ false :: t)) = true :: hd (un d ++ false :: t) := by
      simp [hd]
    rw [e, sel_cons, rlDropU_eq, un_length]
    simp [un, List.drop_replicate]

/-- The gate the code of `(n, l)` reaches after `|J|` skips, from `pairB J s`. -/
def rlG (y : List Bool) : List Bool := rlDropG^[(unpairB y).1.length] (dropN (unpairB y).2)

theorem cpt_rlG : CPTs rlG :=
  cptE (cpt_iterLen cpt_rlDropG rlDropG_length cpt_unpairB1 (cpt_dropN1 cpt_unpairB2))
    (fun _ => rfl)

theorem rlG_in (n i : ℕ) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    rlG (pairB (un i) (rlIn (n, l))) = rlDropG^[i] (encodeList rlGate l) := by
  rw [rlG, unpairB_pairB, rlIn_eq, dropN_un, un_length]

/-- `un n ++ un j`, from `pairB (un j) s`. -/
def rlBase (y : List Bool) : List Bool := hd (unpairB y).2 ++ (unpairB y).1

theorem cpt_rlBase : CPTs rlBase :=
  cptE (cpt_app2 (cpt_hd1 cpt_unpairB2) cpt_unpairB1) (fun _ => rfl)

/-- The code of gate `j` with its marker `true`, from `pairB (un j) s`. -/
def rlBody (y : List Bool) : List Bool :=
  true :: false :: (tk [true] (rlG y).tail ++ true ::
    (rlBin (rlWire (rlG y).tail.tail (rlBase y)) ++ true ::
      (rlBin (rlWire (dropN (rlG y).tail.tail.tail) (rlBase y)) ++ [false])))

theorem cpt_rlBody : CPTs rlBody :=
  cptE (cpt_cons1 true (cpt_cons1 false (cpt_app2 (cpt_tk (cpt_const [true]) (cpt_tail1 cpt_rlG))
    (cpt_cons1 true (cpt_app2 (cpt_comp (cpt_rlWire (cpt_tail1 (cpt_tail1 cpt_rlG)) cpt_rlBase)
      cpt_rlBin) (cpt_cons1 true (cpt_app2 (cpt_comp (cpt_rlWire
        (cpt_dropN1 (cpt_tail1 (cpt_tail1 (cpt_tail1 cpt_rlG)))) cpt_rlBase) cpt_rlBin)
          (cpt_const [false])))))))) (fun _ => rfl)

/-- The gate of record. -/
def rlGateOf (n j : ℕ) (g : Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) : Gate :=
  Gate.mk (if g.1 then GateOp.or else GateOp.and)
    [Sum.elim (fun a : ℕ => a) (fun d : ℕ => n + j - d) g.2.1,
     Sum.elim (fun a : ℕ => a) (fun d : ℕ => n + j - d) g.2.2]

theorem rlBody_spec (n j : ℕ) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) (hj : j < l.length) :
    rlBody (pairB (un j) (rlIn (n, l))) = true :: encodeGate (rlGateOf n j l[j]) := by
  have hG : rlG (pairB (un j) (rlIn (n, l))) =
      encodeList rlGate (l[j] :: l.drop (j + 1)) := by
    rw [rlG_in, rlDropG_iter j l (le_of_lt hj), List.drop_eq_getElem_cons hj]
  have hB : rlBase (pairB (un j) (rlIn (n, l))) = un n ++ un j := by
    rw [rlBase, unpairB_pairB, rlIn_eq, hd_un]
  rw [rlBody, hG, hB, rl_enc_cons]
  generalize l[j] = g
  obtain ⟨b, r1, r2⟩ := g
  simp only [List.tail_cons]
  rw [rl_dropN_ref, rlWire_ref, rlWire_ref, rlBin_un, rlBin_un, tk_eq]
  cases b <;> simp [encodeGate, encodeGateOp, encodeList, rlGateOf]

/-! ### The number of gates, in unary -/

/-- `[true]` while a gate is left. -/
def rlCntBody (y : List Bool) : List Bool := sel (hd (rlG y)) [] [true]

/-- The number of gates in unary. -/
def rlCount (s : List Bool) : List Bool :=
  (List.range s.length).flatMap (fun i => rlCntBody (pairB (un i) s))

theorem cpt_rlCount : CPTs rlCount :=
  cptE (cpt_flatMapRange (cpt_sel (cpt_hd1 cpt_rlG) (cpt_const []) (cpt_const [true])) cpt_id
    cpt_id) (fun _ => rfl)

theorem rl_flatMap_true (m : ℕ) : (List.range m).flatMap (fun _ => [true]) = un m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, ih]; simp [un, List.replicate_succ']

theorem rlCount_spec (n : ℕ) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    rlCount (rlIn (n, l)) = un l.length := by
  have hlen : l.length ≤ (rlIn (n, l)).length := by
    rw [rlIn_eq]
    have := rl_enc_length l
    simp only [List.length_append, List.length_cons]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (rlIn (n, l)).length = l.length + k := ⟨_, (Nat.add_sub_of_le hlen).symm⟩
  rw [rlCount, hk, List.range_add, List.flatMap_append]
  have h1 : (List.range l.length).flatMap (fun i => rlCntBody (pairB (un i) (rlIn (n, l)))) =
      (List.range l.length).flatMap (fun _ => [true]) := by
    apply List.flatMap_congr
    intro i hi
    have hi' : i < l.length := List.mem_range.1 hi
    rw [rlCntBody, rlG_in, rlDropG_iter i l (le_of_lt hi'), List.drop_eq_getElem_cons hi',
      rl_enc_cons]
    simp [hd]
  have h2 : ((List.range k).map (l.length + ·)).flatMap
      (fun i => rlCntBody (pairB (un i) (rlIn (n, l)))) = [] := by
    rw [List.flatMap_map]
    simp only [List.flatMap_eq_nil_iff]
    intro i _
    simp only [rlCntBody, rlG_in, rlDropG_past]
    rfl
  rw [h1, h2, rl_flatMap_true, List.append_nil]

/-! ### The whole map -/

/-- The gate codes, concatenated. -/
def rlGates (s : List Bool) : List Bool :=
  (List.range (rlCount s).length).flatMap (fun i => rlBody (pairB (un i) s))

theorem cpt_rlGates : CPTs rlGates :=
  cptE (cpt_flatMapRange cpt_rlBody cpt_rlCount cpt_id) (fun _ => rfl)

/-- The output string. -/
def rlOut (s : List Bool) : List Bool :=
  hd s ++ false :: (rlGates s ++ false :: rlBin (hd s ++ rlCount s).tail)

theorem cpt_rlOut : CPTs rlOut :=
  cptE (cpt_app2 cpt_hd (cpt_cons1 false (cpt_app2 cpt_rlGates (cpt_cons1 false
    (cpt_comp (cpt_tail1 (cpt_app2 cpt_hd cpt_rlCount)) cpt_rlBin))))) (fun _ => rfl)

theorem rl_un_tail (k : ℕ) : (un k).tail = un (k - 1) := by
  cases k <;> rfl

theorem rlOut_spec (n : ℕ) (l : List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) :
    rlOut (rlIn (n, l)) = encodeLgp (n, Circuit.mk ((List.range l.length).map
      (fun j => rlGateOf n j (l.getD j (false, Sum.inl 0, Sum.inl 0)))) (n + l.length - 1)) := by
  have hh : hd (rlIn (n, l)) = un n := by rw [rlIn_eq, hd_un]
  rw [rlOut, rlGates, hh, rlCount_spec, un_length]
  have e1 : (un n ++ un l.length).tail = un (n + l.length - 1) := by
    have e : un n ++ un l.length = un (n + l.length) := by unfold un; rw [List.replicate_add]
    rw [e, rl_un_tail]
  have e2 : (List.range l.length).flatMap (fun i => rlBody (pairB (un i) (rlIn (n, l)))) =
      (List.range l.length).flatMap
        (fun j => true :: encodeGate (rlGateOf n j (l.getD j (false, Sum.inl 0, Sum.inl 0)))) := by
    apply List.flatMap_congr
    intro i hi
    have hi' : i < l.length := List.mem_range.1 hi
    rw [rlBody_spec n i l hi', List.getD_eq_getElem _ _ hi']
  rw [e1, e2, rlBin_un]
  simp [encodeLgp, encodeList, List.flatMap_map, un]

theorem reloc : PEqualNP.Library.ComputableInPolyTime (fun p : ℕ × List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) => (List.replicate p.1 true ++ [false]) ++ PEqualNP.CircuitLowerBounds.encodeList (fun g : Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) => g.1 :: (Sum.elim (fun a : ℕ => false :: (List.replicate a true ++ [false])) (fun d : ℕ => true :: (List.replicate d true ++ [false])) g.2.1 ++ Sum.elim (fun a : ℕ => false :: (List.replicate a true ++ [false])) (fun d : ℕ => true :: (List.replicate d true ++ [false])) g.2.2)) p.2) PEqualNP.MetaComplexity.encodeLgp (fun p : ℕ × List (Bool × (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) => (p.1, PEqualNP.CircuitLowerBounds.Circuit.mk ((List.range p.2.length).map (fun j : ℕ => PEqualNP.CircuitLowerBounds.Gate.mk (if (p.2.getD j (false, Sum.inl 0, Sum.inl 0)).1 then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and) [Sum.elim (fun a : ℕ => a) (fun d : ℕ => p.1 + j - d) (p.2.getD j (false, Sum.inl 0, Sum.inl 0)).2.1, Sum.elim (fun a : ℕ => a) (fun d : ℕ => p.1 + j - d) (p.2.getD j (false, Sum.inl 0, Sum.inl 0)).2.2])) (p.1 + p.2.length - 1))) := by
  obtain ⟨c⟩ := cpt_rlOut
  exact MachinePair.cpt_transport c rlIn _ (fun _ => rfl) (fun p => (rlOut_spec p.1 p.2).symm)

end PEqualNP.MetaComplexity.Helpers.MachineReloc
