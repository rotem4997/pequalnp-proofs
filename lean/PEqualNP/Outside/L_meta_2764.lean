import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2764

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp <;> omega

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def sortKey (i : ℕ) : ℕ :=
  if i < 9 then i else if i = 24 then 9 else i + 1

def okInput (bound : ℕ) (i : ℕ) : Prop :=
  i < bound ∨ i = 24

def shape (bound : ℕ) (g : Gate) : Prop :=
  g = ⟨.and, []⟩ ∨
  (∃ a : ℕ, okInput bound a ∧ g = ⟨.not, [a]⟩) ∨
  ∃ a b : ℕ, okInput bound a ∧ okInput bound b ∧ sortKey a ≤ sortKey b ∧
    (g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [a, b]⟩)

def clamp (bound i : ℕ) : ℕ :=
  if i < bound then i else 24

theorem clamp_ok (bound i : ℕ) : okInput bound (clamp bound i) := by
  simp only [clamp, okInput]
  split_ifs <;> omega

theorem clamp_getD (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
    w.getD (clamp w.length i) false = w.getD i false := by
  simp only [clamp]
  by_cases h : i < w.length
  · simp [h]
  · rw [ite_eq_right (by exact h), List.getD_eq_default _ _ (by omega : w.length ≤ i),
      List.getD_eq_default _ _ hw]

def binary (op : GateOp) (bound a b : ℕ) : Gate :=
  let a' := clamp bound a
  let b' := clamp bound b
  if sortKey a' ≤ sortKey b' then ⟨op, [a', b']⟩ else ⟨op, [b', a']⟩

theorem binary_shape (bound a b : ℕ) {op : GateOp}
    (hop : op = .and ∨ op = .or) : shape bound (binary op bound a b) := by
  dsimp [binary]
  split_ifs with h
  · refine Or.inr (Or.inr ⟨_, _, clamp_ok bound a, clamp_ok bound b, h, ?_⟩)
    rcases hop with rfl | rfl <;> simp
  · have h' : sortKey (clamp bound b) ≤ sortKey (clamp bound a) := by omega
    refine Or.inr (Or.inr ⟨_, _, clamp_ok bound b, clamp_ok bound a, h', ?_⟩)
    rcases hop with rfl | rfl <;> simp

def normalizeGate (bound : ℕ) : Gate → Gate
  | ⟨.and, []⟩ => ⟨.and, []⟩
  | ⟨.or, []⟩ => ⟨.and, [24, 24]⟩
  | ⟨.and, [a]⟩ => binary .and bound a a
  | ⟨.or, [a]⟩ => binary .or bound a a
  | ⟨.and, a :: b :: _⟩ => binary .and bound a b
  | ⟨.or, a :: b :: _⟩ => binary .or bound a b
  | ⟨.not, []⟩ => ⟨.and, []⟩
  | ⟨.not, a :: _⟩ => ⟨.not, [clamp bound a]⟩
  | g => g

theorem normalizeGate_shape (bound : ℕ) (g : Gate) (hg : allowed g) :
    shape bound (normalizeGate bound g) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact Or.inl rfl
    · exact binary_shape bound a a (Or.inl rfl)
    · exact binary_shape bound a b (Or.inl rfl)
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · refine Or.inr (Or.inr ⟨24, 24, Or.inr rfl, Or.inr rfl, le_rfl, Or.inl rfl⟩)
    · exact binary_shape bound a a (Or.inr rfl)
    · exact binary_shape bound a b (Or.inr rfl)
  | not =>
    cases ins with
    | nil => exact Or.inl rfl
    | cons a _ => exact Or.inr (Or.inl ⟨_, clamp_ok bound a, rfl⟩)
  | mod _ => simp [allowed] at hg
  | maj => simp [allowed] at hg

theorem binary_value (w : List Bool) (hw : w.length ≤ 24) (a b : ℕ) {op : GateOp}
    (hop : op = .and ∨ op = .or) :
    value (binary op w.length a b) w =
      op.eval [w.getD a false, w.getD b false] := by
  dsimp [binary]
  split_ifs with h
  · simp [value, clamp_getD w hw, -List.getD_eq_getElem?_getD]
  · rcases hop with rfl | rfl
    · simp [value, clamp_getD w hw, GateOp.eval, Bool.and_comm,
        -List.getD_eq_getElem?_getD]
    · simp [value, clamp_getD w hw, GateOp.eval, Bool.or_comm,
        -List.getD_eq_getElem?_getD]

theorem getD_24_of_le (w : List Bool) (hw : w.length ≤ 24) :
    w.getD 24 false = false :=
  List.getD_eq_default _ _ hw

theorem normalizeGate_value (w : List Bool) (hw : w.length ≤ 24)
    (g : Gate) (hg : allowed g) :
    value (normalizeGate w.length g) w = value g w := by
  have hd := getD_24_of_le w hw
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [normalizeGate, value, GateOp.eval]
    · change value (binary .and w.length a a) w = _
      rw [binary_value w hw a a (Or.inl rfl)]
      simp [value, GateOp.eval]
    · exact binary_value w hw a b (Or.inl rfl)
    · have : (c :: rest).length + 2 ≤ 2 := hg.2
      simp at this
  | or =>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · have h24 : w[24]?.getD false = false := by
        simpa [List.getD_eq_getElem?_getD] using hd
      simp [normalizeGate, value, GateOp.eval, h24]
    · change value (binary .or w.length a a) w = _
      rw [binary_value w hw a a (Or.inr rfl)]
      simp [value, GateOp.eval]
    · exact binary_value w hw a b (Or.inr rfl)
    · have : (c :: rest).length + 2 ≤ 2 := hg.2
      simp at this
  | not =>
    cases ins with
    | nil => simp [normalizeGate, value, GateOp.eval]
    | cons a rest =>
      simp [normalizeGate, value, GateOp.eval, clamp_getD w hw,
        -List.getD_eq_getElem?_getD]
  | mod _ => simp [allowed] at hg
  | maj => simp [allowed] at hg

def normalize (bound : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => normalizeGate bound g :: normalize (bound + 1) gs

theorem normalize_length (gs : List Gate) (bound : ℕ) :
    (normalize bound gs).length = gs.length := by
  induction gs generalizing bound with
  | nil => rfl
  | cons g gs ih => simp [normalize, ih]

theorem normalize_run (gs : List Gate) (h : ∀ g ∈ gs, allowed g)
    (w : List Bool) (hw : w.length + gs.length ≤ 24) :
    run (normalize w.length gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have ht : ∀ a ∈ gs, allowed a := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have hv := normalizeGate_value w (by omega) g (h g List.mem_cons_self)
    rw [normalize, run_cons, run_cons, hv]
    have hlen : (w ++ [value g w]).length = w.length + 1 := by simp
    have hw' : (w ++ [value g w]).length + gs.length ≤ 24 := by
      simp only [List.length_append, List.length_singleton]
      have : (g :: gs).length = gs.length + 1 := rfl
      omega
    simpa [hlen] using ih ht (w ++ [value g w]) hw'

theorem normalize_shape (gs : List Gate) (h : ∀ g ∈ gs, allowed g) (bound : ℕ)
    (j : Fin (normalize bound gs).length) :
    shape (bound + j.val) ((normalize bound gs).get j) := by
  induction gs generalizing bound with
  | nil => exact Fin.elim0 j
  | cons g gs ih =>
    change Fin ((normalize (bound + 1) gs).length + 1) at j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [normalize] using normalizeGate_shape bound g (h g List.mem_cons_self)
    · have hj := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) (bound + 1) j'
      have he : bound + (j'.val + 1) = bound + 1 + j'.val := by omega
      simpa [normalize, Fin.val_succ, he] using hj

def copy (i : ℕ) : Gate := ⟨.or, [i, i]⟩

theorem copy_shape (bound i : ℕ) (hi : okInput bound i) :
    shape bound (copy i) :=
  Or.inr (Or.inr ⟨i, i, hi, hi, le_rfl, Or.inr rfl⟩)

theorem pad_run (r i : ℕ) (w : List Bool) (hi : i < w.length) :
    run (List.replicate r (copy i)) w = w ++ List.replicate r (w.getD i false) := by
  induction r generalizing w with
  | zero => simp [run, Circuit.wires]
  | succ r ih =>
    rw [List.replicate_succ, run_cons, ih _ (by simp; omega)]
    rw [List.getD_append _ _ _ _ hi]
    simp [copy, value, GateOp.eval, List.replicate_succ, List.append_assoc]

theorem first_shape : shape 9 ⟨.or, [0, 3]⟩ :=
  Or.inr (Or.inr ⟨0, 3, Or.inl (by omega), Or.inl (by omega), by simp [sortKey], Or.inr rfl⟩)

theorem make (C : Circuit) (hfan : FanInTwo C)
    (hfirst : ∀ x : Fin 9 → Bool,
      (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 3))
    (hsize : C.size ≤ 15)
    (hle : 9 ≤ C.output)
    (hlt : C.output < 9 + C.gates.length) :
    ∃ D : Circuit,
      D.gates.length = 15 ∧
      D.output = 23 ∧
      D.gates[0]? = some ⟨.or, [0, 3]⟩ ∧
      (∀ (i : ℕ) (hi : i < D.gates.length),
        shape (9 + i) (D.gates[i])) ∧
      circuitFun 9 D = circuitFun 9 C := by
  let m := C.output + 1 - 9
  have hm : m ≤ C.gates.length := by dsimp [m]; omega
  have hmpos : 0 < m := by dsimp [m]; omega
  have hms : m ≤ 15 := hm.trans hsize
  have hp : (C.gates.take m).length = m := by simp [List.length_take, min_eq_left hm]
  obtain ⟨g, gs, he⟩ : ∃ g gs, C.gates.take m = g :: gs := by
    cases h : C.gates.take m with
    | nil => rw [h] at hp; simp at hp; omega
    | cons g gs => exact ⟨g, gs, rfl⟩
  have hpre : (g :: gs) ++ C.gates.drop m = C.gates := by
    rw [← he, List.take_append_drop]
  have ht (a : Gate) (ha : a ∈ gs) : allowed a := by
    apply hfan
    rw [← hpre]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
  let first : Gate := ⟨.or, [0, 3]⟩
  let core := first :: normalize 10 gs
  let rest := List.replicate (15 - m) (copy C.output)
  have hcore : core.length = m := by
    simp only [core, List.length_cons, normalize_length]
    simpa [he] using hp
  have hrest : rest.length = 15 - m := List.length_replicate
  have hindex : 9 + m = C.output + 1 := by dsimp [m]; omega
  refine ⟨⟨core ++ rest, 23⟩, by simp [hcore, hrest]; omega, rfl, rfl, ?_, ?_⟩
  · intro i hi
    have hi' : i < (core ++ rest).length := by simpa using hi
    by_cases hj : i < core.length
    · have hget : (core ++ rest)[i] = core[i] := List.getElem_append_left hj
      rw [hget]
      let k : Fin core.length := ⟨i, hj⟩
      change shape (9 + k.val) (core.get k)
      change Fin ((normalize 10 gs).length + 1) at k
      refine Fin.cases ?_ (fun q => ?_) k
      · simpa [core, first] using first_shape
      · have heq : 9 + (q.val + 1) = 10 + q.val := by omega
        simpa [core, Fin.val_succ, heq] using normalize_shape gs ht 10 q
    · have hge : core.length ≤ i := by omega
      have hget : (core ++ rest)[i] =
          rest[i - core.length]'(by
            have : i < core.length + rest.length := by simpa [List.length_append] using hi'
            omega) := List.getElem_append_right hge
      rw [hget]
      simp only [rest, List.getElem_replicate]
      refine copy_shape (9 + i) C.output ?_
      left
      have : core.length = m := hcore
      omega
  · funext x
    let w := List.ofFn x
    have hw : w.length = 9 := List.length_ofFn
    have hg : value g w = value first w := by
      have hv : (run C.gates w).getD 9 false = (x 0 || x 3) := by
        simpa [run, Circuit.wires, w] using hfirst x
      have hv' : (run C.gates w).getD 9 false = value first w := by
        rw [hv]
        simp [first, value, GateOp.eval, w, List.getD_eq_getElem, List.getElem_ofFn]
      rw [← hpre, run_append, run_cons,
        run_preserves _ _ _ (by rw [run_length]; simp [hw]; omega),
        run_preserves _ _ _ (by simp [hw]), List.getD_append_right _ _ _ _ (by omega)] at hv'
      simpa [hw] using hv'
    have hr : run core w = run (g :: gs) w := by
      change run (first :: normalize 10 gs) w = run (g :: gs) w
      rw [run_cons, run_cons, hg]
      have hgs : gs.length + 1 = m := by
        have := congrArg List.length he
        simp [hp] at this
        omega
      have hlen : (w ++ [value first w]).length + gs.length ≤ 24 := by
        simp [hw]; omega
      simpa [hw] using normalize_run gs ht (w ++ [value first w]) hlen
    have hlen : (run core w).length = 9 + m := by rw [run_length, hw, hcore]
    have hout : C.output < (run core w).length := by omega
    have hcorrect :
        (run core w).getD C.output false = (run C.gates w).getD C.output false := by
      conv_rhs => rw [← hpre, run_append, ← hr, run_preserves _ _ _ hout]
    change (run (core ++ rest) w).getD 23 false = (run C.gates w).getD C.output false
    dsimp only [rest]
    rw [← hcorrect, run_append, pad_run _ _ _ hout]
    by_cases hz : m = 15
    · have ho : C.output = 23 := by omega
      rw [hz, Nat.sub_self, List.replicate_zero, List.append_nil, ho]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      exact List.getD_replicate _ (by omega)

end PEqualNP.Outside.L_meta_2764

open PEqualNP.Outside.L_meta_2764
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2764 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (15 : ℕ) →
          (∀ (x4 : Fin (9 : ℕ) → Bool),
            (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false =
              (x4 (0 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)))) →
            (9 : ℕ) ≤ x1.output →
              x1.output < (9 : ℕ) + x1.gates.length →
                ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
                  x7.gates.length = (15 : ℕ) ∧
                    x7.output = (23 : ℕ) ∧
                      x7.gates[(0 : ℕ)]? =
                          Option.some
                            { op := PEqualNP.CircuitLowerBounds.GateOp.or,
                              inputs := [(0 : ℕ), (3 : ℕ)] :
                              PEqualNP.CircuitLowerBounds.Gate } ∧
                        (∀ (x8 : ℕ) (x9 : x8 < x7.gates.length),
                          have x10 : PEqualNP.CircuitLowerBounds.Gate := x7.gates[x8];
                          have x11 : ℕ → Prop :=
                            fun (x11 : ℕ) => x11 < (9 : ℕ) + x8 ∨ x11 = (24 : ℕ);
                          have x12 : ℕ → ℕ :=
                            fun (x12 : ℕ) =>
                              if x12 < (9 : ℕ) then x12
                              else if x12 = (24 : ℕ) then (9 : ℕ)
                              else x12 + (1 : ℕ);
                          x10 =
                              { op := PEqualNP.CircuitLowerBounds.GateOp.and,
                                inputs := [] :
                                PEqualNP.CircuitLowerBounds.Gate } ∨
                            (∃ (x13 : ℕ),
                              x11 x13 ∧
                                x10 =
                                  { op := PEqualNP.CircuitLowerBounds.GateOp.not,
                                    inputs := [x13] :
                                    PEqualNP.CircuitLowerBounds.Gate }) ∨
                            ∃ (x13 : ℕ) (x14 : ℕ),
                              x11 x13 ∧
                                x11 x14 ∧
                                  x12 x13 ≤ x12 x14 ∧
                                    (x10 =
                                        { op := PEqualNP.CircuitLowerBounds.GateOp.and,
                                          inputs := [x13, x14] :
                                          PEqualNP.CircuitLowerBounds.Gate } ∨
                                      x10 =
                                        { op := PEqualNP.CircuitLowerBounds.GateOp.or,
                                          inputs := [x13, x14] :
                                          PEqualNP.CircuitLowerBounds.Gate })) ∧
                          PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x7 =
                            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro C hfan hsize hfirst hle hlt
  obtain ⟨D, hlen, hout, hgate, hshape, hfun⟩ := make C hfan hfirst hsize hle hlt
  refine ⟨D, hlen, hout, ?_, ?_, hfun⟩
  · simpa [Gate.mk] using hgate
  · intro i hi
    simpa [shape, okInput, sortKey, Gate.mk] using hshape i hi
