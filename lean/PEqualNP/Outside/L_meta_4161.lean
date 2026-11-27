import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4161

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

inductive WireRef where
  | const (b : Bool)
  | wire (idx : ℕ)
  deriving DecidableEq

def evalRef (w : List Bool) : WireRef → Bool
  | .const b => b
  | .wire idx => w.getD idx false

def RefBounded (k : ℕ) : WireRef → Prop
  | .const _ => True
  | .wire idx => idx < k

lemma refBounded_mono {k k' : ℕ} (hk : k ≤ k') {r : WireRef} (hr : RefBounded k r) : RefBounded k' r := by
  cases r with
  | const b => trivial
  | wire idx => exact Nat.lt_of_lt_of_le hr hk

lemma evalRef_append (w : List Bool) (v : Bool) (r : WireRef) (hr : RefBounded w.length r) :
    evalRef (w ++ [v]) r = evalRef w r := by
  cases r with
  | const b => rfl
  | wire idx =>
    change (w ++ [v]).getD idx false = w.getD idx false
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hr, ← List.getD_eq_getElem?_getD]

lemma lookup_bounded {map : List WireRef} {k : ℕ} (hb : ∀ r ∈ map, RefBounded k r) (i : ℕ) :
    RefBounded k (map.getD i (.const false)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : map[i]? with
  | none => trivial
  | some r => exact hb r (List.mem_of_getElem? h)

def xInp (x : Fin 8 → Bool) : List Bool :=
  [x 1, x 0, x 4, x 7, x 5, x 2, true, x 6, x 3, x 1 || true]

def map0 : List WireRef :=
  [.wire 1, .wire 0, .wire 4, .wire 7, .wire 5, .wire 2, .const true, .wire 6, .wire 3, .const true]

def gateUses (g : Gate) : List ℕ :=
  if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs

def FanInTwoGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def stepOne (g : Gate) (map : List WireRef) (outGates : List Gate) : WireRef × List Gate :=
  let wref (i : ℕ) := map.getD i (.const false)
  match g.op with
  | .not =>
    match g.inputs with
    | [] => (.const true, outGates)
    | i :: _ =>
      match wref i with
      | .const b => (.const (!b), outGates)
      | .wire idx => (.wire (8 + outGates.length), outGates ++ [{ op := .not, inputs := [idx] }])
  | .and =>
    match g.inputs with
    | [] => (.const true, outGates)
    | [i] => (wref i, outGates)
    | [i, k] =>
      match wref i, wref k with
      | .const false, _ => (.const false, outGates)
      | _, .const false => (.const false, outGates)
      | .const true, r => (r, outGates)
      | r, .const true => (r, outGates)
      | .wire idx1, .wire idx2 => (.wire (8 + outGates.length), outGates ++ [{ op := .and, inputs := [idx1, idx2] }])
    | _ => (.const false, outGates)
  | .or =>
    match g.inputs with
    | [] => (.const false, outGates)
    | [i] => (wref i, outGates)
    | [i, k] =>
      match wref i, wref k with
      | .const true, _ => (.const true, outGates)
      | _, .const true => (.const true, outGates)
      | .const false, r => (r, outGates)
      | r, .const false => (r, outGates)
      | .wire idx1, .wire idx2 => (.wire (8 + outGates.length), outGates ++ [{ op := .or, inputs := [idx1, idx2] }])
    | _ => (.const false, outGates)
  | _ => (.const false, outGates)

def stepState (st : List WireRef × List Gate) (g : Gate) : List WireRef × List Gate :=
  let res := stepOne g st.1 st.2
  (st.1 ++ [res.1], res.2)

lemma wires_length_aux (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_append_gate (gs : List Gate) (g : Gate) (w : List Bool) :
    (gs ++ [g]).foldl (fun acc h => acc ++ [h.op.eval (h.inputs.map fun i => acc.getD i false)]) w =
      let w' := gs.foldl (fun acc h => acc ++ [h.op.eval (h.inputs.map fun i => acc.getD i false)]) w
      w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)] := by
  simp

def StateInv (x : Fin 8 → Bool) (origW : List Bool) (map : List WireRef) (outGates : List Gate) : Prop :=
  origW.length = map.length ∧
  (∀ r ∈ map, RefBounded (8 + outGates.length) r) ∧
  (∀ g ∈ outGates, FanInTwoGate g) ∧
  (∀ i : ℕ, origW.getD i false = evalRef (Circuit.wires { gates := outGates, output := 0 } (List.ofFn x)) (map.getD i (.const false)))

lemma stateInv_init (x : Fin 8 → Bool) : StateInv x (xInp x) map0 [] := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r hr
    simp only [map0, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RefBounded]
  · intro g hg
    simp at hg
  · intro i
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
      simp [xInp, map0, evalRef, Circuit.wires, List.getD]

lemma getD_append_match {α : Type} (l : List α) (x : α) (d : α) (n : ℕ) (m : ℕ) (hm : m = l.length) :
    (l ++ [x]).getD n d = if n = m then x else l.getD n d := by
  subst hm
  by_cases hlt : n < l.length
  · have hne : n ≠ l.length := Nat.ne_of_lt hlt
    simp only [hne, ite_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  · by_cases heq : n = l.length
    · subst heq
      simp
    · have hgt : l.length < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
      simp only [heq, ite_false]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      have h1 : (l ++ [x])[n]? = none := List.getElem?_eq_none (by simp; omega)
      have h2 : l[n]? = none := List.getElem?_eq_none (by omega)
      rw [h1, h2]

lemma stateInv_push_const {x : Fin 8 → Bool} {origW : List Bool} {map : List WireRef} {outGates : List Gate}
    (hinv : StateInv x origW map outGates) (v : Bool) (r : WireRef)
    (hr : RefBounded (8 + outGates.length) r)
    (heq : v = evalRef (Circuit.wires { gates := outGates, output := 0 } (List.ofFn x)) r) :
    StateInv x (origW ++ [v]) (map ++ [r]) outGates := by
  rcases hinv with ⟨hlen, hbd, hfan, hmatch⟩
  refine ⟨by simp [hlen], ?_, hfan, ?_⟩
  · intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hbd s hs
    · exact hr
  · intro i
    rw [getD_append_match origW v false i origW.length rfl]
    rw [getD_append_match map r (.const false) i origW.length hlen]
    split_ifs
    · exact heq
    · exact hmatch i

lemma stateInv_push_gate {x : Fin 8 → Bool} {origW : List Bool} {map : List WireRef} {outGates : List Gate}
    (hinv : StateInv x origW map outGates) (v : Bool) (g' : Gate)
    (hg' : FanInTwoGate g')
    (heq : v = g'.op.eval (g'.inputs.map fun i => (Circuit.wires { gates := outGates, output := 0 } (List.ofFn x)).getD i false)) :
    StateInv x (origW ++ [v]) (map ++ [.wire (8 + outGates.length)]) (outGates ++ [g']) := by
  rcases hinv with ⟨hlen, hbd, hfan, hmatch⟩
  let nw := Circuit.wires { gates := outGates, output := 0 } (List.ofFn x)
  have hnwlen : nw.length = 8 + outGates.length := by
    dsimp [nw, Circuit.wires]
    rw [wires_length_aux, List.length_ofFn]
  have hnw' : Circuit.wires { gates := outGates ++ [g'], output := 0 } (List.ofFn x) =
      nw ++ [g'.op.eval (g'.inputs.map fun i => nw.getD i false)] := by
    dsimp [nw, Circuit.wires]
    exact wires_append_gate outGates g' (List.ofFn x)
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact refBounded_mono (by simp) (hbd s hs)
    · simp [RefBounded]
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hfan g hg
    · exact hg'
  · intro i
    rw [hnw']
    rw [getD_append_match origW v false i origW.length rfl]
    rw [getD_append_match map (.wire (8 + outGates.length)) (.const false) i origW.length hlen]
    split_ifs
    · change v = (nw ++ [g'.op.eval (g'.inputs.map fun i => nw.getD i false)]).getD (8 + outGates.length) false
      rw [← hnwlen, getD_append_match nw _ false nw.length nw.length rfl]
      simp only [ite_true]
      exact heq
    · rw [hmatch i]
      symm
      change evalRef (nw ++ [g'.op.eval (g'.inputs.map fun i => nw.getD i false)]) (map.getD i (.const false)) = evalRef nw (map.getD i (.const false))
      apply evalRef_append nw _ (map.getD i (.const false))
      rw [hnwlen]
      exact lookup_bounded hbd i

lemma stepOne_step (g : Gate) (hg : FanInTwoGate g) (x : Fin 8 → Bool)
    (origW : List Bool) (map : List WireRef) (outGates : List Gate)
    (hinv : StateInv x origW map outGates) :
    StateInv x
      (origW ++ [g.op.eval (g.inputs.map fun i => origW.getD i false)])
      (stepState (map, outGates) g).1
      (stepState (map, outGates) g).2 := by
  have hmatch := hinv.2.2.2
  have hbd := hinv.2.1
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  dsimp only at hop hlen ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨k, _ | ⟨z, zs⟩⟩⟩
    · simp [stepState, stepOne, GateOp.eval]
      exact stateInv_push_const hinv true (.const true) trivial rfl
    · simp only [stepState, stepOne, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      exact stateInv_push_const hinv (origW.getD i false) (map.getD i (.const false)) (lookup_bounded hbd i) (hmatch i)
    · simp only [stepState, stepOne, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      have hi := hmatch i
      have hk := hmatch k
      cases hri : map.getD i (.const false) with
      | const bi =>
        cases bi
        · dsimp only
          have him : origW.getD i false = false := by rw [hi, hri]; rfl
          rw [him, Bool.false_and]
          exact stateInv_push_const hinv false (.const false) trivial rfl
        · cases hrk : map.getD k (.const false) with
          | const bk =>
            have him : origW.getD i false = true := by rw [hi, hri]; rfl
            have hkm := hk
            rw [hrk] at hkm
            simp only [evalRef] at hkm
            rw [him, hkm]
            cases bk <;> exact stateInv_push_const hinv _ _ trivial rfl
          | wire idxk =>
            dsimp only
            have him : origW.getD i false = true := by rw [hi, hri]; rfl
            have hkm := hk
            rw [hrk] at hkm
            rw [him, Bool.true_and]
            exact stateInv_push_const hinv _ (.wire idxk) (by rw [← hrk]; exact lookup_bounded hbd k) hkm
      | wire idxi =>
        cases hrk : map.getD k (.const false) with
        | const bk =>
          cases bk
          · dsimp only
            have hkm : origW.getD k false = false := by rw [hk, hrk]; rfl
            rw [hkm, Bool.and_false]
            exact stateInv_push_const hinv false (.const false) trivial rfl
          · dsimp only
            have him := hi
            rw [hri] at him
            have hkm : origW.getD k false = true := by rw [hk, hrk]; rfl
            rw [hkm, Bool.and_true]
            exact stateInv_push_const hinv _ (.wire idxi) (by rw [← hri]; exact lookup_bounded hbd i) him
        | wire idxk =>
          dsimp only
          apply stateInv_push_gate hinv _ { op := .and, inputs := [idxi, idxk] } ⟨by simp, by simp⟩
          rw [hi, hk, hri, hrk]
          simp [evalRef, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨i, _ | ⟨k, _ | ⟨z, zs⟩⟩⟩
    · simp [stepState, stepOne, GateOp.eval]
      exact stateInv_push_const hinv false (.const false) trivial rfl
    · simp only [stepState, stepOne, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      exact stateInv_push_const hinv (origW.getD i false) (map.getD i (.const false)) (lookup_bounded hbd i) (hmatch i)
    · simp only [stepState, stepOne, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have hi := hmatch i
      have hk := hmatch k
      cases hri : map.getD i (.const false) with
      | const bi =>
        cases bi
        · cases hrk : map.getD k (.const false) with
          | const bk =>
            have him : origW.getD i false = false := by rw [hi, hri]; rfl
            have hkm := hk
            rw [hrk] at hkm
            simp only [evalRef] at hkm
            rw [him, hkm]
            cases bk <;> exact stateInv_push_const hinv _ _ trivial rfl
          | wire idxk =>
            dsimp only
            have him : origW.getD i false = false := by rw [hi, hri]; rfl
            have hkm := hk
            rw [hrk] at hkm
            rw [him, Bool.false_or]
            exact stateInv_push_const hinv _ (.wire idxk) (by rw [← hrk]; exact lookup_bounded hbd k) hkm
        · dsimp only
          have him : origW.getD i false = true := by rw [hi, hri]; rfl
          rw [him, Bool.true_or]
          exact stateInv_push_const hinv true (.const true) trivial rfl
      | wire idxi =>
        cases hrk : map.getD k (.const false) with
        | const bk =>
          cases bk
          · dsimp only
            have him := hi
            rw [hri] at him
            have hkm : origW.getD k false = false := by rw [hk, hrk]; rfl
            rw [hkm, Bool.or_false]
            exact stateInv_push_const hinv _ (.wire idxi) (by rw [← hri]; exact lookup_bounded hbd i) him
          · dsimp only
            have hkm : origW.getD k false = true := by rw [hk, hrk]; rfl
            rw [hkm, Bool.or_true]
            exact stateInv_push_const hinv true (.const true) trivial rfl
        | wire idxk =>
          dsimp only
          apply stateInv_push_gate hinv _ { op := .or, inputs := [idxi, idxk] } ⟨by simp, by simp⟩
          rw [hi, hk, hri, hrk]
          simp [evalRef, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨i, is⟩
    · simp [stepState, stepOne, GateOp.eval]
      exact stateInv_push_const hinv true (.const true) trivial rfl
    · dsimp only [stepState, stepOne]
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      have hi := hmatch i
      cases hri : map.getD i (.const false) with
      | const bi =>
        dsimp only
        have him : origW.getD i false = bi := by rw [hi, hri]; rfl
        rw [him]
        exact stateInv_push_const hinv (!bi) (.const (!bi)) trivial rfl
      | wire idxi =>
        dsimp only
        apply stateInv_push_gate hinv _ { op := .not, inputs := [idxi] } ⟨by simp, by simp⟩
        rw [hi, hri]
        rfl

lemma fold_stepState_inv (gs : List Gate) (hfan : ∀ g ∈ gs, FanInTwoGate g) (x : Fin 8 → Bool)
    (origW : List Bool) (map : List WireRef) (outGates : List Gate)
    (hinv : StateInv x origW map outGates) :
    StateInv x
      (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) origW)
      (gs.foldl stepState (map, outGates)).1
      (gs.foldl stepState (map, outGates)).2 := by
  induction gs generalizing origW map outGates with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : FanInTwoGate g := hfan g (by simp)
    have hgs : ∀ h ∈ gs, FanInTwoGate h := fun h hh => hfan h (by simp [hh])
    have hinv' := stepOne_step g hg x origW map outGates hinv
    let st' := stepState (map, outGates) g
    exact ih hgs _ st'.1 st'.2 hinv'

lemma stepState_preserves (st : List WireRef × List Gate) (g : Gate) {w : ℕ} (hw : w < st.1.length) :
    (stepState st g).1.getD w (.const false) = st.1.getD w (.const false) := by
  simp only [stepState]
  rw [getD_append_match st.1 _ (.const false) w st.1.length rfl, if_neg (Nat.ne_of_lt hw)]

lemma fold_stepState_preserves (gs : List Gate) (st : List WireRef × List Gate) {w : ℕ} (hw : w < st.1.length) :
    w < (gs.foldl stepState st).1.length ∧ (gs.foldl stepState st).1.getD w (.const false) = st.1.getD w (.const false) := by
  induction gs generalizing st with
  | nil => exact ⟨hw, rfl⟩
  | cons g gs ih =>
    have hw' : w < (stepState st g).1.length := by simp [stepState]; omega
    have hpre := stepState_preserves st g hw
    rcases ih (stepState st g) hw' with ⟨h1, h2⟩
    exact ⟨h1, h2.trans hpre⟩

lemma stepOne_size_le (g : Gate) (map : List WireRef) (og : List Gate) :
    (stepOne g map og).2.length ≤ og.length + 1 := by
  dsimp only [stepOne]
  repeat' split
  all_goals dsimp only; try simp only [List.length_append, List.length_cons, List.length_nil]
  all_goals omega

lemma stepOne_constTrue (g : Gate) (hg : FanInTwoGate g) (map : List WireRef) (og : List Gate)
    (w : ℕ) (hw : (gateUses g).contains w = true) (hm : map.getD w (.const false) = .const true) :
    (stepOne g map og).2.length = og.length := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  dsimp only at hop hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨k, _ | ⟨z, zs⟩⟩⟩
    · simp [gateUses, GateOp.eval] at hw
    · dsimp only [stepOne]
    · simp [gateUses, GateOp.eval] at hw
      rcases hw with rfl | rfl
      · dsimp only [stepOne]; rw [hm]
        cases map.getD k (.const false) with
        | const bk => cases bk <;> rfl
        | wire idxk => rfl
      · dsimp only [stepOne]; rw [hm]
        cases map.getD i (.const false) with
        | const bi => cases bi <;> rfl
        | wire idxi => rfl
    · simp at hlen
  · rcases ins with _ | ⟨i, _ | ⟨k, _ | ⟨z, zs⟩⟩⟩
    · simp [gateUses, GateOp.eval] at hw
    · dsimp only [stepOne]
    · simp [gateUses, GateOp.eval] at hw
      rcases hw with rfl | rfl
      · dsimp only [stepOne]; rw [hm]
      · dsimp only [stepOne]; rw [hm]
        cases map.getD i (.const false) with
        | const bi => cases bi <;> rfl
        | wire idxi => rfl
    · simp at hlen
  · rcases ins with _ | ⟨i, is⟩
    · simp [gateUses, GateOp.eval] at hw
    · simp [gateUses, GateOp.eval] at hw
      subst hw
      dsimp only [stepOne]; rw [hm]

lemma fold_elim_one (gs : List Gate) (hfan : ∀ g ∈ gs, FanInTwoGate g) (st : List WireRef × List Gate)
    (w : ℕ) (hw : w < st.1.length) (hm : st.1.getD w (.const false) = .const true) :
    (gs.foldl stepState st).2.length + (gs.filter (fun g => (gateUses g).contains w)).length ≤ st.2.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.filter_cons, List.length_cons]
    have hg : FanInTwoGate g := hfan g (by simp)
    have hgs : ∀ h ∈ gs, FanInTwoGate h := fun h hh => hfan h (by simp [hh])
    have hw' : w < (stepState st g).1.length := by simp [stepState]; omega
    have hm' : (stepState st g).1.getD w (.const false) = .const true := (stepState_preserves st g hw).trans hm
    have hrec := ih hgs (stepState st g) hw' hm'
    by_cases hc : (gateUses g).contains w = true
    · simp only [hc, ite_true, List.length_cons]
      have hkill : (stepState st g).2.length = st.2.length := stepOne_constTrue g hg st.1 st.2 w hc hm
      omega
    · have hcf : ((gateUses g).contains w = true) = False := eq_false hc
      rw [if_neg hc]
      have hle : (stepState st g).2.length ≤ st.2.length + 1 := stepOne_size_le g st.1 st.2
      omega

lemma fold_elim_two (gs : List Gate) (hfan : ∀ g ∈ gs, FanInTwoGate g) (st : List WireRef × List Gate)
    (w1 w2 : ℕ) (hw1 : w1 < st.1.length) (hm1 : st.1.getD w1 (.const false) = .const true)
    (hw2 : w2 < st.1.length) (hm2 : st.1.getD w2 (.const false) = .const true) :
    (gs.foldl stepState st).2.length + (gs.filter (fun g => (gateUses g).contains w1 || (gateUses g).contains w2)).length ≤ st.2.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.filter_cons, List.length_cons]
    have hg : FanInTwoGate g := hfan g (by simp)
    have hgs : ∀ h ∈ gs, FanInTwoGate h := fun h hh => hfan h (by simp [hh])
    have hw1' : w1 < (stepState st g).1.length := by simp [stepState]; omega
    have hm1' : (stepState st g).1.getD w1 (.const false) = .const true := (stepState_preserves st g hw1).trans hm1
    have hw2' : w2 < (stepState st g).1.length := by simp [stepState]; omega
    have hm2' : (stepState st g).1.getD w2 (.const false) = .const true := (stepState_preserves st g hw2).trans hm2
    have hrec := ih hgs (stepState st g) hw1' hm1' hw2' hm2'
    by_cases hc : ((gateUses g).contains w1 || (gateUses g).contains w2) = true
    · simp only [hc, ite_true, List.length_cons]
      simp only [Bool.or_eq_true] at hc
      have hkill : (stepState st g).2.length = st.2.length := by
        rcases hc with h1 | h2
        · exact stepOne_constTrue g hg st.1 st.2 w1 h1 hm1
        · exact stepOne_constTrue g hg st.1 st.2 w2 h2 hm2
      omega
    · rw [if_neg hc]
      have hle : (stepState st g).2.length ≤ st.2.length + 1 := stepOne_size_le g st.1 st.2
      omega

lemma stepOne_x5 (x5 : Gate) (hx5op : x5.op = .or) (hx5len : x5.inputs.length ≤ 2)
    (hx5in6 : ((gateUses x5).any fun n => decide (n = 6)) = true)
    (map : List WireRef) (og : List Gate) (hm6 : map.getD 6 (.const false) = .const true) :
    stepOne x5 map og = (.const true, og) := by
  rcases x5 with ⟨op, ins⟩
  dsimp only at hx5op hx5len hx5in6
  subst hx5op
  rcases ins with _ | ⟨i, _ | ⟨k, _ | ⟨z, zs⟩⟩⟩
  · simp [gateUses, GateOp.eval] at hx5in6
  · simp [gateUses, GateOp.eval] at hx5in6
    subst hx5in6
    dsimp only [stepOne]; rw [hm6]
  · simp [gateUses, GateOp.eval] at hx5in6
    rcases hx5in6 with rfl | rfl
    · dsimp only [stepOne]; rw [hm6]
    · dsimp only [stepOne]; rw [hm6]
      cases map.getD i (.const false) with
      | const bi => cases bi <;> rfl
      | wire idxi => rfl
  · simp at hx5len

end PEqualNP.Outside.L_meta_4161

theorem PEqualNP.Outside.L_meta_4161 : have x1 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x1 : Bool) (x2 : Fin (8 : ℕ) → Bool) => [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]; have x2 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs; ∀ (x3 x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x3 ++ x5 :: x4, output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → ((x2 x5).any fun (x10 : ℕ) => Decidable.decide (x10 = (6 : ℕ))) = Bool.true → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => x7.eval (x1 Bool.true x11)) (Max.max (1 : ℕ) (x3.length + x4.length - ((List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => (x2 x11).contains (9 : ℕ)) x3).length + (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => (x2 x11).contains (9 : ℕ) || (x2 x11).contains ((10 : ℕ) + x3.length)) x4).length))) := by
  dsimp only
  intro x3 x4 x5 x6 hfan hx5op hx5in
  have hfan_list : ∀ g ∈ x3 ++ x5 :: x4, PEqualNP.Outside.L_meta_4161.FanInTwoGate g := hfan
  have hfan3 : ∀ g ∈ x3, PEqualNP.Outside.L_meta_4161.FanInTwoGate g := fun g hg => hfan_list g (by simp [hg])
  have hfan5 : PEqualNP.Outside.L_meta_4161.FanInTwoGate x5 := hfan_list x5 (by simp)
  have hfan4 : ∀ g ∈ x4, PEqualNP.Outside.L_meta_4161.FanInTwoGate g := fun g hg => hfan_list g (by simp [hg])
  let st0 : List PEqualNP.Outside.L_meta_4161.WireRef × List PEqualNP.CircuitLowerBounds.Gate := (PEqualNP.Outside.L_meta_4161.map0, [])
  let st1 := x3.foldl PEqualNP.Outside.L_meta_4161.stepState st0
  let st2 := PEqualNP.Outside.L_meta_4161.stepState st1 x5
  let st3 := x4.foldl PEqualNP.Outside.L_meta_4161.stepState st2
  have h9_0 : 9 < st0.1.length ∧ st0.1.getD 9 (.const false) = .const true := by simp [st0, PEqualNP.Outside.L_meta_4161.map0, List.getD]
  have h6_0 : 6 < st0.1.length ∧ st0.1.getD 6 (.const false) = .const true := by simp [st0, PEqualNP.Outside.L_meta_4161.map0, List.getD]
  have hst1_6 := PEqualNP.Outside.L_meta_4161.fold_stepState_preserves x3 st0 h6_0.1
  have hm6_1 : st1.1.getD 6 (.const false) = .const true := hst1_6.2.trans h6_0.2
  have hst1_9 := PEqualNP.Outside.L_meta_4161.fold_stepState_preserves x3 st0 h9_0.1
  have hm9_1 : st1.1.getD 9 (.const false) = .const true := hst1_9.2.trans h9_0.2
  have hx5step : PEqualNP.Outside.L_meta_4161.stepOne x5 st1.1 st1.2 = (.const true, st1.2) :=
    PEqualNP.Outside.L_meta_4161.stepOne_x5 x5 hx5op hfan5.2 (by simpa [PEqualNP.Outside.L_meta_4161.gateUses] using hx5in) st1.1 st1.2 hm6_1
  have hst1_len : st1.1.length = 10 + x3.length := by
    have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List PEqualNP.Outside.L_meta_4161.WireRef × List PEqualNP.CircuitLowerBounds.Gate), (gs.foldl PEqualNP.Outside.L_meta_4161.stepState s).1.length = s.1.length + gs.length := by
      intro gs s
      induction gs generalizing s with
      | nil => simp
      | cons g gs ih => simp [PEqualNP.Outside.L_meta_4161.stepState, ih]; omega
    simp [st1, hfold, st0, PEqualNP.Outside.L_meta_4161.map0]
  have hst2_eq : st2 = (st1.1 ++ [.const true], st1.2) := by simp [st2, PEqualNP.Outside.L_meta_4161.stepState, hx5step]
  have h9_2 : 9 < st2.1.length := by rw [hst2_eq]; simp; omega
  have hm9_2 : st2.1.getD 9 (.const false) = .const true := by
    rw [hst2_eq, PEqualNP.Outside.L_meta_4161.getD_append_match st1.1 _ (.const false) 9 st1.1.length rfl, if_neg (by omega)]
    exact hm9_1
  have h10_2 : 10 + x3.length < st2.1.length := by rw [hst2_eq]; simp [hst1_len]
  have hm10_2 : st2.1.getD (10 + x3.length) (.const false) = .const true := by
    rw [hst2_eq, PEqualNP.Outside.L_meta_4161.getD_append_match st1.1 _ (.const false) (10 + x3.length) st1.1.length rfl, if_pos hst1_len.symm]
  have hbound1 := PEqualNP.Outside.L_meta_4161.fold_elim_one x3 hfan3 st0 9 h9_0.1 h9_0.2
  have hbound2 := PEqualNP.Outside.L_meta_4161.fold_elim_two x4 hfan4 st2 9 (10 + x3.length) h9_2 hm9_2 h10_2 hm10_2
  have hst2_sz : st2.2.length = st1.2.length := by rw [hst2_eq]
  have htotal : st3.2.length ≤ Max.max 1 (x3.length + x4.length - ((List.filter (fun g => (PEqualNP.Outside.L_meta_4161.gateUses g).contains 9) x3).length + (List.filter (fun g => (PEqualNP.Outside.L_meta_4161.gateUses g).contains 9 || (PEqualNP.Outside.L_meta_4161.gateUses g).contains (10 + x3.length)) x4).length)) := by
    have h0sz : st0.2.length = 0 := rfl
    dsimp only [st1, st2, st3] at hbound1 hbound2 hst2_sz ⊢
    exact le_trans (by omega) (Nat.le_max_right 1 _)
  have hinv_all : ∀ x11 : Fin 8 → Bool, PEqualNP.Outside.L_meta_4161.StateInv x11 (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := x3 ++ x5 :: x4, output := x6 } (PEqualNP.Outside.L_meta_4161.xInp x11)) st3.1 st3.2 := by
    intro x11
    have h0 := PEqualNP.Outside.L_meta_4161.stateInv_init x11
    have h1 := PEqualNP.Outside.L_meta_4161.fold_stepState_inv x3 hfan3 x11 (PEqualNP.Outside.L_meta_4161.xInp x11) st0.1 st0.2 h0
    have h2 := PEqualNP.Outside.L_meta_4161.stepOne_step x5 hfan5 x11 _ st1.1 st1.2 h1
    have h3 := PEqualNP.Outside.L_meta_4161.fold_stepState_inv x4 hfan4 x11 _ st2.1 st2.2 h2
    simpa [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append, List.foldl_cons, st1, st2, st3] using h3
  have hinv_fan : PEqualNP.MetaComplexity.FanInTwo { gates := st3.2, output := 0 } := (hinv_all (fun _ => false)).2.2.1
  cases hout : st3.1.getD x6 (.const false) with
  | wire idx =>
    refine ⟨{ gates := st3.2, output := idx }, hinv_fan, ?_, ?_⟩
    · exact htotal
    · intro x11
      have hm := (hinv_all x11).2.2.2 x6
      rw [hout] at hm
      simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_4161.evalRef, PEqualNP.Outside.L_meta_4161.xInp] using hm.symm
  | const b =>
    cases b
    · refine ⟨{ gates := [], output := 8 }, by intro g hg; simp at hg, le_trans (by simp [PEqualNP.CircuitLowerBounds.Circuit.size]) (Nat.le_max_left 1 _), ?_⟩
      intro x11
      have hm := (hinv_all x11).2.2.2 x6
      rw [hout] at hm
      simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_4161.evalRef, PEqualNP.Outside.L_meta_4161.xInp, List.getD] using hm.symm
    · refine ⟨{ gates := [{ op := .not, inputs := [8] }], output := 8 }, by intro g hg; simp at hg; rcases hg with rfl; simp, le_trans (by simp [PEqualNP.CircuitLowerBounds.Circuit.size]) (Nat.le_max_left 1 _), ?_⟩
      intro x11
      have hm := (hinv_all x11).2.2.2 x6
      rw [hout] at hm
      simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.Outside.L_meta_4161.evalRef, PEqualNP.Outside.L_meta_4161.xInp, PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD] using hm.symm
