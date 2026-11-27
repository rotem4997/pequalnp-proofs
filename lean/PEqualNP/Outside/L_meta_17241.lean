import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17241

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

def stepSM (R : List (Option ℕ)) (g : Gate) : List (Option ℕ) :=
  let ins := g.inputs.map fun i => R.getD i none
  R ++ [match g.op with
    | GateOp.or => ins.foldl (fun acc o => match acc, o with
        | none, o => o
        | some a, none => some a
        | some a, some b => some (min a b)) none
    | GateOp.and => ins.foldl (fun acc o => match acc, o with
        | some a, some b => some (a + b)
        | _, _ => none) (some 0)
    | _ => none]

theorem foldl_getD_lt (gs : List Gate) (R : List (Option ℕ)) (i : ℕ) (hi : i < R.length) :
    (gs.foldl stepSM R).getD i none = R.getD i none := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepSM R g) (by simp [stepSM]; omega)]
    simp [stepSM, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_getD_gate (gs : List Gate) (R : List (Option ℕ)) (k : ℕ) (g : Gate)
    (hk : gs[k]? = some g) (a b : ℕ) (hab : g.inputs = [a, b])
    (ha : a < R.length + k) (hb : b < R.length + k) :
    let m := fun i => (gs.foldl stepSM R).getD i none
    (g.op = GateOp.and → m (R.length + k) = (m a).bind fun x => Option.map (fun y => x + y) (m b)) ∧
    (g.op = GateOp.or → m (R.length + k) = (Option.map (fun x => min x ((m b).getD x)) (m a)).orElse fun _ => m b) := by
  induction gs generalizing R k with
  | nil => simp at hk
  | cons g0 gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst g0
      simp only [Nat.add_zero] at ha hb ⊢
      have hlen : R.length < (stepSM R g).length := by simp [stepSM]
      have hout : (gs.foldl stepSM (stepSM R g)).getD R.length none = (stepSM R g).getD R.length none :=
        foldl_getD_lt gs (stepSM R g) R.length hlen
      have ha' : (gs.foldl stepSM (stepSM R g)).getD a none = R.getD a none := by
        rw [foldl_getD_lt gs (stepSM R g) a (by simp [stepSM]; omega)]
        simp [stepSM, List.getD_eq_getElem?_getD, List.getElem?_append_left ha]
      have hb' : (gs.foldl stepSM (stepSM R g)).getD b none = R.getD b none := by
        rw [foldl_getD_lt gs (stepSM R g) b (by simp [stepSM]; omega)]
        simp [stepSM, List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
      rw [List.foldl_cons, hout, ha', hb']
      constructor
      · intro hop
        simp only [stepSM, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases R[a]?.getD none <;> cases R[b]?.getD none <;> simp
      · intro hop
        simp only [stepSM, hop, hab, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases R[a]?.getD none <;> cases R[b]?.getD none <;> simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have hlen : (stepSM R g0).length = R.length + 1 := by simp [stepSM]
      have key := ih (stepSM R g0) k hk (by omega) (by omega)
      dsimp only at key ⊢
      rw [List.foldl_cons, show R.length + (k + 1) = (stepSM R g0).length + k by omega]
      exact key

theorem main_proof :
    ∀ (n : ℕ) (C : Circuit) (S : List ℕ) (v : ℕ),
      let m : ℕ → Option ℕ := fun i => (scalarMults C n S v).getD i none
      (∀ i : Fin n, m i.val = if i.val = v then some 1 else if i.val ∈ S then some 0 else none) ∧
      ∀ (k : ℕ) (g : Gate) (a b : ℕ),
        C.gates[k]? = some g → g.inputs = [a, b] → a < n + k → b < n + k →
        (g.op = GateOp.and → m (n + k) = (m a).bind fun x => Option.map (fun y => x + y) (m b)) ∧
        (g.op = GateOp.or → m (n + k) = (Option.map (fun x => min x ((m b).getD x)) (m a)).orElse fun _ => m b) := by
  intro n C S v
  let init : List (Option ℕ) :=
    (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none
  have hlen : init.length = n := by simp [init]
  have hsm : scalarMults C n S v = C.gates.foldl stepSM init := rfl
  dsimp only
  rw [hsm]
  constructor
  · intro i
    rw [foldl_getD_lt C.gates init i.val (by omega)]
    simp [init, List.getD_eq_getElem?_getD, i.isLt]
  · intro k g a b hk hab ha hb
    have key := foldl_getD_gate C.gates init k g hk a b hab (by omega) (by omega)
    simpa only [hlen] using key

end PEqualNP.Outside.L_meta_17241

theorem PEqualNP.Outside.L_meta_17241 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ) (x4 : ℕ),   have x5 : ℕ → Option ℕ := fun (x5 : ℕ) => (PEqualNP.ReadK.scalarMults x2 x1 x3 x4).getD x5 Option.none;   (∀ (x6 : Fin x1), x5 ↑x6 = if ↑x6 = x4 then Option.some (1 : ℕ) else if ↑x6 ∈ x3 then Option.some (0 : ℕ) else Option.none) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x2.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → x8 < x1 + x6 → x9 < x1 + x6 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 (x1 + x6) = (x5 x8).bind fun (x15 : ℕ) => Option.map (fun (x16 : ℕ) => x15 + x16) (x5 x9)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 (x1 + x6) = (Option.map (fun (x15 : ℕ) => Min.min x15 ((x5 x9).getD x15)) (x5 x8)).orElse fun (x15 : Unit) => x5 x9)) :=
  PEqualNP.Outside.L_meta_17241.main_proof
