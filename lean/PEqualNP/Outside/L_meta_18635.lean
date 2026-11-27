import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18635_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def slot (lim u : ℕ) : ℕ :=
  if u < lim then (if 2 + u < 128 then 2 + u else 0) else 0

theorem slot_lt (lim u : ℕ) : slot lim u < 128 := by
  unfold slot
  split_ifs <;> omega

def gateA (lim : ℕ) (g : Gate) : ℕ :=
  match g.inputs with
  | [] => if isAndOp g.op then 1 else 0
  | u :: _ => slot lim u

def gateB (lim : ℕ) (g : Gate) : ℕ :=
  match g.inputs with
  | [] => if isAndOp g.op then 1 else 0
  | [_] => if isAndOp g.op then 1 else 0
  | _ :: v :: _ => slot lim v

theorem gateA_lt (lim : ℕ) (g : Gate) : gateA lim g < 128 := by
  unfold gateA
  cases g.inputs with
  | nil => simp; split_ifs <;> omega
  | cons u _ => exact slot_lt lim u

theorem gateB_lt (lim : ℕ) (g : Gate) : gateB lim g < 128 := by
  unfold gateB
  cases g.inputs with
  | nil => simp; split_ifs <;> omega
  | cons _ t =>
    cases t with
    | nil => simp; split_ifs <;> omega
    | cons v _ => exact slot_lt lim v

def encGate (lim : ℕ) (g : Gate) : Fin 32768 :=
  ⟨(if isAndOp g.op then 0 else 16384) + gateA lim g + 128 * gateB lim g, by
    have ha := gateA_lt lim g
    have hb := gateB_lt lim g
    split_ifs <;> omega⟩

def encGates : ℕ → List Gate → List (Fin 32768)
  | _, [] => []
  | lim, g :: gs => encGate lim g :: encGates (lim + 1) gs

theorem encGates_length (lim : ℕ) (gs : List Gate) : (encGates lim gs).length = gs.length := by
  induction gs generalizing lim with
  | nil => rfl
  | cons g gs ih => simp [encGates, ih]

def stepEv (grade : Bool) (w : List ℕ) (t : Fin 32768) : List ℕ :=
  let a := w.getD (t.val % 128) 0
  let b := w.getD (t.val / 128 % 128) 0
  w.concat (if t.val < 16384 then cond grade (a + b) (min a b) else max a b)

theorem encGate_parts (lim : ℕ) (g : Gate) :
    let t := encGate lim g
    t.val % 128 = gateA lim g ∧ t.val / 128 % 128 = gateB lim g ∧ (t.val < 16384 ↔ isAndOp g.op = true) := by
  dsimp only [encGate]
  have ha := gateA_lt lim g
  have hb := gateB_lt lim g
  refine ⟨?_, ?_, ?_⟩
  · cases h : isAndOp g.op <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  · cases h : isAndOp g.op <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  · cases h : isAndOp g.op <;> simp only [↓reduceIte, Bool.false_eq_true, iff_false, iff_true] <;> omega

theorem getD_cons_cons_slot (c0 c1 : ℕ) (w : List ℕ) (hw : 2 + w.length ≤ 128) (u : ℕ) :
    (c0 :: c1 :: w).getD (slot w.length u) 0 = if u < w.length then w.getD u 0 else c0 := by
  unfold slot
  by_cases hu : u < w.length
  · have h2 : 2 + u < 128 := by omega
    simp only [hu, h2, ↓reduceIte, List.getD_eq_getElem?_getD]
    have hidx : 2 + u = u + 2 := by omega
    rw [hidx]
    rfl
  · simp [hu]

theorem step_bool (w : List Bool) (g : Gate)
    (hmono : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hw : 2 + w.length ≤ 128) :
    stepEv false (0 :: 1 :: w.map Bool.toNat) (encGate w.length g) =
      0 :: 1 :: (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map Bool.toNat := by
  obtain ⟨hop, hlen⟩ := hmono
  have hp := encGate_parts w.length g
  dsimp only at hp
  obtain ⟨hmod, hdiv, hlt⟩ := hp
  simp only [stepEv, hmod, hdiv, gateA, gateB, List.concat_eq_append, List.map_append, List.map_singleton,
    List.cons_append]
  have hslot : ∀ u, (0 :: 1 :: w.map Bool.toNat).getD (slot w.length u) 0 = (w.getD u false).toNat := by
    intro u
    have h1 := getD_cons_cons_slot 0 1 (w.map Bool.toNat) (by simpa using hw) u
    rw [List.length_map] at h1
    rw [h1]
    by_cases hu : u < w.length
    · simp [hu, List.getD_eq_getElem?_getD]
    · simp only [hu, ↓reduceIte]
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu)]
      rfl
  rcases hop with hand | hor
  · have hia : isAndOp g.op = true := by rw [hand]; rfl
    have hcond : (encGate w.length g).val < 16384 := hlt.mpr hia
    simp only [hcond, ↓reduceIte, Bool.cond_false, hand]
    cases hi : g.inputs with
    | nil => simp [GateOp.eval, isAndOp]
    | cons u t =>
      cases t with
      | nil =>
        simp only [hslot u, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, isAndOp, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
        cases w.getD u false <;> rfl
      | cons v r =>
        cases r with
        | nil =>
          simp only [hslot u, hslot v, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, Bool.and_true]
          cases w.getD u false <;> cases w.getD v false <;> rfl
        | cons _ _ => rw [hi] at hlen; simp at hlen
  · have hia : isAndOp g.op = false := by rw [hor]; rfl
    have hcond : ¬ (encGate w.length g).val < 16384 := by rw [hlt, hia]; decide
    simp only [hcond, ↓reduceIte, hor]
    cases hi : g.inputs with
    | nil => simp [GateOp.eval, isAndOp]
    | cons u t =>
      cases t with
      | nil =>
        simp only [hslot u, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          Bool.or_false, isAndOp, Bool.false_eq_true, ↓reduceIte, List.getD_cons_zero]
        cases w.getD u false <;> rfl
      | cons v r =>
        cases r with
        | nil =>
          simp only [hslot u, hslot v, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, Bool.or_false]
          cases w.getD u false <;> cases w.getD v false <;> rfl
        | cons _ _ => rw [hi] at hlen; simp at hlen

theorem step_deg (d : List ℕ) (g : Gate)
    (hmono : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hd : 2 + d.length ≤ 128) :
    stepEv true (0 :: 0 :: d) (encGate d.length g) =
      0 :: 0 :: (d ++ [g.lineDegree d]) := by
  obtain ⟨hop, hlen⟩ := hmono
  have hp := encGate_parts d.length g
  dsimp only at hp
  obtain ⟨hmod, hdiv, hlt⟩ := hp
  simp only [stepEv, hmod, hdiv, gateA, gateB, List.concat_eq_append, List.cons_append]
  have hslot : ∀ u, (0 :: 0 :: d).getD (slot d.length u) 0 = d.getD u 0 := by
    intro u
    rw [getD_cons_cons_slot 0 0 d hd u]
    by_cases hu : u < d.length
    · simp [hu]
    · simp only [hu, ↓reduceIte]
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu)]
  rcases hop with hand | hor
  · have hia : isAndOp g.op = true := by rw [hand]; rfl
    have hcond : (encGate d.length g).val < 16384 := hlt.mpr hia
    have hld : g.lineDegree d = (g.inputs.map fun i => d.getD i 0).sum := by
      simp [Gate.lineDegree, hand]
    simp only [hcond, ↓reduceIte, cond_true, hia, hld]
    cases hi : g.inputs with
    | nil => simp
    | cons u t =>
      cases t with
      | nil =>
        rw [hslot u]
        simp
      | cons v r =>
        cases r with
        | nil =>
          rw [hslot u, hslot v]
          simp
        | cons _ _ => rw [hi] at hlen; simp at hlen
  · have hia : isAndOp g.op = false := by rw [hor]; rfl
    have hcond : ¬ (encGate d.length g).val < 16384 := by rw [hlt, hia]; decide
    have hld : g.lineDegree d = (g.inputs.map fun i => d.getD i 0).foldr max 0 := by
      simp [Gate.lineDegree, hor]
    simp only [hcond, ↓reduceIte, hia, Bool.false_eq_true, hld]
    cases hi : g.inputs with
    | nil => simp
    | cons u t =>
      cases t with
      | nil =>
        rw [hslot u]
        simp
      | cons v r =>
        cases r with
        | nil =>
          rw [hslot u, hslot v]
          simp
        | cons _ _ => rw [hi] at hlen; simp at hlen

theorem fold_bool (gs : List Gate) (w : List Bool)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hbd : 2 + w.length + gs.length ≤ 128) :
    (encGates w.length gs).foldl (stepEv false) (0 :: 1 :: w.map Bool.toNat) =
      0 :: 1 :: (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).map Bool.toNat := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [encGates, List.foldl_cons]
    rw [step_bool w g (hmono g (by simp)) (by omega)]
    have hlen : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by simp
    rw [← hlen]
    exact ih _ (fun g' hg' => hmono g' (by simp [hg'])) (by rw [hlen]; simp at hbd; omega)

theorem fold_deg (gs : List Gate) (d : List ℕ)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hbd : 2 + d.length + gs.length ≤ 128) :
    (encGates d.length gs).foldl (stepEv true) (0 :: 0 :: d) =
      0 :: 0 :: gs.foldl (fun d g => d ++ [g.lineDegree d]) d := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    simp only [encGates, List.foldl_cons]
    rw [step_deg d g (hmono g (by simp)) (by omega)]
    have hlen : (d ++ [g.lineDegree d]).length = d.length + 1 := by simp
    rw [← hlen]
    exact ih _ (fun g' hg' => hmono g' (by simp [hg'])) (by rw [hlen]; simp at hbd; omega)

theorem range_eq_ofFn (M : Finset ℕ) :
    (List.range 26).map (fun i => if i ∈ M then 1 else 0) =
      List.ofFn (fun i : Fin 26 => if i.val ∈ M then 1 else 0) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem main_proof :
    let ev := fun (grade : Bool) (p : List (Fin 32768)) (v : List ℕ) =>
      (p.foldl (fun w t =>
        let a := w.getD (t.val % 128) 0
        let b := w.getD (t.val / 128 % 128) 0
        w.concat (if t.val < 16384 then cond grade (a + b) (min a b) else max a b))
        (0 :: (cond grade 0 1) :: v)).getD (27 + p.length) 0
    ∀ C : Circuit, Monotone2 C →
      C.size ≤ 63 → C.output + 1 = 26 + C.size →
      ∃ p : List (Fin 32768), p.length = C.size ∧
      (∀ x : List Bool, x.length = 26 → ev false p (x.map Bool.toNat) = (C.eval x).toNat) ∧
      ∀ M : Finset ℕ, ev true p (List.ofFn (fun i : Fin 26 => if i.val ∈ M then 1 else 0)) = C.lineDeg 26 M := by
  intro ev C hmono hsz hout
  refine ⟨encGates 26 C.gates, encGates_length 26 C.gates, ?_, ?_⟩
  · intro x hx
    have hfb := fold_bool C.gates x hmono (by simp [Circuit.size] at hsz; omega)
    rw [hx] at hfb
    change ((encGates 26 C.gates).foldl (stepEv false) (0 :: 1 :: x.map Bool.toNat)).getD (27 + (encGates 26 C.gates).length) 0 = _
    rw [hfb, encGates_length]
    have hidx : 27 + C.gates.length = C.output + 2 := by simp [Circuit.size] at hout; omega
    rw [hidx]
    change ((C.wires x).map Bool.toNat).getD C.output 0 = ((C.wires x).getD C.output false).toNat
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (C.wires x)[C.output]? <;> rfl
  · intro M
    have hlen : ((List.range 26).map fun i => if i ∈ M then 1 else 0).length = 26 := by simp
    have hfd := fold_deg C.gates ((List.range 26).map fun i => if i ∈ M then 1 else 0) hmono
      (by rw [hlen]; simp [Circuit.size] at hsz; omega)
    rw [hlen, range_eq_ofFn M] at hfd
    change ((encGates 26 C.gates).foldl (stepEv true) (0 :: 0 :: List.ofFn (fun i : Fin 26 => if i.val ∈ M then 1 else 0))).getD (27 + (encGates 26 C.gates).length) 0 = _
    rw [hfd, encGates_length]
    have hidx : 27 + C.gates.length = C.output + 2 := by simp [Circuit.size] at hout; omega
    rw [hidx]
    change (C.lineDegrees 26 M).getD C.output 0 = C.lineDeg 26 M
    rfl

end PEqualNP.Outside.L_meta_18635_aux

theorem PEqualNP.Outside.L_meta_18635 : (have x1 : Bool → List (Fin (32768 : ℕ)) → List ℕ → ℕ := fun (x1 : Bool) (x2 : List (Fin (32768 : ℕ))) (x3 : List ℕ) =>   (List.foldl         (fun (x4 : List ℕ) (x5 : Fin (32768 : ℕ)) =>           have x6 : ℕ := x4.getD (↑x5 % (128 : ℕ)) (0 : ℕ);           have x7 : ℕ := x4.getD (↑x5 / (128 : ℕ) % (128 : ℕ)) (0 : ℕ);           x4.concat (if ↑x5 < (16384 : ℕ) then bif x1 then x6 + x7 else Min.min x6 x7 else Max.max x6 x7))         ((0 : ℕ) :: (bif x1 then (0 : ℕ) else (1 : ℕ)) :: x3) x2).getD     ((27 : ℕ) + x2.length) (0 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → x2.output + (1 : ℕ) = (26 : ℕ) + x2.size → ∃ (x6 : List (Fin (32768 : ℕ))), x6.length = x2.size ∧ (∀ (x7 : List Bool), x7.length = (26 : ℕ) → x1 Bool.false x6 (List.map Bool.toNat x7) = (x2.eval x7).toNat) ∧ ∀ (x7 : Finset ℕ), x1 Bool.true x6 (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 ∈ x7 then (1 : ℕ) else (0 : ℕ)) = x2.lineDeg (26 : ℕ) x7)  := by
  exact PEqualNP.Outside.L_meta_18635_aux.main_proof
