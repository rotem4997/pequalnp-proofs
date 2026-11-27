import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2511

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A NOT gate ignores every operand after the first.
private def active (g : Gate) : List ℕ :=
  if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs

private def reader (g : Gate) : Bool :=
  (active g).any fun i => i == 4 || i == 9

private def Ok (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private def rd (w : List Bool) (i : ℕ) := w.getD i false

private def val (g : Gate) (w : List Bool) := g.op.eval ((active g).map (rd w))

private def run : List Gate → List Bool → List Bool
  | [], w => w
  | g :: gs, w => run gs (w ++ [val g w])

private theorem ok_of_fan {C : Circuit} (h : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
    Ok g := by
  have hg' := h g hg
  simpa [Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using hg'

private theorem reader_iff (g : Gate) :
    reader g = true ↔ 4 ∈ active g ∨ 9 ∈ active g := by
  simp [reader, List.any_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩
    exacts [Or.inl hi, Or.inr hi]
  · rintro (hi | hi)
    exacts [⟨4, hi, Or.inl rfl⟩, ⟨9, hi, Or.inr rfl⟩]

private theorem active_and (g : Gate) (h : g.op = .and) : active g = g.inputs := by
  simp [active, h, GateOp.eval]

private theorem active_or (g : Gate) (h : g.op = .or) : active g = g.inputs := by
  simp [active, h, GateOp.eval]

private theorem active_not (g : Gate) (h : g.op = .not) : active g = g.inputs.take 1 := by
  simp [active, h, GateOp.eval]

private theorem val_actual (g : Gate) (w : List Bool) (hg : Ok g) :
    val g w = g.op.eval (g.inputs.map (rd w)) := by
  rcases hg.1 with h | h | h
  · simp [val, active_and g h]
  · simp [val, active_or g h]
  · rw [val, active_not g h, h]
    cases g.inputs <;> rfl

private theorem run_actual (gs : List Gate) (w : List Bool)
    (h : ∀ g ∈ gs, Ok g) :
    run gs w = gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map (rd u))]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run, List.foldl_cons, val_actual g w (h g (by simp))]
    exact ih _ (fun a ha => h a (by simp [ha]))

private theorem wire_run (C : Circuit) (h : FanInTwo C) (w : List Bool) :
    C.wires w = run C.gates w :=
  (run_actual _ _ (fun _ hg => ok_of_fan h hg)).symm

private theorem run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    rd (run gs w) i = rd w i := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih _ (by simp; omega), rd, List.getD_append _ _ _ _ hi]
    rfl

private theorem rd_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    rd (w ++ [b]) i = if i = w.length then b else rd w i := by
  by_cases he : i = w.length
  · subst i
    rw [ite_eq_left rfl, rd, List.getD_append_right _ _ _ _ (by rfl)]
    simp
  · rw [ite_eq_right he]
    by_cases hlt : i < w.length
    · exact List.getD_append _ _ _ _ hlt
    · have hgt : w.length < i := by omega
      have hsub : 0 < i - w.length := by omega
      have hz : Option.getD ([b][i - w.length]?) false = false := by
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_append, ite_eq_right hlt, hz,
        List.getElem?_eq_none (by omega : w.length ≤ i), Option.getD_none]

private theorem rd_ofFn (x : Fin 9 → Bool) (i : Fin 9) : rd (List.ofFn x) i = x i := by
  rw [rd, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

private theorem rd_first (x : Fin 9 → Bool) (b : Bool) :
    rd (List.ofFn x ++ [b]) 9 = b := by
  rw [rd_snoc, List.length_ofFn]
  rfl

private theorem val_congr {g : Gate} {w v : List Bool}
    (h : ∀ i ∈ active g, rd w i = rd v i) : val g w = val g v := by
  unfold val
  rw [List.map_congr_left h]

-- Agreement away from input 4 propagates when every gate evaluates equally.
private theorem run_agree (gs : List Gate) (w v : List Bool)
    (hLen : w.length = v.length) (hPrefix : 9 < w.length)
    (h9w : rd w 9 = false) (h9v : rd v 9 = false)
    (hwv : ∀ i, i ≠ 4 → rd w i = rd v i)
    (hStep : ∀ g ∈ gs, ∀ u z : List Bool, rd u 9 = false → rd z 9 = false →
      (∀ i, i ≠ 4 → rd u i = rd z i) → val g u = val g z) :
    ∀ i, i ≠ 4 → rd (run gs w) i = rd (run gs v) i := by
  induction gs generalizing w v with
  | nil => exact hwv
  | cons g gs ih =>
    have hv : val g w = val g v := hStep g (by simp) w v h9w h9v hwv
    rw [run, run, hv]
    apply ih
    · simp [hLen]
    · simp; omega
    · rwa [rd_snoc, ite_eq_right (by omega : 9 ≠ w.length)]
    · rwa [rd_snoc, ite_eq_right (by omega : 9 ≠ v.length)]
    · intro i hi
      simp [rd_snoc, hLen, hwv i hi]
    · intro r hr
      exact hStep r (by simp [hr])

-- Deleting the first gate shifts later wires down and routes its former wire to input 4.
private def reroute (i : ℕ) : ℕ := if i = 9 then 4 else if i < 9 then i else i - 1

private def shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map reroute⟩

private theorem shiftOk {g : Gate} (hg : Ok g) : Ok (shiftGate g) :=
  ⟨hg.1, by simpa [shiftGate] using hg.2⟩

private theorem rd_remove (u t : List Bool) (b : Bool) (hu : u.length = 9)
    {i : ℕ} (hi : i ≠ 9) :
    rd (u ++ t) (reroute i) = rd (u ++ [b] ++ t) i := by
  by_cases h : i < 9
  · simp only [reroute, ite_eq_right hi, ite_eq_left h, rd]
    rw [List.getD_append _ _ _ _ (by omega : i < u.length),
      List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by omega : i < u.length)]
  · have hgt : 9 < i := by omega
    simp only [reroute, ite_eq_right hi, ite_eq_right h, rd]
    rw [List.getD_append_right _ _ _ _ (by omega : u.length ≤ i - 1),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp only [List.length_append, List.length_singleton]
    omega

private theorem active_shift (g : Gate) :
    active (shiftGate g) = (active g).map reroute := by
  unfold active shiftGate
  by_cases h : g.op.eval [false, false] = true <;> simp [h, List.map_take]

private theorem val_shift (u t : List Bool) (b : Bool) (hu : u.length = 9)
    (hb : b = true → rd u 4 = true)
    {g : Gate}
    (hg : 9 ∉ active g ∨ g.op = .or ∧ (active g = [4, 9] ∨ active g = [9, 4])) :
    val (shiftGate g) (u ++ t) = val g (u ++ [b] ++ t) := by
  unfold val
  rw [active_shift, List.map_map]
  change g.op.eval ((active g).map (rd (u ++ t) ∘ reroute)) =
    g.op.eval ((active g).map (rd (u ++ [b] ++ t)))
  rcases hg with hn | ⟨ho, hp⟩
  · congr 1
    exact List.map_congr_left (fun i hi => rd_remove u t b hu (fun e => hn (e ▸ hi)))
  · have hu4 : rd (u ++ t) 4 = rd u 4 := List.getD_append _ _ _ _ (by omega)
    have hv4 : rd (u ++ [b] ++ t) 4 = rd u 4 := by
      change (u ++ [b] ++ t).getD 4 false = u.getD 4 false
      rw [List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append _ _ _ _ (by omega : 4 < u.length)]
    have hv9 : rd (u ++ [b] ++ t) 9 = b := by
      change (u ++ [b] ++ t).getD 9 false = b
      rw [List.getD_append _ _ _ _ (by simp [hu])]
      exact (rd_snoc u b 9).trans (ite_eq_left hu.symm)
    have hb' : (rd u 4 || b) = rd u 4 := Bool.or_eq_left_iff_imp.mpr hb
    rcases hp with hp | hp
    all_goals
      simp only [ho, hp, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, id_eq, Bool.or_false, Function.comp_apply]
      change (rd (u ++ t) 4 || rd (u ++ t) 4) = _
      rw [hu4, Bool.or_self, hv4, hv9]
    · exact hb'.symm
    · rw [Bool.or_comm b]
      exact hb'.symm

-- The two evaluations retain the same suffix after the deleted wire is accounted for.
private theorem run_shift (gs : List Gate) (u t : List Bool) (b : Bool) (hu : u.length = 9)
    (hb : b = true → rd u 4 = true)
    (hg : ∀ g ∈ gs, 9 ∉ active g ∨ g.op = .or ∧
      (active g = [4, 9] ∨ active g = [9, 4])) :
    ∃ z : List Bool, run (gs.map shiftGate) (u ++ t) = u ++ z ∧
      run gs (u ++ [b] ++ t) = u ++ [b] ++ z := by
  induction gs generalizing t with
  | nil => exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    have he := val_shift u t b hu hb (hg g (by simp))
    simp only [List.map_cons, run, he, List.append_assoc]
    simpa only [List.append_assoc] using
      (ih (t ++ [val g (u ++ [b] ++ t)]) (fun r hr => hg r (by simp [hr])))

private theorem pair_list {l : List ℕ} (hl : l.length ≤ 2)
    (h4 : 4 ∈ l) (h9 : 9 ∈ l) : l = [4, 9] ∨ l = [9, 4] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at h4
  · simp at h4 h9
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4 h9
    rcases h4 with h | h <;> rcases h9 with k | k <;> first | omega | simp [h, k]
  · simp at hl

private theorem pair_form {g : Gate} (hg : Ok g)
    (h4 : 4 ∈ active g) (h9 : 9 ∈ active g) :
    (g.op = .and ∨ g.op = .or) ∧ (active g = [4, 9] ∨ active g = [9, 4]) := by
  rcases hg.1 with h | h | h
  · exact ⟨Or.inl h, pair_list (by simpa [active_and g h] using hg.2) h4 h9⟩
  · exact ⟨Or.inr h, pair_list (by simpa [active_or g h] using hg.2) h4 h9⟩
  · rw [active_not g h] at h4 h9
    have hlen : (g.inputs.take 1).length ≤ 1 := by simp [List.length_take]
    have hp := pair_list (by omega : (g.inputs.take 1).length ≤ 2) h4 h9
    rcases hp with hp | hp <;> simp [hp] at hlen

private theorem one_reader {p : Gate → Bool} {gs : List Gate} {r : Gate}
    (hr : r ∈ gs) (hpr : p r = true) (hc : gs.countP p < 2) :
    ∀ g ∈ gs, p g = true → g = r := by
  have hm : 1 ≤ gs.countP p := List.one_le_countP_iff.mpr ⟨r, hr, hpr⟩
  have hl : (gs.filter p).length = 1 := by
    rw [← List.countP_eq_length_filter]
    omega
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hl
  intro g hgt hpg
  have hr' : r ∈ gs.filter p := List.mem_filter.mpr ⟨hr, hpr⟩
  have hg' : g ∈ gs.filter p := List.mem_filter.mpr ⟨hgt, hpg⟩
  rw [ht] at hr' hg'
  exact (List.mem_singleton.mp hg').trans (List.mem_singleton.mp hr').symm

private def single3 (i : Fin 9) : Bool := decide (i = 3)

private def pair34 (i : Fin 9) : Bool := decide (i = 3 ∨ i = 4)

private def pair12 (i : Fin 9) : Bool := decide (i = 1 ∨ i = 2)

private theorem compare_inputs (i : ℕ) (hi : i ≠ 4) :
    rd (List.ofFn single3 ++ [false]) i = rd (List.ofFn pair34 ++ [false]) i := by
  rw [rd_snoc, rd_snoc, List.length_ofFn, List.length_ofFn]
  by_cases h9 : i = 9
  · rw [ite_eq_left h9, ite_eq_left h9]
  · simp only [ite_eq_right h9]
    by_cases hf : i < 9
    · let j : Fin 9 := ⟨i, hf⟩
      change rd (List.ofFn single3) j = rd (List.ofFn pair34) j
      rw [rd_ofFn, rd_ofFn]
      have hj : j ≠ 4 := fun he => hi (congrArg Fin.val he)
      simp [single3, pair34, hj]
    · simp only [rd, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hf]

private theorem proof (C : Circuit) (hmin : IsMinimalCircuit 9 C)
    (hFirst : ∀ x : Fin 9 → Bool, rd (C.wires (List.ofFn x)) 9 = (x 0 && x 4))
    (hDiff : circuitFun 9 C single3 ≠ circuitFun 9 C pair34)
    (hPos : circuitFun 9 C pair12 = true) :
    2 ≤ C.gates.tail.countP reader := by
  obtain ⟨a, tail, hC⟩ : ∃ a tail, C.gates = a :: tail := by
    cases hGates : C.gates with
    | nil =>
      have h := hFirst (fun _ => true)
      rw [wire_run C hmin.1, hGates, run] at h
      change false = true at h
      contradiction
    | cons a tail => exact ⟨a, tail, rfl⟩
  have firstVal (x : Fin 9 → Bool) : val a (List.ofFn x) = (x 0 && x 4) := by
    have h := hFirst x
    rw [wire_run C hmin.1, hC, run, run_keeps _ _ _ (by simp), rd_first] at h
    exact h
  have hout4 : C.output ≠ 4 := by
    intro ho
    have h := hPos
    change rd (C.wires (List.ofFn pair12)) C.output = true at h
    rw [ho, wire_run C hmin.1, run_keeps _ _ _ (by simp)] at h
    change rd (List.ofFn pair12) (4 : Fin 9) = true at h
    rw [rd_ofFn] at h
    exact Bool.noConfusion h
  have hout9 : C.output ≠ 9 := by
    intro ho
    have h := hPos
    change rd (C.wires (List.ofFn pair12)) C.output = true at h
    rw [ho, hFirst] at h
    exact Bool.noConfusion h
  -- An OR of wires 4 and 9 can read wire 4 twice when wire 9 is removed.
  have dead (hValidity : ∀ g ∈ tail, 9 ∉ active g ∨ g.op = .or ∧
      (active g = [4, 9] ∨ active g = [9, 4])) : False := by
    let D : Circuit := ⟨tail.map shiftGate, reroute C.output⟩
    have hD : FanInTwo D := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have hf : Ok (shiftGate g') := shiftOk (ok_of_fan hmin.1 (by rw [hC]; simp [hg']))
      simpa [Ok, Set.mem_insert_iff, Set.mem_singleton_iff] using hf
    have hfun : circuitFun 9 D = circuitFun 9 C := by
      funext x
      change rd (D.wires (List.ofFn x)) (reroute C.output) =
        rd (C.wires (List.ofFn x)) C.output
      rw [wire_run D hD, wire_run C hmin.1, hC, run]
      change rd (run (tail.map shiftGate) (List.ofFn x)) (reroute C.output) =
        rd (run tail (List.ofFn x ++ [val a (List.ofFn x)])) C.output
      rw [firstVal]
      have hb : (x 0 && x 4) = true → rd (List.ofFn x) 4 = true := by
        change _ → rd (List.ofFn x) (4 : Fin 9) = true
        rw [rd_ofFn]
        exact fun hx => (Bool.and_eq_true_iff.mp hx).2
      obtain ⟨z, hz, hz'⟩ := run_shift tail (List.ofFn x) [] (x 0 && x 4)
        List.length_ofFn hb hValidity
      rw [List.append_nil] at hz hz'
      rw [hz, hz']
      exact rd_remove _ _ _ List.length_ofFn hout9
    have hn := hmin.2 D hD hfun
    simp only [Circuit.size, hC, List.length_cons, D, List.length_map] at hn
    omega
  -- Wire 9 is false on both witness inputs and masks input 4 in an AND gate.
  have noChange (hSteps : ∀ g ∈ tail, 4 ∉ active g ∨ g.op = .and ∧
      (active g = [4, 9] ∨ active g = [9, 4])) : False := by
    apply hDiff
    change rd (C.wires (List.ofFn single3)) C.output =
      rd (C.wires (List.ofFn pair34)) C.output
    rw [wire_run C hmin.1, wire_run C hmin.1, hC, run, run, firstVal, firstVal]
    change rd (run tail (List.ofFn single3 ++ [false])) C.output =
      rd (run tail (List.ofFn pair34 ++ [false])) C.output
    refine run_agree tail _ _ (by simp) (by simp) (rd_first _ _) (rd_first _ _)
      compare_inputs ?_ _ hout4
    intro g hg u z hu hz he
    rcases hSteps g hg with hf | ⟨ha, hp⟩
    · exact val_congr (fun i hi => he i (fun e => hf (e ▸ hi)))
    · rcases hp with hp | hp <;> simp [val, ha, hp, GateOp.eval, hu, hz]
  by_contra hn
  have hc : tail.countP reader < 2 := by
    simpa only [hC, List.tail_cons, Nat.not_le] using hn
  by_cases hUsed : ∃ g ∈ tail, 9 ∈ active g
  · obtain ⟨r, hr, hr9⟩ := hUsed
    have hUnique := one_reader hr ((reader_iff r).2 (Or.inr hr9)) hc
    have h4 : 4 ∈ active r := by
      by_contra h4
      apply noChange
      intro g hg
      left
      intro hgr
      exact h4 (hUnique g hg ((reader_iff g).2 (Or.inl hgr)) ▸ hgr)
    have hOk : Ok r := ok_of_fan hmin.1 (by rw [hC]; simp [hr])
    obtain ⟨ha | ho, hpair⟩ := pair_form hOk h4 hr9
    · apply noChange
      intro g hg
      by_cases hgr : 4 ∈ active g
      · have hEq := hUnique g hg ((reader_iff g).2 (Or.inl hgr))
        exact Or.inr (hEq.symm ▸ ⟨ha, hpair⟩)
      · exact Or.inl hgr
    · apply dead
      intro g hg
      by_cases hgr : 9 ∈ active g
      · have hEq := hUnique g hg ((reader_iff g).2 (Or.inr hgr))
        exact Or.inr (hEq.symm ▸ ⟨ho, hpair⟩)
      · exact Or.inl hgr
  · exact dead (fun g hg => Or.inl (fun hr => hUsed ⟨g, hg, hr⟩))

end PEqualNP.Outside.L_meta_2511

theorem PEqualNP.Outside.L_meta_2511 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)))) → ((PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = (3 : Fin (9 : ℕ)))) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = (3 : Fin (9 : ℕ)) ∨ x5 = (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 fun (x6 : Fin (9 : ℕ)) => Decidable.decide (x6 = (1 : Fin (9 : ℕ)) ∨ x6 = (2 : Fin (9 : ℕ)))) = Bool.true → (2 : ℕ) ≤ List.countP x1 x2.gates.tail := by
  exact PEqualNP.Outside.L_meta_2511.proof
