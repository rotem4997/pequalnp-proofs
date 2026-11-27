import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_6166_451
    (search :
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        ComputesIncidence (fun l : Fin 13 => singerLines3 (-l)) C)
    (normalize : ∀ C : Circuit, Monotone2 C →
      ComputesIncidence (fun l : Fin 13 => singerLines3 (-l)) C →
      ∃ (D : Circuit) (h : Gate) (gs : List Gate), D.gates = h :: gs ∧ Monotone2 D ∧
        D.size ≤ C.size ∧
        ComputesIncidence (fun l : Fin 13 => singerLines3 (-l)) D ∧
        (h.op = .and ∧ h.inputs = [0, 13] ∨ h.op = .or ∧ h.inputs ∈ [[0, 1], [0, 13], [2, 13]]))
    (encode : ∀ (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      Monotone2 C → C.size ≤ s → (∀ r ∈ rows, r < 2 ^ n) →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = f r) →
      FormulaSat (enc n s f rows)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, x4 + x3 ∉ x1}; have x3 : List (List Bool) := List.flatMap (fun (x3 : Fin (13 : ℕ)) => List.map (fun (x4 : Fin (13 : ℕ)) => PEqualNP.GenericRejection.incidenceInput {x3} {x4 - x3}) x1.toList) (List.finRange (13 : ℕ)); have x4 : List (Finset (Fin (13 : ℕ))) := List.flatMap (fun (x4 : ℕ) => (Finset.powersetCard x4 Finset.univ).toList) (List.range (4 : ℕ)); have x5 : List (List Bool) := List.flatMap (fun (x5 : Finset (Fin (13 : ℕ))) => [PEqualNP.GenericRejection.incidenceInput x5 (x2 x5), PEqualNP.GenericRejection.incidenceInput (x2 x5) x5]) x4; ∃ (x6 : PEqualNP.CircuitLowerBounds.Gate),   (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x6.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]]) ∧     have x7 : List Bool → ℕ := fun (x7 : List Bool) => List.foldr Nat.bit (0 : ℕ) (x7 ++ [x6.op.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x6.inputs)]);     have x8 : List ℕ := List.map x7 x3;     PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (27 : ℕ) (62 : ℕ) (fun (x9 : ℕ) => x8.contains x9) (x8 ++ List.map x7 x5).eraseDups) := by
  let diff : Finset (Fin 13) := {0, 1, 3, 9}
  let lines : Fin 13 → Finset (Fin 13) := fun l => singerLines3 (-l)
  let off : Finset (Fin 13) → Finset (Fin 13) := fun s => {l | ∀ p ∈ s, p + l ∉ diff}
  let positive := (List.finRange 13).flatMap fun p =>
    diff.toList.map fun d => incidenceInput {p} {d - p}
  let small := (List.range 4).flatMap fun count =>
    (Finset.powersetCard count (Finset.univ : Finset (Fin 13))).toList
  let negative := small.flatMap fun s => [incidenceInput s (off s), incidenceInput (off s) s]
  obtain ⟨C, mono, bound, computes⟩ := search
  obtain ⟨E, h, gs, gateEq, eMono, eSize, eComputes, canonical⟩ := normalize C mono computes
  let suffix : Circuit := ⟨gs, E.output⟩
  let augment (x : List Bool) := x ++ [h.op.eval (h.inputs.map fun i => x.getD i false)]
  let key (x : List Bool) := (augment x).foldr Nat.bit 0
  let on := positive.map key
  let rows := (on ++ negative.map key).eraseDups
  change ∃ g : Gate, (g.op = .and ∧ g.inputs = [0, 13] ∨
    g.op = .or ∧ g.inputs ∈ [[0, 1], [0, 13], [2, 13]]) ∧
    (let st := fun (x : List Bool) => (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).foldr Nat.bit 0
     let codes := positive.map st
     FormulaSat (enc 27 62 (fun r => codes.contains r) (codes ++ negative.map st).eraseDups))
  refine ⟨h, canonical, ?_⟩
  change FormulaSat (enc 27 62 (fun r => on.contains r) rows)
  have suffixMono : Monotone2 suffix := by
    intro g hg
    apply eMono
    rw [gateEq]
    exact List.mem_cons_of_mem _ hg
  have suffixSize : suffix.size ≤ 62 := by
    have hsize := eSize.trans bound
    change E.gates.length ≤ 63 at hsize
    rw [gateEq, List.length_cons] at hsize
    change gs.length ≤ 62
    omega
  have eEval (x : List Bool) : suffix.eval (augment x) = E.eval x := by
    delta Circuit.eval Circuit.wires
    rw [gateEq, List.foldl_cons]
  have sizeInput (s t : Finset (Fin 13)) : (incidenceInput s t).length = 26 := by
    delta incidenceInput
    simp
  have posSpec {x : List Bool} (mem : x ∈ positive) :
      ∃ p l : Fin 13, p + l ∈ diff ∧ x = incidenceInput {p} {l} := by
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp mem
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact ⟨p, v-p, by rw [show p+(v-p) = v by abel]; exact Finset.mem_toList.mp hv, rfl⟩
  have negSpec {x : List Bool} (mem : x ∈ negative) :
      ∃ s t : Finset (Fin 13), x = incidenceInput s t ∧ ∀ p ∈ s, ∀ l ∈ t, p + l ∉ diff := by
    obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with he | he
    · exact ⟨u, off u, he, fun p hp l hl => (Finset.mem_filter.mp hl).2 p hp⟩
    · refine ⟨off u, u, he, fun p hp l hl => ?_⟩
      simpa only [add_comm l p] using (Finset.mem_filter.mp hp).2 l hl
  have isInc : ∀ p l : Fin 13, p ∈ lines l ↔ p + l ∈ diff := by
    change ∀ p l : Fin 13, p ∈ singerLines3 (-l) ↔
      p + l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
    decide +kernel
  have posEval {x : List Bool} (mem : x ∈ positive) : E.eval x = true := by
    obtain ⟨p, l, hpl, rfl⟩ := posSpec mem
    rw [eComputes]
    exact decide_eq_true (⟨p, by simp, l, by simp, (isInc _ _).mpr hpl⟩)
  have negEval {x : List Bool} (mem : x ∈ negative) : E.eval x = false := by
    obtain ⟨s, t, rfl, no⟩ := negSpec mem
    rw [eComputes]
    exact decide_eq_false (by rintro ⟨p, hp, l, hl, inc⟩; exact no p hp l hl ((isInc _ _).mp inc))
  have posLen {x : List Bool} (mem : x ∈ positive) : x.length = 26 := by
    obtain ⟨p, l, _, rfl⟩ := posSpec mem
    exact sizeInput _ _
  have negLen {x : List Bool} (mem : x ∈ negative) : x.length = 26 := by
    obtain ⟨s, t, rfl, _⟩ := negSpec mem
    exact sizeInput _ _
  have bit (bits : List Bool) (j : ℕ) : (bits.foldr Nat.bit 0).testBit j = bits.getD j false := by
    induction bits generalizing j with
    | nil => simp
    | cons b t ih =>
      cases j with
      | zero => simp
      | succ j => simp [Nat.testBit_bit_succ, ih]
  have foldLt (bits : List Bool) : bits.foldr Nat.bit 0 < 2 ^ bits.length := by
    induction bits with
    | nil => simp
    | cons b bs ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      cases b <;> simp [Nat.bit] <;> omega
  have augmentLen (x : List Bool) (len : x.length = 26) : (augment x).length = 27 := by
    simp [augment, len]
  have keyLt (x : List Bool) (len : x.length = 26) : key x < 2 ^ (27 : ℕ) := by
    simpa only [key, augmentLen x len] using foldLt (augment x)
  have keyDec (x : List Bool) (len : x.length = 26) :
      List.ofFn (fun i : Fin 27 => (key x).testBit i.val) = augment x := by
    apply List.ext_getElem
    · simp [augmentLen x len]
    · intro i hi haug
      rw [List.getElem_ofFn, bit]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem haug]
      rfl
  have eitherRow {r : ℕ} (mem : r ∈ rows) : r ∈ on ∨ r ∈ negative.map key := by
    exact List.mem_append.mp (List.mem_eraseDups.mp mem)
  refine encode 27 62 (fun r => on.contains r) rows suffix suffixMono suffixSize ?_ ?_
  · intro r mem
    rcases eitherRow mem with hrow | hrow
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
      exact keyLt x (posLen hx)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
      exact keyLt x (negLen hx)
  · intro r mem
    by_cases hp : r ∈ on
    · have label : on.contains r = true := List.contains_iff_mem.mpr hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      rw [label, keyDec x (posLen hx), eEval]
      exact posEval hx
    · have label : on.contains r = false := by
        cases hval : on.contains r
        · rfl
        · exact False.elim (hp (List.contains_iff_mem.mp hval))
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((eitherRow mem).resolve_left hp)
      rw [label, keyDec x (negLen hx), eEval]
      exact negEval hx
