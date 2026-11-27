import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4730

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shiftWire (s : Fin 13) (w : ℕ) : ℕ :=
  if h1 : w < 13 then (((⟨w, h1⟩ : Fin 13) - s : Fin 13) : ℕ)
  else if h2 : w < 26 then 13 + (((⟨w - 13, by omega⟩ : Fin 13) - s : Fin 13) : ℕ)
  else w

lemma shiftWire_lt (s : Fin 13) (w k : ℕ) (hw : w < 27 + k) :
    shiftWire s w < 27 + k := by
  unfold shiftWire
  split_ifs with h1 h2
  · have := ((⟨w, h1⟩ : Fin 13) - s).isLt; omega
  · have := ((⟨w - 13, by omega⟩ : Fin 13) - s).isLt; omega
  · exact hw

lemma getD_inputs (u v : Fin 13 → Bool) (b : Bool) (w : ℕ) :
    ((List.ofFn u ++ List.ofFn v) ++ [b]).getD w false =
      if h1 : w < 13 then u ⟨w, h1⟩
      else if h2 : w < 26 then v ⟨w - 13, by omega⟩
      else if w = 26 then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : w < 13
  · rw [dif_pos h1]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_ofFn, dif_pos h1]; rfl
  · rw [dif_neg h1]
    by_cases h2 : w < 26
    · rw [dif_pos h2]
      rw [List.getElem?_append_left (by simp; omega)]
      rw [List.getElem?_append_right (by simp; omega)]
      rw [List.length_ofFn, List.getElem?_ofFn, dif_pos (by omega : w - 13 < 13)]; rfl
    · rw [dif_neg h2]
      rw [List.getElem?_append_right (by simp; omega)]
      by_cases h26 : w = 26
      · rw [if_pos h26]; subst h26; simp
      · rw [if_neg h26]
        rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma foldl_shift_eq (s : Fin 13) :
    ∀ (gs : List Gate) (acc1 acc2 : List Bool),
      acc1.length = acc2.length →
      27 ≤ acc1.length →
      (∀ w < 27, acc1.getD (shiftWire s w) false = acc2.getD w false) →
      (∀ w, 27 ≤ w → acc1.getD w false = acc2.getD w false) →
      let gs' := gs.map (fun g => { op := g.op, inputs := g.inputs.map (shiftWire s) : Gate })
      let r1 := gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc1
      let r2 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc2
      (∀ w < 27, r1.getD (shiftWire s w) false = r2.getD w false) ∧
      (∀ w, 27 ≤ w → r1.getD w false = r2.getD w false) := by
  intro gs
  induction gs with
  | nil =>
    intro acc1 acc2 _ _ hlt hge
    exact ⟨hlt, hge⟩
  | cons g rest ih =>
    intro acc1 acc2 hlen h27 hlt hge
    have hmap : ((g.inputs.map (shiftWire s)).map fun i => acc1.getD i false) =
        (g.inputs.map fun i => acc2.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < 27
      · exact hlt i hi
      · have hsw : shiftWire s i = i := by
          unfold shiftWire
          split_ifs <;> omega
        rw [hsw]
        exact hge i (by omega)
    have hval : g.op.eval ((g.inputs.map (shiftWire s)).map fun i => acc1.getD i false) =
        g.op.eval (g.inputs.map fun i => acc2.getD i false) := by
      rw [hmap]
    have hget_app : ∀ (l : List Bool) (b : Bool) (k : ℕ),
        (l ++ [b]).getD k false =
          if k < l.length then l.getD k false else if k = l.length then b else false := by
      intro l b k
      simp only [List.getD_eq_getElem?_getD]
      by_cases hk : k < l.length
      · rw [if_pos hk, List.getElem?_append_left hk]
      · rw [if_neg hk, List.getElem?_append_right (Nat.le_of_not_lt hk)]
        by_cases hkeq : k = l.length
        · subst hkeq; simp
        · rw [if_neg hkeq]
          rw [List.getElem?_eq_none (by simp; omega)]; rfl
    simp only [List.map_cons, List.foldl_cons]
    apply ih
      (acc1 ++ [g.op.eval ((g.inputs.map (shiftWire s)).map fun i => acc1.getD i false)])
      (acc2 ++ [g.op.eval (g.inputs.map fun i => acc2.getD i false)])
    · simp [hlen]
    · simp; omega
    · intro w hw
      have hsw27 : shiftWire s w < 27 := by
        unfold shiftWire
        split_ifs with h1 h2
        · have := ((⟨w, h1⟩ : Fin 13) - s).isLt; omega
        · have := ((⟨w - 13, by omega⟩ : Fin 13) - s).isLt; omega
        · omega
      rw [hget_app, hget_app, if_pos (by omega), if_pos (by omega)]
      exact hlt w hw
    · intro w hw
      rw [hget_app, hget_app, hlen]
      split_ifs
      · exact hge w hw
      · exact hval
      · rfl

lemma eval_shift_eq (x5 : Circuit) (s : Fin 13) (u v : Fin 13 → Bool) (b : Bool) :
    let x11 : Circuit :=
      { gates := x5.gates.map (fun g => { op := g.op, inputs := g.inputs.map (shiftWire s) })
        output := shiftWire s x5.output }
    x11.eval ((List.ofFn u ++ List.ofFn v) ++ [b]) =
      x5.eval ((List.ofFn (fun i => u (i - s)) ++ List.ofFn (fun i => v (i - s))) ++ [b]) := by
  intro x11
  let acc1 := (List.ofFn u ++ List.ofFn v) ++ [b]
  let acc2 := (List.ofFn (fun i => u (i - s)) ++ List.ofFn (fun i => v (i - s))) ++ [b]
  have hinit_lt : ∀ w < 27, acc1.getD (shiftWire s w) false = acc2.getD w false := by
    intro w hw
    dsimp only [acc1, acc2]
    rw [getD_inputs, getD_inputs]
    unfold shiftWire
    by_cases h1 : w < 13
    · rw [dif_pos h1, dif_pos h1]
      have hlt : (((⟨w, h1⟩ : Fin 13) - s : Fin 13) : ℕ) < 13 := ((⟨w, h1⟩ : Fin 13) - s).isLt
      rw [dif_pos hlt]
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : w < 26
      · rw [dif_pos h2, dif_pos h2]
        have hlt : (((⟨w - 13, by omega⟩ : Fin 13) - s : Fin 13) : ℕ) < 13 :=
          ((⟨w - 13, by omega⟩ : Fin 13) - s).isLt
        rw [dif_neg (by omega), dif_pos (by omega)]
        congr 1
        ext
        simp
      · rw [dif_neg h2, dif_neg h2, dif_neg h1, dif_neg h2]
  have hinit_ge : ∀ w, 27 ≤ w → acc1.getD w false = acc2.getD w false := by
    intro w hw
    dsimp only [acc1, acc2]
    rw [getD_inputs, getD_inputs]
    simp [show ¬ w < 13 by omega, show ¬ w < 26 by omega, show w ≠ 26 by omega]
  have hres := foldl_shift_eq s x5.gates acc1 acc2
    (by simp [acc1, acc2]) (by simp [acc1]) hinit_lt hinit_ge
  change (x11.wires acc1).getD (shiftWire s x5.output) false = (x5.wires acc2).getD x5.output false
  by_cases ho : x5.output < 27
  · exact hres.1 x5.output ho
  · have hsw : shiftWire s x5.output = x5.output := by
      unfold shiftWire; split_ifs <;> omega
    rw [hsw]
    exact hres.2 x5.output (by omega)

lemma main_proof
    (x5 : Circuit) (x6 : Fin 13) (x7 : Bool)
    (hM : Monotone2 x5)
    (hRB : ∀ (i : Fin x5.gates.length), ∀ w ∈ (x5.gates.get i).inputs, w < 27 + (i : ℕ))
    (hQ : ∀ Q : Finset (Fin 13),
      (Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      x5.eval (((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
        List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) ++ [x7]) = false) :
    ∃ x11 : Circuit,
      Monotone2 x11 ∧
      (∀ (i : Fin x11.gates.length), ∀ w ∈ (x11.gates.get i).inputs, w < 27 + (i : ℕ)) ∧
      x11.size ≤ x5.size ∧
      (∀ p l : Fin 13,
        x11.eval (((List.ofFn fun i : Fin 13 => decide (i = p)) ++
          List.ofFn fun i : Fin 13 => decide (i = l)) ++ [x7]) =
        x5.eval (((List.ofFn fun i : Fin 13 => decide (i = p + x6)) ++
          List.ofFn fun i : Fin 13 => decide (i = l + x6)) ++ [x7])) ∧
      ∀ Q : Finset (Fin 13),
        (Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
        x11.eval (((List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - i ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) ++ [x7]) = false := by
  let x11 : Circuit :=
    { gates := x5.gates.map (fun g => { op := g.op, inputs := g.inputs.map (shiftWire x6) })
      output := shiftWire x6 x5.output }
  refine ⟨x11, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    obtain ⟨hop, hlen⟩ := hM g0 hg0
    exact ⟨hop, by simpa using hlen⟩
  · intro i w hw
    have hi : (i : ℕ) < x5.gates.length := by simpa [x11] using i.isLt
    have hget : x11.gates.get i =
        { op := (x5.gates.get ⟨i, hi⟩).op, inputs := (x5.gates.get ⟨i, hi⟩).inputs.map (shiftWire x6) } := by
      simp [x11]
    rw [hget] at hw
    rw [List.mem_map] at hw
    rcases hw with ⟨w0, hw0, rfl⟩
    exact shiftWire_lt x6 w0 i (hRB ⟨i, hi⟩ w0 hw0)
  · simp [x11, Circuit.size]
  · intro p l
    rw [eval_shift_eq x5 x6 _ _ x7]
    have h1 : (List.ofFn fun i : Fin 13 => decide (i - x6 = p)) =
        (List.ofFn fun i : Fin 13 => decide (i = p + x6)) :=
      congrArg List.ofFn (funext fun i => decide_eq_decide.mpr sub_eq_iff_eq_add)
    have h2 : (List.ofFn fun i : Fin 13 => decide (i - x6 = l)) =
        (List.ofFn fun i : Fin 13 => decide (i = l + x6)) :=
      congrArg List.ofFn (funext fun i => decide_eq_decide.mpr sub_eq_iff_eq_add)
    rw [h1, h2]
  · intro Q ⟨hcard, hline⟩
    rw [eval_shift_eq x5 x6 _ _ x7]
    let Q' : Finset (Fin 13) := Q.image (fun p => p + x6)
    have hinj : Function.Injective (fun p : Fin 13 => p + x6) := fun a b h => add_right_cancel h
    have hcard' : Q'.card = 4 := by
      rw [Finset.card_image_of_injective Q hinj, hcard]
    have hsub_fin : ∀ (a b c : Fin 13), a - (b - c) = a + c - b := by
      intro a b c; abel
    have hline' : ∀ l : Fin 13, (Q'.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2 := by
      intro l
      have hsub_eq : (Q'.filter (fun p => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))) =
          (Q.filter (fun p => p - (l - x6) ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).image (fun p => p + x6) := by
        ext z
        simp only [Q', Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨p, hp, rfl⟩, hmem⟩
          exact ⟨p, ⟨hp, by rw [hsub_fin]; exact hmem⟩, rfl⟩
        · rintro ⟨p, ⟨hp, hmem⟩, rfl⟩
          exact ⟨⟨p, hp, rfl⟩, by rw [← hsub_fin]; exact hmem⟩
      rw [hsub_eq, Finset.card_image_of_injective _ hinj]
      exact hline (l - x6)
    have hQ' := hQ Q' ⟨hcard', hline'⟩
    have h1 : (List.ofFn fun i : Fin 13 => decide (i - x6 ∈ Q)) =
        (List.ofFn fun i : Fin 13 => decide (i ∈ Q')) :=
      congrArg List.ofFn (funext fun i => decide_eq_decide.mpr (by
        simp only [Q', Finset.mem_image]
        exact ⟨fun h => ⟨i - x6, h, sub_add_cancel i x6⟩,
          fun ⟨p, hp, hpi⟩ => by rw [← hpi, add_sub_cancel_right]; exact hp⟩))
    have h2 : (List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p - (i - x6) ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) =
        (List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q', p - i ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) :=
      congrArg List.ofFn (funext fun i => decide_eq_decide.mpr (by
        exact ⟨fun h p' hp' => by
            simp only [Q', Finset.mem_image] at hp'
            rcases hp' with ⟨p, hp, rfl⟩
            rw [← hsub_fin]; exact h p hp,
          fun h p hp => by
            rw [hsub_fin]; exact h (p + x6) (Finset.mem_image_of_mem _ hp)⟩))
    rw [h1, h2]
    exact hQ'

end PEqualNP.Outside.L_meta_4730

theorem PEqualNP.Outside.L_meta_4730 :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 : Finset (Fin (13 : ℕ))), x4 x10 → x5.eval (x3 x10 ++ [x7]) = Bool.false) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ (∀ (x12 : Fin x11.gates.length), ∀ x13 ∈ (x11.gates.get x12).inputs, x13 < (27 : ℕ) + ↑x12) ∧ x11.size ≤ x5.size ∧ (∀ (x12 x13 : Fin (13 : ℕ)), x11.eval (x2 x12 x13 ++ [x7]) = x5.eval (x2 (x12 + x6) (x13 + x6) ++ [x7])) ∧ ∀ (x12 : Finset (Fin (13 : ℕ))), x4 x12 → x11.eval (x3 x12 ++ [x7]) = Bool.false := by
  intro x1 x2 x3 x4 x5 x6 x7 hM hRB hQ
  exact PEqualNP.Outside.L_meta_4730.main_proof x5 x6 x7 hM hRB hQ
