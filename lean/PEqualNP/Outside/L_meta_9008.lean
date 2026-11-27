import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9008

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (gateAt)

private abbrev Vertex := Fin 13 ⊕ Fin 13
private abbrev Family := Finset (Finset Vertex)

private def bits (S : Finset Vertex) : List Bool :=
  (List.ofFn fun i : Fin 13 => decide (Sum.inl i ∈ S)) ++
    List.ofFn fun i : Fin 13 => decide (Sum.inr i ∈ S)

private def vertex (i : ℕ) (hi : i < 26) : Vertex :=
  if h : i < 13 then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - 13, by omega⟩

private lemma bits_length (S : Finset Vertex) : (bits S).length = 26 := by
  simp [bits]

private lemma bits_getD (S : Finset Vertex) (i : ℕ) (hi : i < 26) :
    (bits S).getD i false = decide (vertex i hi ∈ S) := by
  by_cases h : i < 13
  · unfold bits
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp only [vertex, h, dite_true, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      Option.getD_some]
  · unfold bits
    rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    have hr : i - 13 < 13 := by omega
    simp only [vertex, h, dite_false, List.length_ofFn, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, hr, dite_true, Option.getD_some]

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private lemma fold_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_assoc, Nat.add_comm 1]

private lemma fold_getD (gs : List Gate) (xs : List Bool) {i : ℕ} (hi : i < xs.length) :
    (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step xs g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private lemma fold_gate (gs : List Gate) (xs : List Bool) (j : ℕ) (hj : j < gs.length)
    (hb : ∀ i ∈ gs[j].inputs, i < xs.length + j) :
    (gs.foldl step xs).getD (xs.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl step xs).getD i false) := by
  induction gs generalizing xs j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have hnew : xs.length < (step xs g).length := by simp [step]
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero] at hb ⊢
      rw [fold_getD gs (step xs g) hnew]
      have hlast : (step xs g).getD xs.length false =
          g.op.eval (g.inputs.map fun i => xs.getD i false) := by
        simp [step]
      rw [hlast]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hb i hi
      rw [fold_getD gs (step xs g) (by omega)]
      exact (List.getD_append _ _ _ _ hi').symm
    | succ j =>
      have hlen : xs.length + (j + 1) = (step xs g).length + j := by
        simp [step]; omega
      simp only [List.foldl_cons, List.getElem_cons_succ, hlen] at hb ⊢
      exact ih (step xs g) j (by simpa using hj) hb

private lemma gate_data (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (j : ℕ) (hj : j < C.size) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < 26 + j ∧ b < 26 + j ∧
      ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) := by
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := he ▸ List.getElem_mem hj
  have hlen := hC.2.2 _ hm
  obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C j).inputs = [a, b] := by
    cases hs : (gateAt C j).inputs with
    | nil => simp [hs] at hlen
    | cons a rest =>
      cases rest with
      | nil => simp [hs] at hlen
      | cons b tail =>
        have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa [hs] using hlen)
        exact ⟨a, b, by rw [ht]⟩
  exact ⟨a, b, hab, hC.2.1 j hj a (by simp [hab]), hC.2.1 j hj b (by simp [hab]),
    hC.1 _ hm⟩

private def families (C : Circuit) (i : ℕ) : Family :=
  if hi : i < 26 then {Finset.univ.erase (vertex i hi)}
  else
    let g := gateAt C (i - 26)
    match g.inputs with
    | [a, b] =>
      if _ha : a < i then
        if _hb : b < i then
          match g.op with
          | .and => families C a ∪ families C b
          | .or => Finset.image₂ (· ∩ ·) (families C a) (families C b)
          | _ => ∅
        else ∅
      else ∅
    | _ => ∅
termination_by i

private def Covers (S : Finset Vertex) (F : Family) : Prop := ∃ T ∈ F, S ⊆ T

private lemma covers_input (S : Finset Vertex) (e : Vertex) :
    Covers S {Finset.univ.erase e} ↔ e ∉ S := by
  simp only [Covers, Finset.mem_singleton, exists_eq_left]
  exact ⟨fun h he => (Finset.mem_erase.mp (h he)).1 rfl,
    fun h _ hw => Finset.mem_erase.mpr ⟨fun he => h (he ▸ hw), Finset.mem_univ _⟩⟩

private lemma covers_union (S : Finset Vertex) (F G : Family) :
    Covers S (F ∪ G) ↔ Covers S F ∨ Covers S G := by
  simp only [Covers, Finset.mem_union, or_and_right, exists_or]

private lemma covers_inter (S : Finset Vertex) (F G : Family) :
    Covers S (Finset.image₂ (· ∩ ·) F G) ↔ Covers S F ∧ Covers S G := by
  constructor
  · rintro ⟨T, hT, hST⟩
    obtain ⟨A, hA, B, hB, rfl⟩ := Finset.mem_image₂.mp hT
    exact ⟨⟨A, hA, fun _ hx => (Finset.mem_inter.mp (hST hx)).1⟩,
      ⟨B, hB, fun _ hx => (Finset.mem_inter.mp (hST hx)).2⟩⟩
  · rintro ⟨⟨A, hA, hSA⟩, ⟨B, hB, hSB⟩⟩
    exact ⟨A ∩ B, Finset.mem_image₂_of_mem hA hB,
      fun _ hx => Finset.mem_inter.mpr ⟨hSA hx, hSB hx⟩⟩

private lemma families_gate (C : Circuit) (j a b : ℕ)
    (hab : (gateAt C j).inputs = [a, b]) (ha : a < 26 + j) (hb : b < 26 + j) :
    families C (26 + j) =
      match (gateAt C j).op with
      | .and => families C a ∪ families C b
      | .or => Finset.image₂ (· ∩ ·) (families C a) (families C b)
      | _ => ∅ := by
  rw [families]
  simp only [show ¬26 + j < 26 by omega, dite_false, Nat.add_sub_cancel_left, hab, ha, hb,
    dite_true]

private lemma wire_correct (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (S : Finset Vertex) (i : ℕ) (hi : i < 26 + C.size) :
    (C.wires (bits S)).getD i false = false ↔ Covers S (families C i) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < 26
    · change (C.gates.foldl step (bits S)).getD i false = false ↔ _
      rw [fold_getD C.gates (bits S) (by simpa [bits_length] using hin),
        bits_getD S i hin, families, dite_eq_left hin, covers_input]
      exact decide_eq_false_iff_not
    · let j := i - 26
      have hi' : i = 26 + j := by dsimp [j]; omega
      have hj : j < C.size := by omega
      obtain ⟨a, b, hab, ha, hb, hop⟩ := gate_data C hC j hj
      have ha' := ih a (by omega) (by omega)
      have hb' := ih b (by omega) (by omega)
      have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      have hback : ∀ u ∈ C.gates[j].inputs, u < (bits S).length + j := by
        simpa only [← he, bits_length] using hC.2.1 j hj
      have hgate := fold_gate C.gates (bits S) j hj hback
      change (C.gates.foldl step (bits S)).getD i false = false ↔ _
      rw [hi', families_gate C j a b hab ha hb]
      rw [bits_length, ← he, hab] at hgate
      rw [hgate]
      rcases hop with h | h
      · rw [h, covers_union, ← ha', ← hb']
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_false_iff]
        rfl
      · rw [h, covers_inter, ← ha', ← hb']
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, Bool.or_eq_false_iff]
        rfl

private lemma output_bound (C : Circuit) (S : Finset Vertex) (h : C.eval (bits S) = true) :
    C.output < 26 + C.size := by
  by_contra! hout
  change (C.gates.foldl step (bits S)).getD C.output false = true at h
  rw [List.getD_eq_default _ _ (by simpa only [fold_length, bits_length, Circuit.size] using hout)]
    at h
  contradiction

end PEqualNP.Outside.L_meta_9008

theorem PEqualNP.Outside.L_meta_9008 :
have x1 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inl x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (Sum.inr x2 ∈ x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∃ (x4 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x2.eval (x1 x4) = Bool.true) → ∃ (x5 : ℕ → Finset (Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)))), ∃ x6 < (26 : ℕ) + x2.size, (∀ x7 < (26 : ℕ), ∃ (x9 : Fin (13 : ℕ) ⊕ Fin (13 : ℕ)), x5 x7 = {Finset.univ.erase x9}) ∧ (∀ x7 < x2.size, ∃ x9 < (26 : ℕ) + x7, ∃ x10 < (26 : ℕ) + x7, x5 ((26 : ℕ) + x7) = x5 x9 ∪ x5 x10 ∨ x5 ((26 : ℕ) + x7) = Finset.image₂ (fun (x11 x12 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x11 ∩ x12) (x5 x9) (x5 x10)) ∧ ∀ (x7 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x2.eval (x1 x7) = Bool.false ↔ ∃ x8 ∈ x5 x6, x7 ⊆ x8 := by
  intro x1 C hC htrue
  change (∃ S, C.eval (L_meta_9008.bits S) = true) at htrue
  obtain ⟨S, hS⟩ := htrue
  have hout := L_meta_9008.output_bound C S hS
  refine ⟨L_meta_9008.families C, C.output, hout, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨L_meta_9008.vertex i hi, by rw [L_meta_9008.families, dite_eq_left hi]⟩
  · intro j hj
    obtain ⟨a, b, hab, ha, hb, hop⟩ := L_meta_9008.gate_data C hC j hj
    refine ⟨a, ha, b, hb, ?_⟩
    have hgate := L_meta_9008.families_gate C j a b hab ha hb
    rcases hop with h | h
    · exact Or.inl (by rwa [h] at hgate)
    · exact Or.inr (by rwa [h] at hgate)
  · intro T
    exact L_meta_9008.wire_correct C hC T C.output hout
