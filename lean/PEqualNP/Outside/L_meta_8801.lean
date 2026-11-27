import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8801

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8801

theorem PEqualNP.Outside.L_meta_8801 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → x2.output < x1 + x1 + x2.size → (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) → x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false → ∃ (x9 : Finset ℕ), x3.card ≤ x9.card + (1 : ℕ) ∧ ∀ x10 ∈ x9, x10 < x2.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) (x1 + x1 + x10) = Bool.false ∧ ∃ (x12 : ℕ) (x13 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs = [x12, x13] ∧ (∃ (x14 : Fin x1) (x15 : Fin x1), PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x14} {x4}) x12 = Bool.true ∧ PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x15} {x4}) x13 = Bool.true) ∧ ∀ (x14 : Fin x1), PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x14} {x4}) x12 = Bool.true → PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput {x14} {x4}) x13 = Bool.false := by
  intro n C A l hAO hout hacc hrej
  classical
  let inp : Fin n → List Bool := fun x => PEqualNP.GenericRejection.incidenceInput {x} {l}
  let base : List Bool := PEqualNP.GenericRejection.incidenceInput Aᶜ {l}
  let V : Fin n → ℕ → Bool := fun x w => PEqualNP.CircuitLowerBounds.wireValue C (inp x) w
  let B : ℕ → Bool := fun w => PEqualNP.CircuitLowerBounds.wireValue C base w
  have len : ∀ (X Y : Finset (Fin n)), (PEqualNP.GenericRejection.incidenceInput X Y).length = n + n := by
    intro X Y; simp [PEqualNP.GenericRejection.incidenceInput]
  obtain ⟨hop, hrb, hlen⟩ := hAO
  have hga : ∀ j (hj : j < C.gates.length), PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    intro j hj
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  have hin : ∀ j (hj : j < C.gates.length), ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + n + j ∧ b < n + n + j := by
    intro j hj
    have h2 := hlen _ (List.getElem_mem hj)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 h2
    have h3 := hrb j hj
    rw [hga j hj, hab] at h3
    exact ⟨a, b, hab, h3 a (by simp), h3 b (by simp)⟩
  have gate : ∀ (X Y : Finset (Fin n)) j (hj : j < C.gates.length) a b, C.gates[j].inputs = [a, b] → a < n + n + j → b < n + n + j →
      PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) (n + n + j) =
      C.gates[j].op.eval [PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) a, PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) b] := by
    intro X Y j hj a b hab ha hb
    have h := PEqualNP.Outside.L_meta_8801.run_gate C.gates (PEqualNP.GenericRejection.incidenceInput X Y) j hj
    rw [len, hab] at h
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at h
    exact h
  have input : ∀ (X Y : Finset (Fin n)) w, w < n + n → PEqualNP.CircuitLowerBounds.wireValue C (PEqualNP.GenericRejection.incidenceInput X Y) w =
      (PEqualNP.GenericRejection.incidenceInput X Y).getD w false := by
    intro X Y w hw
    exact PEqualNP.Outside.L_meta_8801.run_input C.gates _ w (by rw [len]; exact hw)
  have inL : ∀ (X Y : Finset (Fin n)) w (hw : w < n), (PEqualNP.GenericRejection.incidenceInput X Y).getD w false = decide ((⟨w, hw⟩ : Fin n) ∈ X) := by
    intro X Y w hw
    unfold PEqualNP.GenericRejection.incidenceInput
    rw [List.getD_append _ _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]
  have inR : ∀ (X Y : Finset (Fin n)) w (hw : w < n), (PEqualNP.GenericRejection.incidenceInput X Y).getD (n + w) false = decide ((⟨w, hw⟩ : Fin n) ∈ Y) := by
    intro X Y w hw
    unfold PEqualNP.GenericRejection.incidenceInput
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]
  let good : ℕ → Prop := fun j => j < C.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ B (n + n + j) = false ∧
    ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧ (∃ x y, V x a = true ∧ V y b = true) ∧ ∀ x, V x a = true → V x b = false
  have key : ∀ k, k ≤ C.gates.length → ∃ (Q : Finset ℕ) (f : Fin n → Fin n), (∀ j ∈ Q, j < k) ∧ A.card ≤ Q.card + (A.image f).card ∧ (∀ j ∈ Q, good j) ∧
      ∀ w < n + n + k, B w = false → ∀ x y, V x w = true → V y w = true → f x = f y := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, id, by simp, by simp, by simp, ?_⟩
      intro w hw hB x y hx hy
      have hw : w < n + n := by simpa using hw
      by_cases hwn : w < n
      · have hx : _ = true := (input _ _ w hw).symm.trans hx
        have hy : _ = true := (input _ _ w hw).symm.trans hy
        rw [inL _ _ w hwn] at hx hy
        have e1 : (⟨w, hwn⟩ : Fin n) = x := by simpa using hx
        have e2 : (⟨w, hwn⟩ : Fin n) = y := by simpa using hy
        exact e1.symm.trans e2
      · exfalso
        obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hwn)
        have hv : v < n := by omega
        have hx : _ = true := (input _ _ _ hw).symm.trans hx
        have hB : _ = false := (input _ _ _ hw).symm.trans hB
        rw [inR _ _ v hv] at hx hB
        rw [hx] at hB
        cases hB
    | succ k ih =>
      intro hk
      obtain ⟨Q, f, hQ, hc, hg, hf⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      obtain ⟨a, b, hab, ha, hb⟩ := hin k hk'
      have gV : ∀ x, V x (n + n + k) = C.gates[k].op.eval [V x a, V x b] := fun x => gate _ _ k hk' a b hab ha hb
      have gB : B (n + n + k) = C.gates[k].op.eval [B a, B b] := gate _ _ k hk' a b hab ha hb
      have old : ∀ g : Fin n → Fin n, (∀ x y, f x = f y → g x = g y) → (B (n + n + k) = false → ∀ x y, V x (n + n + k) = true → V y (n + n + k) = true → g x = g y) →
          ∀ w < n + n + (k + 1), B w = false → ∀ x y, V x w = true → V y w = true → g x = g y := by
        intro g h1 h2 w hw hB x y hx hy
        by_cases e : w = n + n + k
        · subst e; exact h2 hB x y hx hy
        · exact h1 x y (hf w (by omega) hB x y hx hy)
      have keep : (B (n + n + k) = false → ∀ x y, V x (n + n + k) = true → V y (n + n + k) = true → f x = f y) →
          ∃ (Q : Finset ℕ) (f : Fin n → Fin n), (∀ j ∈ Q, j < k + 1) ∧ A.card ≤ Q.card + (A.image f).card ∧ (∀ j ∈ Q, good j) ∧
          ∀ w < n + n + (k + 1), B w = false → ∀ x y, V x w = true → V y w = true → f x = f y := fun h =>
        ⟨Q, f, fun j hj => Nat.lt_succ_of_lt (hQ j hj), hc, hg, old f (fun _ _ h => h) h⟩
      rcases hop _ (List.getElem_mem hk') with ho | ho
      · refine keep fun hB x y hx hy => ?_
        rw [gV, ho] at hx hy
        rw [gB, ho] at hB
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id, Bool.and_eq_true] at hx hy
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id, Bool.and_eq_false_iff] at hB
        rcases hB with hB | hB
        · exact hf a ha hB x y hx.1 hy.1
        · exact hf b hb hB x y hx.2 hy.2
      · have vo : ∀ x, V x (n + n + k) = true ↔ V x a = true ∨ V x b = true := by
          intro x
          rw [gV, ho]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        have bo : B (n + n + k) = false ↔ B a = false ∧ B b = false := by
          rw [gB, ho]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        by_cases hB : B (n + n + k) = false
        swap
        · exact keep fun h => absurd h hB
        obtain ⟨Ba, Bb⟩ := bo.1 hB
        by_cases hE : (∃ x y, V x a = true ∧ V y b = true) ∧ ∀ x, V x a = true → V x b = false
        · obtain ⟨⟨x0, y0, hx0, hy0⟩, hd⟩ := hE
          refine ⟨insert k Q, fun z => if f z = f y0 then f x0 else f z, ?_, ?_, ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · omega
            · have := hQ j hj; omega
          · rw [Finset.card_insert_of_notMem (fun h => by have := hQ k h; omega)]
            have hsub : A.image f ⊆ insert (f y0) (A.image fun z => if f z = f y0 then f x0 else f z) := by
              intro v hv
              obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
              by_cases e : f z = f y0
              · rw [e]; exact Finset.mem_insert_self _ _
              · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨z, hz, if_neg e⟩)
            have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
            omega
          · intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact ⟨hk', by rw [hga j hk']; exact ho, hB, a, b, by rw [hga j hk']; exact hab, ⟨x0, y0, hx0, hy0⟩, hd⟩
            · exact hg j hj
          · refine old _ (fun x y h => by simp only [h]) ?_
            intro _ x y hx hy
            have one : ∀ x, V x (n + n + k) = true → (if f x = f y0 then f x0 else f x) = f x0 := by
              intro x hx
              rcases (vo x).1 hx with h | h
              · have := hf a ha Ba x x0 h hx0
                split_ifs
                · rfl
                · exact this
              · rw [if_pos (hf b hb Bb x y0 h hy0)]
            simp only [one x hx, one y hy]
        · refine keep fun _ x y hx hy => ?_
          by_cases h1 : ∃ x y, V x a = true ∧ V y b = true
          · have h2 : ∃ c, V c a = true ∧ V c b = true := by
              by_contra hno
              refine hE ⟨h1, fun c hc => ?_⟩
              by_contra hcb
              exact hno ⟨c, hc, by simpa using hcb⟩
            obtain ⟨c, hca, hcb⟩ := h2
            have one : ∀ x, V x (n + n + k) = true → f x = f c := by
              intro x hx
              rcases (vo x).1 hx with h | h
              · exact hf a ha Ba x c h hca
              · exact hf b hb Bb x c h hcb
            rw [one x hx, one y hy]
          · rcases (vo x).1 hx with h | h <;> rcases (vo y).1 hy with h' | h'
            · exact hf a ha Ba x y h h'
            · exact absurd ⟨x, y, h, h'⟩ h1
            · exact absurd ⟨y, x, h', h⟩ h1
            · exact hf b hb Bb x y h h'
  obtain ⟨Q, f, _, hc, hg, hf⟩ := key C.gates.length le_rfl
  refine ⟨Q, ?_, fun j hj => hg j hj⟩
  have : (A.image f).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    exact hf C.output hout hrej x y (hacc x hx) (hacc y hy)
  omega
