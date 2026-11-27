import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4508

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma eval_input (C : Circuit) (inp : List Bool) (h : C.output < inp.length) :
    C.eval inp = inp.getD C.output false :=
  foldl_getD_lt C.gates inp C.output h

lemma inc_len (N : ℕ) (X Y : Finset (Fin N)) : (incidenceInput X Y).length = N + N := by
  simp [incidenceInput]

lemma inc_point (N : ℕ) (X Y : Finset (Fin N)) (o : ℕ) (ho : o < N) :
    (incidenceInput X Y).getD o false = decide ((⟨o, ho⟩ : Fin N) ∈ X) := by
  simp [incidenceInput, List.getD_eq_getElem?_getD, List.getElem?_append_left, ho]

lemma inc_line (N : ℕ) (X Y : Finset (Fin N)) (k : ℕ) (hk : k < N) :
    (incidenceInput X Y).getD (N + k) false = decide ((⟨k, hk⟩ : Fin N) ∈ Y) := by
  simp [incidenceInput, List.getD_eq_getElem?_getD, hk]

end PEqualNP.Outside.L_meta_4508

open PEqualNP.Outside.L_meta_4508 PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection in
theorem PEqualNP.Outside.L_meta_4508 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ) := by
  intro q N S C hq hN hcard huniq hAO hout hR hF
  exfalso
  have hN3 : 3 ≤ N := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    omega
  by_cases ho : C.output < N
  · have hc : 1 < (S ⟨0, by omega⟩).card := by rw [hcard]; omega
    obtain ⟨p, hp, hne⟩ := Finset.exists_mem_ne hc (⟨C.output, ho⟩ : Fin N)
    have h1 := hR ⟨0, by omega⟩ p hp
    rw [eval_input C _ (by rw [inc_len]; exact hout), inc_point N _ _ C.output ho] at h1
    have h2 : (⟨C.output, ho⟩ : Fin N) = p := by simpa using h1
    exact hne h2.symm
  · have hk : C.output - N < N := by omega
    have hex : ∃ l : Fin N, l ≠ ⟨C.output - N, hk⟩ := by
      by_cases h0 : C.output - N = 0
      · exact ⟨⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; simp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, by intro h; have := congrArg Fin.val h; simp at this; omega⟩
    obtain ⟨l, hl⟩ := hex
    have hpos : 0 < (S l).card := by rw [hcard]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have h1 := hR l p hp
    have ho2 : C.output = N + (C.output - N) := by omega
    rw [eval_input C _ (by rw [inc_len]; exact hout), ho2, inc_line N _ _ (C.output - N) hk] at h1
    have h2 : (⟨C.output - N, hk⟩ : Fin N) = l := by simpa using h1
    exact hl h2.symm
