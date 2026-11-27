import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_8978
import PEqualNP.Outside.L_meta_8980
import PEqualNP.Outside.L_meta_8981
import PEqualNP.Outside.L_meta_8982
import PEqualNP.Outside.L_meta_9018

theorem PEqualNP.Outside.L_meta_9019 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.Represents.HasLitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (s + 3 * 2 ^ k + 3 * 2 ^ l)) := by
  intro k l s A hlit
  obtain ⟨C, hCmono, hCsize, hCeval⟩ := hlit
  obtain ⟨P, hPmono, hPlen, w1, hw1⟩ := PEqualNP.Outside.L_meta_8980 k (2 ^ l)
  obtain ⟨Q, hQmono, hQlen, w2, hw2⟩ := PEqualNP.Outside.L_meta_8981 (2 ^ k) l
  let D : Set (List Bool) :=
    {x | ∃ (u : Fin (2 ^ k)) (v : Fin (2 ^ l)), x = PEqualNP.Represents.oneEach u v}
  have hD : ∀ x ∈ D, x.length = 2 ^ k + 2 ^ l := by
    rintro x ⟨u, v, rfl⟩
    simp [PEqualNP.Represents.oneEach]
  let w1' : Fin (k + k) → ℕ := fun j =>
    if h : j.val < k then w1 ⟨j.val, h⟩ true else w1 ⟨j.val - k, by omega⟩ false
  let w2' : Fin (l + l) → ℕ := fun j =>
    if h : j.val < l then w2 ⟨j.val, h⟩ true else w2 ⟨j.val - l, by omega⟩ false
  let f1 : Fin (k + k) → List Bool → Bool := fun j x =>
    ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w1' j) false
  let f2 : Fin (l + l) → List Bool → Bool := fun j x =>
    ((⟨Q, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w2' j) false
  obtain ⟨R, hRmono, hRlen, v1, v2, hv⟩ :=
    PEqualNP.Outside.L_meta_8982 (2 ^ k + 2 ^ l) (k + k) (l + l) D P Q w1' w2' f1 f2
      hD hPmono hQmono (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  let wAll : Fin ((k + l) + (k + l)) → ℕ := fun j =>
    if h1 : j.val < k then v1 ⟨j.val, by omega⟩
    else if h2 : j.val < k + l then v2 ⟨j.val - k, by omega⟩
    else if h3 : j.val < (k + l) + k then v1 ⟨k + (j.val - (k + l)), by omega⟩
    else v2 ⟨l + (j.val - (k + l) - k), by omega⟩
  let gAll : Fin ((k + l) + (k + l)) → List Bool → Bool := fun j x =>
    ((⟨R, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (wAll j) false
  obtain ⟨C', hC'mono, hC'size, hC'eval⟩ :=
    PEqualNP.Outside.L_meta_9018 (2 ^ k + 2 ^ l) ((k + l) + (k + l)) D R wAll gAll C
      hD hRmono hCmono (fun _ _ _ => rfl)
  refine ⟨C', hC'mono, by omega, fun u v => ?_⟩
  have hmem : PEqualNP.Represents.oneEach u v ∈ D := ⟨u, v, rfl⟩
  rw [hC'eval _ hmem]
  let xuv : Fin (k + l) → Bool := fun j =>
    if h : j.val < k then (u : ℕ).testBit j.val else (v : ℕ).testBit (j.val - k)
  have hlist : (List.ofFn fun j => gAll j (PEqualNP.Represents.oneEach u v)) =
      List.ofFn xuv ++ List.ofFn (fun i => !xuv i) := by
    apply List.ext_getElem
    · simp
    · intro m hm1 hm2
      simp only [List.length_ofFn] at hm1
      rw [List.getElem_ofFn]
      have hvuv := hv (PEqualNP.Represents.oneEach u v) hmem
      by_cases h1 : m < k
      · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
        dsimp only [gAll, wAll]
        rw [dif_pos h1, hvuv.1]
        dsimp only [f1, w1']
        rw [dif_pos h1, hw1 u v ⟨m, h1⟩ true]
        dsimp only [xuv]
        rw [dif_pos h1]
        cases (u : ℕ).testBit m <;> rfl
      · by_cases h2 : m < k + l
        · rw [List.getElem_append_left (by simp; omega), List.getElem_ofFn]
          dsimp only [gAll, wAll]
          rw [dif_neg h1, dif_pos h2, hvuv.2]
          dsimp only [f2, w2']
          rw [dif_pos (by omega : m - k < l), hw2 u v ⟨m - k, by omega⟩ true]
          dsimp only [xuv]
          rw [dif_neg h1]
          cases (v : ℕ).testBit (m - k) <;> rfl
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_ofFn, List.getElem_ofFn]
          by_cases h3 : m < (k + l) + k
          · dsimp only [gAll, wAll]
            rw [dif_neg h1, dif_neg h2, dif_pos h3, hvuv.1]
            dsimp only [f1, w1']
            rw [dif_neg (by omega : ¬ k + (m - (k + l)) < k)]
            have heq : k + (m - (k + l)) - k = m - (k + l) := by omega
            have hlt : m - (k + l) < k := by omega
            have hidx : (⟨k + (m - (k + l)) - k, by omega⟩ : Fin k) = ⟨m - (k + l), hlt⟩ := by
              ext; exact heq
            rw [hidx, hw1 u v ⟨m - (k + l), hlt⟩ false]
            dsimp only [xuv]
            rw [dif_pos hlt]
            cases (u : ℕ).testBit (m - (k + l)) <;> rfl
          · dsimp only [gAll, wAll]
            rw [dif_neg h1, dif_neg h2, dif_neg h3, hvuv.2]
            dsimp only [f2, w2']
            rw [dif_neg (by omega : ¬ l + (m - (k + l) - k) < l)]
            have heq : l + (m - (k + l) - k) - l = m - (k + l) - k := by omega
            have hlt : m - (k + l) - k < l := by omega
            have hidx : (⟨l + (m - (k + l) - k) - l, by omega⟩ : Fin l) = ⟨m - (k + l) - k, hlt⟩ := by
              ext; exact heq
            rw [hidx, hw2 u v ⟨m - (k + l) - k, hlt⟩ false]
            dsimp only [xuv]
            rw [dif_neg (by omega : ¬ m - (k + l) < k)]
            cases (v : ℕ).testBit (m - (k + l) - k) <;> rfl
  rw [hlist, hCeval xuv]
  unfold PEqualNP.Represents.adjFun
  have hu : (fun i : Fin k => xuv (Fin.castAdd l i)) = fun i : Fin k => (u : ℕ).testBit i := by
    funext i
    dsimp only [xuv]
    simp [i.isLt]
  have hv' : (fun j : Fin l => xuv (Fin.natAdd k j)) = fun j : Fin l => (v : ℕ).testBit j := by
    funext j
    dsimp only [xuv]
    simp
  rw [hu, hv', PEqualNP.Outside.L_meta_8978 k u, PEqualNP.Outside.L_meta_8978 l v]
  have hu2 : Fin.ofNat (2 ^ k) (u : ℕ) = u := by
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt u.isLt]
  have hv2 : Fin.ofNat (2 ^ l) (v : ℕ) = v := by
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt v.isLt]
  rw [hu2, hv2]
