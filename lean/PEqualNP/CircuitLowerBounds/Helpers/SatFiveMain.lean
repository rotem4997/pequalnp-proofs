import PEqualNP.CircuitLowerBounds.Helpers.SatFive
import PEqualNP.MetaComplexity.Helpers.PermInputs

/-!
# The SAT slice at length `4 k + 2` needs `5 k + 1` gates

Helper module (proofs only, no statement may use it). The positions `4 r + 1` (`r < k`) are
fixed in increasing order, each saving two gates (`PermInputs.fix_many`); the conditions are
the witness strings of `SatFive`. The other `3 k + 2` positions all matter afterwards.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.SatFive

open PEqualNP.Search PEqualNP.MetaComplexity.Helpers.PermInputs

theorem flip_ne (D : PEqualNP.CircuitLowerBounds.Circuit) (N : ℕ)
    (hdec : D.Decides SAT N) (l : List Bool) (hl : l.length = N) (i : Fin N)
    (hin : l ∈ SAT) (hout : l.set i (!l.getD i false) ∉ SAT) :
    (fun x : Fin N → Bool => D.eval (List.ofFn x))
        (Function.update (fun j : Fin N => l.getD j false) i
          (!(fun j : Fin N => l.getD j false) i))
      ≠ (fun x : Fin N → Bool => D.eval (List.ofFn x)) (fun j : Fin N => l.getD j false) := by
  have hx : List.ofFn (fun j : Fin N => l.getD j false) = l := by
    apply List.ext_getElem (by simp [hl])
    intro j h1 h2
    simp [List.getElem?_eq_getElem h2]
  simp only
  rw [PEqualNP.CircuitLowerBounds.Helpers.SatSlice.ofFn_update, hx]
  have h1 := (hdec l hl).2 hin
  intro heq
  rw [h1] at heq
  exact hout ((hdec _ (by simp [hl])).1 heq)

theorem main (k : ℕ) (hk : 4 ≤ k) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : ∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
    (hdec : D.Decides SAT (4 * k + 2)) : 5 * k + 1 ≤ D.size := by
  set f : (Fin (4 * k + 2) → Bool) → Bool := fun x => D.eval (List.ofFn x) with hf
  set L : List (Fin (4 * k + 2)) :=
    List.ofFn (fun r : Fin k => (⟨4 * r + 1, by omega⟩ : Fin (4 * k + 2))) with hL
  set T : Finset (Fin (4 * k + 2)) := Finset.univ.filter (fun i => i ∉ L) with hT
  have hLlen : L.length = k := by simp [hL]
  have hnd : L.Nodup := by
    rw [hL, List.nodup_ofFn]
    intro r s h
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    omega
  have hLget : ∀ (j : ℕ) (hj : j < L.length), (L[j]'hj).val = 4 * j + 1 := by
    intro j hj
    simp [hL]
  have memL : ∀ q : Fin (4 * k + 2), q ∈ L → ∃ r, r < k ∧ q.val = 4 * r + 1 := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    exact ⟨j, by omega, hLget j hj⟩
  set α : (Fin (4 * k + 2) → Bool) → List Bool :=
    fun a => List.ofFn (fun r : Fin k => a ⟨4 * r + 1, by omega⟩) with hα
  have hαlen : ∀ a, (α a).length = k := by intro a; simp [hα]
  have hαget : ∀ a (r : ℕ) (hr : r < k), (α a).getD r false = a ⟨4 * r + 1, by omega⟩ := by
    intro a r hr
    rw [List.getD_eq_getElem _ _ (by rw [hαlen]; exact hr)]
    simp [hα]
  have hαne : ∀ a, α a ≠ [] := by
    intro a h
    have := hαlen a
    rw [h] at this
    simp at this
    omega
  have hcard : T.card = 4 * k + 2 - k := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (4 * k + 2) => i ∈ L)
    have e : Finset.univ.filter (fun i : Fin (4 * k + 2) => i ∈ L) = L.toFinset := by
      ext i; simp
    rw [e, List.toFinset_card_of_nodup hnd, hLlen, Finset.card_univ, Fintype.card_fin] at h
    rw [hT]
    omega
  have hTne : T.Nonempty := by
    refine ⟨⟨4 * k, by omega⟩, ?_⟩
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun h => ?_⟩
    obtain ⟨r, hr, e⟩ := memL _ h
    simp at e
    omega
  have hdis : ∀ p ∈ L, p ∉ T := by
    intro p hp hpT
    rw [hT, Finset.mem_filter] at hpT
    exact hpT.2 hp
  have hC : ∀ (a : Fin (4 * k + 2) → Bool), ∀ i ∈ T, ∃ x : Fin (4 * k + 2) → Bool,
      (∀ q ∈ L, x q = a q) ∧ f (Function.update x i (!x i)) ≠ f x := by
    intro a i hi
    rw [hT, Finset.mem_filter] at hi
    have h1 : i.val % 4 ≠ 1 ∨ i.val = 4 * (α a).length + 1 := by
      rw [hαlen]
      by_contra hc
      push Not at hc
      apply hi.2
      have hr : i.val / 4 < k := by have := i.2; omega
      have : i = L[i.val / 4]'(by rw [hLlen]; exact hr) := by
        apply Fin.ext
        rw [hLget]
        omega
      rw [this]
      exact List.getElem_mem _
    obtain ⟨l, hl, hag, hin, hout⟩ :=
      condC (α a) (hαne a) i (by rw [hαlen]; exact i.2) h1
    rw [hαlen] at hl
    refine ⟨fun j => l.getD j false, ?_, flip_ne D _ hdec l hl i hin hout⟩
    intro q hq
    obtain ⟨r, hr, hqr⟩ := memL q hq
    have := hag r (by rw [hαlen]; exact hr)
    rw [hαget a r hr] at this
    simp only [hqr]
    rw [this]
    congr 1
    exact Fin.ext hqr.symm
  have hA : ∀ (a : Fin (4 * k + 2) → Bool) (pre post : List (Fin (4 * k + 2)))
      (p : Fin (4 * k + 2)), L = pre ++ p :: post →
      ∃ x : Fin (4 * k + 2) → Bool, (∀ q ∈ pre, x q = a q) ∧
        f (Function.update x p (!x p)) ≠ f x := by
    intro a pre post p hsplit
    have hlen : pre.length < L.length := by rw [hsplit]; simp
    have hp : p.val = 4 * pre.length + 1 := by
      have : L[pre.length]'hlen = p := by
        simp only [hsplit, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
      rw [← this, hLget]
    have hpre : ∀ q ∈ pre, ∃ j, j < pre.length ∧ q.val = 4 * j + 1 := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
      refine ⟨j, hj, ?_⟩
      have : L[j]'(by omega) = pre[j] := by
        simp only [hsplit, List.getElem_append_left hj]
      rw [← this, hLget]
    rcases Nat.eq_zero_or_pos pre.length with h0 | h0
    · obtain ⟨l, hl, hin, hout⟩ := condA0 k hk
      have hp1 : (p : ℕ) = 1 := by rw [hp, h0]
      refine ⟨fun j => l.getD j false, ?_, flip_ne D _ hdec l hl p hin (by rw [hp1]; exact hout)⟩
      intro q hq
      rw [List.length_eq_zero_iff] at h0
      rw [h0] at hq
      simp at hq
    · obtain ⟨l, hl, hag, hin, hout⟩ :=
        condA (α a) pre.length h0 (by have := hαlen a; omega)
      rw [hαlen] at hl
      refine ⟨fun j => l.getD j false, ?_, flip_ne D _ hdec l hl p hin (by rw [hp]; exact hout)⟩
      intro q hq
      obtain ⟨j, hj, hqj⟩ := hpre q hq
      have := hag j hj
      rw [hαget a j (by rw [← hLlen]; omega)] at this
      simp only [hqj]
      rw [this]
      congr 1
      exact Fin.ext hqj.symm
  have := fix_many T hTne L f hnd hdis hA hC D.size ⟨D, hD, le_rfl, fun _ => rfl⟩
  rw [hcard, hLlen] at this
  omega

end PEqualNP.CircuitLowerBounds.Helpers.SatFive
