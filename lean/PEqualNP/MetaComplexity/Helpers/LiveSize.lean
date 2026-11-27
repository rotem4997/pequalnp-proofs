import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.NormalForm

/-!
# Helpers for L-meta-3312: a circuit with its dead gates deleted has the live size

* `cone_iff`: `InCone n C i j` is the transitive closure of the one-step read relation `RR`.
* `unread_last`: the last gate outside `liveGates` is read by no gate and is not the output.
* `delU`: deleting such a gate (set it to `AND [0, 0]`, then `LiftFix.del`); it keeps `IsAO2`,
  the output value, and the live size, and drops the size by one.
-/

namespace PEqualNP.MetaComplexity.LiveSize

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Lift
open PEqualNP.MetaComplexity.LiftFix
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.TopForm

/-- One step of reading: gate `j` exists, `i < j`, and `j` reads the wire `n + i`. -/
def RG (n : ℕ) (gs : List Gate) (i j : ℕ) : Prop :=
  j < gs.length ∧ i < j ∧ n + i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs

theorem tg_last {α : Type} {R : α → α → Prop} {a b : α} (h : Relation.TransGen R a b) :
    ∃ c, R c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

theorem cones_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, coneStep, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem RG_snoc (n : ℕ) (gs : List Gate) (g : Gate) (a b : ℕ) (hb : b < gs.length) :
    RG n (gs ++ [g]) a b ↔ RG n gs a b := by
  unfold RG
  have : (gs ++ [g]).getD b ⟨GateOp.or, []⟩ = gs.getD b ⟨GateOp.or, []⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
  rw [this]
  simp only [List.length_append, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨hb, h2, h3⟩
  · rintro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩

theorem tg_snoc (n : ℕ) (gs : List Gate) (g : Gate) (i j : ℕ) (hj : j < gs.length) :
    Relation.TransGen (RG n (gs ++ [g])) i j ↔ Relation.TransGen (RG n gs) i j := by
  constructor
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ hj).mp h)
    | @tail b c _ hbc ih =>
      have hb : b < gs.length := by have := hbc.2.1; omega
      exact Relation.TransGen.tail (ih hb) ((RG_snoc n gs g _ _ hj).mp hbc)
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ h.1).mpr h)
    | tail _ hbc ih => exact Relation.TransGen.tail (ih (lt_trans hbc.2.1 hbc.1)) ((RG_snoc n gs g _ _ hbc.1).mpr hbc)

theorem cone_list (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔ Relation.TransGen (RG n gs) i j := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i j
    simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, false_iff]
    intro h
    obtain ⟨c, hc⟩ := tg_last h
    exact absurd hc.1 (by simp)
  | append_singleton gs g ih =>
    intro i j
    have hL := cones_length n gs []
    simp only [List.length_nil, Nat.zero_add] at hL
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cs := gs.foldl (coneStep n) [] with hcs
    rcases Nat.lt_trichotomy j gs.length with h1 | h1 | h1
    · rw [tg_snoc n gs g i j h1, ← ih i j]
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · subst h1
      have hget : (coneStep n cs g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hL]
      rw [hget, hL]
      have hRL : ∀ c, RG n (gs ++ [g]) c gs.length ↔ c < gs.length ∧ n + c ∈ g.inputs := by
        intro c
        unfold RG
        have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [this]
        simp
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, hw1, hw2⟩, hi | hi⟩
        · apply Relation.TransGen.single
          rw [hRL]
          refine ⟨by omega, ?_⟩
          have : n + i = w := by omega
          rw [this]; exact hw
        · have h2 := (ih i (w - n)).mp hi
          rw [← tg_snoc n gs g i (w - n) (by omega)] at h2
          refine Relation.TransGen.tail h2 ((hRL _).mpr ⟨by omega, ?_⟩)
          have : n + (w - n) = w := by omega
          rw [this]; exact hw
      · intro h
        cases h with
        | single h =>
          obtain ⟨hc, hm⟩ := (hRL i).mp h
          exact ⟨n + i, ⟨hm, by omega, by omega⟩, Or.inl (by omega)⟩
        | @tail c _ hic hc =>
          obtain ⟨hc1, hm⟩ := (hRL c).mp hc
          refine ⟨n + c, ⟨hm, by omega, by omega⟩, Or.inr ?_⟩
          have : n + c - n = c := by omega
          rw [this, ih]
          exact (tg_snoc n gs g i c hc1).mp hic
    · have hnil : (coneStep n cs g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [hnil]
      simp only [List.not_mem_nil, false_iff]
      intro h
      obtain ⟨c, hc⟩ := tg_last h
      have := hc.1
      simp at this
      omega

/-- The one-step read relation of `C`. -/
def RR (n : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  j < C.gates.length ∧ i < j ∧ n + i ∈ (gateAt C j).inputs

theorem cone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ Relation.TransGen (RR n C) i j := by
  unfold InCone cones
  rw [cone_list n C.gates i j]
  rfl


theorem mem_live (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ PEqualNP.FactorSubst.liveGates n C ↔ j < C.gates.length ∧ n ≤ C.output ∧
      (j = C.output - n ∨ Relation.TransGen (RR n C) j (C.output - n)) := by
  unfold PEqualNP.FactorSubst.liveGates
  rw [Finset.mem_filter, Finset.mem_range, cone_iff]

/-- The last gate outside the live set is read by no gate and is not the output. -/
theorem unread_last (n : ℕ) (C : Circuit) (hC : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length)
    (hkl : k ∉ PEqualNP.FactorSubst.liveGates n C)
    (hlast : ∀ j, k < j → j < C.gates.length → j ∈ PEqualNP.FactorSubst.liveGates n C) :
    (∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) ∧ C.output ≠ n + k := by
  rw [mem_live] at hkl
  constructor
  · intro j hj hm
    have hkj : k < j := by have := hC j hj _ hm; omega
    obtain ⟨_, ho, hjo⟩ := (mem_live n C j).mp (hlast j hkj hj)
    have hR : RR n C k j := ⟨hj, hkj, hm⟩
    apply hkl
    refine ⟨hk, ho, Or.inr ?_⟩
    rcases hjo with h | h
    · rw [← h]; exact Relation.TransGen.single hR
    · exact Relation.TransGen.head hR h
  · intro ho
    exact hkl ⟨hk, by omega, Or.inl (by omega)⟩

/-- The gate `AND [0, 0]`. -/
def X0 : Gate := ⟨GateOp.and, [0, 0]⟩

/-- Delete gate `k` (meant: an unread gate that is not the output). -/
def delU (n k : ℕ) (C : Circuit) : Circuit := del n k 0 ⟨C.gates.set k X0, C.output⟩

theorem pos_of_AO (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    0 < n + k := by
  have hl := hC.2.2 _ (gateAt_mem C k hk)
  match h : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    have := hC.2.1 k hk a (by rw [h]; simp)
    omega

theorem delU_AO (n k : ℕ) (C : Circuit) (hC : IsAO2 n C) (hk : k < C.gates.length) :
    IsAO2 n (delU n k C) := by
  have hp := pos_of_AO n C hC k hk
  apply del_AO n k 0 _ _ hp
  exact isAO2_set n C _ k X0 hC hk (Or.inl rfl) rfl (by intro i hi; simp [X0] at hi; omega)

theorem delU_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delU n k C).gates.length + 1 = C.gates.length := by
  have := del_length n k 0 ⟨C.gates.set k X0, C.output⟩ (by simpa using hk)
  simp only [List.length_set] at this
  exact this

theorem delU_fun (n k : ℕ) (C : Circuit) (hC : IsAO2 n C) (hk : k < C.gates.length)
    (hun : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (ho : C.output ≠ n + k) :
    circuitFun n (delU n k C) = circuitFun n C := by
  have hp := pos_of_AO n C hC k hk
  set E : Circuit := ⟨C.gates.set k X0, C.output⟩ with hE
  have hEAO : IsAO2 n E :=
    isAO2_set n C _ k X0 hC hk (Or.inl rfl) rfl (by intro i hi; simp [X0] at hi; omega)
  have hEf : circuitFun n E = circuitFun n C := set_unread_fun n C k X0 hk hun ho
  have hEh : E.gates[k]? = some X0 := by simp [hE, hk]
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD 0 false := by
    intro x
    have := wires_gate E k X0 hEh (List.ofFn x) (by intro i hi; simp [X0] at hi; simp; omega)
    simp only [List.length_ofFn] at this
    rw [this]
    simp [X0, GateOp.eval]
  have hDf := del_fun n k 0 E (by simpa [hE] using hk) hp (readsBack_take n E hEAO.2.1 k) hcopy
  unfold delU
  rw [← hE, hDf, hEf]

/-- Gate renaming up and down around a deleted gate `k`. -/
def up (k a : ℕ) : ℕ := if a < k then a else a + 1
def dn (k a : ℕ) : ℕ := if a < k then a else a - 1

theorem delU_gateAt (n k : ℕ) (C : Circuit) (b : ℕ) (hb : b < (delU n k C).gates.length) :
    gateAt (delU n k C) b = rd (n + k) 0 (gateAt C (up k b)) := by
  have hs := gateAt_some (delU n k C) b hb
  obtain ⟨g0, hg0, hg⟩ := del_get_inv n k 0 _ b _ hs
  rw [hg]
  congr 1
  have hne : up k b ≠ k := by unfold up; split_ifs <;> omega
  change (C.gates.set k X0)[up k b]? = some g0 at hg0
  rw [List.getElem?_set_ne (Ne.symm hne)] at hg0
  exact (gateAt_eq C _ g0 hg0).symm

theorem sig_iff (n k a w : ℕ) (hw : w ≠ n + k) : sig (n + k) 0 w = n + a ↔ w = n + up k a := by
  unfold sig up
  split_ifs <;> omega

theorem RR_del (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (hun : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (a b : ℕ) :
    RR n (delU n k C) a b ↔ RR n C (up k a) (up k b) := by
  have hl := delU_length n k C hk
  unfold RR
  by_cases hb : b < (delU n k C).gates.length
  · rw [delU_gateAt n k C b hb]
    have hub : up k b < C.gates.length := by unfold up; split_ifs <;> omega
    have hlt : a < b ↔ up k a < up k b := by unfold up; split_ifs <;> omega
    have hmem : n + a ∈ (rd (n + k) 0 (gateAt C (up k b))).inputs ↔
        n + up k a ∈ (gateAt C (up k b)).inputs := by
      simp only [rd, List.mem_map]
      constructor
      · rintro ⟨w, hw, he⟩
        have hwk : w ≠ n + k := fun e => hun _ hub (e ▸ hw)
        rw [sig_iff n k a w hwk] at he
        rw [← he]; exact hw
      · intro h
        refine ⟨_, h, ?_⟩
        rw [sig_iff n k a _ (fun e => hun _ hub (e ▸ h))]
    rw [hlt, hmem]
    simp [hb, hub]
  · simp only [hb, false_and, false_iff, not_and]
    intro h
    exfalso
    unfold up at h
    split_ifs at h <;> omega

theorem delU_output (n k : ℕ) (C : Circuit) : (delU n k C).output = sig (n + k) 0 C.output := rfl

theorem tg_up (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (hun : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (a b : ℕ)
    (h : Relation.TransGen (RR n (delU n k C)) a b) :
    Relation.TransGen (RR n C) (up k a) (up k b) := by
  induction h with
  | single h => exact Relation.TransGen.single ((RR_del n k C hk hun _ _).mp h)
  | tail _ hbc ih => exact Relation.TransGen.tail ih ((RR_del n k C hk hun _ _).mp hbc)

theorem up_dn (k a : ℕ) (ha : a ≠ k) : up k (dn k a) = a := by
  unfold up dn; split_ifs <;> omega

theorem dn_up (k a : ℕ) : dn k (up k a) = a := by
  unfold up dn; split_ifs <;> omega

theorem tg_dn (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (hun : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (a b : ℕ)
    (h : Relation.TransGen (RR n C) a b) (hb : b ≠ k) :
    Relation.TransGen (RR n (delU n k C)) (dn k a) (dn k b) := by
  have hnk : ∀ c d, RR n C c d → c ≠ k := by
    intro c d hcd e
    subst e
    exact hun d hcd.1 hcd.2.2
  have hone : ∀ c d, RR n C c d → d ≠ k → RR n (delU n k C) (dn k c) (dn k d) := by
    intro c d hcd hd
    rw [RR_del n k C hk hun, up_dn k c (hnk c d hcd), up_dn k d hd]
    exact hcd
  induction h with
  | single h => exact Relation.TransGen.single (hone _ _ h hb)
  | @tail c d _ hcd ih =>
    exact Relation.TransGen.tail (ih (hnk c d hcd)) (hone _ _ hcd hb)

theorem delU_live (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (hun : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (ho : C.output ≠ n + k) :
    PEqualNP.FactorSubst.liveSize n (delU n k C) = PEqualNP.FactorSubst.liveSize n C := by
  have hl := delU_length n k C hk
  unfold PEqualNP.FactorSubst.liveSize
  -- the output of the new circuit
  have hout : n ≤ C.output → n ≤ (delU n k C).output ∧
      (delU n k C).output - n = dn k (C.output - n) := by
    intro hn
    rw [delU_output]
    unfold sig dn
    split_ifs <;> omega
  have hout2 : n ≤ (delU n k C).output → n ≤ C.output := by
    rw [delU_output]
    unfold sig
    split_ifs <;> omega
  have notk : ∀ a ∈ PEqualNP.FactorSubst.liveGates n C, a = k → False := by
    intro a ha e
    subst e
    obtain ⟨_, hn, ha2⟩ := (mem_live n C a).mp ha
    rcases ha2 with h | h
    · omega
    · obtain ⟨c, hc, _⟩ := Relation.TransGen.head'_iff.mp h
      exact hun c hc.1 hc.2.2
  symm
  apply Finset.card_bij' (fun a _ => dn k a) (fun b _ => up k b)
  · intro a ha
    obtain ⟨ha1, hn, ha2⟩ := (mem_live n C a).mp ha
    have hak : a ≠ k := fun e => notk a ha e
    obtain ⟨hn', ho'⟩ := hout hn
    have hok' : C.output - n ≠ k := by omega
    rw [mem_live]
    refine ⟨by unfold dn; split_ifs <;> omega, hn', ?_⟩
    rw [ho']
    rcases ha2 with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (tg_dn n k C hk hun _ _ h hok')
  · intro b hb
    obtain ⟨hb1, hn, hb2⟩ := (mem_live n (delU n k C) b).mp hb
    have hn0 := hout2 hn
    obtain ⟨_, ho'⟩ := hout hn0
    have hok' : C.output - n ≠ k := by omega
    rw [mem_live]
    refine ⟨by unfold up; split_ifs <;> omega, hn0, ?_⟩
    rw [ho'] at hb2
    rcases hb2 with h | h
    · exact Or.inl (by rw [h, up_dn k _ hok'])
    · have := tg_up n k C hk hun _ _ h
      rw [up_dn k _ hok'] at this
      exact Or.inr this
  · intro a ha
    exact up_dn k a (fun e => notk a ha e)
  · intro b _
    exact dn_up k b

theorem wireVal_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C C.output x = circuitFun n C x := rfl

theorem all_live (n : ℕ) (C : Circuit)
    (hall : ∀ j < C.gates.length, j ∈ PEqualNP.FactorSubst.liveGates n C) :
    C.size = PEqualNP.FactorSubst.liveSize n C := by
  unfold PEqualNP.FactorSubst.liveSize Circuit.size
  have : PEqualNP.FactorSubst.liveGates n C = Finset.range C.gates.length := by
    ext j
    constructor
    · intro hj
      exact Finset.mem_range.mpr ((mem_live n C j).mp hj).1
    · intro hj
      exact hall j (Finset.mem_range.mp hj)
  rw [this, Finset.card_range]

theorem live_main (n : ℕ) : ∀ s (C : Circuit), C.gates.length = s → IsAO2 n C →
    ∃ D : Circuit, IsAO2 n D ∧ D.size = PEqualNP.FactorSubst.liveSize n C ∧
      ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n D D.output x =
        PEqualNP.CleanedNonEdge.wireVal n C C.output x := by
  intro s
  induction s with
  | zero =>
    intro C hs hC
    exact ⟨C, hC, all_live n C (fun j hj => by omega), fun _ => rfl⟩
  | succ s ih =>
    intro C hs hC
    by_cases hall : ∀ j < C.gates.length, j ∈ PEqualNP.FactorSubst.liveGates n C
    · exact ⟨C, hC, all_live n C hall, fun _ => rfl⟩
    · push Not at hall
      set S := (Finset.range C.gates.length).filter
        (fun j => j ∉ PEqualNP.FactorSubst.liveGates n C) with hS
      have hne : S.Nonempty := by
        obtain ⟨j, hj, hjl⟩ := hall
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjl⟩⟩
      set k := S.max' hne with hkdef
      have hkS : k ∈ S := Finset.max'_mem S hne
      obtain ⟨hk, hkl⟩ := Finset.mem_filter.mp hkS
      have hk' : k < C.gates.length := Finset.mem_range.mp hk
      have hlast : ∀ j, k < j → j < C.gates.length → j ∈ PEqualNP.FactorSubst.liveGates n C := by
        intro j hkj hj
        by_contra hjl
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjl⟩
        have := Finset.le_max' S j hjS
        omega
      obtain ⟨hun, ho⟩ := unread_last n C hC.2.1 k hk' hkl hlast
      have hl := delU_length n k C hk'
      obtain ⟨D, hD, hDs, hDv⟩ := ih (delU n k C) (by omega) (delU_AO n k C hC hk')
      refine ⟨D, hD, by rw [hDs, delU_live n k C hk' hun ho], fun x => ?_⟩
      rw [hDv, wireVal_out, wireVal_out, delU_fun n k C hC hk' hun ho]

end PEqualNP.MetaComplexity.LiveSize
