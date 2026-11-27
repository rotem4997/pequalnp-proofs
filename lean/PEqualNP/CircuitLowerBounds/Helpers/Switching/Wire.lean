import PEqualNP.CircuitLowerBounds.Helpers.Switching.Basic
import PEqualNP.CircuitLowerBounds.Helpers.Switching.Bridge

/-!
# The bridge statement of the plan, from `Switching.Bridge.layered`

The graded list of entries of the bridge becomes the levelled family of gate functions of the
plan: the functions of the entries of grade between `1` and `d`, at level one more than their
least grade. Nothing here is checked until L-lib-034 is.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Plan

open PEqualNP.CircuitLowerBounds
open PEqualNP.CircuitLowerBounds.Switching

theorem low_of_isBase {n : ℕ} {f : BF (Fin n)} (h : Bridge.IsBase f) : Low 1 f := by
  rcases h with ⟨b, rfl⟩ | ⟨i, rfl | rfl⟩
  · exact ⟨fun x hx => ⟨∅, by simp, fun y _ => hx⟩, fun x hx => ⟨∅, by simp, fun y _ => hx⟩⟩
  · exact ⟨fun x hx => ⟨{i}, by simp, fun y hy => by
        show y i = true; rw [hy i (by simp)]; exact hx⟩,
      fun x hx => ⟨{i}, by simp, fun y hy => by
        show y i = false; rw [hy i (by simp)]; exact hx⟩⟩
  · exact ⟨fun x hx => ⟨{i}, by simp, fun y hy => by
        show (!y i) = true; rw [hy i (by simp)]; exact hx⟩,
      fun x hx => ⟨{i}, by simp, fun y hy => by
        show (!y i) = false; rw [hy i (by simp)]; exact hx⟩⟩

theorem cnt_ofFn : ∀ (n : ℕ) (x : Fin n → Bool),
    cnt x = (((List.ofFn x).count true : ℕ) : ZMod 2) := by
  intro n
  induction n with
  | zero => intro x; simp [cnt]
  | succ n ih =>
    intro x
    have h := ih (fun i => x i.succ)
    unfold cnt at h ⊢
    rw [Fin.sum_univ_succ, h, List.ofFn_succ, List.count_cons]
    cases x 0 <;> simp <;> ring

theorem par_ofFn (n : ℕ) (x : Fin n → Bool) :
    par x = decide ((List.ofFn x).count true % 2 = 1) := by
  unfold par
  rw [cnt_ofFn]
  generalize (List.ofFn x).count true = k
  have h : ((k : ℕ) : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod k 2).symm
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [h, h0]; simp
  · rw [h, h1]; simp

theorem bridgeStmt : BridgeStmt := by
  classical
  intro d n C hops hdep hdec
  obtain ⟨F, out, hlen, hout, hgr, heval, -, hok⟩ :=
    Bridge.layered C n ((C.gates.map fun g => g.inputs.length).foldr max 0)
      (fun g hg => ⟨hops g hg, Bridge.le_foldr_max _ (List.mem_map_of_mem hg)⟩)
  let G : Finset (BF (Fin n)) :=
    ((F.filter fun q => 0 < q.1 ∧ q.1 ≤ d).map Prod.snd).toFinset
  let lev : BF (Fin n) → ℕ := fun f => 1 + sInf {j : ℕ | 0 < j ∧ j ≤ d ∧ (j, f) ∈ F}
  have hmemG : ∀ f : BF (Fin n), f ∈ G ↔ ∃ j, 0 < j ∧ j ≤ d ∧ (j, f) ∈ F := by
    intro f
    simp only [G, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨q, ⟨hq, h0, hd⟩, rfl⟩
      exact ⟨q.1, h0, hd, hq⟩
    · rintro ⟨j, h0, hd, hq⟩
      exact ⟨(j, f), ⟨hq, h0, hd⟩, rfl⟩
  have hlevle : ∀ (f : BF (Fin n)) (j : ℕ), 0 < j → j ≤ d → (j, f) ∈ F → lev f ≤ 1 + j := by
    intro f j h0 hd hq
    exact Nat.add_le_add_left (Nat.sInf_le (show j ∈ {j : ℕ | 0 < j ∧ j ≤ d ∧ (j, f) ∈ F} from ⟨h0, hd, hq⟩)) 1
  have hbase : ∀ q ∈ F, q.1 = 0 → Low 1 q.2 := by
    intro q hq h0
    rcases hok q hq with ⟨-, hb⟩ | ⟨hpos, -⟩
    · exact low_of_isBase hb
    · omega
  refine ⟨G, lev, out.2, ?_, ?_, ?_, ?_⟩
  · calc G.card ≤ ((F.filter fun q => 0 < q.1 ∧ q.1 ≤ d).map Prod.snd).length :=
          List.toFinset_card_le _
      _ ≤ F.length := by rw [List.length_map]; exact List.length_filter_le _ _
      _ ≤ 2 * (n + C.size) + 2 := hlen
  · intro g hg
    have hne : {j : ℕ | 0 < j ∧ j ≤ d ∧ (j, g) ∈ F}.Nonempty := (hmemG g).mp hg
    obtain ⟨hm0, hmd, hmF⟩ := Nat.sInf_mem hne
    set m := sInf {j : ℕ | 0 < j ∧ j ≤ d ∧ (j, g) ∈ F} with hm
    refine ⟨by show 2 ≤ 1 + m; omega, by show 1 + m ≤ d + 1; omega, ?_⟩
    rcases hok (m, g) hmF with ⟨h0, -⟩ | ⟨-, l, -, hl, hfun⟩
    · exact absurd h0 (by simpa using hm0.ne')
    refine ⟨{h | ∃ q ∈ l, q.2 = h}, ?_, ?_⟩
    · rintro h ⟨q, hq, rfl⟩
      obtain ⟨hqF, hqlt⟩ := hl q hq
      have hqlt' : q.1 < m := hqlt
      by_cases h0 : q.1 = 0
      · exact Or.inr (hbase q hqF h0)
      · left
        have hq' : (q.1, q.2) ∈ F := hqF
        refine ⟨(hmemG q.2).mpr ⟨q.1, by omega, by omega, hq'⟩, ?_⟩
        have := hlevle q.2 q.1 (by omega) (by omega) hq'
        show lev q.2 < 1 + m
        omega
    · rcases hfun with hall | hany
      · right
        intro x
        have : g x = (l.all fun q => q.2 x) := by
          have := congrFun hall x; simpa [Bridge.allOf] using this
        rw [this, List.all_eq_true]
        constructor
        · rintro h _ ⟨q, hq, rfl⟩; exact h q hq
        · intro h q hq; exact h q.2 ⟨q, hq, rfl⟩
      · left
        intro x
        have : g x = (l.any fun q => q.2 x) := by
          have := congrFun hany x; simpa [Bridge.anyOf] using this
        rw [this, List.any_eq_true]
        constructor
        · rintro ⟨q, hq, hx⟩; exact ⟨q.2, ⟨q, hq, rfl⟩, hx⟩
        · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩; exact ⟨q, hq, hx⟩
  · by_cases h0 : out.1 = 0
    · exact Or.inr (hbase out hout h0)
    · exact Or.inl ((hmemG out.2).mpr ⟨out.1, by omega, by omega, hout⟩)
  · refine ⟨false, fun x => ?_⟩
    rw [Bool.false_xor, par_ofFn, heval]
    have this : C.eval (List.ofFn x) = true ↔ (List.ofFn x).count true % 2 = 1 :=
      hdec (List.ofFn x) (List.length_ofFn)
    cases hE : C.eval (List.ofFn x)
    · have hc : ¬ (List.ofFn x).count true % 2 = 1 := fun hc => by
        rw [this.mpr hc] at hE; cases hE
      exact (decide_eq_false hc).symm
    · exact (decide_eq_true (this.mp hE)).symm

/-- The recorded statement of L-lib-034, from one round of the switching argument. -/
theorem stmt034_of_round (hR : Round) : Stmt034 :=
  assembly bridgeStmt (iterate_of_round hR) finalArith

end PEqualNP.CircuitLowerBounds.Switching.Plan
