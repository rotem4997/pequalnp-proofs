import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8980
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def sg (N a i : ℕ) : ℕ := if i < N then i else i + a

def rgS (N a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg N a)⟩

theorem keyS (N : ℕ) (x A G : List Bool) (hx : x.length = N) (i : ℕ) :
    (x ++ G).getD i false = (x ++ A ++ G).getD (sg N A.length i) false := by
  unfold sg
  by_cases hi : i < N
  · rw [if_pos hi, List.getD_append _ _ _ _ (by omega), List.append_assoc,
      List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hi, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp
    omega

theorem simSh (N : ℕ) (x A : List Bool) (hx : x.length = N) : ∀ (gs : List Gate) (G : List Bool),
    ∃ G' : List Bool, G'.length = G.length + gs.length ∧ wf gs (x ++ G) = x ++ G' ∧
      wf (gs.map (rgS N A.length)) (x ++ A ++ G) = x ++ A ++ G' := by
  intro gs
  induction gs with
  | nil => intro G; exact ⟨G, rfl, rfl, rfl⟩
  | cons g gs ih =>
    intro G
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : (rgS N A.length g).op.eval ((rgS N A.length g).inputs.map fun i => (x ++ A ++ G).getD i false)
        = g.op.eval (g.inputs.map fun i => (x ++ G).getD i false) := by
      show g.op.eval ((g.inputs.map (sg N A.length)).map fun i => (x ++ A ++ G).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (keyS N x A G hx a).symm
    rw [hv, List.append_assoc x G, List.append_assoc (x ++ A) G]
    obtain ⟨G', h1, h2, h3⟩ := ih (G ++ [g.op.eval (g.inputs.map fun i => (x ++ G).getD i false)])
    exact ⟨G', by simp at h1 ⊢; omega, h2, h3⟩

theorem gof {α : Type} (n : ℕ) (f : Fin n → α) (i : ℕ) (d : α) (h : i < n) :
    (List.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]

theorem app_read : ∀ (E : List Gate) (U V : List Bool), (∀ g ∈ E, ∀ a ∈ g.inputs, a < U.length) →
    wf E (U ++ V) = U ++ V ++ E.map (fun g => g.op.eval (g.inputs.map fun a => U.getD a false)) := by
  intro E
  induction E with
  | nil => intro U V _; simp [wf]
  | cons g E ih =>
    intro U V h
    rw [wf_cons, List.append_assoc U V, ih U _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    have hv : g.op.eval (g.inputs.map fun i => (U ++ V).getD i false)
        = g.op.eval (g.inputs.map fun a => U.getD a false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact List.getD_append _ _ _ _ (h g (List.mem_cons_self ..) a ha)
    rw [hv]
    simp

theorem split_ex (k : ℕ) (P : ℕ → Prop) :
    (∃ t < 2 ^ (k + 1), P t) ↔ (∃ t < 2 ^ k, P t) ∨ ∃ t < 2 ^ k, P (2 ^ k + t) := by
  have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
  constructor
  · rintro ⟨t, ht, hP⟩
    by_cases h : t < 2 ^ k
    · exact Or.inl ⟨t, h, hP⟩
    · refine Or.inr ⟨t - 2 ^ k, by omega, ?_⟩
      have : 2 ^ k + (t - 2 ^ k) = t := by omega
      rw [this]
      exact hP
  · rintro (⟨t, ht, hP⟩ | ⟨t, ht, hP⟩)
    · exact ⟨t, by omega, hP⟩
    · exact ⟨2 ^ k + t, by omega, hP⟩

def Lit (N o k : ℕ) (gs : List Gate) (w : ℕ → Bool → ℕ) (tw : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ i < k, ∀ b, w i b < N + gs.length) ∧ tw < N + gs.length ∧
  ∀ x : List Bool, x.length = N →
    (∀ i < k, ∀ b, (wf gs x).getD (w i b) false
      = decide (∃ t < 2 ^ k, t.testBit i = b ∧ x.getD (o + t) false = true)) ∧
    (wf gs x).getD tw false = decide (∃ t < 2 ^ k, x.getD (o + t) false = true)

def orG (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩

theorem orG_eval (a b : ℕ) (f : ℕ → Bool) :
    (orG a b).op.eval ((orG a b).inputs.map f) = (f a || f b) := by
  simp [orG, GateOp.eval]

theorem lit : ∀ (k o N : ℕ), o + 2 ^ k ≤ N → ∃ (gs : List Gate) (w : ℕ → Bool → ℕ) (tw : ℕ),
    Lit N o k gs w tw ∧ gs.length + 2 * k + 3 ≤ 3 * 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro o N h
    refine ⟨[], fun _ _ => 0, o, ⟨fun g hg => by simp at hg, fun i hi => by omega, by simp at h ⊢; omega,
      fun x hx => ⟨fun i hi => by omega, ?_⟩⟩, by simp⟩
    show x.getD o false = decide (∃ t < 2 ^ 0, x.getD (o + t) false = true)
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    constructor
    · intro hh
      exact ⟨0, by simp, by simpa using hh⟩
    · rintro ⟨t, ht, hx'⟩
      have ht0 : t = 0 := by simpa using ht
      subst ht0
      simpa using hx'
  | succ k ih =>
    intro o N h
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    rw [hp] at h
    obtain ⟨P, w1, t1, ⟨hP1, hP2, hP3, hP4⟩, hPl⟩ := ih o N
      (Nat.le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) o) h)
    obtain ⟨Q, w2, t2, ⟨hQ1, hQ2, hQ3, hQ4⟩, hQl⟩ := ih (o + 2 ^ k) N (by rw [Nat.add_assoc]; exact h)
    let E : List Gate := List.ofFn (fun j : Fin (2 * k + 1) =>
      if j.val < 2 * k then orG (w1 (j.val / 2) (decide (j.val % 2 = 1))) (sg N P.length (w2 (j.val / 2) (decide (j.val % 2 = 1))))
      else orG t1 (sg N P.length t2))
    let base : ℕ := N + P.length + Q.length
    refine ⟨P ++ Q.map (rgS N P.length) ++ E,
      fun i b => if i < k then base + (2 * i + (if b then 1 else 0)) else (if b then sg N P.length t2 else t1),
      base + 2 * k, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact hP1 g hg
        · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          exact ⟨(hQ1 g0 hg0).1, by simpa [rgS] using (hQ1 g0 hg0).2⟩
      · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
        dsimp only
        split_ifs <;> exact ⟨Or.inr rfl, le_refl 2⟩
    · intro i hi b
      simp only [List.length_append, List.length_map, List.length_ofFn, E, base]
      split_ifs
      · omega
      · omega
      · unfold sg; split_ifs <;> omega
      · omega
    · simp only [List.length_append, List.length_map, List.length_ofFn, E, base]
      omega
    · intro x hx
      obtain ⟨A, hA1, hA2, _⟩ := simSh N x [] hx P []
      rw [List.append_nil] at hA2
      have hA1' : A.length = P.length := by simpa using hA1
      obtain ⟨B, hB1, hB2, hB3⟩ := simSh N x A hx Q []
      rw [List.append_nil] at hB2 hB3
      have hB1' : B.length = Q.length := by simpa using hB1
      rw [hA1'] at hB3
      have hUlen : (x ++ A ++ B).length = base := by simp [base]; omega
      have hold1 : ∀ p, p < N + P.length → (x ++ A ++ B).getD p false = (wf P x).getD p false := by
        intro p hp'
        rw [hA2, List.getD_append _ _ _ _ (by simp; omega)]
      have hold2 : ∀ q, (x ++ A ++ B).getD (sg N P.length q) false = (wf Q x).getD q false := by
        intro q
        rw [hB2]
        have := keyS N x A B hx q
        rw [hA1'] at this
        exact this.symm
      have hEin : ∀ g ∈ E, ∀ a ∈ g.inputs, a < (x ++ A ++ B).length := by
        intro g hg a ha
        rw [hUlen]
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
        dsimp only at ha
        split_ifs at ha with hj
        · simp only [orG, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hP2 (j.val / 2) (by omega) (decide (j.val % 2 = 1)); omega
          · have := hQ2 (j.val / 2) (by omega) (decide (j.val % 2 = 1)); unfold sg; split_ifs <;> omega
        · simp only [orG, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · omega
          · unfold sg; split_ifs <;> omega
      have hW : wf (P ++ Q.map (rgS N P.length) ++ E) x
          = x ++ A ++ B ++ E.map (fun g => g.op.eval (g.inputs.map fun a => (x ++ A ++ B).getD a false)) := by
        rw [wf_append, wf_append, hA2, hB3]
        have := app_read E (x ++ A ++ B) [] hEin
        rw [List.append_nil] at this
        exact this
      have hnew : ∀ j (hj : j < 2 * k + 1), (wf (P ++ Q.map (rgS N P.length) ++ E) x).getD (base + j) false
          = (if j < 2 * k then
              ((wf P x).getD (w1 (j / 2) (decide (j % 2 = 1))) false || (wf Q x).getD (w2 (j / 2) (decide (j % 2 = 1))) false)
            else ((wf P x).getD t1 false || (wf Q x).getD t2 false)) := by
        intro j hj
        rw [hW, List.getD_append_right _ _ _ _ (by omega), hUlen, Nat.add_sub_cancel_left]
        simp only [E, List.map_ofFn]
        rw [gof _ _ _ _ hj]
        simp only [Function.comp]
        split_ifs with hj2
        · have := hP2 (j / 2) (by omega) (decide (j % 2 = 1))
          rw [orG_eval, hold1 _ this, hold2]
        · rw [orG_eval, hold1 _ hP3, hold2]
      have hkeep : ∀ p, p < base → (wf (P ++ Q.map (rgS N P.length) ++ E) x).getD p false
          = (x ++ A ++ B).getD p false := by
        intro p hp'
        rw [hW, List.getD_append _ _ _ _ (by omega)]
      obtain ⟨hPa, hPb⟩ := hP4 x hx
      obtain ⟨hQa, hQb⟩ := hQ4 x hx
      constructor
      · intro i hi b
        dsimp only
        by_cases hik : i < k
        · rw [if_pos hik]
          have hj : 2 * i + (if b then 1 else 0) < 2 * k + 1 := by split_ifs <;> omega
          rw [hnew _ hj, if_pos (by split_ifs <;> omega)]
          have e1 : (2 * i + (if b then 1 else 0)) / 2 = i := by split_ifs <;> omega
          have e2 : decide ((2 * i + (if b then 1 else 0)) % 2 = 1) = b := by cases b <;> simp <;> omega
          rw [e1, e2, hPa i hik b, hQa i hik b]
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_iff]
          rw [split_ex k (fun t => t.testBit i = b ∧ x.getD (o + t) false = true)]
          apply or_congr Iff.rfl
          constructor
          · rintro ⟨t, ht, hb, hx'⟩
            exact ⟨t, ht, by rw [Nat.testBit_two_pow_add_gt hik]; exact hb, by rw [← Nat.add_assoc]; exact hx'⟩
          · rintro ⟨t, ht, hb, hx'⟩
            exact ⟨t, ht, by rw [Nat.testBit_two_pow_add_gt hik] at hb; exact hb, by rw [Nat.add_assoc]; exact hx'⟩
        · have hie : i = k := by omega
          subst hie
          rw [if_neg hik]
          rw [Bool.eq_iff_iff, decide_eq_true_iff,
            split_ex i (fun t => t.testBit i = b ∧ x.getD (o + t) false = true)]
          cases b with
          | false =>
            simp only [Bool.false_eq_true, if_false]
            rw [hkeep t1 (by omega), hold1 t1 hP3, hPb, decide_eq_true_iff]
            constructor
            · rintro ⟨t, ht, hx'⟩
              exact Or.inl ⟨t, ht, Nat.testBit_lt_two_pow ht, hx'⟩
            · rintro (⟨t, ht, _, hx'⟩ | ⟨t, ht, hb, _⟩)
              · exact ⟨t, ht, hx'⟩
              · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht] at hb
                simp at hb
          | true =>
            simp only [if_true]
            rw [hkeep _ (by unfold sg; split_ifs <;> omega), hold2 t2, hQb, decide_eq_true_iff]
            constructor
            · rintro ⟨t, ht, hx'⟩
              exact Or.inr ⟨t, ht, by rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht]; rfl,
                by rw [← Nat.add_assoc]; exact hx'⟩
            · rintro (⟨t, ht, hb, _⟩ | ⟨t, ht, _, hx'⟩)
              · rw [Nat.testBit_lt_two_pow ht] at hb
                simp at hb
              · exact ⟨t, ht, by rw [Nat.add_assoc]; exact hx'⟩
      · rw [hnew (2 * k) (by omega), if_neg (by omega), hPb, hQb, Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff]
        rw [split_ex k (fun t => x.getD (o + t) false = true)]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨t, ht, hx'⟩
          exact ⟨t, ht, by rw [← Nat.add_assoc]; exact hx'⟩
        · rintro ⟨t, ht, hx'⟩
          exact ⟨t, ht, by rw [Nat.add_assoc]; exact hx'⟩
    · simp only [List.length_append, List.length_map, List.length_ofFn, E]
      have e3 : 3 * 2 ^ (k + 1) = 3 * 2 ^ k + 3 * 2 ^ k := by rw [pow_succ]; ring
      rw [e3]
      omega

end PEqualNP.Outside.L_meta_8980

open PEqualNP.Outside.L_meta_8980 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8980 : ∀ (k m : ℕ), ∃ gs : List PEqualNP.CircuitLowerBounds.Gate, PEqualNP.MetaComplexity.Monotone2 (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ gs.length ≤ 3 * 2 ^ k ∧ ∃ w : Fin k → Bool → ℕ, ∀ (u : Fin (2 ^ k)) (v : Fin m) (i : Fin k) (b : Bool), ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (PEqualNP.Represents.oneEach u v)).getD (w i b) false = decide ((u : ℕ).testBit i = b) := by
  intro k m
  obtain ⟨gs, w, tw, ⟨h1, _, _, h4⟩, hl⟩ := lit k 0 (2 ^ k + m) (by omega)
  refine ⟨gs, fun g hg => ⟨by rcases (h1 g hg).1 with h | h <;> simp [h], (h1 g hg).2⟩, by omega,
    fun i b => w i.val b, fun u v i b => ?_⟩
  have hx : (PEqualNP.Represents.oneEach u v).length = 2 ^ k + m := by
    simp [PEqualNP.Represents.oneEach]
  have := (h4 _ hx).1 i.val i.isLt b
  show (wf gs (PEqualNP.Represents.oneEach u v)).getD (w i.val b) false = _
  rw [this, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  have hval : ∀ t, t < 2 ^ k → ((PEqualNP.Represents.oneEach u v).getD (0 + t) false = true ↔ t = u.val) := by
    intro t ht
    unfold PEqualNP.Represents.oneEach
    rw [Nat.zero_add, List.getD_append _ _ _ _ (by simpa using ht), gof _ _ _ _ ht]
    simp [Fin.ext_iff]
  constructor
  · rintro ⟨t, ht, hb, hx'⟩
    rw [← (hval t ht).1 hx']
    exact hb
  · intro hb
    exact ⟨u.val, u.isLt, hb, (hval u.val u.isLt).2 rfl⟩
