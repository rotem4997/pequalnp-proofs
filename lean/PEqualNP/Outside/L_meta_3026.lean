import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.SplitCount

-- evaluation toolkit (step .. mono) copied from the merged L_meta_1406, zero from L_meta_2780
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h

lemma zero {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : Fin n → Bool) (hx : ∀ v, x v = false) : ∀ i, val gs x i = false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_lt gs x i h1]
      exact hx _
    · by_cases h2 : n + gs.length ≤ i
      · exact val_ge gs x i h2
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = false := by
          intro a
          by_cases hlt : a < n + k
          · rw [if_pos hlt]
            exact ih a hlt
          · rw [if_neg hlt]
        obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
        rcases hop with rfl | rfl <;> simp [GateOp.eval, rd]

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)

-- cone characterisation (cones_len .. inCone_trans) copied from the merged L_meta_2067
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

structure Good (n : ℕ) (C : Circuit) : Prop where
  ao : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  rb : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma two {n : ℕ} {C : Circuit} (hG : Good n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]
    exact List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hG.ao _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  exact ⟨a, b, hab, hG.rb j hj a (by simp [hab]), hG.rb j hj b (by simp [hab]), hop⟩

lemma val_and {n : ℕ} {C : Circuit} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (hop : (gateAt C j).op = GateOp.and) :
    val C.gates x (n + j) = (val C.gates x a && val C.gates x b) := by
  rw [val_gate C.gates x j hj, ← gateAt_eq C j hj, hin, hop]
  simp [GateOp.eval, ha, hb]

lemma val_or {n : ℕ} {C : Circuit} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hin : (gateAt C j).inputs = [a, b]) (ha : a < n + j) (hb : b < n + j)
    (hop : (gateAt C j).op = GateOp.or) :
    val C.gates x (n + j) = (val C.gates x a || val C.gates x b) := by
  rw [val_gate C.gates x j hj, ← gateAt_eq C j hj, hin, hop]
  simp [GateOp.eval, ha, hb]

inductive Reach (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop
  | refl (w : ℕ) : Reach n C w w
  | step (v g w : ℕ) : g < C.gates.length → v ∈ (gateAt C g).inputs → Reach n C (n + g) w →
      Reach n C v w

lemma reach_trans {n : ℕ} {C : Circuit} {v w u : ℕ} (h1 : Reach n C v w) (h2 : Reach n C w u) :
    Reach n C v u := by
  induction h1 with
  | refl w => exact h2
  | step v g w hg hin _ ih => exact Reach.step v g u hg hin (ih h2)

lemma reach_le {n : ℕ} {C : Circuit} (hG : Good n C) {v w : ℕ} (h : Reach n C v w) : v ≤ w := by
  induction h with
  | refl w => exact le_refl _
  | step v g w hg hin _ ih =>
    have := hG.rb g hg v hin
    omega

lemma reach_in {n : ℕ} {C : Circuit} {a g : ℕ} (hg : g < C.gates.length)
    (hin : a ∈ (gateAt C g).inputs) : Reach n C a (n + g) :=
  Reach.step a g (n + g) hg hin (Reach.refl _)

lemma reach_cases {n : ℕ} {C : Circuit} {v w : ℕ} (h : Reach n C v w) :
    v = w ∨ ∃ g, g < C.gates.length ∧ v ∈ (gateAt C g).inputs ∧ Reach n C (n + g) w := by
  induction h with
  | refl w => exact Or.inl rfl
  | step v g w hg hin hr _ => exact Or.inr ⟨g, hg, hin, hr⟩

lemma dep {n : ℕ} {C : Circuit} (hG : Good n C) (x x' : Fin n → Bool) :
    ∀ w, (∀ v : Fin n, Reach n C v.val w → x v = x' v) →
      val C.gates x w = val C.gates x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < n
    · rw [val_lt _ x w h1, val_lt _ x' w h1]
      exact h ⟨w, h1⟩ (Reach.refl _)
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_ge _ x w h2, val_ge _ x' w h2]
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        obtain ⟨a, b, hab, ha, hb, hop⟩ := two hG k hk
        have ea := ih a ha (fun v hv => h v (reach_trans hv (reach_in hk (by simp [hab]))))
        have eb := ih b hb (fun v hv => h v (reach_trans hv (reach_in hk (by simp [hab]))))
        rcases hop with hop | hop
        · rw [val_and x k hk a b hab ha hb hop, val_and x' k hk a b hab ha hb hop, ea, eb]
        · rw [val_or x k hk a b hab ha hb hop, val_or x' k hk a b hab ha hb hop, ea, eb]

lemma lin_reach {n : ℕ} {C : Circuit} (hG : Good n C) (v : Fin n) (w : ℕ)
    (h : val C.gates (eof v) w = true) : Reach n C v.val w := by
  by_contra hn
  have e := dep hG (eof v) (fun _ => false) w (fun u hu => by
    have hne : u ≠ v := fun huv => hn (huv ▸ hu)
    simp [eof, hne])
  rw [e, zero C.gates hG.ao (fun _ => false) (fun _ => rfl) w] at h
  exact absurd h (by simp)

lemma dep_pr {n : ℕ} {C : Circuit} (hG : Good n C) (u u' : Fin n) (w : ℕ)
    (hn : ¬ Reach n C u.val w) : val C.gates (pr u u') w = val C.gates (eof u') w :=
  dep hG _ _ w (fun v hv => by
    have hne : v ≠ u := fun h => hn (h ▸ hv)
    simp [pr, eof, hne])

lemma dep_pr' {n : ℕ} {C : Circuit} (hG : Good n C) (u u' : Fin n) (w : ℕ)
    (hn : ¬ Reach n C u'.val w) : val C.gates (pr u u') w = val C.gates (eof u) w :=
  dep hG _ _ w (fun v hv => by
    have hne : v ≠ u' := fun h => hn (h ▸ hv)
    simp [pr, eof, hne])

lemma cone_reach (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ c, InCone n C g c → Reach n C (n + g) (n + c) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h
    · subst h3
      exact reach_in h0 hin
    · exact reach_trans (ih k hk h3) (reach_in h0 hin)

lemma reach_cone {n : ℕ} {C : Circuit} (hG : Good n C) {v w : ℕ} (h : Reach n C v w) :
    ∀ g c, v = n + g → w = n + c → c < C.gates.length → InConeOrSelf n C g c := by
  induction h with
  | refl w =>
    intro g c h1 h2 _
    left
    omega
  | step v g' w hg' hin _ ih =>
    intro g c h1 h2 hc
    subst h1 h2
    have hlt := hG.rb g' hg' _ hin
    have hgg : InCone n C g g' :=
      (inCone_iff n C g g').2 ⟨hg', g, by omega, hin, Or.inl rfl⟩
    rcases ih g' c rfl rfl hc with h | h
    · subst h
      exact Or.inr hgg
    · exact Or.inr (inCone_trans n C g g' hgg c h)

lemma memK {n : ℕ} {C : Circuit} (hG : Good n C) (c : ℕ) (hc : c < C.gates.length) (k : ℕ) :
    k ∈ (Finset.range C.gates.length).filter (fun k => InConeOrSelf n C k c) ↔
      Reach n C (n + k) (n + c) := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h | h⟩
    · subst h
      exact Reach.refl _
    · exact cone_reach n C k c h
  · intro h
    have := reach_le hG h
    exact ⟨by omega, reach_cone hG h k c rfl rfl hc⟩

def R (n : ℕ) (C : Circuit) (c : ℕ) (w : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range C.gates.length).filter (fun k => InConeOrSelf n C k c),
    (gateAt C j).inputs.count w

lemma R_pos {n : ℕ} {C : Circuit} {c : ℕ} (hG : Good n C) (hc : c < C.gates.length) {w g : ℕ}
    (hgK : Reach n C (n + g) (n + c)) (hin : w ∈ (gateAt C g).inputs) :
    1 ≤ R n C c w := by
  unfold R
  have hm := (memK hG c hc g).2 hgK
  calc 1 ≤ (gateAt C g).inputs.count w := List.count_pos_iff.2 hin
    _ ≤ _ := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w)
        (fun _ _ => Nat.zero_le _) hm

lemma reach_R {n : ℕ} {C : Circuit} {c : ℕ} (hG : Good n C) (hc : c < C.gates.length) {w : ℕ}
    (h : Reach n C w (n + c)) (hne : w ≠ n + c) : 1 ≤ R n C c w := by
  rcases reach_cases h with h | ⟨g, _, hin, hr⟩
  · exact absurd h hne
  · exact R_pos hG hc hr hin

lemma count_sum (N a b : ℕ) (ha : a < N) (hb : b < N) :
    ∑ w ∈ Finset.range N, [a, b].count w = 2 := by
  have e : ∀ w, [a, b].count w = (if a = w then 1 else 0) + (if b = w then 1 else 0) := by
    intro w
    by_cases h1 : a = w <;> by_cases h2 : b = w <;> simp [List.count_cons, h1, h2]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range, ha, hb, if_true]

lemma R_sum {n : ℕ} {C : Circuit} (hG : Good n C) (c : ℕ) :
    ∑ w ∈ Finset.range (n + C.gates.length), R n C c w =
      2 * ((Finset.range C.gates.length).filter (fun k => InConeOrSelf n C k c)).card := by
  unfold R
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjl : j < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
  obtain ⟨a, b, hab, ha, hb, _⟩ := two hG j hjl
  rw [hab, count_sum _ a b (by omega) (by omega)]
  rfl

lemma tight (W A : Finset ℕ) (R : ℕ → ℕ) (hA : A ⊆ W) (h1 : ∀ w ∈ A, 1 ≤ R w)
    (hs : ∑ w ∈ W, R w ≤ A.card) :
    (∀ w ∈ W, R w ≤ 1) ∧ ∀ w ∈ W, w ∉ A → R w = 0 := by
  classical
  have e : ∑ w ∈ W, R w = ∑ w ∈ W, (R w - if w ∈ A then 1 else 0) +
      ∑ w ∈ W, (if w ∈ A then (1 : ℕ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hwA : w ∈ A
    · have := h1 w hwA
      simp only [hwA, if_true]
      omega
    · simp [hwA]
  have e2 : ∑ w ∈ W, (if w ∈ A then (1 : ℕ) else 0) = A.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA]
    simp
  have z : ∑ w ∈ W, (R w - if w ∈ A then 1 else 0) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at z
  constructor
  · intro w hw
    have := z w hw
    by_cases hwA : w ∈ A
    · simp only [hwA, if_true] at this
      omega
    · simp only [hwA, if_false] at this
      omega
  · intro w hw hwA
    have := z w hw
    simpa [hwA] using this

structure Tree (n : ℕ) (C : Circuit) (c : ℕ) : Prop where
  good : Good n C
  hc : c < C.gates.length
  up : ∀ g g' w, g < C.gates.length → g' < C.gates.length → Reach n C (n + g) (n + c) →
    Reach n C (n + g') (n + c) → w ∈ (gateAt C g).inputs → w ∈ (gateAt C g').inputs → g = g'
  nd : ∀ g a, g < C.gates.length → Reach n C (n + g) (n + c) → (gateAt C g).inputs = [a, a] →
    False

lemma mkTree {n : ℕ} {C : Circuit} {c : ℕ} (hG : Good n C) (hc : c < C.gates.length)
    (hR1 : ∀ w ∈ Finset.range (n + C.gates.length), R n C c w ≤ 1) : Tree n C c := by
  refine ⟨hG, hc, ?_, ?_⟩
  · intro g g' w hg hg' hgK hgK' hin hin'
    by_contra hne
    have hw : w ∈ Finset.range (n + C.gates.length) := by
      have := hG.rb g hg w hin
      rw [Finset.mem_range]
      omega
    have h1 := hR1 w hw
    have hsub : ({g, g'} : Finset ℕ) ⊆
        (Finset.range C.gates.length).filter (fun k => InConeOrSelf n C k c) := by
      intro k hk
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact (memK hG c hc _).2 hgK
      · exact (memK hG c hc _).2 hgK'
    have h2 : ∑ j ∈ ({g, g'} : Finset ℕ), (gateAt C j).inputs.count w ≤ R n C c w :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair hne] at h2
    have := List.count_pos_iff.2 hin
    have := List.count_pos_iff.2 hin'
    omega
  · intro g a hg hgK hin
    have hw : a ∈ Finset.range (n + C.gates.length) := by
      have := hG.rb g hg a (by simp [hin])
      rw [Finset.mem_range]
      omega
    have h1 := hR1 a hw
    have h2 : (gateAt C g).inputs.count a ≤ R n C c a :=
      Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count a)
        (fun _ _ => Nat.zero_le _) ((memK hG c hc g).2 hgK)
    rw [hin] at h2
    simp at h2
    omega

lemma chain {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) {v a : ℕ} (h : Reach n C v a) :
    ∀ b, Reach n C v b → Reach n C a (n + c) → Reach n C b (n + c) →
      Reach n C a b ∨ Reach n C b a := by
  induction h with
  | refl w =>
    intro b hb _ _
    exact Or.inl hb
  | step v g a hg hin hr ih =>
    intro b hb hac hbc
    rcases reach_cases hb with h | ⟨g', hg', hin', hr'⟩
    · subst h
      exact Or.inr (Reach.step _ g _ hg hin hr)
    · have e : g = g' :=
        hT.up g g' v hg hg' (reach_trans hr hac) (reach_trans hr' hbc) hin hin'
      subst e
      exact ih b hr' hac hbc

lemma disj {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) {G a b v : ℕ}
    (hGl : G < C.gates.length) (hGc : Reach n C (n + G) (n + c))
    (hin : (gateAt C G).inputs = [a, b]) (ha : Reach n C v a) (hb : Reach n C v b) : False := by
  have hG := hT.good
  have hia : a ∈ (gateAt C G).inputs := by simp [hin]
  have hib : b ∈ (gateAt C G).inputs := by simp [hin]
  have hla := hG.rb G hGl a hia
  have hlb := hG.rb G hGl b hib
  have hac := reach_trans (reach_in hGl hia) hGc
  have hbc := reach_trans (reach_in hGl hib) hGc
  have key : ∀ p q, p ∈ (gateAt C G).inputs → q < n + G → Reach n C q (n + c) →
      Reach n C p q → p = q := by
    intro p q hp hq hqc hpq
    rcases reach_cases hpq with h | ⟨g, hg, hin', hr⟩
    · exact h
    · have e : g = G := hT.up g G p hg hGl (reach_trans hr hqc) hGc hin' hp
      subst e
      have := reach_le hG hr
      omega
  have e : a = b := by
    rcases chain hT ha b hb hac hbc with h | h
    · exact key a b hia hlb hbc h
    · exact (key b a hib hla hac h).symm
  subst e
  exact hT.nd G a hGl hGc hin

inductive OrP (n : ℕ) (C : Circuit) (c : ℕ) : ℕ → Prop
  | base : OrP n C c (n + c)
  | step (g w : ℕ) : g < C.gates.length → (gateAt C g).op = GateOp.or →
      w ∈ (gateAt C g).inputs → OrP n C c (n + g) → OrP n C c w

lemma orp_up {n : ℕ} {C : Circuit} {c : ℕ} (hG : Good n C) (x : Fin n → Bool) {w : ℕ}
    (h : OrP n C c w) : val C.gates x w = true → val C.gates x (n + c) = true := by
  induction h with
  | base => exact id
  | step g w hg hor hin _ ih =>
    intro hw
    apply ih
    obtain ⟨a, b, hab, ha, hb, _⟩ := two hG g hg
    rw [val_or x g hg a b hab ha hb hor, Bool.or_eq_true]
    rw [hab] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw

lemma orp_reach {n : ℕ} {C : Circuit} {c : ℕ} {w : ℕ} (h : OrP n C c w) :
    Reach n C w (n + c) := by
  induction h with
  | base => exact Reach.refl _
  | step g w hg _ hin _ ih => exact Reach.step w g _ hg hin ih

lemma orp_leaf {n : ℕ} {C : Circuit} {c : ℕ} (hG : Good n C) (x : Fin n → Bool) :
    ∀ g, g < C.gates.length → OrP n C c (n + g) → val C.gates x (n + g) = true →
      ∃ w, OrP n C c w ∧ val C.gates x w = true ∧
        (w < n ∨ ∃ g', g' < C.gates.length ∧ w = n + g' ∧ (gateAt C g').op = GateOp.and) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg ho hv
    obtain ⟨a, b, hab, ha, hb, hop⟩ := two hG g hg
    rcases hop with hop | hop
    · exact ⟨n + g, ho, hv, Or.inr ⟨g, hg, rfl, hop⟩⟩
    · rw [val_or x g hg a b hab ha hb hop, Bool.or_eq_true] at hv
      have key : ∀ a', a' ∈ (gateAt C g).inputs → a' < n + g → val C.gates x a' = true →
          ∃ w, OrP n C c w ∧ val C.gates x w = true ∧
            (w < n ∨ ∃ g', g' < C.gates.length ∧ w = n + g' ∧
              (gateAt C g').op = GateOp.and) := by
        intro a' hin hlt hva
        have hoa : OrP n C c a' := OrP.step g a' hg hop hin ho
        by_cases h : a' < n
        · exact ⟨a', hoa, hva, Or.inl h⟩
        · obtain ⟨k, rfl⟩ : ∃ k, a' = n + k := ⟨a' - n, by omega⟩
          exact ih k (by omega) (by omega) hoa hva
      rcases hv with hv | hv
      · exact key a (by simp [hab]) ha hv
      · exact key b (by simp [hab]) hb hv

lemma orp_uniq {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) {v : ℕ} (h : OrP n C c v) :
    ∀ G, G < C.gates.length → (gateAt C G).op = GateOp.and → Reach n C v (n + G) →
      Reach n C (n + G) (n + c) → v ≠ n + G → False := by
  induction h with
  | base =>
    intro G _ _ h1 h2 hne
    have := reach_le hT.good h1
    have := reach_le hT.good h2
    omega
  | step g w hg hor hin hprev ih =>
    intro G hGl hop h1 h2 hne
    rcases reach_cases h1 with h | ⟨g', hg', hin', hr⟩
    · exact hne h
    · have e : g = g' :=
        hT.up g g' w hg hg' (orp_reach hprev) (reach_trans hr h2) hin hin'
      subst e
      by_cases hgG : g = G
      · subst hgG
        rw [hor] at hop
        cases hop
      · exact ih G hGl hop hr h2 (by omega)

lemma lin_orp {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) (v : Fin n)
    (h : val C.gates (eof v) (n + c) = true) : OrP n C c v.val := by
  have hG := hT.good
  obtain ⟨w, hwo, hwv, hw | ⟨G, hGl, rfl, hop⟩⟩ := orp_leaf hG (eof v) c hT.hc OrP.base h
  · rw [val_lt _ _ w hw] at hwv
    simp only [eof, decide_eq_true_eq] at hwv
    subst hwv
    exact hwo
  · exfalso
    obtain ⟨a, b, hab, ha, hb, _⟩ := two hG G hGl
    rw [val_and _ G hGl a b hab ha hb hop, Bool.and_eq_true] at hwv
    exact disj hT hGl (orp_reach hwo) hab (lin_reach hG v a hwv.1) (lin_reach hG v b hwv.2)

lemma split2 {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) (u u' : Fin n)
    (h1 : val C.gates (eof u) (n + c) = false) (h2 : val C.gates (eof u') (n + c) = false)
    (h3 : val C.gates (pr u u') (n + c) = true) :
    ∃ G a b, G < C.gates.length ∧ (gateAt C G).op = GateOp.and ∧ OrP n C c (n + G) ∧
      (gateAt C G).inputs = [a, b] ∧
      ((val C.gates (eof u) a = true ∧ val C.gates (eof u') b = true) ∨
       (val C.gates (eof u') a = true ∧ val C.gates (eof u) b = true)) := by
  have hG := hT.good
  obtain ⟨w, hwo, hwv, hw | ⟨G, hGl, rfl, hop⟩⟩ := orp_leaf hG (pr u u') c hT.hc OrP.base h3
  · exfalso
    rw [val_lt _ _ w hw] at hwv
    simp only [pr, decide_eq_true_eq] at hwv
    rcases hwv with h | h
    · have := orp_up hG (eof u) hwo (by rw [val_lt _ _ w hw]; simp [eof, h])
      rw [h1] at this
      exact absurd this (by simp)
    · have := orp_up hG (eof u') hwo (by rw [val_lt _ _ w hw]; simp [eof, h])
      rw [h2] at this
      exact absurd this (by simp)
  · obtain ⟨a, b, hab, ha, hb, _⟩ := two hG G hGl
    have hGc := orp_reach hwo
    rw [val_and _ G hGl a b hab ha hb hop, Bool.and_eq_true] at hwv
    refine ⟨G, a, b, hGl, hop, hwo, hab, ?_⟩
    by_cases hr : Reach n C u.val a
    · have hnb : ¬ Reach n C u.val b := fun h => disj hT hGl hGc hab hr h
      have hb' : val C.gates (eof u') b = true := by
        rw [← dep_pr hG u u' b hnb]
        exact hwv.2
      have hna : ¬ Reach n C u'.val a :=
        fun h => disj hT hGl hGc hab h (lin_reach hG u' b hb')
      left
      refine ⟨?_, hb'⟩
      rw [← dep_pr' hG u u' a hna]
      exact hwv.1
    · have ha' : val C.gates (eof u') a = true := by
        rw [← dep_pr hG u u' a hr]
        exact hwv.1
      have hnb : ¬ Reach n C u'.val b :=
        fun h => disj hT hGl hGc hab (lin_reach hG u' a ha') h
      right
      refine ⟨ha', ?_⟩
      rw [← dep_pr' hG u u' b hnb]
      exact hwv.2

def Seen {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Prop) (c : ℕ) (x : Fin n) : Prop :=
  ∀ z : Fin n → Bool, val C.gates z (n + c) = true → z x = true → F z

lemma notB {n : ℕ} {C : Circuit} {c : ℕ} (F : (Fin n → Bool) → Prop)
    (hstop : ∀ j < C.gates.length, ¬ (∀ z, val C.gates z (n + j) = true → F z) →
      ∀ w ∈ (gateAt C j).inputs, ¬ (∀ z, val C.gates z w = true → F z))
    (hnB : ¬ (∀ z, val C.gates z (n + c) = true → F z)) {w u : ℕ} (h : Reach n C w u) :
    u = n + c → ¬ (∀ z, val C.gates z w = true → F z) := by
  induction h with
  | refl w =>
    intro h
    subst h
    exact hnB
  | step v g w hg hin _ ih =>
    intro h
    exact hstop g hg (ih h) v hin

lemma swap {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) (F : (Fin n → Bool) → Prop)
    (hRU : ∀ y : Fin n, Reach n C y.val (n + c) → val C.gates (eof y) (n + c) = true ∨
      ∃ o : Fin n, val C.gates (eof y) (n + c) = false ∧ val C.gates (eof o) (n + c) = false ∧
        val C.gates (pr y o) (n + c) = true ∧ (Seen C F c y ∨ Seen C F c o))
    {G a b : ℕ} (hGl : G < C.gates.length) (hop : (gateAt C G).op = GateOp.and)
    (hGo : OrP n C c (n + G))
    (hin : (gateAt C G).inputs = [a, b] ∨ (gateAt C G).inputs = [b, a])
    (z : Fin n → Bool) (hz : val C.gates z (n + c) = true) (hFz : ¬ F z)
    (y : Fin n) (hy : z y = true) (hya : Reach n C y.val a) :
    ∃ x : Fin n, Seen C F c x ∧ val C.gates (eof x) b = true := by
  have hGc := orp_reach hGo
  have hain : a ∈ (gateAt C G).inputs := by
    rcases hin with h | h <;> simp [h]
  have hyG : Reach n C y.val (n + G) := reach_trans hya (reach_in hGl hain)
  have hyb : ¬ Reach n C y.val b := by
    intro hyb
    rcases hin with h | h
    · exact disj hT hGl hGc h hya hyb
    · exact disj hT hGl hGc h hyb hya
  have hbf : ¬ (val C.gates (eof y) b = true) := fun h => hyb (lin_reach hT.good y b h)
  rcases hRU y (reach_trans hyG hGc) with hl | ⟨o, h1, h2, h3, hs⟩
  · exact (orp_uniq hT (lin_orp hT y hl) G hGl hop hyG hGc (by have := y.isLt; omega)).elim
  · have hso : Seen C F c o := by
      rcases hs with hs | hs
      · exact absurd (hs z hz hy) hFz
      · exact hs
    obtain ⟨G', a', b', hG'l, hop', hG'o, hin', hd⟩ := split2 hT y o h1 h2 h3
    have hG'c := orp_reach hG'o
    have hyG' : Reach n C y.val (n + G') := by
      rcases hd with ⟨h, _⟩ | ⟨_, h⟩
      · exact reach_trans (lin_reach hT.good y a' h) (reach_in hG'l (by simp [hin']))
      · exact reach_trans (lin_reach hT.good y b' h) (reach_in hG'l (by simp [hin']))
    have hGG : G' = G := by
      by_contra hne
      rcases chain hT hyG (n + G') hyG' hGc hG'c with h | h
      · exact orp_uniq hT hGo G' hG'l hop' h hG'c (by omega)
      · exact orp_uniq hT hG'o G hGl hop h hGc (by omega)
    subst hGG
    refine ⟨o, hso, ?_⟩
    rcases hin with h | h
    · rw [hin'] at h
      obtain ⟨e1, e2⟩ : a' = a ∧ b' = b := by simpa using h
      subst e1 e2
      rcases hd with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h hbf
    · rw [hin'] at h
      obtain ⟨e1, e2⟩ : a' = b ∧ b' = a := by simpa using h
      subst e1 e2
      rcases hd with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hbf
      · exact h

lemma final {n : ℕ} {C : Circuit} {c : ℕ} (hT : Tree n C c) (F : (Fin n → Bool) → Prop)
    (side : Fin n → Bool) (hF : ∀ u v : Fin n, F (pr u v) → side u ≠ side v)
    (hstop : ∀ j < C.gates.length, ¬ (∀ z, val C.gates z (n + j) = true → F z) →
      ∀ w ∈ (gateAt C j).inputs, ¬ (∀ z, val C.gates z w = true → F z))
    (hnB : ¬ (∀ z, val C.gates z (n + c) = true → F z))
    (v0 : Fin n) (hv0 : val C.gates (eof v0) (n + c) = true)
    (hRU : ∀ y : Fin n, Reach n C y.val (n + c) → val C.gates (eof y) (n + c) = true ∨
      ∃ o : Fin n, val C.gates (eof y) (n + c) = false ∧ val C.gates (eof o) (n + c) = false ∧
        val C.gates (pr y o) (n + c) = true ∧ (Seen C F c y ∨ Seen C F c o))
    (y o : Fin n) (h1 : val C.gates (eof y) (n + c) = false)
    (h2 : val C.gates (eof o) (n + c) = false) (h3 : val C.gates (pr y o) (n + c) = true) :
    False := by
  have hG := hT.good
  have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨(hG.ao g hg).1, le_of_eq (hG.ao g hg).2⟩
  obtain ⟨G, a, b, hGl, hop, hGo, hin, _⟩ := split2 hT y o h1 h2 h3
  have hGc := orp_reach hGo
  have hnBG := notB F hstop hnB hGc rfl
  push_neg at hnBG
  obtain ⟨z, hzG, hFz⟩ := hnBG
  have ha : a < n + G := hG.rb G hGl a (by simp [hin])
  have hb : b < n + G := hG.rb G hGl b (by simp [hin])
  have hzG' := hzG
  rw [val_and z G hGl a b hin ha hb hop, Bool.and_eq_true] at hzG'
  have hz := orp_up hG z hGo hzG
  have ex : ∀ w, val C.gates z w = true → ∃ y : Fin n, z y = true ∧ Reach n C y.val w := by
    intro w hw
    by_contra hn
    push_neg at hn
    have e := dep hG z (fun _ => false) w (fun v hv => by
      by_contra hne
      exact hn v (by simpa using hne) hv)
    rw [e, zero C.gates hG.ao (fun _ => false) (fun _ => rfl) w] at hw
    exact absurd hw (by simp)
  obtain ⟨y1, hy1, hr1⟩ := ex a hzG'.1
  obtain ⟨y2, hy2, hr2⟩ := ex b hzG'.2
  obtain ⟨x1, hs1, hb1⟩ := swap hT F hRU hGl hop hGo (Or.inl hin) z hz hFz y1 hy1 hr1
  obtain ⟨x2, hs2, ha2⟩ := swap hT F hRU hGl hop hGo (Or.inr hin) z hz hFz y2 hy2 hr2
  have hGp : val C.gates (pr x2 x1) (n + G) = true := by
    rw [val_and _ G hGl a b hin ha hb hop, Bool.and_eq_true]
    constructor
    · exact mono C.gates hmono (eof x2) (pr x2 x1)
        (fun v hv => by simp only [eof, pr, decide_eq_true_eq] at hv ⊢; exact Or.inl hv) a ha2
    · exact mono C.gates hmono (eof x1) (pr x2 x1)
        (fun v hv => by simp only [eof, pr, decide_eq_true_eq] at hv ⊢; exact Or.inr hv) b hb1
  have hcp := orp_up hG _ hGo hGp
  have f12 := hF _ _ (hs1 _ hcp (by simp [pr]))
  have hc1 : val C.gates (pr v0 x1) (n + c) = true :=
    mono C.gates hmono (eof v0) (pr v0 x1)
      (fun v hv => by simp only [eof, pr, decide_eq_true_eq] at hv ⊢; exact Or.inl hv) _ hv0
  have hc2 : val C.gates (pr v0 x2) (n + c) = true :=
    mono C.gates hmono (eof v0) (pr v0 x2)
      (fun v hv => by simp only [eof, pr, decide_eq_true_eq] at hv ⊢; exact Or.inl hv) _ hv0
  have f01 := hF _ _ (hs1 _ hc1 (by simp [pr]))
  have f02 := hF _ _ (hs2 _ hc2 (by simp [pr]))
  revert f12 f01 f02
  cases side v0 <;> cases side x1 <;> cases side x2 <;> simp

theorem core {n : ℕ} {C : Circuit} {c : ℕ} (hG : Good n C) (hc : c < C.gates.length)
    (F : (Fin n → Bool) → Prop) (side : Fin n → Bool)
    (hF : ∀ u v : Fin n, F (pr u v) → side u ≠ side v)
    (hstop : ∀ j < C.gates.length, ¬ (∀ z, val C.gates z (n + j) = true → F z) →
      ∀ w ∈ (gateAt C j).inputs, ¬ (∀ z, val C.gates z w = true → F z))
    (hnB : ¬ (∀ z, val C.gates z (n + c) = true → F z))
    (v0 : Fin n) (hv0 : val C.gates (eof v0) (n + c) = true)
    (LIN LV : Finset (Fin n))
    (hLIN : ∀ v ∈ LIN, val C.gates (eof v) (n + c) = true)
    (hLV : ∀ y ∈ LV, ∃ o : Fin n, val C.gates (eof y) (n + c) = false ∧
      val C.gates (eof o) (n + c) = false ∧ val C.gates (pr y o) (n + c) = true ∧
      (Seen C F c y ∨ Seen C F c o))
    (hex : LV.Nonempty) :
    LIN.card + LV.card ≤
      ((Finset.range C.gates.length).filter fun k => InConeOrSelf n C k c).card := by
  by_contra hlt
  push_neg at hlt
  have hcK : c ∈ (Finset.range C.gates.length).filter (fun k => InConeOrSelf n C k c) :=
    (memK hG c hc c).2 (Reach.refl _)
  have hdis : Disjoint LIN LV := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨o, h3, _⟩ := hLV v h2
    rw [hLIN v h1] at h3
    exact absurd h3 (by simp)
  have hdisA : Disjoint ((LIN ∪ LV).image (fun v : Fin n => v.val))
      ((((Finset.range C.gates.length).filter
        (fun k => InConeOrSelf n C k c)).erase c).image (fun g => n + g)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨g, _, hg⟩ := Finset.mem_image.1 h2
    have := v.isLt
    omega
  have hAcard : ((LIN ∪ LV).image (fun v : Fin n => v.val) ∪
      (((Finset.range C.gates.length).filter
        (fun k => InConeOrSelf n C k c)).erase c).image (fun g => n + g)).card =
      LIN.card + LV.card + (((Finset.range C.gates.length).filter
        (fun k => InConeOrSelf n C k c)).card - 1) := by
    rw [Finset.card_union_of_disjoint hdisA,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_erase_of_mem hcK]
  have hAW : ((LIN ∪ LV).image (fun v : Fin n => v.val) ∪
      (((Finset.range C.gates.length).filter
        (fun k => InConeOrSelf n C k c)).erase c).image (fun g => n + g)) ⊆
      Finset.range (n + C.gates.length) := by
    intro w hw
    rw [Finset.mem_range]
    rcases Finset.mem_union.1 hw with hw | hw
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hw
      have := v.isLt
      omega
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hw
      have := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hg)).1
      omega
  have hA1 : ∀ w ∈ ((LIN ∪ LV).image (fun v : Fin n => v.val) ∪
      (((Finset.range C.gates.length).filter
        (fun k => InConeOrSelf n C k c)).erase c).image (fun g => n + g)),
      1 ≤ R n C c w := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
      apply reach_R hG hc _ (by have := v.isLt; omega)
      rcases Finset.mem_union.1 hv with hv | hv
      · exact lin_reach hG v _ (hLIN v hv)
      · obtain ⟨o, _, h2, h3, _⟩ := hLV v hv
        by_contra hn
        rw [dep_pr hG v o _ hn, h2] at h3
        exact absurd h3 (by simp)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hw
      have hgK := Finset.mem_of_mem_erase hg
      exact reach_R hG hc ((memK hG c hc g).1 hgK)
        (by have := Finset.ne_of_mem_erase hg; omega)
  have hsum := R_sum hG c
  have hKpos : 1 ≤ ((Finset.range C.gates.length).filter
      (fun k => InConeOrSelf n C k c)).card := Finset.card_pos.2 ⟨c, hcK⟩
  obtain ⟨hR1, hR0⟩ := tight _ _ (R n C c) hAW hA1 (by rw [hsum, hAcard]; omega)
  have hT : Tree n C c := mkTree hG hc hR1
  have hRU : ∀ y : Fin n, Reach n C y.val (n + c) → val C.gates (eof y) (n + c) = true ∨
      ∃ o : Fin n, val C.gates (eof y) (n + c) = false ∧ val C.gates (eof o) (n + c) = false ∧
        val C.gates (pr y o) (n + c) = true ∧ (Seen C F c y ∨ Seen C F c o) := by
    intro y hy
    have hy1 : 1 ≤ R n C c y.val := reach_R hG hc hy (by have := y.isLt; omega)
    have hyA : y ∈ LIN ∪ LV := by
      by_contra hn
      have h0 := hR0 y.val (by rw [Finset.mem_range]; have := y.isLt; omega) (by
        intro hmem
        rcases Finset.mem_union.1 hmem with hw | hw
        · obtain ⟨v, hv, hvy⟩ := Finset.mem_image.1 hw
          have : v = y := Fin.ext hvy
          subst this
          exact hn hv
        · obtain ⟨g, _, hg⟩ := Finset.mem_image.1 hw
          have := y.isLt
          omega)
      omega
    rcases Finset.mem_union.1 hyA with h | h
    · exact Or.inl (hLIN y h)
    · exact Or.inr (hLV y h)
  obtain ⟨y, hy⟩ := hex
  obtain ⟨o, h1, h2, h3, _⟩ := hLV y hy
  exact final hT F side hF hstop hnB v0 hv0 hRU y o h1 h2 h3

lemma set_same {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (c : ℕ)
    (h : val gs x (n + c) = false) :
    ∀ i, val (gs.set c ⟨GateOp.or, []⟩) x i = val gs x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_lt _ x i h1, val_lt _ x i h1]
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge _ x i (by simpa using h2), val_ge _ x i h2]
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        have hk' : k < (gs.set c ⟨GateOp.or, []⟩).length := by simpa using hk
        rw [val_gate _ x k hk']
        by_cases hkc : k = c
        · subst hkc
          rw [h]
          simp [GateOp.eval]
        · rw [val_gate gs x k hk]
          have e : (gs.set c ⟨GateOp.or, []⟩)[k]'hk' = gs[k] :=
            List.getElem_set_ne (Ne.symm hkc) _
          rw [e]
          congr 1
          apply List.map_congr_left
          intro j _
          by_cases hj : j < n + k
          · rw [if_pos hj, if_pos hj]
            exact ih j hj
          · rw [if_neg hj, if_neg hj]

lemma wrap {Np Nl : ℕ} (S1 : Finset (Fin (Np + Nl))) (S2 : Finset (Fin Np))
    (S3 : Finset (Fin Nl)) (K : ℕ)
    (h : S1.card + (S2.image (Fin.castAdd Nl) ∪ S3.image (Fin.natAdd Np)).card ≤ K) :
    S1.card + S2.card + S3.card ≤ K := by
  have hd : Disjoint (S2.image (Fin.castAdd Nl)) (S3.image (Fin.natAdd Np)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨l, _, hl⟩ := Finset.mem_image.1 h2
    have e := congrArg Fin.val hl
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at e
    have := p.isLt
    omega
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
    Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)] at h
  omega

def FF (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (z : Fin (Np + Nl) → Bool) : Prop :=
  ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true

lemma FF_side (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) (u v : Fin (Np + Nl))
    (h : FF Np Nl I (pr u v)) : decide (u.val < Np) ≠ decide (v.val < Np) := by
  obtain ⟨p, l, _, h1, h2⟩ := h
  simp only [pr, decide_eq_true_eq] at h1 h2
  have hp := p.isLt
  have e1 : (Fin.castAdd Nl p).val = p.val := rfl
  have e2 : (Fin.natAdd Np l).val = Np + l.val := rfl
  simp only [ne_eq, decide_eq_decide]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  all_goals
    rw [h1] at e1
    rw [h2] at e2
    omega

theorem main : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (∀ p47 : Fin Np, ∀ l48 : Fin Nl, (I p47 l48 ∧ (C.wires (List.ofFn (fun i51 : Fin (Np + Nl) => decide (i51 = Fin.castAdd Nl p47)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i52 : Fin (Np + Nl) => decide (i52 = Fin.natAdd Np l48)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i53 : Fin (Np + Nl) => decide (i53 = Fin.castAdd Nl p47 ∨ i53 = Fin.natAdd Np l48)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p47 ∨ i54 = Fin.natAdd Np l48)) = false) → ∃ j49 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ z55 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z55)).getD ((Np + Nl) + j49) false = true → ∃ p56 : Fin Np, ∃ l57 : Fin Nl, I p56 l57 ∧ z55 (Fin.castAdd Nl p56) = true ∧ z55 (Fin.natAdd Np l57) = true) ∧ ∃ w50 : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [(Np + Nl) + c, w50] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [w50, (Np + Nl) + c]) ∧ ((C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p47)))).getD (w50) false = true ∨ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l48)))).getD (w50) false = true)) → (Finset.univ.filter fun v60 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i66 : Fin (Np + Nl) => decide (i66 = v60)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p61 : Fin Np => ∃ l62 : Fin Nl, (I p61 l62 ∧ (C.wires (List.ofFn (fun i67 : Fin (Np + Nl) => decide (i67 = Fin.castAdd Nl p61)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i68 : Fin (Np + Nl) => decide (i68 = Fin.natAdd Np l62)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i69 : Fin (Np + Nl) => decide (i69 = Fin.castAdd Nl p61 ∨ i69 = Fin.natAdd Np l62)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i70 : Fin (Np + Nl) => decide (i70 = Fin.castAdd Nl p61 ∨ i70 = Fin.natAdd Np l62)) = false)).card + (Finset.univ.filter fun l64 : Fin Nl => ∃ p63 : Fin Np, (I p63 l64 ∧ (C.wires (List.ofFn (fun i71 : Fin (Np + Nl) => decide (i71 = Fin.castAdd Nl p63)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i72 : Fin (Np + Nl) => decide (i72 = Fin.natAdd Np l64)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i73 : Fin (Np + Nl) => decide (i73 = Fin.castAdd Nl p63 ∨ i73 = Fin.natAdd Np l64)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i74 : Fin (Np + Nl) => decide (i74 = Fin.castAdd Nl p63 ∨ i74 = Fin.natAdd Np l64)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k65 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k65 c).card := by
  intro Np Nl I _ C c _ hAO _ _ hstop _ _ hc hnB _ hlin hlost hpartner
  have hG : Good (Np + Nl) C := ⟨fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩, hAO.2.1⟩
  have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨(hG.ao g hg).1, le_of_eq (hG.ao g hg).2⟩
  obtain ⟨v0, hv0⟩ := hlin
  have key : ∀ (p : Fin Np) (l : Fin Nl),
      (I p l ∧ val C.gates (eof (Fin.castAdd Nl p)) ((Np + Nl) + c) = false ∧
        val C.gates (eof (Fin.natAdd Np l)) ((Np + Nl) + c) = false ∧
        val C.gates (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) C.output = true ∧
        val (C.gates.set c ⟨GateOp.or, []⟩) (pr (Fin.castAdd Nl p) (Fin.natAdd Np l))
          C.output = false) →
      val C.gates (eof (Fin.castAdd Nl p)) ((Np + Nl) + c) = false ∧
        val C.gates (eof (Fin.natAdd Np l)) ((Np + Nl) + c) = false ∧
        val C.gates (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) ((Np + Nl) + c) = true ∧
        (Seen C (FF Np Nl I) c (Fin.castAdd Nl p) ∨ Seen C (FF Np Nl I) c (Fin.natAdd Np l)) := by
    intro p l hL
    obtain ⟨hI, h1, h2, h3, h4⟩ := hL
    refine ⟨h1, h2, ?_, ?_⟩
    · by_contra hn
      have hn' : val C.gates (pr (Fin.castAdd Nl p) (Fin.natAdd Np l)) ((Np + Nl) + c) = false := by
        simpa using hn
      rw [set_same C.gates _ c hn' C.output, h3] at h4
      exact absurd h4 (by simp)
    · obtain ⟨j, hj, hop, hBj, w, hin, hw⟩ := hpartner p l ⟨hI, h1, h2, h3, h4⟩
      have seen : ∀ x : Fin (Np + Nl), val C.gates (eof x) w = true →
          Seen C (FF Np Nl I) c x := by
        intro x hx z hz hzx
        apply hBj z
        have hwz : val C.gates z w = true :=
          mono C.gates hmono (eof x) z (fun v hv => by
            simp only [eof, decide_eq_true_eq] at hv
            rw [hv]
            exact hzx) w hx
        show val C.gates z (Np + Nl + j) = true
        rcases hin with hin | hin
        · rw [val_and z j hj _ _ hin (hG.rb j hj _ (by simp [hin]))
            (hG.rb j hj _ (by simp [hin])) hop, hz, hwz]
          rfl
        · rw [val_and z j hj _ _ hin (hG.rb j hj _ (by simp [hin]))
            (hG.rb j hj _ (by simp [hin])) hop, hz, hwz]
          rfl
      rcases hw with hw | hw
      · exact Or.inl (seen _ hw)
      · exact Or.inr (seen _ hw)
  apply wrap
  refine core hG hc (FF Np Nl I) (fun u => decide (u.val < Np)) (FF_side Np Nl I)
    (fun j hj hnb w hw => hstop j hj (Or.inr hnb) w hw) hnB v0 hv0 _ _ ?_ ?_ ?_
  · intro v hv
    exact (Finset.mem_filter.1 hv).2
  · intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨l, hl⟩ := (Finset.mem_filter.1 hp).2
      obtain ⟨k1, k2, k3, k4⟩ := key p l hl
      exact ⟨Fin.natAdd Np l, k1, k2, k3, k4⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨p, hp⟩ := (Finset.mem_filter.1 hl).2
      obtain ⟨k1, k2, k3, k4⟩ := key p l hp
      refine ⟨Fin.castAdd Nl p, k2, k1, ?_, k4.symm⟩
      have e : pr (Fin.natAdd Np l) (Fin.castAdd Nl p) =
          pr (Fin.castAdd Nl p) (Fin.natAdd Np l) := by
        funext i
        simp [pr, or_comm]
      rw [e]
      exact k3
  · obtain ⟨p, l, hl⟩ := hlost
    exact ⟨Fin.castAdd Nl p, Finset.mem_union.2 (Or.inl (Finset.mem_image.2
      ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, l, hl⟩, rfl⟩))⟩

end PEqualNP.Outside.L_meta_3026_aux

theorem PEqualNP.Outside.L_meta_3026 : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (∀ p47 : Fin Np, ∀ l48 : Fin Nl, (I p47 l48 ∧ (C.wires (List.ofFn (fun i51 : Fin (Np + Nl) => decide (i51 = Fin.castAdd Nl p47)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i52 : Fin (Np + Nl) => decide (i52 = Fin.natAdd Np l48)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i53 : Fin (Np + Nl) => decide (i53 = Fin.castAdd Nl p47 ∨ i53 = Fin.natAdd Np l48)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p47 ∨ i54 = Fin.natAdd Np l48)) = false) → ∃ j49 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ z55 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z55)).getD ((Np + Nl) + j49) false = true → ∃ p56 : Fin Np, ∃ l57 : Fin Nl, I p56 l57 ∧ z55 (Fin.castAdd Nl p56) = true ∧ z55 (Fin.natAdd Np l57) = true) ∧ ∃ w50 : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [(Np + Nl) + c, w50] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [w50, (Np + Nl) + c]) ∧ ((C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p47)))).getD (w50) false = true ∨ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l48)))).getD (w50) false = true)) → (Finset.univ.filter fun v60 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i66 : Fin (Np + Nl) => decide (i66 = v60)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p61 : Fin Np => ∃ l62 : Fin Nl, (I p61 l62 ∧ (C.wires (List.ofFn (fun i67 : Fin (Np + Nl) => decide (i67 = Fin.castAdd Nl p61)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i68 : Fin (Np + Nl) => decide (i68 = Fin.natAdd Np l62)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i69 : Fin (Np + Nl) => decide (i69 = Fin.castAdd Nl p61 ∨ i69 = Fin.natAdd Np l62)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i70 : Fin (Np + Nl) => decide (i70 = Fin.castAdd Nl p61 ∨ i70 = Fin.natAdd Np l62)) = false)).card + (Finset.univ.filter fun l64 : Fin Nl => ∃ p63 : Fin Np, (I p63 l64 ∧ (C.wires (List.ofFn (fun i71 : Fin (Np + Nl) => decide (i71 = Fin.castAdd Nl p63)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i72 : Fin (Np + Nl) => decide (i72 = Fin.natAdd Np l64)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i73 : Fin (Np + Nl) => decide (i73 = Fin.castAdd Nl p63 ∨ i73 = Fin.natAdd Np l64)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i74 : Fin (Np + Nl) => decide (i74 = Fin.castAdd Nl p63 ∨ i74 = Fin.natAdd Np l64)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k65 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k65 c).card := by
  exact PEqualNP.Outside.L_meta_3026_aux.main
