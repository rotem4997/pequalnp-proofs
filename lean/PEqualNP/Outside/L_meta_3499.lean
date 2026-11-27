import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import PEqualNP.Defs

-- The OR bound and point-degree argument come from L-meta-1778 (#4053).
-- The AND-operand count follows steveDOTdigital's argument in PR #5875.

namespace PEqualNP.Outside.L_meta_3499_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma wv_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wv (gs ++ [g]) x = step (wv gs x) g := by
  simp [wv, List.foldl_append]

lemma wv_len (gs : List Gate) (x : List Bool) : (wv gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wv]
  | append_singleton gs g ih =>
    rw [wv_snoc]
    simp [step, ih]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false) else false := by
  unfold step
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    have h1 : ¬ i < w.length := by omega
    have h2 : i ≠ w.length := by omega
    rw [hk]
    simp [h1, h2]

lemma gate_cases (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

lemma image_merge {ι : Type} [DecidableEq ι] (X : Finset ι) (a b : ι) :
    X.card ≤ (X.image (fun x => if x = a then b else x)).card + 1 := by
  have h1 : X.erase a ⊆ X.image (fun x => if x = a then b else x) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact Finset.mem_image.mpr ⟨x, hx.2, by simp [hx.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := X) (a := a)
  omega

lemma gate_key {ι : Type} [DecidableEq ι] (S : Finset ι) (W0 : ℕ → Bool) (Wv : ι → ℕ → Bool)
    (c : ι → ι)
    (hc : ∀ i, W0 i = false → ∀ v ∈ S, ∀ v' ∈ S, Wv v i = true → Wv v' i = true → c v = c v')
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    ∃ c' : ι → ι,
      (S.image c).card ≤ (S.image c').card + (if g.op.eval [true, false] = true then 1 else 0) ∧
      (∀ v v', c v = c v' → c' v = c' v') ∧
      (g.op.eval (g.inputs.map W0) = false → ∀ v ∈ S, ∀ v' ∈ S,
        g.op.eval (g.inputs.map (Wv v)) = true → g.op.eval (g.inputs.map (Wv v')) = true →
        c' v = c' v') := by
  rcases gate_cases g.inputs hlen with hi | ⟨a, hi⟩ | ⟨a, b, hi⟩
  · refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, ?_⟩
    rw [hi]
    intro h0 v hv v' hv' h1 h2
    rcases hop with ho | ho <;> rw [ho] at h0 h1 <;> simp [GateOp.eval] at h0 h1
  · refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, ?_⟩
    rw [hi]
    intro h0 v hv v' hv' h1 h2
    rcases hop with ho | ho <;> rw [ho] at h0 h1 h2 <;> simp [GateOp.eval] at h0 h1 h2 <;>
      exact hc a h0 v hv v' hv' h1 h2
  · rcases hop with ho | ho
    · refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, ?_⟩
      rw [hi, ho]
      intro h0 v hv v' hv' h1 h2
      simp [GateOp.eval] at h0 h1 h2
      cases hA : W0 a with
      | false => exact hc a hA v hv v' hv' h1.1 h2.1
      | true => exact hc b (h0 hA) v hv v' hv' h1.2 h2.2
    · by_cases hex : ∃ va ∈ S, ∃ vb ∈ S, Wv va a = true ∧ Wv vb b = true
      · obtain ⟨va, hva, vb, hvb, hta, htb⟩ := hex
        refine ⟨fun v => if c v = c va then c vb else c v, ?_, ?_, ?_⟩
        · have e : S.image (fun v => if c v = c va then c vb else c v) =
              (S.image c).image (fun x => if x = c va then c vb else x) := by
            rw [Finset.image_image]
            rfl
          rw [e, ho]
          have := image_merge (S.image c) (c va) (c vb)
          simpa [GateOp.eval] using this
        · intro v v' h
          simp only [h]
        · rw [hi, ho]
          intro h0 v hv v' hv' h1 h2
          simp [GateOp.eval] at h0 h1 h2
          have key : ∀ w ∈ S, (Wv w a = true ∨ Wv w b = true) →
              (if c w = c va then c vb else c w) = c vb := by
            intro w hw h
            rcases h with h | h
            · have := hc a h0.1 w hw va hva h hta
              simp [this]
            · have := hc b h0.2 w hw vb hvb h htb
              simp [this]
          show (if c v = c va then c vb else c v) = (if c v' = c va then c vb else c v')
          rw [key v hv h1, key v' hv' h2]
      · refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, ?_⟩
        rw [hi, ho]
        intro h0 v hv v' hv' h1 h2
        simp [GateOp.eval] at h0 h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact hc a h0.1 v hv v' hv' h1 h2
        · exact absurd ⟨v, hv, v', hv', h1, h2⟩ hex
        · exact absurd ⟨v', hv', v, hv, h2, h1⟩ hex
        · exact hc b h0.2 v hv v' hv' h1 h2

lemma filter_snoc (gs : List Gate) (g : Gate) :
    ((gs ++ [g]).filter (fun g => g.op.eval [true, false])).length =
      (gs.filter (fun g => g.op.eval [true, false])).length +
        (if g.op.eval [true, false] = true then 1 else 0) := by
  rw [List.filter_append, List.length_append]
  by_cases h : g.op.eval [true, false] = true <;> simp [h]

lemma core {ι : Type} [DecidableEq ι] (S : Finset ι) (x0 : List Bool) (xs : ι → List Bool)
    (hlen : ∀ v, (xs v).length = x0.length)
    (hin : ∀ i, x0.getD i false = false → ∀ v ∈ S, ∀ v' ∈ S,
      (xs v).getD i false = true → (xs v').getD i false = true → v = v')
    (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∃ c : ι → ι,
      S.card ≤ (S.image c).card + (gs.filter (fun g => g.op.eval [true, false])).length ∧
      ∀ i, (wv gs x0).getD i false = false → ∀ v ∈ S, ∀ v' ∈ S,
        (wv gs (xs v)).getD i false = true → (wv gs (xs v')).getD i false = true →
        c v = c v' := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro i h0 v hv v' hv' h1 h2
    exact hin i h0 v hv v' hv' h1 h2
  | append_singleton gs g ih =>
    intro hm
    obtain ⟨c, hc1, hc2⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
    have hg := hm g (by simp)
    obtain ⟨c', k1, k2, k3⟩ := gate_key S (fun i => (wv gs x0).getD i false)
      (fun v i => (wv gs (xs v)).getD i false) c hc2 g hg.1 hg.2
    refine ⟨c', ?_, ?_⟩
    · rw [filter_snoc]
      omega
    · intro i h0 v hv v' hv' h1 h2
      rw [wv_snoc, step_getD, wv_len] at h0 h1 h2
      rw [hlen] at h1 h2
      by_cases hi : i < x0.length + gs.length
      · simp only [hi, ite_true] at h0 h1 h2
        exact k2 v v' (hc2 i h0 v hv v' hv' h1 h2)
      · by_cases hi2 : i = x0.length + gs.length
        · simp only [hi2, ite_true, ite_false, lt_irrefl] at h0 h1 h2
          exact k3 h0 v hv v' hv' h1 h2
        · simp [hi, hi2] at h1

lemma mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ i, (wv gs x).getD i false = true → (wv gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i h
    exact hxy i h
  | append_singleton gs g ih =>
    intro hm i h
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    have hg := hm g (by simp)
    rw [wv_snoc, step_getD, wv_len] at h ⊢
    rw [← hl]
    by_cases hi : i < x.length + gs.length
    · simp only [hi, ite_true] at h ⊢
      exact ih' i h
    · by_cases hi2 : i = x.length + gs.length
      · simp only [hi2, ite_true, ite_false, lt_irrefl] at h ⊢
        rcases hg.1 with ho | ho
        · rw [ho] at h ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h ⊢
          rintro b ⟨k, hk, rfl⟩
          exact ih' k (h _ ⟨k, hk, rfl⟩)
        · rw [ho] at h ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h ⊢
          obtain ⟨b, ⟨k, hk, rfl⟩, hb⟩ := h
          exact ⟨_, ⟨k, hk, rfl⟩, ih' k hb⟩
      · simp [hi, hi2] at h

lemma ofFn_getD (n : ℕ) (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

lemma cf_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = (wv C.gates (List.ofFn x)).getD C.output false :=
  rfl

lemma mono2 (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  fun g hg => ⟨(hM g hg).1, (hM g hg).2⟩

lemma cf_mono (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (h : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true := by
  rw [cf_eq] at h ⊢
  refine mono C.gates _ _ (by simp) ?_ (mono2 C hM) _ h
  intro i hi
  rw [ofFn_getD] at hi ⊢
  by_cases hin : i < n
  · simp only [hin, dite_true] at hi ⊢
    exact hxy _ hi
  · simp [hin] at hi

lemma count (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (b : Fin n → Bool) (S : Finset (Fin n))
    (h0 : PEqualNP.MetaComplexity.circuitFun n C b = false)
    (h1 : ∀ v ∈ S, PEqualNP.MetaComplexity.circuitFun n C (fun i => b i || decide (i = v)) = true) :
    S.card ≤ (C.gates.filter (fun g => g.op.eval [true, false])).length + 1 := by
  obtain ⟨c, hc1, hc2⟩ := core S (List.ofFn b)
    (fun v => List.ofFn (fun i => b i || decide (i = v))) (by simp) (by
      intro i hi v hv v' hv' ha hb'
      rw [ofFn_getD] at hi ha hb'
      by_cases hin : i < n
      · simp only [hin, dite_true] at hi ha hb'
        simp [hi] at ha hb'
        rw [← ha, ← hb']
      · simp [hin] at ha) C.gates (mono2 C hM)
  have hle : (S.image c).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha a' ha'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp ha'
    exact hc2 C.output h0 v hv v' hv' (h1 v hv) (h1 v' hv')
  omega

lemma lines_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (c : Fin N) :
    (Finset.univ.filter (fun l => I c l)).card = q + 1 := by
  have e : (Finset.univ.filter (fun l => I c l)).biUnion
      (fun l => (Finset.univ.filter (fun p => I p l)).erase c) = Finset.univ.erase c := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨l, _, hp, _⟩
      exact hp
    · intro hp
      obtain ⟨l, ⟨h1, h2⟩, _⟩ := hu p c hp
      exact ⟨l, h2, hp, h1⟩
  have hd : ∀ l ∈ Finset.univ.filter (fun l => I c l), ∀ l' ∈ Finset.univ.filter (fun l => I c l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun p => I p l)).erase c)
        ((Finset.univ.filter (fun p => I p l')).erase c) := by
    intro l hl1 l' hl1' hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hl1 hl1' hp hp'
    obtain ⟨l0, _, hun⟩ := hu p c hp.1
    exact hne ((hun l ⟨hp.2, hl1⟩).trans (hun l' ⟨hp'.2, hl1'⟩).symm)
  have hc := Finset.card_biUnion hd
  rw [e] at hc
  have hs : ∀ l ∈ Finset.univ.filter (fun l => I c l),
      ((Finset.univ.filter (fun p => I p l)).erase c).card = q := by
    intro l hl1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1
    rw [Finset.card_erase_of_mem (by simp [hl1]), hl l]
    rfl
  rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, Fintype.card_fin] at hc
  have h3 : (Finset.univ.filter (fun l => I c l)).card * q = (q + 1) * q := by
    rw [← hc, hN]
    have : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
      rw [Nat.add_sub_cancel]
      ring
    exact this
  exact Nat.eq_of_mul_eq_mul_right (by omega) h3

lemma main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl' : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hacc : ∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (hsound : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ (p : Fin N) (l : Fin N), I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x = false) :
    2 * q ^ 2 + 1 ≤ (C.gates.filter (fun g => g.op.eval [true, false])).length := by
  have hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    rw [← hl' l, Fintype.card_subtype]
  have hr := lines_card q N I hq hN hl hu
  have hNpos : 0 < N := by omega
  obtain ⟨c, hcm⟩ : ∃ c, c ∈ Finset.univ.filter (fun p => I p (⟨0, hNpos⟩ : Fin N)) := by
    apply Finset.card_pos.mp
    rw [hl]
    omega
  generalize (⟨0, hNpos⟩ : Fin N) = m at hcm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm
  have hP : ((Finset.univ.filter (fun p => I p m)).erase c).card = q := by
    rw [Finset.card_erase_of_mem (by simp [hcm]), hl m]
    rfl
  have hL0 : ((Finset.univ.filter (fun l => I c l)).erase m).card = q := by
    rw [Finset.card_erase_of_mem (by simp [hcm]), hr c]
    rfl
  have two : ∀ p : Fin N, p ≠ c → I p m → ∀ l : Fin N, I p l → I c l → l = m := by
    intro p hp hpm l h1 h2
    obtain ⟨l0, _, hun⟩ := hu p c hp
    exact (hun l ⟨h1, h2⟩).trans (hun m ⟨hpm, hcm⟩).symm
  have two' : ∀ p p' : Fin N, p ≠ p' → I p m → I p' m → ∀ l : Fin N, I p l → I p' l → l = m := by
    intro p p' hp hpm hpm' l h1 h2
    obtain ⟨l0, _, hun⟩ := hu p p' hp
    exact (hun l ⟨h1, h2⟩).trans (hun m ⟨hpm, hpm'⟩).symm
  -- the baseline and the two halves of the test set
  have hLS : (insert m (((Finset.univ.filter (fun p => I p m)).erase c).biUnion
      (fun p => (Finset.univ.filter (fun l => I p l)).erase m))).card = q ^ 2 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_biUnion]
    · have hs : ∀ p ∈ (Finset.univ.filter (fun p => I p m)).erase c,
          ((Finset.univ.filter (fun l => I p l)).erase m).card = q := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hp
        rw [Finset.card_erase_of_mem (by simp [hp.2]), hr p]
        rfl
      rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul, hP]
      ring
    · intro p hp p' hp' hne
      change Disjoint _ _
      rw [Finset.mem_coe] at hp hp'
      rw [Finset.disjoint_left]
      intro l h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hp hp' h1 h2
      exact h1.1 (two' p p' hne hp.2 hp'.2 l h1.2 h2.2)
  have hPc : (((Finset.univ.filter (fun p => I p m)).erase c)ᶜ).card = q ^ 2 + 1 := by
    rw [Finset.card_compl, hP, Fintype.card_fin, hN]
    omega
  have hcount := count (N + N) C hM
    (Fin.addCases (fun p => decide (p ∈ (Finset.univ.filter (fun p => I p m)).erase c))
      (fun l => decide (l ∈ (Finset.univ.filter (fun l => I c l)).erase m)))
    ((((Finset.univ.filter (fun p => I p m)).erase c)ᶜ).image (Fin.castAdd N) ∪
      (insert m (((Finset.univ.filter (fun p => I p m)).erase c).biUnion
        (fun p => (Finset.univ.filter (fun l => I p l)).erase m))).image (Fin.natAdd N))
    (by
      apply hsound
      · rw [Fintype.card_subtype]
        simp only [Fin.addCases_right, decide_eq_true_eq]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hL0]
      · rintro ⟨p, l, hI, hp, hl0⟩
        simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq, Finset.mem_erase,
          Finset.mem_filter, Finset.mem_univ, true_and] at hp hl0
        exact hl0.1 (two p hp.1 hp.2 l hI hl0.2))
    (by
      intro v hv
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hv
      have hfin : ∀ p l : Fin N, I p l →
          (∀ i : Fin (N + N), (i = Fin.castAdd N p ∨ i = Fin.natAdd N l) →
            (Fin.addCases (fun p => decide (p ∈ (Finset.univ.filter (fun p => I p m)).erase c))
              (fun l => decide (l ∈ (Finset.univ.filter (fun l => I c l)).erase m)) i
              || decide (i = v)) = true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) C (fun i =>
            Fin.addCases (fun p => decide (p ∈ (Finset.univ.filter (fun p => I p m)).erase c))
              (fun l => decide (l ∈ (Finset.univ.filter (fun l => I c l)).erase m)) i
              || decide (i = v)) = true := by
        intro p l hI hle
        refine cf_mono (N + N) C hM _ _ ?_ (hacc p l hI)
        intro i hi
        exact hle i (by simpa using hi)
      rcases hv with ⟨p, hp, rfl⟩ | ⟨l, hl0, rfl⟩
      · simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
          true_and, not_and] at hp
        have hex : ∃ l, l ≠ m ∧ I c l ∧ I p l := by
          by_cases hpc : p = c
          · obtain ⟨l, hl1⟩ : ∃ l, l ∈ (Finset.univ.filter (fun l => I c l)).erase m := by
              apply Finset.card_pos.mp
              omega
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hl1
            exact ⟨l, hl1.1, hl1.2, hpc ▸ hl1.2⟩
          · obtain ⟨l, ⟨h1, h2⟩, _⟩ := hu p c hpc
            refine ⟨l, ?_, h2, h1⟩
            rintro rfl
            exact hp hpc h1
        obtain ⟨l, hlm, hcl, hpl⟩ := hex
        apply hfin p l hpl
        rintro i (rfl | rfl)
        · simp
        · rw [Fin.addCases_right]
          simp [hlm, hcl]
      · simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_filter,
          Finset.mem_univ, true_and] at hl0
        have hex : ∃ p, p ≠ c ∧ I p m ∧ I p l := by
          rcases hl0 with rfl | ⟨p, hp, _, hpl⟩
          · obtain ⟨p, hp1⟩ : ∃ p, p ∈ (Finset.univ.filter (fun p => I p l)).erase c := by
              apply Finset.card_pos.mp
              omega
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hp1
            exact ⟨p, hp1.1, hp1.2, hp1.2⟩
          · exact ⟨p, hp.1, hp.2, hpl⟩
        obtain ⟨p, hpc, hpm, hpl⟩ := hex
        apply hfin p l hpl
        rintro i (rfl | rfl)
        · simp [hpc, hpm]
        · simp)
  have hS : ((((Finset.univ.filter (fun p => I p m)).erase c)ᶜ).image (Fin.castAdd N) ∪
      (insert m (((Finset.univ.filter (fun p => I p m)).erase c).biUnion
        (fun p => (Finset.univ.filter (fun l => I p l)).erase m))).image (Fin.natAdd N)).card =
      (q ^ 2 + 1) + (q ^ 2 + 1) := by
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (Fin.castAdd_injective N N),
      Finset.card_image_of_injective _ (Fin.natAdd_injective N N), hPc, hLS]
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨l, _, hlv⟩ := Finset.mem_image.mp h2
    have := congrArg Fin.val hlv
    simp at this
    omega
  rw [hS] at hcount
  omega



open PEqualNP.MetaComplexity

private def readsEarlier (n : ℕ) (C : Circuit) : Prop :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
    ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j

private def wire (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wv C.gates (List.ofFn x)).getD i false

private theorem keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wv gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wv_snoc, step_getD, if_pos (by rw [wv_len]; omega)]
    exact ih

private theorem prefixWire (gs : List Gate) (w : List Bool) (k i : ℕ)
    (hk : k ≤ gs.length) (hi : i < w.length + k) :
    (wv gs w).getD i false = (wv (gs.take k) w).getD i false := by
  have split : wv gs w = wv (gs.drop k) (wv (gs.take k) w) := by
    unfold wv
    rw [← List.foldl_append, List.take_append_drop]
  rw [split]
  exact keepWire _ _ _ (by simpa [wv_len, List.length_take, Nat.min_eq_left hk] using hi)

private theorem inputWire (C : Circuit) {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    wire C x i.val = x i := by
  rw [wire, keepWire _ _ _ (by simpa using i.isLt), ofFn_getD, dif_pos i.isLt]

private theorem gateWire (C : Circuit) {n j a b : ℕ} (hj : j < C.gates.length)
    (pins : C.gates[j].inputs = [a, b]) (ha : a < n+j) (hb : b < n+j)
    (x : Fin n → Bool) :
    wire C x (n+j) = C.gates[j].op.eval [wire C x a, wire C x b] := by
  let xs := List.ofFn x
  have len : xs.length = n := List.length_ofFn
  change (wv C.gates xs).getD (n+j) false = _
  rw [prefixWire C.gates xs (j+1) _ (by omega) (by omega),
    List.take_succ_eq_append_getElem hj, wv_snoc, step_getD]
  have plen : (wv (C.gates.take j) xs).length = n+j := by
    rw [wv_len, len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  simp only [plen, lt_irrefl, if_false, if_true, pins, List.map_cons, List.map_nil]
  rw [← prefixWire C.gates xs j a (Nat.le_of_lt hj) (by omega),
    ← prefixWire C.gates xs j b (Nat.le_of_lt hj) (by omega)]
  rfl

private def oneBit {n : ℕ} (p : Fin n) (i : Fin n) : Bool := decide (i = p)

private def addBit {n : ℕ} (x : Fin n → Bool) (p : Fin n) (i : Fin n) : Bool :=
  x i || oneBit p i

private def goesUp {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) (w : ℕ) : Prop :=
  wire C x w = false ∧ wire C (addBit x p) w = true

private def changingAnd {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) (j : ℕ) : Prop :=
  C.gates[j]?.map Gate.op = some .and ∧ goesUp C x p (n+j)

-- Before an AND changes, an input flip can reach a changed wire through ORs alone.
private theorem propagatedFromSingleton {n limit : ℕ} (C : Circuit) (legal : Monotone2 C)
    (readable : readsEarlier n C) (x : Fin n → Bool) (p : Fin n)
    (size : limit ≤ C.gates.length) (unchanged : ∀ j < limit, ¬ changingAnd C x p j)
    (w : ℕ) (hw : w < n+limit) (changeUp : goesUp C x p w) : wire C (oneBit p) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · let i : Fin n := ⟨w, raw⟩
      change goesUp C x p i.val at changeUp
      change wire C (oneBit p) i.val = true
      obtain ⟨no, yes⟩ := changeUp
      rw [inputWire] at no yes ⊢
      simpa [addBit, no] using yes
    · let j := w - n
      have same : n+j = w := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      have hg : C.gates[j]? = some C.gates[j] := by simp [List.getElem?_eq_getElem, hj]
      obtain ⟨a, b, pins, order, bound⟩ := readable j C.gates[j] hg
      rcases (mono2 C legal C.gates[j] (List.getElem_mem hj)).1 with andOp | orOp
      · exact (unchanged j (by omega) ⟨by simp [hg, andOp], by simpa [same] using changeUp⟩).elim
      · obtain ⟨no, yes⟩ := changeUp
        rw [← same, gateWire C hj pins (by omega) bound, orOp] at no yes ⊢
        have neither : wire C x a = false ∧ wire C x b = false := by simpa [GateOp.eval] using no
        have either : wire C (addBit x p) a = true ∨ wire C (addBit x p) b = true := by
          simpa [GateOp.eval] using yes
        rcases either with ha | hb
        · simp [GateOp.eval, ih a (by omega) (by omega) ⟨neither.1, ha⟩]
        · simp [GateOp.eval, ih b (by omega) (by omega) ⟨neither.2, hb⟩]

private theorem wireMono {n : ℕ} (C : Circuit) (legal : Monotone2 C)
    (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) (w : ℕ)
    (hx : wire C x w = true) : wire C y w = true := by
  refine mono C.gates _ _ (by simp) ?_ (mono2 C legal) w hx
  intro i hi
  rw [ofFn_getD] at hi ⊢
  by_cases h : i < n
  · simp only [h, dite_true] at hi ⊢
    exact le _ hi
  · simp [h] at hi

private def isOr (g : Gate) : Bool := g.op.eval [true, false]

private noncomputable def andSlots (C : Circuit) : Finset (Gate × Bool) := by
  classical
  exact ((C.gates.filter fun g => !isOr g).toFinset).product Finset.univ

private theorem slotCount (C : Circuit) :
    (andSlots C).card ≤ 2 * (C.gates.filter fun g => !isOr g).length := by
  classical
  simp only [andSlots, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  have bound := List.toFinset_card_le (C.gates.filter fun g => !isOr g)
  omega

private noncomputable def slotPoints {N : ℕ} (C : Circuit) (s : Gate × Bool) : Finset (Fin N) :=
  Finset.univ.filter fun p => wire C (oneBit (Fin.castAdd N p)) (s.1.inputs.getD s.2.toNat 0) = true

private def lineRow {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    Fin (N+N) → Bool := Fin.addCases (fun p => decide (¬ I p l)) (fun m => decide (m = l))

private theorem shoresSeparate {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have eq := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at eq
  omega

private theorem lineRowSound {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (l : Fin N)
    (sound : ∀ x : Fin (N+N) → Bool, Fintype.card {m : Fin N // x (Fin.natAdd N m) = true} ≤ q →
      (¬ ∃ p m : Fin N, I p m ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N m) = true) →
      circuitFun (N+N) C x = false) : circuitFun (N+N) C (lineRow I l) = false := by
  apply sound
  · have card : Fintype.card {m : Fin N // lineRow I l (Fin.natAdd N m) = true} = 1 := by
      rw [Fintype.card_subtype]
      have rows : (Finset.univ.filter fun m : Fin N => lineRow I l (Fin.natAdd N m) = true) = {l} := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          lineRow, Fin.addCases_right, decide_eq_true_eq]
      rw [rows, Finset.card_singleton]
    omega
  · rintro ⟨p, m, inc, hp, hm⟩
    have ms : m = l := by simpa only [lineRow, Fin.addCases_right, decide_eq_true_eq] using hm
    subst m
    simp only [lineRow, Fin.addCases_left, decide_eq_true_eq] at hp
    exact hp inc

private theorem onePointSound {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (p : Fin N)
    (sound : ∀ x : Fin (N+N) → Bool, Fintype.card {m : Fin N // x (Fin.natAdd N m) = true} ≤ q →
      (¬ ∃ v m : Fin N, I v m ∧ x (Fin.castAdd N v) = true ∧ x (Fin.natAdd N m) = true) →
      circuitFun (N+N) C x = false) : circuitFun (N+N) C (oneBit (Fin.castAdd N p)) = false := by
  have noLine (m : Fin N) : oneBit (Fin.castAdd N p) (Fin.natAdd N m) = false := by
    rw [oneBit, decide_eq_false_iff_not]
    exact Ne.symm (shoresSeparate p m)
  apply sound
  · rw [Fintype.card_subtype]
    simp only [noLine, Bool.false_eq_true, Finset.filter_false, Finset.card_empty, Nat.zero_le]
  · rintro ⟨v, m, _, _, hm⟩
    rw [noLine] at hm
    contradiction

-- Each incidence is witnessed by one operand of the first AND whose output rises.
private theorem witnessSlot {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (legal : Monotone2 C) (output : C.output < N+N+C.size)
    (readable : readsEarlier (N+N) C)
    (accept : ∀ p l : Fin N, I p l → circuitFun (N+N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (sound : ∀ x : Fin (N+N) → Bool, Fintype.card {m : Fin N // x (Fin.natAdd N m) = true} ≤ q →
      (¬ ∃ v m : Fin N, I v m ∧ x (Fin.castAdd N v) = true ∧ x (Fin.natAdd N m) = true) →
      circuitFun (N+N) C x = false)
    (p l : Fin N) (incident : I p l) :
    ∃ s ∈ andSlots C, p ∈ slotPoints C s ∧ ∀ v ∈ slotPoints C s, I v l := by
  classical
  let x := lineRow I l
  let k := Fin.castAdd N p
  have no : wire C x C.output = false := lineRowSound I C hq l sound
  have solo : wire C (oneBit k) C.output = false := onePointSound I C p sound
  have yes : wire C (addBit x k) C.output = true := by
    apply wireMono C legal (fun i => decide (i = k ∨ i = Fin.natAdd N l))
    · intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · simp [addBit, oneBit]
      · simp only [addBit, x, lineRow, Fin.addCases_right, decide_true, Bool.true_or]
    · exact accept p l incident
  have existsAnd : ∃ j, j < C.gates.length ∧ changingAnd C x k j := by
    by_contra! none
    have reaches := propagatedFromSingleton C legal readable x k (limit := C.gates.length)
      le_rfl none C.output output ⟨no, yes⟩
    rw [solo] at reaches
    contradiction
  let j := Nat.find existsAnd
  have hj : j < C.gates.length := (Nat.find_spec existsAnd).1
  obtain ⟨hop, before, after⟩ := (Nat.find_spec existsAnd).2
  let g := C.gates[j]
  have hget : C.gates[j]? = some g := by simp [g, List.getElem?_eq_getElem, hj]
  change C.gates[j]?.map Gate.op = some .and at hop
  have isAnd : g.op = .and := by
    simpa only [hget, Option.map_some, Option.some.injEq] using hop
  obtain ⟨a, b, pins, order, bound⟩ := readable j g hget
  have previously (i : ℕ) (hi : i < j) : ¬ changingAnd C x k i := by
    intro up
    exact (Nat.not_lt_of_ge (Nat.find_min' existsAnd ⟨by omega, up⟩)) hi
  rw [gateWire C hj pins (by omega) bound, isAnd] at before after
  have still : wire C x a = false ∨ wire C x b = false := by
    cases ea : wire C x a with
    | false => exact Or.inl rfl
    | true => exact Or.inr (by simpa [GateOp.eval, ea] using before)
  have both : wire C (addBit x k) a = true ∧ wire C (addBit x k) b = true := by
    simpa [GateOp.eval] using after
  have build (s : Bool) (early : g.inputs.getD s.toNat 0 < N+N+j)
      (base : wire C x (g.inputs.getD s.toNat 0) = false)
      (raised : wire C (addBit x k) (g.inputs.getD s.toNat 0) = true) :
      ∃ t ∈ andSlots C, p ∈ slotPoints C t ∧ ∀ v ∈ slotPoints C t, I v l := by
    have reaches := propagatedFromSingleton C legal readable x k (Nat.le_of_lt hj) previously
      (g.inputs.getD s.toNat 0) early ⟨base, raised⟩
    refine ⟨(g, s), ?_, by simpa [slotPoints, k] using reaches, ?_⟩
    · simp [andSlots, isOr, isAnd, GateOp.eval, g, List.getElem_mem hj]
    · intro v hv
      have one : wire C (oneBit (Fin.castAdd N v)) (g.inputs.getD s.toNat 0) = true := by
        simpa [slotPoints] using hv
      by_contra notIncident
      have raised := wireMono C legal (oneBit (Fin.castAdd N v)) x (by
        intro i hi
        have ie : i = Fin.castAdd N v := by simpa [oneBit] using hi
        subst i
        simp [x, lineRow, notIncident]) _ one
      rw [base] at raised
      contradiction
  rcases still with ha | hb
  · exact build false (by simpa [pins] using (show a < N+N+j from by omega))
      (by simpa [pins] using ha) (by simpa [pins] using both.1)
  · exact build true (by simpa [pins] using bound)
      (by simpa [pins] using hb) (by simpa [pins] using both.2)

private noncomputable def coveredFlags {N : ℕ} (I : Fin N → Fin N → Prop)
    (S : Finset (Fin N)) : Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter fun e => e.1 ∈ S ∧ ∀ p ∈ S, I p e.2

private theorem coveredCount {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (lineDegree : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q+1)
    (pointDegree : ∀ p : Fin N, (Finset.univ.filter fun l => I p l).card = q+1)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (S : Finset (Fin N)) : (coveredFlags I S).card ≤ q+1 := by
  classical
  rcases S.eq_empty_or_nonempty with empty | ⟨p, hp⟩
  · simp [coveredFlags, empty]
  by_cases single : S ⊆ {p}
  · have contained : coveredFlags I S ⊆ ({p} : Finset (Fin N)).product
        (Finset.univ.filter fun l => I p l) := by
      intro e he
      have eh : e.1 ∈ S ∧ ∀ a ∈ S, I a e.2 := by simpa [coveredFlags] using he
      exact Finset.mem_product.mpr ⟨single eh.1, by simp [eh.2 p hp]⟩
    have card := Finset.card_le_card contained
    simpa [Finset.card_product, pointDegree p] using card
  · have multiple : ∃ r ∈ S, r ≠ p := by
      by_contra! onlyP
      exact single (fun r hr => Finset.mem_singleton.mpr (onlyP r hr))
    obtain ⟨r, hr, different⟩ := multiple
    obtain ⟨l, _, unique⟩ := join p r different.symm
    have contained : coveredFlags I S ⊆ (Finset.univ.filter fun a => I a l).product
        ({l} : Finset (Fin N)) := by
      intro e he
      have eh : e.1 ∈ S ∧ ∀ a ∈ S, I a e.2 := by simpa [coveredFlags] using he
      have line : e.2 = l := unique e.2 ⟨eh.2 p hp, eh.2 r hr⟩
      exact Finset.mem_product.mpr ⟨by simpa [← line] using eh.2 e.1 eh.1, by simp [line]⟩
    have card := Finset.card_le_card contained
    simpa [Finset.card_product, lineDegree l] using card

private theorem incidenceCard {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) :
    (Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2).card = N*(q+1) := by
  let swap : {e : Fin N × Fin N // I e.1 e.2} ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
    { toFun := fun e => ⟨e.1.2, e.1.1, e.2⟩
      invFun := fun z => ⟨⟨z.2.1, z.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have card := Fintype.card_congr swap
  rw [Fintype.card_sigma] at card
  simpa [degree, Fintype.card_subtype] using card

private theorem countAnds {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q^2 + q + 1)
    (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (legal : Monotone2 C) (output : C.output < N+N+C.size) (readable : readsEarlier (N+N) C)
    (accept : ∀ p l : Fin N, I p l → circuitFun (N+N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (sound : ∀ x : Fin (N+N) → Bool, Fintype.card {m : Fin N // x (Fin.natAdd N m) = true} ≤ q →
      (¬ ∃ p m : Fin N, I p m ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N m) = true) →
      circuitFun (N+N) C x = false) : N ≤ 2 * (C.gates.filter fun g => !isOr g).length := by
  classical
  let flags := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2
  let covered := fun s => coveredFlags I (slotPoints C s)
  have lineDegree (l : Fin N) : (Finset.univ.filter fun p => I p l).card = q+1 :=
    (Fintype.card_subtype (fun p : Fin N => I p l)).symm.trans (degree l)
  have pointDegree := lines_card q N I hq hN lineDegree join
  have cover : flags ⊆ (andSlots C).biUnion covered := by
    intro e he
    have ie : I e.1 e.2 := (Finset.mem_filter.mp he).2
    obtain ⟨s, hs, heS, hwithin⟩ := witnessSlot I C hq legal output readable accept sound e.1 e.2 ie
    exact Finset.mem_biUnion.mpr ⟨s, hs, by simpa [covered, coveredFlags] using And.intro heS hwithin⟩
  have count : N*(q+1) ≤ (andSlots C).card*(q+1) := calc
    N*(q+1) = flags.card := (incidenceCard I degree).symm
    _ ≤ ((andSlots C).biUnion covered).card := Finset.card_le_card cover
    _ ≤ ∑ s ∈ andSlots C, (covered s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ andSlots C, (q+1) := Finset.sum_le_sum fun s _ =>
      coveredCount I lineDegree pointDegree join (slotPoints C s)
    _ = (andSlots C).card*(q+1) := by simp
  exact (Nat.le_of_mul_le_mul_right count (by omega)).trans (slotCount C)

theorem sizeBound {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q^2 + q + 1)
    (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (legal : Monotone2 C) (output : C.output < N+N+C.size) (readable : readsEarlier (N+N) C)
    (accept : ∀ p l : Fin N, I p l → circuitFun (N+N) C
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (sound : ∀ x : Fin (N+N) → Bool, Fintype.card {m : Fin N // x (Fin.natAdd N m) = true} ≤ q →
      (¬ ∃ p m : Fin N, I p m ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N m) = true) →
      circuitFun (N+N) C x = false) : 4*q^2 + 2 + N ≤ 2*C.size := by
  have ors : 2*q^2+1 ≤ (C.gates.filter isOr).length := main q N I C hq hN degree join legal accept sound
  have ands := countAnds I C hq hN degree join legal output readable accept sound
  have partition (gs : List Gate) : (gs.filter isOr).length +
      (gs.filter fun g => !isOr g).length = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih => cases b : isOr g <;> simp [b] <;> omega
  have tally := partition C.gates
  change 4*q^2 + 2 + N ≤ 2*C.gates.length
  omega

end PEqualNP.Outside.L_meta_3499_aux

theorem PEqualNP.Outside.L_meta_3499 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → (4 : ℕ) * x1 ^ (2 : ℕ) + (2 : ℕ) + x2 ≤ (2 : ℕ) * x5.size := by
  intro q N I _ C hq hN degree join legal output readable accept sound
  exact PEqualNP.Outside.L_meta_3499_aux.sizeBound I C hq hN degree join legal output readable accept sound
