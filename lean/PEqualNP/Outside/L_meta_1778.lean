import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1778

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

end PEqualNP.Outside.L_meta_1778

theorem PEqualNP.Outside.L_meta_1778 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7
  exact PEqualNP.Outside.L_meta_1778.main x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7
