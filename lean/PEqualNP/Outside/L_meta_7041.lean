import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7041
open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_true_lt (l : List Bool) (i : ℕ) (h : l.getD i false = true) : i < l.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by omega)] at h
  exact Bool.false_ne_true h

theorem W_input (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_length]; omega), ih]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem gate_sep (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f h : ℕ → Bool)
    (h1 : g.op.eval (g.inputs.map f) = true) (h2 : g.op.eval (g.inputs.map h) = false) :
    ∃ u ∈ g.inputs, f u = true ∧ h u = false := by
  rcases hg with hg | hg
  · rw [hg] at h1 h2
    simp [GateOp.eval] at h1 h2
    obtain ⟨u, hu, hu2⟩ := h2
    exact ⟨u, hu, h1 u hu, hu2⟩
  · rw [hg] at h1 h2
    simp [GateOp.eval] at h1 h2
    obtain ⟨u, hu, hu1⟩ := h1
    exact ⟨u, hu, hu1, h2 u hu⟩

theorem trace (gs : List Gate) (hm : Mono gs) (xs ys : List Bool) (hl : xs.length = ys.length) :
    ∀ i, (W gs xs).getD i false = true → (W gs ys).getD i false = false → xs.length ≤ i →
      ∃ k, ∃ hk : k < gs.length, i = xs.length + k ∧ ∃ u ∈ (gs[k]).inputs, u < i ∧
        (W gs xs).getD u false = true ∧ (W gs ys).getD u false = false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i h1 h2 hi
    have := getD_true_lt _ _ h1
    simp [W] at this
    omega
  | append_singleton gs g ih =>
    intro i h1 h2 hi
    have hm' : Mono gs := fun g' hg' => hm g' (List.mem_append_left _ hg')
    have hLx : (W gs xs).length = xs.length + gs.length := W_length _ _
    have hLy : (W gs ys).length = xs.length + gs.length := by rw [W_length, hl]
    simp only [W_snoc] at h1 h2 ⊢
    rcases Nat.lt_trichotomy i (xs.length + gs.length) with hlt | heq | hgt
    · rw [List.getD_append _ _ _ _ (by omega)] at h1 h2
      obtain ⟨k, hk, he, u, hu, hui, a, b⟩ := ih hm' i h1 h2 hi
      refine ⟨k, by simp; omega, he, u, ?_, hui, ?_, ?_⟩
      · rw [List.getElem_append_left hk]; exact hu
      · rw [List.getD_append _ _ _ _ (by omega)]; exact a
      · rw [List.getD_append _ _ _ _ (by omega)]; exact b
    · rw [List.getD_append_right _ _ _ _ (by omega)] at h1 h2
      have e1 : i - (W gs xs).length = 0 := by omega
      have e2 : i - (W gs ys).length = 0 := by omega
      rw [e1] at h1
      rw [e2] at h2
      simp only [List.getD_cons_zero] at h1 h2
      obtain ⟨u, hu, a, b⟩ := gate_sep g (hm g (by simp)).1 _ _ h1 h2
      have hul := getD_true_lt _ _ a
      refine ⟨gs.length, by simp, heq, u, ?_, by omega, ?_, ?_⟩
      · simpa using hu
      · rw [List.getD_append _ _ _ _ (by omega)]; exact a
      · rw [List.getD_append _ _ _ _ (by omega)]; exact b
    · have := getD_true_lt _ _ h1
      simp at this
      omega

def val (gs : List Gate) {N : ℕ} (x : Fin N → Bool) (i : ℕ) : Bool :=
  (W gs (List.ofFn x)).getD i false

theorem val_input (gs : List Gate) {N : ℕ} (x : Fin N → Bool) (i : ℕ) (h : i < N) :
    val gs x i = x ⟨i, h⟩ := by
  unfold val
  rw [W_input _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem trace' (gs : List Gate) (hm : Mono gs) {N : ℕ} (x y : Fin N → Bool) (i : ℕ)
    (h1 : val gs x i = true) (h2 : val gs y i = false) (hi : N ≤ i) :
    ∃ k, ∃ hk : k < gs.length, i = N + k ∧ ∃ u ∈ (gs[k]).inputs, u < i ∧
      val gs x u = true ∧ val gs y u = false := by
  obtain ⟨k, hk, he, u, hu, hui, a, b⟩ :=
    trace gs hm (List.ofFn x) (List.ofFn y) (by simp) i h1 h2 (by simpa using hi)
  exact ⟨k, hk, by simpa using he, u, hu, hui, a, b⟩

theorem inputSep (gs : List Gate) (hm : Mono gs) {N : ℕ} (x y : Fin N → Bool) :
    ∀ i, val gs x i = true → val gs y i = false → ∃ u : Fin N, x u = true ∧ y u = false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h1 h2
    by_cases hi : i < N
    · rw [val_input _ _ _ hi] at h1 h2
      exact ⟨_, h1, h2⟩
    · obtain ⟨k, hk, he, u, hu, hui, a, b⟩ := trace' gs hm x y i h1 h2 (by omega)
      exact ih u hui a b

def Cert1 (gs : List Gate) {N : ℕ} {ι κ : Type} (E : ι → Fin N → Bool) (Z : κ → Fin N → Bool)
    (a : ι) (b : κ) (c : Fin gs.length × Fin 2) : Prop :=
  (val gs (E a) (N + c.1.val) = true ∧ val gs (Z b) (N + c.1.val) = false) ∧
  (∃ a', a' ≠ a ∧ val gs (E a') (N + c.1.val) = true) ∧
  ∃ u, (gs.get c.1).inputs[c.2.val]? = some u ∧ val gs (E a) u = true ∧
    ∀ a', val gs (E a') u = true → a' = a

theorem Cert1_inj (gs : List Gate) (hm : Mono gs) {N : ℕ} {ι κ : Type} (E : ι → Fin N → Bool)
    (Z : κ → Fin N → Bool) (R : ι → κ → Prop)
    (hR : ∀ a b (u : Fin N), E a u = true → Z b u = false → R a b)
    (huniq : ∀ a a' b b', a ≠ a' → R a b → R a' b → R a b' → R a' b' → b = b')
    (a1 a2 : ι) (b1 b2 : κ) (c : Fin gs.length × Fin 2)
    (h1 : Cert1 gs E Z a1 b1 c) (h2 : Cert1 gs E Z a2 b2 c) : a1 = a2 ∧ b1 = b2 := by
  obtain ⟨⟨d1, d1'⟩, ⟨a', ha', hv'⟩, u, hu, hu0, hu1⟩ := h1
  obtain ⟨⟨d2, d2'⟩, _, u2, hu2, hu20, hu3⟩ := h2
  have hu' : u2 = u := by rw [hu] at hu2; exact (Option.some.inj hu2).symm
  subst hu'
  have ha : a2 = a1 := hu1 a2 hu20
  subst ha
  refine ⟨rfl, ?_⟩
  have hRR : ∀ a b, val gs (E a) (N + c.1.val) = true → val gs (Z b) (N + c.1.val) = false → R a b := by
    intro a b h1 h2
    obtain ⟨u, hx, hy⟩ := inputSep gs hm (E a) (Z b) _ h1 h2
    exact hR a b u hx hy
  exact huniq a2 a' b1 b2 (Ne.symm ha') (hRR _ _ d1 d1') (hRR _ _ hv' d1') (hRR _ _ d1 d2')
    (hRR _ _ hv' d2')

theorem Cert1_exists (gs : List Gate) (hm : Mono gs) {N : ℕ} {ι κ : Type} (E : ι → Fin N → Bool)
    (Z : κ → Fin N → Bool)
    (hE : ∀ a a' (u : Fin N), E a u = true → E a' u = true → a = a') (a : ι) (b : κ) :
    ∀ i, val gs (E a) i = true → val gs (Z b) i = false →
      (∃ a', a' ≠ a ∧ val gs (E a') i = true) → ∃ c, Cert1 gs E Z a b c := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h1 h2 h3
    by_cases hi : i < N
    · exfalso
      obtain ⟨a', ha', hv⟩ := h3
      rw [val_input _ _ _ hi] at h1 hv
      exact ha' (hE a' a _ hv h1)
    · obtain ⟨k, hk, he, u, hu, hui, hx, hy⟩ := trace' gs hm (E a) (Z b) i h1 h2 (by omega)
      by_cases hs : ∀ a', val gs (E a') u = true → a' = a
      · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hu
        have hp2 : p < 2 := by
          have h4 := (hm (gs[k]) (List.getElem_mem hk)).2
          have h5 : p < (gs[k]).inputs.length := by
            by_contra hc
            rw [List.getElem?_eq_none (by omega)] at hp
            cases hp
          omega
        subst he
        exact ⟨(⟨k, hk⟩, ⟨p, hp2⟩), ⟨h1, h2⟩, h3, u, hp, hx, hs⟩
      · push Not at hs
        obtain ⟨a', hv, hne⟩ := hs
        exact ih u hui hx hy ⟨a', hne, hv⟩

def Cert3 (gs : List Gate) {N : ℕ} {ι κ : Type} (E : ι → Fin N → Bool) (F : κ → Fin N → Bool)
    (a : ι) (b : κ) (c : Fin gs.length × Fin 2 × Fin 2) : Prop :=
  ∃ i j, (gs.get c.1).inputs[c.2.1.val]? = some i ∧ (gs.get c.1).inputs[c.2.2.val]? = some j ∧
    val gs (E a) i = true ∧ val gs (F b) j = true ∧
    (∀ a', val gs (E a') i = true → a' = a) ∧ (∀ b', val gs (F b') j = true → b' = b)

theorem Cert3_inj (gs : List Gate) {N : ℕ} {ι κ : Type} (E : ι → Fin N → Bool)
    (F : κ → Fin N → Bool) (a1 a2 : ι) (b1 b2 : κ) (c : Fin gs.length × Fin 2 × Fin 2)
    (h1 : Cert3 gs E F a1 b1 c) (h2 : Cert3 gs E F a2 b2 c) : a1 = a2 ∧ b1 = b2 := by
  obtain ⟨i, j, hi, hj, v1, v2, u1, u2⟩ := h1
  obtain ⟨i', j', hi', hj', v1', v2', _, _⟩ := h2
  have e1 : i' = i := by rw [hi] at hi'; exact (Option.some.inj hi').symm
  have e2 : j' = j := by rw [hj] at hj'; exact (Option.some.inj hj').symm
  subst e1 e2
  exact ⟨(u1 a2 v1').symm, (u2 b2 v2').symm⟩

theorem card_le_of_rel {α C : Type} [Fintype C] (T : Finset α) (P : α → C → Prop)
    (h : ∀ x ∈ T, ∃ c, P x c) (inj : ∀ x y c, P x c → P y c → x = y) :
    T.card ≤ Fintype.card C := by
  classical
  choose f hf using fun x : T => h x.1 x.2
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply inj _ _ (f x) (hf x)
    rw [hxy]
    exact hf y
  simpa using Fintype.card_le_of_injective f hinj

theorem mem_idx (l : List ℕ) (hl : l.length ≤ 2) (u : ℕ) (hu : u ∈ l) :
    ∃ p : Fin 2, l[p.val]? = some u := by
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hu
  have h5 : p < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hp
    cases hp
  exact ⟨⟨p, by omega⟩, hp⟩

theorem main (n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit)
    (huq : ∀ (x5 x6 : Fin n), x5 ≠ x6 → ∃! x8 : Fin n, R x5 x8 ∧ R x6 x8)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (T : Finset (Fin n × Fin n))
    (hT : ∀ x ∈ T, ∃ g ∈ C.gates, ∃ i ∈ g.inputs, ∃ j ∈ g.inputs,
      val C.gates (PEqualNP.PairShadow.unitInput (Fin.castAdd n x.1)) i = true ∧
      val C.gates (PEqualNP.PairShadow.unitInput (Fin.natAdd n x.2)) j = true ∧
      val C.gates (Fin.append (fun (x9 : Fin n) => decide ¬R x9 x.2)
        (PEqualNP.PairShadow.unitInput x.2)) i = false ∧
      val C.gates (Fin.append (PEqualNP.PairShadow.unitInput x.1)
        fun (x10 : Fin n) => decide ¬R x.1 x10) j = false) :
    T.card ≤ 8 * C.size := by
  have hm : Mono C.gates := by
    intro g hg
    have h := hmono g hg
    refine ⟨?_, h.2⟩
    simpa using h.1
  let EL : Fin n → Fin (n + n) → Bool := fun a => PEqualNP.PairShadow.unitInput (Fin.castAdd n a)
  let ER : Fin n → Fin (n + n) → Bool := fun b => PEqualNP.PairShadow.unitInput (Fin.natAdd n b)
  let X : Fin n → Fin (n + n) → Bool := fun b =>
    Fin.append (fun (x9 : Fin n) => decide ¬R x9 b) (PEqualNP.PairShadow.unitInput b)
  let Y : Fin n → Fin (n + n) → Bool := fun a =>
    Fin.append (PEqualNP.PairShadow.unitInput a) fun (x10 : Fin n) => decide ¬R a x10
  have hEL : ∀ a a' (u : Fin (n + n)), EL a u = true → EL a' u = true → a = a' := by
    intro a a' u h1 h2
    simp only [EL, PEqualNP.PairShadow.unitInput, decide_eq_true_eq] at h1 h2
    exact Fin.castAdd_injective n n (h1.symm.trans h2)
  have hER : ∀ a a' (u : Fin (n + n)), ER a u = true → ER a' u = true → a = a' := by
    intro a a' u h1 h2
    simp only [ER, PEqualNP.PairShadow.unitInput, decide_eq_true_eq] at h1 h2
    exact Fin.natAdd_injective n n (h1.symm.trans h2)
  have hRL : ∀ a b (u : Fin (n + n)), EL a u = true → X b u = false → R a b := by
    intro a b u h1 h2
    simp only [EL, PEqualNP.PairShadow.unitInput, decide_eq_true_eq] at h1
    subst h1
    simp only [X, Fin.append_left] at h2
    simpa using h2
  have hRR : ∀ b a (u : Fin (n + n)), ER b u = true → Y a u = false → R a b := by
    intro b a u h1 h2
    simp only [ER, PEqualNP.PairShadow.unitInput, decide_eq_true_eq] at h1
    subst h1
    simp only [Y, Fin.append_right] at h2
    simpa using h2
  have hU1 : ∀ a a' b b', a ≠ a' → R a b → R a' b → R a b' → R a' b' → b = b' := by
    intro a a' b b' hne h1 h2 h3 h4
    obtain ⟨w, _, hw⟩ := huq a a' hne
    rw [hw b ⟨h1, h2⟩, hw b' ⟨h3, h4⟩]
  have hU2 : ∀ b b' a a', b ≠ b' → R a b → R a b' → R a' b → R a' b' → a = a' := by
    intro b b' a a' hne h1 h2 h3 h4
    by_contra hc
    exact hne (hU1 a a' b b' hc h1 h3 h2 h4)
  have key : T.card ≤ Fintype.card ((Fin C.gates.length × Fin 2) ⊕
      ((Fin C.gates.length × Fin 2) ⊕ (Fin C.gates.length × Fin 2 × Fin 2))) := by
    apply card_le_of_rel T (fun x c => match c with
      | Sum.inl c => Cert1 C.gates EL X x.1 x.2 c
      | Sum.inr (Sum.inl c) => Cert1 C.gates ER Y x.2 x.1 c
      | Sum.inr (Sum.inr c) => Cert3 C.gates EL ER x.1 x.2 c)
    · intro x hx
      obtain ⟨g, hg, i, hi, j, hj, h1, h2, h3, h4⟩ := hT x hx
      by_cases hA : ∃ a', a' ≠ x.1 ∧ val C.gates (EL a') i = true
      · obtain ⟨c, hc⟩ := Cert1_exists C.gates hm EL X hEL x.1 x.2 i h1 h3 hA
        exact ⟨Sum.inl c, hc⟩
      · by_cases hB : ∃ b', b' ≠ x.2 ∧ val C.gates (ER b') j = true
        · obtain ⟨c, hc⟩ := Cert1_exists C.gates hm ER Y hER x.2 x.1 j h2 h4 hB
          exact ⟨Sum.inr (Sum.inl c), hc⟩
        · push Not at hA hB
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
          obtain ⟨p, hp⟩ := mem_idx _ (hm _ hg).2 i hi
          obtain ⟨q, hq⟩ := mem_idx _ (hm _ hg).2 j hj
          refine ⟨Sum.inr (Sum.inr (⟨k, hk⟩, p, q)), i, j, hp, hq, h1, h2, ?_, ?_⟩
          · intro a' ha'
            by_contra hne
            have := hA a' hne
            rw [ha'] at this
            exact this rfl
          · intro b' hb'
            by_contra hne
            have := hB b' hne
            rw [hb'] at this
            exact this rfl
    · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ (c | c | c) h1 h2
      · obtain ⟨e1, e2⟩ := Cert1_inj C.gates hm EL X R hRL hU1 a1 a2 b1 b2 c h1 h2
        rw [e1, e2]
      · obtain ⟨e1, e2⟩ := Cert1_inj C.gates hm ER Y (fun b a => R a b) hRR
          (fun b b' a a' hne h1 h2 h3 h4 => hU2 b b' a a' hne h1 h2 h3 h4) b1 b2 a1 a2 c h1 h2
        rw [e1, e2]
      · obtain ⟨e1, e2⟩ := Cert3_inj C.gates EL ER a1 a2 b1 b2 c h1 h2
        rw [e1, e2]
  simp [Fintype.card_sum, Fintype.card_prod] at key
  unfold Circuit.size
  omega

end PEqualNP.Outside.L_meta_7041

theorem PEqualNP.Outside.L_meta_7041 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x5 x6 : Fin x1), x5 ≠ x6 → ∃! x8 : Fin x1, x2 x5 x8 ∧ x2 x6 x8) →     PEqualNP.MetaComplexity.Monotone2 x4 →       have x7 : (Fin (x1 + x1) → Bool) → ℕ → Bool := fun (x7 : Fin (x1 + x1) → Bool) (x8 : ℕ) => (x4.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : Fin x1 → Fin (x1 + x1) → Bool := fun (x8 : Fin x1) => Fin.append (fun (x9 : Fin x1) => Decidable.decide ¬x2 x9 x8) (PEqualNP.PairShadow.unitInput x8);       have x9 : Fin x1 → Fin (x1 + x1) → Bool := fun (x9 : Fin x1) => Fin.append (PEqualNP.PairShadow.unitInput x9) fun (x10 : Fin x1) => Decidable.decide ¬x2 x9 x10;       ∀ (x10 : Finset (Fin x1 × Fin x1)), (∀ x11 ∈ x10, ∃ x13 ∈ x4.gates, ∃ x14 ∈ x13.inputs, ∃ x15 ∈ x13.inputs, x7 (PEqualNP.PairShadow.unitInput (Fin.castAdd x1 x11.1)) x14 = Bool.true ∧ x7 (PEqualNP.PairShadow.unitInput (Fin.natAdd x1 x11.2)) x15 = Bool.true ∧ x7 (x8 x11.2) x14 = Bool.false ∧ x7 (x9 x11.1) x15 = Bool.false) → x10.card ≤ (8 : ℕ) * x4.size := by
  intro n R _ C huq hmono V X Y T hT
  exact PEqualNP.Outside.L_meta_7041.main n R C huq hmono T hT
