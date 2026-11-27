import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3289

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ h

theorem read {N : ℕ} (x : Fin N → Bool) (i : Fin N) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

abbrev at_ (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

theorem run_gate {N : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step x).getD (N + j) false =
      (at_ gs j).op.eval ((at_ gs j).inputs.map fun i =>
        if i < N + j then (gs.foldl step x).getD i false else false) := by
  have hg : at_ gs j = gs[j] := by
    simp [at_, List.getD_eq_getElem?_getD, hj]
  have split : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  have whole : gs.foldl step x = (gs.drop (j + 1)).foldl step
      (step ((gs.take j).foldl step x) gs[j]) := by
    have h := congrArg (fun l => List.foldl step x l) split
    simp only [List.foldl_append, List.foldl_cons] at h
    exact h
  have len : ((gs.take j).foldl step x).length = N + j := by
    rw [run_length, hx, List.length_take]
    omega
  have low (i : ℕ) (hi : i < N + j) :
      (gs.foldl step x).getD i false = ((gs.take j).foldl step x).getD i false := by
    rw [whole, run_keep _ _ _ (by simp [step, len]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  have args : (gs[j].inputs.map fun i => ((gs.take j).foldl step x).getD i false) =
      (gs[j].inputs.map fun i => if i < N + j then (gs.foldl step x).getD i false else false) := by
    apply List.map_congr_left
    intro i _
    by_cases h : i < N + j
    · rw [if_pos h, low i h]
    · rw [if_neg h, getD_big _ _ (by omega)]
  have top : (gs.foldl step x).getD (N + j) false =
      (step ((gs.take j).foldl step x) gs[j]).getD (N + j) false := by
    rw [whole, run_keep _ _ _ (by simp [step, len])]
  rw [top, hg, step, List.getD_append_right _ _ _ _ (by omega), len, args]
  simp

def pt {n : ℕ} (x z : Fin n) : Fin n → Bool := fun j => decide (j = x ∨ j = z)

theorem agree {n : ℕ} (L D : Finset ℕ) (R : ℕ → List ℕ) (run : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ (S : Fin n → Bool) (i : Fin n), run S i.val = S i)
    (hL : ∀ k ∈ L, n ≤ k)
    (hc : ∀ k ∈ L, ∀ r ∈ R k, r < k → n ≤ r → r ∈ L)
    (hg : ∀ (S S' : Fin n → Bool), ∀ k ∈ L, (∀ r ∈ R k, r < k → run S r = run S' r) → run S k = run S' k)
    (S S' : Fin n → Bool) (hS : ∀ i : Fin n, i.val ∉ D → S i = S' i) (b : ℕ)
    (hk : ∀ k < b, k ∈ L → k ∉ D → (∃ r ∈ R k, r < k ∧ r ∈ D) → run S k = run S' k) (w : ℕ) (hw : w < b)
    (hl : w < n ∨ w ∈ L) (hD : w ∉ D) : run S w = run S' w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := hin S ⟨w, hn⟩
      have h2 := hin S' ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hS _ hD
    have hwL : w ∈ L := hl.resolve_left hn
    by_cases hr : ∃ r ∈ R w, r < w ∧ r ∈ D
    · exact hk w hw hwL hD hr
    · refine hg S S' w hwL fun r h1 h2 => ih r h2 (by omega) ?_ fun h => hr ⟨r, h1, h2, h⟩
      by_cases hrn : r < n
      · exact Or.inl hrn
      · exact Or.inr (hc w hwL r h1 h2 (by omega))

theorem core {n s out : ℕ} (R : ℕ → List ℕ) (run : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ (S : Fin n → Bool) (i : Fin n), run S i.val = S i)
    (hbig : ∀ S i, n + s ≤ i → run S i = false)
    (hlen : ∀ k, (R k).length ≤ 2)
    (hg : ∀ (S S' : Fin n → Bool) (k : ℕ), n ≤ k → k < n + s → (∀ r ∈ R k, r < k → run S r = run S' r) →
      run S k = run S' k)
    (hmono : ∀ (S S' : Fin n → Bool), (∀ i, S i = true → S' i = true) → ∀ w, run S w = true → run S' w = true)
    (hsing : ∀ x : Fin n, run (pt x x) out = false)
    (hK : ∀ x y z z' : Fin n, x ≠ y → z ≠ z' → run (pt x z) out = true → run (pt x z') out = true →
      run (pt y z) out = true → run (pt y z') out = true → False)
    (X : Finset (Fin n)) (hX : ∀ x ∈ X, ∃ z, run (pt x z) out = true)
    (Two : Fin n → Prop)
    (hTwo : ∀ x, Two x → x ∈ X ∧ ∃ z z', z ≠ z' ∧ run (pt x z) out = true ∧ run (pt x z') out = true) :
    ∃ A ⊆ X, X.card + A.card ≤ s + 1 ∧ ∀ x z z', x ∉ A → z ∉ A → z' ∉ A → Two x → Two z → Two z' →
      run (pt x z) out = true → run (pt x z') out = true → z = z' := by
  classical
  have comm (x z : Fin n) : pt x z = pt z x := by
    funext j
    simp only [pt, or_comm]
  have ptx (x z : Fin n) : pt x z x = true := by simp [pt]
  have ptz (x z : Fin n) : pt x z z = true := by simp [pt]
  have sub (x z : Fin n) (i : Fin n) (h : pt x x i = true) : pt x z i = true := by
    simp only [pt, or_self, decide_eq_true_eq] at h
    simp [pt, h]
  have sub' (x z : Fin n) (i : Fin n) (h : pt z z i = true) : pt x z i = true := by
    simp only [pt, or_self, decide_eq_true_eq] at h
    simp [pt, h]
  have off (x z : Fin n) (i : Fin n) (h : i ≠ x) : pt x z i = pt z z i := by
    simp [pt, h]
  rcases X.eq_empty_or_nonempty with hemp | ⟨x0, hx0⟩
  · subst hemp
    refine ⟨∅, by simp, by simp, ?_⟩
    intro x z z' _ _ _ h
    simpa using (hTwo x h).1
  obtain ⟨z0, hz0⟩ := hX x0 hx0
  have hout1 : out < n + s := by
    by_contra h
    rw [hbig _ _ (by omega)] at hz0
    exact Bool.false_ne_true hz0
  have hout0 : n ≤ out := by
    by_contra h
    have e2 := hsing ⟨out, by omega⟩
    have e3 := hin (pt (⟨out, by omega⟩ : Fin n) ⟨out, by omega⟩) ⟨out, by omega⟩
    rw [ptx] at e3
    simp only at e3
    rw [e3] at e2
    exact absurd e2 (by simp)
  let closed : Finset ℕ → Prop := fun L => out ∈ L ∧ ∀ k ∈ L, ∀ r ∈ R k, r < k → n ≤ r → r ∈ L
  obtain ⟨L, hLm, hLmin⟩ := Finset.exists_min_image ((Finset.Ico n (n + s)).powerset.filter closed)
    Finset.card ⟨Finset.Ico n (n + s), by
      refine Finset.mem_filter.mpr ⟨by simp, by simp [hout0, hout1], ?_⟩
      intro k hk r _ h1 h2
      rw [Finset.mem_Ico] at hk ⊢
      omega⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hLm
  obtain ⟨hLs, hLo, hLc⟩ := hLm
  have hLn : ∀ k ∈ L, n ≤ k := fun k h => (Finset.mem_Ico.mp (hLs h)).1
  have hLk : ∀ k ∈ L, k < n + s := fun k h => (Finset.mem_Ico.mp (hLs h)).2
  have live : ∀ g ∈ L, g ≠ out → ∃ k ∈ L, g ∈ R k ∧ g < k := by
    intro g hgL hgo
    by_contra hno
    have h := hLmin (L.erase g) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      ((Finset.erase_subset _ _).trans hLs), Finset.mem_erase.mpr ⟨fun h => hgo h.symm, hLo⟩, ?_⟩)
    · have := Finset.card_erase_lt_of_mem hgL
      omega
    · intro k hk r hr h1 h2
      have hk' := Finset.mem_of_mem_erase hk
      refine Finset.mem_erase.mpr ⟨?_, hLc k hk' r hr h1 h2⟩
      rintro rfl
      exact hno ⟨k, hk', hr, h1⟩
  have hgL : ∀ (S S' : Fin n → Bool), ∀ k ∈ L, (∀ r ∈ R k, r < k → run S r = run S' r) → run S k = run S' k :=
    fun S S' k h => hg S S' k (hLn k h) (hLk k h)
  have ag := fun D => agree L D R run hin hLn hLc hgL
  let Pos : Finset (ℕ × ℕ) := (L ×ˢ Finset.range 2).filter fun p =>
    p.2 < (R p.1).length ∧ (R p.1).getD p.2 0 < p.1
  let tgt : ℕ × ℕ → ℕ := fun p => (R p.1).getD p.2 0
  let f : ℕ → ℕ := fun w => (Pos.filter fun p => tgt p = w).card
  have posof : ∀ k ∈ L, ∀ w ∈ R k, w < k → ∃ i, (k, i) ∈ Pos.filter fun p => tgt p = w := by
    intro k hk w hw hwk
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
    have e : (R k).getD i 0 = w := by
      rw [List.getD_eq_getElem?_getD]
      simp [hi, hiw]
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk,
      Finset.mem_range.mpr ?_⟩, hi, ?_⟩, e⟩⟩
    · have := hlen k
      omega
    · simp only [e]
      exact hwk
  let Dom : Fin n → ℕ → Finset ℕ → Prop := fun x c D => x.val ∈ D ∧ c ∈ D ∧ (c = x.val ∨ c ∈ L) ∧
    (∀ w ∈ D, run (pt x x) w = true) ∧ ∀ w ∈ D, w ≠ c → ∀ k ∈ L, w ∈ R k → w < k → k ∈ D
  have outD : ∀ x c D, Dom x c D → out ∉ D := by
    intro x c D h ho
    have := h.2.2.2.1 out ho
    rw [hsing x] at this
    exact Bool.false_ne_true this
  have cut : ∀ x c D, Dom x c D → ∀ S S' : Fin n → Bool, (∀ i, i ≠ x → S i = S' i) → run S c = run S' c →
      run S out = run S' out := by
    intro x c D h S S' hS hc
    refine ag (D.erase c) S S' ?_ (out + 1) ?_ out (by omega) (Or.inr hLo)
      (fun ho => outD x c D h (Finset.mem_of_mem_erase ho))
    · intro i hi
      by_cases hix : i = x
      · subst hix
        have : i.val = c := by
          by_contra hne
          exact hi (Finset.mem_erase.mpr ⟨hne, h.1⟩)
        rw [← this, hin, hin] at hc
        exact hc
      · exact hS i hix
    · rintro k _ hk hkD ⟨r, hr, hrk, hrD⟩
      rw [Finset.mem_erase] at hrD
      have hkD' := h.2.2.2.2 r hrD.2 hrD.1 k hk hr hrk
      have : k = c := by
        by_contra hne
        exact hkD (Finset.mem_erase.mpr ⟨hne, hkD'⟩)
      rw [this]
      exact hc
  have rdx : ∀ x ∈ X, ∃ k ∈ L, x.val ∈ R k ∧ x.val < k := by
    intro x hx
    obtain ⟨z, hz⟩ := hX x hx
    by_contra hno
    have e := ag {x.val} (pt x z) (pt z z) ?_ (out + 1) ?_ out (by omega) (Or.inr hLo) ?_
    · rw [hz, hsing] at e
      exact absurd e (by simp)
    · intro i hi
      refine off x z i ?_
      rintro rfl
      simp at hi
    · rintro k _ hk _ ⟨r, hr, hrk, hrD⟩
      rw [Finset.mem_singleton] at hrD
      subst hrD
      exact (hno ⟨k, hk, hr, hrk⟩).elim
    · rw [Finset.mem_singleton]
      have := x.isLt
      omega
  have rdc : ∀ x c D, x ∈ X → Dom x c D → ∃ k ∈ L, c ∈ R k ∧ c < k := by
    intro x c D hx h
    rcases h.2.2.1 with e | e
    · rw [e]
      exact rdx x hx
    · refine live c e ?_
      rintro rfl
      exact outD x _ D h h.2.1
  let Term : Fin n → ℕ → Finset ℕ → Prop := fun x c D => Dom x c D ∧ (2 ≤ f c ∨ ∃ k ∈ L, c ∈ R k ∧ c < k ∧
    run (pt x x) k = false ∧ ∀ k' ∈ L, c ∈ R k' → c < k' → k' = k)
  have climb : ∀ (d : ℕ) x c D, x ∈ X → Dom x c D → n + s ≤ c + d → ∃ c' D', Term x c' D' := by
    intro d
    induction d with
    | zero =>
      intro x c D hx h hd
      obtain ⟨k, hk, _, h2⟩ := rdc x c D hx h
      have := hLk k hk
      omega
    | succ d ih =>
      intro x c D hx h hd
      by_cases h2 : 2 ≤ f c
      · exact ⟨c, D, h, Or.inl h2⟩
      obtain ⟨k, hk, hck, hlt⟩ := rdc x c D hx h
      have uni : ∀ k' ∈ L, c ∈ R k' → c < k' → k' = k := by
        intro k' hk' hck' hlt'
        obtain ⟨i, hi⟩ := posof k hk c hck hlt
        obtain ⟨i', hi'⟩ := posof k' hk' c hck' hlt'
        have : (Pos.filter fun p => tgt p = c).card ≤ 1 := by
          have : f c ≤ 1 := by omega
          exact this
        have := Finset.card_le_one.mp this _ hi _ hi'
        exact (congrArg Prod.fst this).symm
      cases hv : run (pt x x) k with
      | false => exact ⟨c, D, h, Or.inr ⟨k, hk, hck, hlt, hv, uni⟩⟩
      | true =>
        refine ih x k (insert k D) hx ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_self _ _, Or.inr hk, ?_, ?_⟩
          (by omega)
        · intro w hw
          rcases Finset.mem_insert.mp hw with e | e
          · rw [e]
            exact hv
          · exact h.2.2.2.1 w e
        · intro w hw hwk k' hk' hr hlt'
          have hwD := (Finset.mem_insert.mp hw).resolve_left hwk
          by_cases hwc : w = c
          · subst hwc
            rw [uni k' hk' hr hlt']
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (h.2.2.2.2 w hwD hwc k' hk' hr hlt')
  have term : ∀ x, ∃ c D, x ∈ X → Term x c D := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨c, D, h⟩ := climb (n + s) x x.val {x.val} hx ⟨by simp, by simp, Or.inl rfl, by
        intro w hw
        rw [Finset.mem_singleton] at hw
        rw [hw, hin]
        exact ptx x x, by
        intro w hw hne
        exact (hne (Finset.mem_singleton.mp hw)).elim⟩ (by omega)
      exact ⟨c, D, fun _ => h⟩
    · exact ⟨0, ∅, fun h => (hx h).elim⟩
  choose e D he using term
  have inj : ∀ x y, Two x → Two y → e x = e y → x = y := by
    intro x y hx hy hxy
    by_contra hne
    obtain ⟨hxX, z, z', hzz, hz, hz'⟩ := hTwo x hx
    have hdx := (he x hxX).1
    have hdy := (he y (hTwo y hy).1).1
    have key : ∀ z, run (pt x z) out = true → run (pt y z) out = true := by
      intro z hz
      have hc : run (pt y y) (e x) = true := by
        rw [hxy]
        exact hdy.2.2.2.1 _ hdy.2.1
      have h1 : run (pt y z) (e x) = true := hmono _ _ (sub y z) _ hc
      have h2 : run (fun i => pt y z i || decide (i = x)) (e x) = true :=
        hmono (pt y z) _ (fun i hi => by simp [hi]) _ h1
      rw [cut x (e x) (D x) hdx (pt y z) (fun i => pt y z i || decide (i = x)) (fun i hi => by simp [hi])
        (by rw [h1, h2])]
      refine hmono (pt x z) _ (fun i hi => ?_) _ hz
      simp only [pt, decide_eq_true_eq] at hi
      rcases hi with hi | hi <;> simp [pt, hi]
    exact hK x y z z' hne hzz hz hz' (key z hz) (key z' hz')
  let A : Finset (Fin n) := X.filter fun x => Two x ∧ 2 ≤ f (e x)
  refine ⟨A, Finset.filter_subset _ _, ?_, ?_⟩
  · let W0 : Finset ℕ := X.image (fun x => x.val) ∪ L.erase out
    have cX : (X.image (fun x => x.val)).card = X.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have dis : Disjoint (X.image (fun x => x.val)) (L.erase out) := by
      refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h1
      have := hLn _ (Finset.mem_of_mem_erase h2)
      have := x.isLt
      omega
    have cW : W0.card = X.card + (L.card - 1) := by
      rw [Finset.card_union_of_disjoint dis, cX, Finset.card_erase_of_mem hLo]
    have cL : L.card ≤ s := by
      have := Finset.card_le_card hLs
      simpa using this
    have cL0 : 0 < L.card := Finset.card_pos.mpr ⟨out, hLo⟩
    have one : ∀ w ∈ W0, 1 ≤ f w := by
      intro w hw
      have : ∃ k ∈ L, w ∈ R k ∧ w < k := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
          exact rdx x hx
        · rw [Finset.mem_erase] at h
          exact live w h.2 h.1
      obtain ⟨k, hk, h1, h2⟩ := this
      obtain ⟨i, hi⟩ := posof k hk w h1 h2
      exact Finset.card_pos.mpr ⟨_, hi⟩
    have big : A.card ≤ (W0.filter fun w => 2 ≤ f w).card := by
      refine Finset.card_le_card_of_injOn e ?_ ?_
      · intro x hx
        have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
        have hd := (he x hx'.1).1
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hx'.2.2⟩)
        rcases hd.2.2.1 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx'.1, h.symm⟩)
        · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, h⟩)
          intro h'
          exact outD _ _ _ hd (h' ▸ hd.2.1)
      · intro x hx y hy hxy
        exact inj x y (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2.1
          (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2.1 hxy
    have sum1 : W0.card + (W0.filter fun w => 2 ≤ f w).card ≤ ∑ w ∈ W0, f w := by
      rw [Finset.card_eq_sum_ones, Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun w hw => ?_
      have := one w hw
      split <;> omega
    have sum2 : ∑ w ∈ W0, f w ≤ Pos.card := by
      have h := Finset.card_eq_sum_card_fiberwise (f := tgt) (s := Pos.filter fun p => tgt p ∈ W0) (t := W0)
        (fun p hp => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2)
      have h2 : ∑ w ∈ W0, f w = ∑ w ∈ W0, ((Pos.filter fun p => tgt p ∈ W0).filter fun p => tgt p = w).card := by
        refine Finset.sum_congr rfl fun w hw => ?_
        refine congrArg Finset.card ?_
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨⟨a, b ▸ hw⟩, b⟩
        · rintro ⟨⟨a, _⟩, b⟩
          exact ⟨a, b⟩
      rw [h2, ← h]
      exact Finset.card_filter_le _ _
    have sum3 : Pos.card ≤ L.card * 2 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_range]
    omega
  · have nolt : ∀ x z cx Dx cz Dz kx kz, Dom x cx Dx → Dom z cz Dz → kx ∈ L → run (pt x x) kx = false →
        (∀ k' ∈ L, cx ∈ R k' → cx < k' → k' = kx) → (∀ k' ∈ L, cz ∈ R k' → cz < k' → k' = kz) →
        run (pt x z) out = true → ¬ kx < kz := by
      intro x z cx Dx cz Dz kx kz dx dz hkx vx ux uz hxz hlt
      have a1 : run (pt x z) kx ≠ run (pt z z) kx := by
        intro heq
        have := ag Dx (pt x z) (pt z z) ?_ (out + 1) ?_ out (by omega) (Or.inr hLo) (outD _ _ _ dx)
        · rw [hxz, hsing] at this
          exact absurd this (by simp)
        · intro i hi
          refine off x z i ?_
          rintro rfl
          exact hi dx.1
        · rintro k _ hk hkD ⟨r, hr, hrk, hrD⟩
          by_cases hrc : r = cx
          · subst hrc
            rw [ux k hk hr hrk]
            exact heq
          · exact (hkD (dx.2.2.2.2 r hrD hrc k hk hr hrk)).elim
      have a2 : run (pt z z) kx = false := by
        cases h : run (pt z z) kx with
        | false => rfl
        | true => exact (a1 (by rw [h, hmono _ _ (sub' x z) _ h])).elim
      have a3 : run (pt x z) kx = true := by
        cases h : run (pt x z) kx with
        | true => rfl
        | false => exact (a1 (by rw [h, a2])).elim
      have a4 : run (pt x z) kx = run (pt x x) kx := by
        refine ag Dz (pt x z) (pt x x) ?_ kz ?_ kx hlt (Or.inr hkx) ?_
        · intro i hi
          rw [comm x z]
          refine off z x i ?_
          rintro rfl
          exact hi dz.1
        · rintro k hkb hk hkD ⟨r, hr, hrk, hrD⟩
          by_cases hrc : r = cz
          · subst hrc
            have := uz k hk hr hrk
            omega
          · exact (hkD (dz.2.2.2.2 r hrD hrc k hk hr hrk)).elim
        · intro h
          have := dz.2.2.2.1 _ h
          rw [a2] at this
          exact Bool.false_ne_true this
      rw [a3, vx] at a4
      exact absurd a4 (by simp)
    have small : ∀ x, x ∉ A → Two x → ∃ k ∈ L, e x ∈ R k ∧ run (pt x x) k = false ∧
        ∀ k' ∈ L, e x ∈ R k' → e x < k' → k' = k := by
      intro x hxA hx
      have hxX := (hTwo x hx).1
      rcases (he x hxX).2 with h | ⟨k, h1, h2, _, h3, h4⟩
      · exact (hxA (Finset.mem_filter.mpr ⟨hxX, hx, h⟩)).elim
      · exact ⟨k, h1, h2, h3, h4⟩
    have same : ∀ x z, x ∉ A → z ∉ A → Two x → Two z → run (pt x z) out = true → ∀ k kz,
        (k ∈ L ∧ run (pt x x) k = false ∧ ∀ k' ∈ L, e x ∈ R k' → e x < k' → k' = k) →
        (kz ∈ L ∧ run (pt z z) kz = false ∧ ∀ k' ∈ L, e z ∈ R k' → e z < k' → k' = kz) → k = kz := by
      intro x z _ _ hx hz hxz k kz ⟨h1, h2, h3⟩ ⟨j1, j2, j3⟩
      have dx := (he x (hTwo x hx).1).1
      have dz := (he z (hTwo z hz).1).1
      have b1 := nolt x z (e x) (D x) (e z) (D z) k kz dx dz h1 h2 h3 j3 hxz
      have b2 := nolt z x (e z) (D z) (e x) (D x) kz k dz dx j1 j2 j3 h3 (by rw [comm z x]; exact hxz)
      omega
    intro x z z' hxA hzA hzA' hx hz hz' hxz hxz'
    by_contra hne
    obtain ⟨k, k1, k2, k3, k4⟩ := small x hxA hx
    obtain ⟨j, j1, j2, j3, j4⟩ := small z hzA hz
    obtain ⟨i, i1, i2, i3, i4⟩ := small z' hzA' hz'
    have e1 := same x z hxA hzA hx hz hxz k j ⟨k1, k3, k4⟩ ⟨j1, j3, j4⟩
    have e2 := same x z' hxA hzA' hx hz' hxz' k i ⟨k1, k3, k4⟩ ⟨i1, i3, i4⟩
    subst e1
    subst e2
    have nx : ∀ w, run (pt x w) out = true → x ≠ w := by
      rintro w hw rfl
      rw [hsing] at hw
      exact Bool.false_ne_true hw
    have c3 : ({e x, e z, e z'} : Finset ℕ).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨e x, e z, e z', fun h => nx z hxz (inj _ _ hx hz h), fun h => nx z' hxz' (inj _ _ hx hz' h),
        fun h => hne (inj _ _ hz hz' h), rfl⟩
    have c4 : ({e x, e z, e z'} : Finset ℕ) ⊆ (R k).toFinset := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [List.mem_toFinset]
      rcases hw with h | h | h <;> rw [h] <;> assumption
    have := Finset.card_le_card c4
    have := List.toFinset_card_le (R k)
    have := hlen k
    omega

theorem op_mono {op : GateOp} (h : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (l : List ℕ) (u v : ℕ → Bool)
    (huv : ∀ r ∈ l, u r = true → v r = true) (hu : op.eval (l.map u) = true) : op.eval (l.map v) = true := by
  rcases h with rfl | h
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hu ⊢
    exact fun r hr => huv r hr (hu r hr)
  · rw [Set.mem_singleton_iff] at h
    subst h
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hu ⊢
    obtain ⟨r, hr, h⟩ := hu
    exact ⟨r, hr, huv r hr h⟩

def rn {n : ℕ} (C : Circuit) (S : Fin n → Bool) (w : ℕ) : Bool := (C.gates.foldl step (List.ofFn S)).getD w false

theorem rn_in {n : ℕ} (C : Circuit) (S : Fin n → Bool) (i : Fin n) : rn C S i.val = S i := by
  rw [rn, run_keep _ _ _ (by simp), read]

theorem rn_big {n : ℕ} (C : Circuit) (S : Fin n → Bool) (i : ℕ) (h : n + C.gates.length ≤ i) : rn C S i = false := by
  apply getD_big
  rw [run_length]
  simpa using h

theorem rn_gate {n : ℕ} (C : Circuit) (S : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    rn C S (n + j) = (at_ C.gates j).op.eval ((at_ C.gates j).inputs.map fun i =>
        if i < n + j then rn C S i else false) :=
  run_gate (N := n) C.gates (List.ofFn S) (by simp) j hj

theorem at_mem (l : List Gate) (j : ℕ) (h : j < l.length) : at_ l j ∈ l := by
  simp [at_, List.getD_eq_getElem?_getD, h]

theorem rn_mono {n : ℕ} (C : Circuit) (hC : Monotone2 C) (S S' : Fin n → Bool)
    (h : ∀ i, S i = true → S' i = true) (w : ℕ) : rn C S w = true → rn C S' w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := rn_in C S ⟨w, hn⟩
      have h2 := rn_in C S' ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact h _
    by_cases hb : n + C.gates.length ≤ w
    · rw [rn_big C S w hb]
      simp
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    rw [rn_gate C S j (by omega), rn_gate C S' j (by omega)]
    refine op_mono (hC _ (at_mem _ _ (by omega))).1 _ _ _ ?_
    intro r _ hr
    by_cases hrj : r < n + j
    · rw [if_pos hrj] at hr ⊢
      exact ih r hrj hr
    · rw [if_neg hrj] at hr
      exact absurd hr (by simp)

theorem degree {N q : ℕ} (inc : Fin N → Fin N → Prop) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (pts : Fin N → Finset (Fin N)) (hp : ∀ p l, p ∈ pts l ↔ inc p l) (hl : ∀ l, (pts l).card = q + 1)
    (hu : ∀ a b, a ≠ b → ∃! l, inc a l ∧ inc b l) (p : Fin N) (Ls : Finset (Fin N)) (hLs : ∀ l ∈ Ls, inc p l) :
    Ls.card ≤ q + 1 := by
  classical
  have h := Finset.card_biUnion (s := Ls) (t := fun l => (pts l).erase p) (by
    intro l hl' m hm hne
    refine Finset.disjoint_left.mpr fun a ha hb => hne ?_
    rw [Finset.mem_erase, hp] at ha hb
    exact (hu a p ha.1).unique ⟨ha.2, hLs l hl'⟩ ⟨hb.2, hLs m hm⟩)
  have h1 : ∑ l ∈ Ls, ((pts l).erase p).card = Ls.card * q := by
    rw [Finset.sum_const_nat]
    intro l hl'
    rw [Finset.card_erase_of_mem ((hp p l).mpr (hLs l hl')), hl]
    rfl
  have h2 : (Ls.biUnion fun l => (pts l).erase p) ⊆ Finset.univ.erase p := by
    intro a ha
    obtain ⟨l, _, h⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp h).1, Finset.mem_univ _⟩
  have h3 := Finset.card_le_card h2
  rw [h, h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h3
  have h4 : Ls.card * q ≤ (q + 1) * q := by
    have : N - 1 = (q + 1) * q := by
      rw [hN, Nat.add_sub_cancel]
      ring
    omega
  exact Nat.le_of_mul_le_mul_right h4 (by omega)

theorem final (m X A s x y : ℕ) (h1 : m ≤ 131 * x) (h2 : m ≤ 131 * y) (h3 : m ≤ x * y) (hxy : x + y = X)
    (h4 : m ≤ 130 * A + X) (h5 : A ≤ X) (h6 : X + A ≤ s + 1) : m ≤ 44 * s := by
  by_cases a : 66 ≤ A
  · omega
  by_cases b : 2 * A + 2 ≤ X
  · omega
  have h7 : 4 * m ≤ X * X := by
    subst hxy
    have : 4 * (x * y) ≤ (x + y) * (x + y) := by
      zify
      nlinarith [sq_nonneg ((x : ℤ) - y)]
    omega
  have h8 : X * X ≤ 131 * X := Nat.mul_le_mul_right _ (by omega)
  by_cases c : 2 ≤ X
  · omega
  · have : X * X ≤ 1 * X := Nat.mul_le_mul_right _ (by omega)
    omega

theorem main : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  intro q N inc _ C hq hq' hN hl hu hC hs
  classical
  let pts : Fin N → Finset (Fin N) := fun l => Finset.univ.filter fun p => inc p l
  have hp : ∀ p l, p ∈ pts l ↔ inc p l := fun p l => by simp [pts]
  have hcard : ∀ l, (pts l).card = q + 1 := fun l => by
    rw [← hl l, Fintype.card_subtype]
  let acc : Fin (N + N) → Fin (N + N) → Prop := fun x z => rn C (pt x z) C.output = true
  have comm (x z : Fin (N + N)) : pt x z = pt z x := by
    funext j
    simp only [pt, or_comm]
  have sound : ∀ x z, acc x z → ∃ p l, inc p l ∧ ((x = Fin.castAdd N p ∧ z = Fin.natAdd N l) ∨
      (x = Fin.natAdd N l ∧ z = Fin.castAdd N p)) := by
    intro x z h
    by_contra hno
    have h0 : circuitFun (N + N) C (pt x z) = false := by
      refine hs (pt x z) ?_ ?_
      · have : Fintype.card { l : Fin N // pt x z (Fin.natAdd N l) = true } ≤ ({x, z} : Finset (Fin (N + N))).card := by
          rw [Fintype.card_subtype]
          refine Finset.card_le_card_of_injOn (Fin.natAdd N) ?_ ?_
          · intro l hl'
            have h' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl')).2
            simp only [pt, decide_eq_true_eq] at h'
            refine Finset.mem_coe.mpr ?_
            rw [Finset.mem_insert, Finset.mem_singleton]
            exact h'
          · intro a _ b _ hab
            exact Fin.natAdd_injective _ _ hab
        exact this.trans (Finset.card_le_two.trans hq)
      · rintro ⟨p, l, hpl, h1, h2⟩
        simp only [pt, decide_eq_true_eq] at h1 h2
        have ne : Fin.castAdd N p ≠ Fin.natAdd N l := by
          intro e
          have e' := congrArg Fin.val e
          simp only [Fin.val_castAdd, Fin.val_natAdd] at e'
          have := p.isLt
          omega
        apply hno
        refine ⟨p, l, hpl, ?_⟩
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact (ne (h1.trans h2.symm)).elim
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩
        · exact (ne (h1.trans h2.symm)).elim
    have h1 : circuitFun (N + N) C (pt x z) = rn C (pt x z) C.output := rfl
    rw [h1] at h0
    rw [show rn C (pt x z) C.output = true from h] at h0
    exact absurd h0 (by simp)
  have ne (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro e
    have e' := congrArg Fin.val e
    simp only [Fin.val_castAdd, Fin.val_natAdd] at e'
    have := p.isLt
    omega
  have ci : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := Fin.castAdd_injective _ _
  have ni : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := Fin.natAdd_injective _ _
  have accp : ∀ p z, acc (Fin.castAdd N p) z → ∃ l, inc p l ∧ z = Fin.natAdd N l := by
    intro p z h
    obtain ⟨p', l, hi, ⟨h1, h2⟩ | ⟨h1, _⟩⟩ := sound _ _ h
    · rw [ci h1]
      exact ⟨l, hi, h2⟩
    · exact (ne _ _ h1).elim
  have accl : ∀ l z, acc (Fin.natAdd N l) z → ∃ p, inc p l ∧ z = Fin.castAdd N p := by
    intro l z h
    obtain ⟨p', l', hi, ⟨h1, _⟩ | ⟨h1, h2⟩⟩ := sound _ _ h
    · exact (ne _ _ h1.symm).elim
    · rw [ni h1]
      exact ⟨p', hi, h2⟩
  have hsing : ∀ x : Fin (N + N), rn C (pt x x) C.output = false := by
    intro x
    cases h : rn C (pt x x) C.output with
    | false => rfl
    | true =>
      obtain ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := sound x x h
      · exact (ne _ _ (h1.symm.trans h2)).elim
      · exact (ne _ _ (h2.symm.trans h1)).elim
  have hK : ∀ x y z z' : Fin (N + N), x ≠ y → z ≠ z' → acc x z → acc x z' → acc y z → acc y z' → False := by
    intro x y
    refine Fin.addCases (fun p => ?_) (fun l => ?_) x
    · intro z z' hxy hzz h1 h2 h3 h4
      obtain ⟨l, i1, rfl⟩ := accp _ _ h1
      obtain ⟨l', i2, rfl⟩ := accp _ _ h2
      rw [show acc y (Fin.natAdd N l) = acc (Fin.natAdd N l) y from by simp only [acc, comm]] at h3
      rw [show acc y (Fin.natAdd N l') = acc (Fin.natAdd N l') y from by simp only [acc, comm]] at h4
      obtain ⟨p', i3, rfl⟩ := accl _ _ h3
      obtain ⟨p'', i4, e⟩ := accl _ _ h4
      rw [← ci e] at i4
      refine hzz (congrArg _ ((hu p p' ?_).unique ⟨i1, i3⟩ ⟨i2, i4⟩))
      rintro rfl
      exact hxy rfl
    · intro z z' hxy hzz h1 h2 h3 h4
      obtain ⟨p, i1, rfl⟩ := accl _ _ h1
      obtain ⟨p', i2, rfl⟩ := accl _ _ h2
      rw [show acc y (Fin.castAdd N p) = acc (Fin.castAdd N p) y from by simp only [acc, comm]] at h3
      rw [show acc y (Fin.castAdd N p') = acc (Fin.castAdd N p') y from by simp only [acc, comm]] at h4
      obtain ⟨l', i3, rfl⟩ := accp _ _ h3
      obtain ⟨l'', i4, e⟩ := accp _ _ h4
      rw [← ni e] at i4
      refine hxy (congrArg _ ((hu p p' ?_).unique ⟨i1, i2⟩ ⟨i3, i4⟩))
      rintro rfl
      exact hzz rfl
  let X : Finset (Fin (N + N)) := Finset.univ.filter fun x => ∃ z, acc x z
  let Two : Fin (N + N) → Prop := fun x => ∃ z z', z ≠ z' ∧ acc x z ∧ acc x z'
  obtain ⟨A, hAX, hA, hM⟩ := core (s := C.gates.length) (out := C.output)
    (fun k => (at_ C.gates (k - (N + N))).inputs) (rn (n := N + N) C) (rn_in C) (rn_big C)
    (by
      intro k
      by_cases h : k - (N + N) < C.gates.length
      · exact (hC _ (at_mem _ _ h)).2
      · simp [at_, List.getD_eq_getElem?_getD, h])
    (by
      intro S S' k hk hk' h
      obtain ⟨j, rfl⟩ : ∃ j, k = N + N + j := ⟨k - (N + N), by omega⟩
      rw [Nat.add_sub_cancel_left] at h
      rw [rn_gate C S j (by omega), rn_gate C S' j (by omega)]
      congr 1
      apply List.map_congr_left
      intro r hr
      by_cases hrj : r < N + N + j
      · rw [if_pos hrj, if_pos hrj]
        exact h r hr hrj
      · rw [if_neg hrj, if_neg hrj])
    (rn_mono C hC) hsing hK X (fun x hx => (Finset.mem_filter.mp hx).2) Two
    (by
      intro x hx
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hx⟩
      obtain ⟨z, _, _, h, _⟩ := hx
      exact ⟨z, h⟩)
  let T : Finset (Fin N × Fin N) := Finset.univ.filter fun t =>
    inc t.1 t.2 ∧ acc (Fin.castAdd N t.1) (Fin.natAdd N t.2)
  have hT : ∀ t ∈ T, inc t.1 t.2 ∧ acc (Fin.castAdd N t.1) (Fin.natAdd N t.2) :=
    fun t h => (Finset.mem_filter.mp h).2
  have hT' : ∀ t ∈ T, acc (Fin.natAdd N t.2) (Fin.castAdd N t.1) := by
    intro t h
    have := (hT t h).2
    simp only [acc] at this ⊢
    rw [comm]
    exact this
  let E : Fin (N + N) → Finset (Fin N × Fin N) := fun a =>
    T.filter fun t => Fin.castAdd N t.1 = a ∨ Fin.natAdd N t.2 = a
  have hE : ∀ a, (E a).card ≤ 131 := by
    intro a
    refine Fin.addCases (fun p => ?_) (fun l => ?_) a
    · have e : ∀ t ∈ E (Fin.castAdd N p), t ∈ T ∧ t.1 = p := by
        intro t ht
        obtain ⟨h1, h2 | h2⟩ := Finset.mem_filter.mp ht
        · exact ⟨h1, ci h2⟩
        · exact (ne _ _ h2.symm).elim
      have h := degree inc hq hN pts hp hcard hu p ((E (Fin.castAdd N p)).image Prod.snd) (by
        intro l hl'
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl'
        obtain ⟨h1, h2⟩ := e t ht
        rw [← h2]
        exact (hT t h1).1)
      rw [Finset.card_image_of_injOn] at h
      · omega
      · intro t ht t' ht' htt
        exact Prod.ext ((e t ht).2.trans (e t' ht').2.symm) htt
    · have e : ∀ t ∈ E (Fin.natAdd N l), t ∈ T ∧ t.2 = l := by
        intro t ht
        obtain ⟨h1, h2 | h2⟩ := Finset.mem_filter.mp ht
        · exact (ne _ _ h2).elim
        · exact ⟨h1, ni h2⟩
      have h : (E (Fin.natAdd N l)).card ≤ (pts l).card := by
        refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
        · intro t ht
          obtain ⟨h1, h2⟩ := e t ht
          refine Finset.mem_coe.mpr ((hp _ _).mpr ?_)
          rw [← h2]
          exact (hT t h1).1
        · intro t ht t' ht' htt
          exact Prod.ext htt ((e t ht).2.trans (e t' ht').2.symm)
      rw [hcard] at h
      omega
  have tp : ∀ t ∈ T, Fin.castAdd N t.1 ∈ X := fun t h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, (hT t h).2⟩
  have tl : ∀ t ∈ T, Fin.natAdd N t.2 ∈ X := fun t h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hT' t h⟩
  let XP := X.filter fun x => x.val < N
  let XL := X.filter fun x => ¬ x.val < N
  have hXX : XP.card + XL.card = X.card := Finset.card_filter_add_card_filter_not _
  have tp' : ∀ t ∈ T, Fin.castAdd N t.1 ∈ XP := fun t h =>
    Finset.mem_filter.mpr ⟨tp t h, by simp⟩
  have tl' : ∀ t ∈ T, Fin.natAdd N t.2 ∈ XL := fun t h =>
    Finset.mem_filter.mpr ⟨tl t h, by simp⟩
  have b1 : T.card ≤ 131 * XP.card := by
    rw [mul_comm]
    refine le_trans (Finset.card_le_card (t := XP.biUnion E) fun t ht => ?_)
      (Finset.card_biUnion_le_card_mul _ _ _ fun a _ => hE a)
    exact Finset.mem_biUnion.mpr ⟨_, tp' t ht, Finset.mem_filter.mpr ⟨ht, Or.inl rfl⟩⟩
  have b2 : T.card ≤ 131 * XL.card := by
    rw [mul_comm]
    refine le_trans (Finset.card_le_card (t := XL.biUnion E) fun t ht => ?_)
      (Finset.card_biUnion_le_card_mul _ _ _ fun a _ => hE a)
    exact Finset.mem_biUnion.mpr ⟨_, tl' t ht, Finset.mem_filter.mpr ⟨ht, Or.inr rfl⟩⟩
  have b3 : T.card ≤ XP.card * XL.card := by
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun t => (Fin.castAdd N t.1, Fin.natAdd N t.2)) ?_ ?_
    · intro t ht
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨tp' t ht, tl' t ht⟩)
    · intro t _ t' _ h
      exact Prod.ext (ci (congrArg Prod.fst h)) (ni (congrArg Prod.snd h))
  have b4 : T.card ≤ 130 * A.card + X.card := by
    let T1 := T.filter fun t => Fin.castAdd N t.1 ∈ A ∨ Fin.natAdd N t.2 ∈ A
    let T2 := T.filter fun t => ¬ (Fin.castAdd N t.1 ∈ A ∨ Fin.natAdd N t.2 ∈ A)
    have h12 : T1.card + T2.card = T.card := Finset.card_filter_add_card_filter_not _
    have h1 : T1.card ≤ A.card * 131 := by
      refine le_trans (Finset.card_le_card (t := A.biUnion E) fun t ht => ?_)
        (Finset.card_biUnion_le_card_mul _ _ _ fun a _ => hE a)
      obtain ⟨ht, h | h⟩ := Finset.mem_filter.mp ht
      · exact Finset.mem_biUnion.mpr ⟨_, h, Finset.mem_filter.mpr ⟨ht, Or.inl rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨_, h, Finset.mem_filter.mpr ⟨ht, Or.inr rfl⟩⟩
    have h2 : T2.card ≤ (X \ A).card := by
      let g : Fin N × Fin N → Fin (N + N) := fun t =>
        if Two (Fin.castAdd N t.1) ∧ ¬ Two (Fin.natAdd N t.2) then Fin.natAdd N t.2 else Fin.castAdd N t.1
      refine Finset.card_le_card_of_injOn g ?_ ?_
      · intro t ht
        obtain ⟨ht, hno⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
        refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ?_)
        simp only [g]
        split
        · exact ⟨tl t ht, fun h => hno (Or.inr h)⟩
        · exact ⟨tp t ht, fun h => hno (Or.inl h)⟩
      · intro t ht u hu' htu
        obtain ⟨ht, hno⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
        obtain ⟨hu', hno'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu')
        simp only [g] at htu
        split at htu
        · rename_i c1
          split at htu
          · have e := ni htu
            by_contra hne
            refine c1.2 ⟨Fin.castAdd N t.1, Fin.castAdd N u.1, fun h => hne (Prod.ext (ci h) e), hT' t ht, ?_⟩
            rw [e]
            exact hT' u hu'
          · exact (ne _ _ htu.symm).elim
        · rename_i c1
          split at htu
          · exact (ne _ _ htu).elim
          · rename_i c2
            have e := ci htu
            by_contra hne
            have hne2 : Fin.natAdd N t.2 ≠ Fin.natAdd N u.2 := fun h => hne (Prod.ext e (ni h))
            have hu2 : acc (Fin.castAdd N t.1) (Fin.natAdd N u.2) := by
              rw [e]
              exact (hT u hu').2
            have two : Two (Fin.castAdd N t.1) := ⟨_, _, hne2, (hT t ht).2, hu2⟩
            have two1 : Two (Fin.natAdd N t.2) := by
              by_contra h
              exact c1 ⟨two, h⟩
            have two2 : Two (Fin.natAdd N u.2) := by
              by_contra h
              exact c2 ⟨e ▸ two, h⟩
            exact hne2 (hM _ _ _ (fun h => hno (Or.inl h)) (fun h => hno (Or.inr h)) (fun h => hno' (Or.inr h))
              two two1 two2 (hT t ht).2 hu2)
    have h3 := Finset.card_sdiff_add_card_eq_card hAX
    omega
  have hm := final T.card X.card A.card C.gates.length XP.card XL.card b1 b2 b3 hXX b4 (Finset.card_le_card hAX) hA
  have goal : Fintype.card { x13 : Fin N × Fin N // inc x13.1 x13.2 ∧ (circuitFun (N + N) C
      fun (x14 : Fin (N + N)) => decide (x14 = Fin.castAdd N x13.1 ∨ x14 = Fin.natAdd N x13.2)) = true } = T.card := by
    rw [Fintype.card_subtype]
    refine congrArg Finset.card ?_
    ext t
    simp only [T, Finset.mem_filter]
    exact Iff.rfl
  have e := goal.le.trans hm
  convert e using 1
  rfl

end PEqualNP.Outside.L_meta_3289

theorem PEqualNP.Outside.L_meta_3289 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2)) = Bool.true } ≤ (44 : ℕ) * x5.size :=
  PEqualNP.Outside.L_meta_3289.main
