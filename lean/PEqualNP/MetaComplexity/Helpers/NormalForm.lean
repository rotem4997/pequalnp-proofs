import PEqualNP.MetaComplexity.Helpers.NormalFormLift

/-!
# Helpers for L-meta-2925: a least `IsAO2` circuit has no AND gate reading a wire below `F`

* `wires_set_lt`: setting gate `g` keeps every wire below `n + g`.
* `gateAt_set`, `isAO2_set`: setting one gate.
* `swap_all`: with the swap move (L-meta-2772 as a hypothesis), every read of wire `n + h` is
  moved to a wire `t` with `n + h <= t <= f`, one read at a time.
* `fold_agree`, `set_unread_fun`: an unread gate that is not the output may be set to anything.
* `wires_and_copy`, `del_AO`: a gate `AND [t, t]` is a copy of `t` and is deleted by `del`.
-/

namespace PEqualNP.MetaComplexity.LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Lift
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

/-- The swap move (the recorded statement of L-meta-2772). -/
def SwapHyp : Prop := ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size

theorem wires_set_lt (gs : List Gate) (g : ℕ) (X : Gate) :
    ∀ (x : List Bool) (i : ℕ), i < x.length + g →
      ((gs.set g X).foldl step x).getD i false = (gs.foldl step x).getD i false := by
  induction gs generalizing g with
  | nil => intro x i _; simp
  | cons a gs ih =>
    intro x i hi
    cases g with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      rw [foldl_step_getD _ _ _ (by simp [step]; omega),
        foldl_step_getD _ _ _ (by simp [step]; omega)]
      unfold step
      rw [getD_append_left _ _ _ (by omega), getD_append_left _ _ _ (by omega)]
    | succ g =>
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih g _ _ (by simp [step]; omega)

theorem eval_set_lt (n : ℕ) (gs : List Gate) (g : ℕ) (X : Gate) (i : ℕ) (hi : i < n + g)
    (x : Fin n → Bool) :
    Circuit.eval ⟨gs.set g X, i⟩ (List.ofFn x) = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  simp only [Circuit.eval, wires_eq]
  exact wires_set_lt gs g X _ i (by simpa using hi)

theorem gateAt_set (C : Circuit) (o h : ℕ) (X : Gate) (hh : h < C.gates.length) (j : ℕ) :
    gateAt ⟨C.gates.set h X, o⟩ j = if j = h then X else gateAt C j := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hj : j = h
  · subst hj; simp [hh]
  · simp [Ne.symm hj, hj]

theorem isAO2_set (n : ℕ) (C : Circuit) (o h : ℕ) (X : Gate) (hC : IsAO2 n C)
    (hh : h < C.gates.length) (hop : X.op = GateOp.and ∨ X.op = GateOp.or)
    (hl : X.inputs.length = 2) (hr : ∀ i ∈ X.inputs, i < n + h) :
    IsAO2 n ⟨C.gates.set h X, o⟩ := by
  refine ⟨fun g hg => ?_, fun j hj => ?_, fun g hg => ?_⟩
  · rcases List.mem_or_eq_of_mem_set hg with h1 | h1
    · exact hC.1 g h1
    · subst h1; exact hop
  · rw [gateAt_set C o h X hh j]
    simp only [List.length_set] at hj
    split_ifs with h1
    · subst h1; exact hr
    · exact hC.2.1 j hj
  · rcases List.mem_or_eq_of_mem_set hg with h1 | h1
    · exact hC.2.2 g h1
    · subst h1; exact hl

/-- The number of reads of wire `w`. -/
def mu (w : ℕ) (C : Circuit) : ℕ := ∑ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count w

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates :=
  List.mem_of_getElem? (gateAt_some C j hj)

theorem swap_all (n : ℕ) (hswap : SwapHyp) (h t : ℕ) (ht : t < n + h) :
    ∀ N (C : Circuit), mu (n + h) C = N → IsAO2 n C →
      (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, n + h⟩ (List.ofFn x) = true →
        Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true) →
      (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        circuitFun n C x = true) →
      ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = circuitFun n C ∧
        C'.gates.length = C.gates.length ∧ C'.output = C.output ∧
        ∀ j < C'.gates.length, n + h ∉ (gateAt C' j).inputs := by
  intro N
  induction N with
  | zero =>
    intro C hmu hC _ _
    refine ⟨C, hC, rfl, rfl, rfl, fun j hj hmem => ?_⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hmu) j (by simpa using hj)
    exact (List.count_eq_zero.mp h0) hmem
  | succ N ih =>
    intro C hmu hC hw ht'
    have hex : ∃ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count (n + h) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_eq_zero hcon
      unfold mu at hmu
      omega
    obtain ⟨j, hjr, hjc⟩ := hex
    have hj : j < C.gates.length := by simpa using hjr
    have hmem : n + h ∈ (gateAt C j).inputs := List.count_pos_iff.mp (Nat.pos_of_ne_zero hjc)
    have hhj : n + h < n + j := hC.2.1 j hj _ hmem
    have hl2 := hC.2.2 _ (gateAt_mem C j hj)
    obtain ⟨b, hb, hget⟩ : ∃ b, b < 2 ∧ (gateAt C j).inputs.getD b 0 = n + h := by
      match hins : (gateAt C j).inputs, hl2, hmem with
      | [a, c], _, hm =>
        simp at hm
        rcases hm with hm | hm
        · exact ⟨0, by omega, by simp [hm]⟩
        · exact ⟨1, by omega, by simp [hm]⟩
    obtain ⟨hC1, hf1, _⟩ := hswap n C j b (n + h) t
      ⟨hC, hC.2.1, hj, hb, hget, by omega, hw, ht'⟩
    set X : Gate := ⟨(gateAt C j).op, (gateAt C j).inputs.set b t⟩ with hX
    set C1 : Circuit := ⟨C.gates.set j X, C.output⟩ with hC1def
    have hlen : C1.gates.length = C.gates.length := by simp [hC1def]
    have hcount : X.inputs.count (n + h) + 1 = (gateAt C j).inputs.count (n + h) := by
      simp only [hX]
      match hins : (gateAt C j).inputs, hl2, hget with
      | [a, c], _, hg =>
        have htne : t ≠ n + h := by omega
        interval_cases b
        · simp at hg; subst hg; simp [List.count_cons, htne]
        · simp at hg; subst hg; simp [List.count_cons, htne]; omega
    have hmu1 : mu (n + h) C1 = N := by
      unfold mu at hmu ⊢
      rw [hlen] at *
      rw [← Finset.add_sum_erase _ _ hjr] at hmu ⊢
      have hrest : ∑ x ∈ (Finset.range C.gates.length).erase j, (gateAt C1 x).inputs.count (n + h) =
          ∑ x ∈ (Finset.range C.gates.length).erase j, (gateAt C x).inputs.count (n + h) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hC1def, gateAt_set C _ j X hj x, if_neg (Finset.ne_of_mem_erase hx)]
      rw [hrest]
      have : gateAt C1 j = X := by rw [hC1def, gateAt_set C _ j X hj j, if_pos rfl]
      rw [this]
      omega
    obtain ⟨C', h1, h2, h3, h4, h5⟩ := ih C1 hmu1 hC1
      (fun x hx => by
        rw [eval_set_lt n C.gates j X t (by omega)]
        rw [eval_set_lt n C.gates j X (n + h) hhj] at hx
        exact hw x hx)
      (fun x hx => by
        rw [eval_set_lt n C.gates j X t (by omega)] at hx
        rw [hf1]
        exact ht' x hx)
    exact ⟨C', h1, h2.trans hf1, h3.trans hlen, h4, h5⟩

theorem fold_agree (m : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, m ∉ g.inputs) :
    ∀ a b : List Bool, a.length = b.length → (∀ i, i ≠ m → a.getD i false = b.getD i false) →
      (gs.foldl step a).length = (gs.foldl step b).length ∧
      ∀ i, i ≠ m → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
  induction gs with
  | nil => intro a b hl hab; exact ⟨hl, hab⟩
  | cons g gs ih =>
    intro a b hl hab
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false) := by
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hab i (fun e => hgs g (by simp) (e ▸ hi))
      intro i hi
      unfold step
      by_cases hia : i = a.length
      · subst hia
        rw [getD_append_singleton_last, hl, getD_append_singleton_last]
        exact hv
      · rw [getD_append_singleton _ _ _ hia, getD_append_singleton _ _ _ (by rw [← hl]; exact hia)]
        exact hab i hi

theorem set_unread_fun (n : ℕ) (C : Circuit) (h : ℕ) (X : Gate) (hh : h < C.gates.length)
    (hun : ∀ j < C.gates.length, n + h ∉ (gateAt C j).inputs) (ho : C.output ≠ n + h) :
    circuitFun n ⟨C.gates.set h X, C.output⟩ = circuitFun n C := by
  funext x
  unfold circuitFun Circuit.eval
  simp only [wires_eq]
  have hw0l : (List.ofFn x).length = n := by simp
  have hgk : C.gates[h]? = some C.gates[h] := List.getElem?_eq_getElem hh
  have hsk : (C.gates.set h X)[h]? = some X := by simp [List.getElem?_set, hh]
  rw [foldl_split C.gates h _ hgk, foldl_split (C.gates.set h X) h X hsk,
    List.take_set_of_le (le_refl h), List.drop_set_of_lt (Nat.lt_succ_self h)]
  have hl := take_fold_length C.gates h hh (List.ofFn x)
  set Wp := (C.gates.take h).foldl step (List.ofFn x)
  have hall : ∀ g ∈ C.gates.drop (h + 1), n + h ∉ g.inputs := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_drop hg)
    have := hun j hj
    rwa [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  have := fold_agree (n + h) _ hall (step Wp X) (step Wp C.gates[h]) (by simp [step]) (by
    intro i hi
    unfold step
    rw [getD_append_singleton _ _ _ (by omega), getD_append_singleton _ _ _ (by omega)])
  exact this.2 _ ho

theorem wires_gate (F : Circuit) (k : ℕ) (g : Gate) (hk : F.gates[k]? = some g) (w0 : List Bool)
    (hr : ∀ i ∈ g.inputs, i < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false =
      g.op.eval (g.inputs.map fun i => (F.wires w0).getD i false) := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega)]
  have hm : g.inputs.map (fun i => ((F.gates.drop (k + 1)).foldl step (step Wp g)).getD i false) =
      g.inputs.map fun i => Wp.getD i false := by
    apply List.map_congr_left
    intro i hi
    have := hr i hi
    rw [foldl_step_getD _ _ _ (by simp [step]; omega)]
    unfold step
    rw [getD_append_left _ _ _ (by omega)]
  rw [hm]
  unfold step
  rw [← hl, getD_append_singleton_last]

theorem del_AO (n k u : ℕ) (E : Circuit) (hE : IsAO2 n E) (hu : u < n + k) :
    IsAO2 n (del n k u E) := by
  refine ⟨fun g hg => ?_, del_readsBack n k u E hE.2.1 hu, fun g hg => ?_⟩
  · simp only [del, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rd] using hE.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · simp only [del, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rd] using hE.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

theorem gateAt_eq (D : Circuit) (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) : gateAt D j = g := by
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  rw [gateAt_some D j hj] at hg
  exact Option.some.inj hg

theorem least_noAndBelow (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hswap : SwapHyp) (D : Circuit) (hD : IsLeastAO G D) :
    ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true) := by
  intro h hh hand t ht hbelow
  obtain ⟨hAO, hF, hmin⟩ := hD
  have htl : t < n + h := hAO.2.1 h hh t ht
  have hw : ∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, n + h⟩ (List.ofFn x) = true →
      Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true := by
    intro x hx
    have hg := wires_gate D h (gateAt D h) (gateAt_some D h hh) (List.ofFn x)
      (by simpa using hAO.2.1 h hh)
    simp only [List.length_ofFn] at hg
    change (D.wires (List.ofFn x)).getD (n + h) false = true at hx
    change (D.wires (List.ofFn x)).getD t false = true
    rw [hg, hand] at hx
    simp only [GateOp.eval] at hx
    have := List.all_eq_true.mp hx _ (List.mem_map_of_mem ht)
    simpa using this
  set o' := if D.output = n + h then t else D.output with ho'
  set C1 : Circuit := ⟨D.gates, o'⟩ with hC1
  have hC1AO : IsAO2 n C1 := hAO
  have hC1f : circuitFun n C1 = circuitFun n D := by
    funext x
    by_cases ho : D.output = n + h
    · have e1 : circuitFun n C1 x = Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) := by
        simp only [circuitFun, hC1, ho', if_pos ho]
      have e2 : circuitFun n D x = Circuit.eval ⟨D.gates, n + h⟩ (List.ofFn x) := by
        simp only [circuitFun, Circuit.eval, ← ho]
      rw [e1, e2]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        have := hbelow x hx
        rw [← hF, e2] at this
        exact this
      · exact hw x
    · simp only [circuitFun, hC1, ho', if_neg ho]
  have hlen1 : C1.gates.length = D.gates.length := rfl
  obtain ⟨C2, hC2AO, hC2f, hC2l, hC2o, hC2un⟩ := swap_all n hswap h t htl _ C1 rfl hC1AO
    (fun x hx => hw x hx)
    (fun x hx => by rw [hC1f, hF]; exact hbelow x hx)
  have hh2 : h < C2.gates.length := by omega
  have ho2 : C2.output ≠ n + h := by
    rw [hC2o]
    show o' ≠ n + h
    by_cases ho : D.output = n + h
    · rw [ho', if_pos ho]; omega
    · rw [ho', if_neg ho]; exact ho
  set X : Gate := ⟨GateOp.and, [t, t]⟩ with hX
  set E : Circuit := ⟨C2.gates.set h X, C2.output⟩ with hE
  have hEAO : IsAO2 n E := isAO2_set n C2 _ h X hC2AO hh2 (Or.inl rfl) rfl
    (by intro i hi; simp [hX] at hi; omega)
  have hEf : circuitFun n E = circuitFun n C2 := set_unread_fun n C2 h X hh2 hC2un ho2
  have hEh : E.gates[h]? = some X := by simp [hE, List.getElem?_set, hh2]
  have hEl : E.gates.length = C2.gates.length := by simp [hE]
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + h) false = (E.wires (List.ofFn x)).getD t false := by
    intro x
    have := wires_gate E h X hEh (List.ofFn x) (by intro i hi; simp [hX] at hi; simp; omega)
    simp only [List.length_ofFn] at this
    rw [this]
    simp [hX, GateOp.eval]
  have hDf := del_fun n h t E (by omega) htl (readsBack_take n E hEAO.2.1 h) hcopy
  have hDl := del_length n h t E (by omega)
  have := hmin (del n h t E) (del_AO n h t E hEAO htl) (by rw [hDf, hEf, hC2f, hC1f, hF])
  simp only [Circuit.size] at this
  omega

theorem exists_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : IsAO2 n C) (hCF : circuitFun n C = graphFun G ∅) : ∃ D : Circuit, IsLeastAO G D := by
  classical
  have hex : ∃ s, ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = graphFun G ∅ ∧ C'.size = s :=
    ⟨_, C, hC, hCF, rfl⟩
  obtain ⟨D, hD1, hD2, hD3⟩ := Nat.find_spec hex
  refine ⟨D, hD1, hD2, fun C' h1 h2 => ?_⟩
  rw [hD3]
  exact Nat.find_min' hex ⟨C', h1, h2, rfl⟩

end PEqualNP.MetaComplexity.LiftFix
