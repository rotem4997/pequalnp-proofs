import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6060_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

private def circuitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wireFun {α : Type} (inps : List (α → Bool)) (gs : List Gate) (i : ℕ) : α → Bool :=
  fun a => (gs.foldl circuitStep (inps.map fun f => f a)).getD i false

private def notCnt (gs : List Gate) : ℕ :=
  (gs.filter fun g => decide (g.op = GateOp.not)).length

private def baseAllow {α : Type} (inps : List (α → Bool)) (L : List (α → Bool)) (f : α → Bool) : Prop :=
  (f = fun _ => Bool.false) ∨ (f = fun _ => Bool.true) ∨ f ∈ inps ∨ f ∈ L

private def allow {α : Type} (inps : List (α → Bool)) (x5 : List (α → Bool))
    (L : List (α → Bool)) (f : α → Bool) : Prop :=
  baseAllow inps L f ∨ ∃ h ∈ x5, baseAllow inps L h ∧ f = fun a => !h a

private lemma baseAllow_mono {α : Type} {inps L₁ L₂ : List (α → Bool)}
    (hsub : ∀ f ∈ L₁, f ∈ L₂) {f : α → Bool} (hf : baseAllow inps L₁ f) :
    baseAllow inps L₂ f := by
  rcases hf with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (hsub f h)))

private lemma allow_mono_x5 {α : Type} {inps x5₁ x5₂ L : List (α → Bool)}
    (hsub : ∀ h ∈ x5₁, h ∈ x5₂) {f : α → Bool} (hf : allow inps x5₁ L f) :
    allow inps x5₂ L f := by
  rcases hf with hb | ⟨h, hmem, hb, heq⟩
  · exact Or.inl hb
  · exact Or.inr ⟨h, hsub h hmem, hb, heq⟩

private lemma allow_mono_L {α : Type} {inps x5 L₁ L₂ : List (α → Bool)}
    (hsub : ∀ f ∈ L₁, f ∈ L₂) {f : α → Bool} (hf : allow inps x5 L₁ f) :
    allow inps x5 L₂ f := by
  rcases hf with hb | ⟨h, hmem, hb, heq⟩
  · exact Or.inl (baseAllow_mono hsub hb)
  · exact Or.inr ⟨h, hmem, baseAllow_mono hsub hb, heq⟩

private lemma foldl_circuitStep_len (gs : List Gate) (w : List Bool) :
    (gs.foldl circuitStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [circuitStep]; omega

private lemma getD_snoc_lt {β : Type*} (l : List β) (v d : β) (i : ℕ) (hi : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {β : Type*} (l : List β) (v d : β) :
    (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_snoc_gt {β : Type*} (l : List β) (v d : β) (i : ℕ) (hi : l.length < i) :
    (l ++ [v]).getD i d = d := by
  apply List.getD_eq_default
  simp only [List.length_append, List.length_singleton]
  omega

private lemma notCnt_snoc (gs : List Gate) (g : Gate) :
    notCnt (gs ++ [g]) = notCnt gs + if g.op = GateOp.not then 1 else 0 := by
  unfold notCnt
  rw [List.filter_append, List.length_append]
  by_cases h : g.op = GateOp.not
  · simp [h]
  · simp [h]

private lemma wireFun_snoc_lt {α : Type} (inps : List (α → Bool)) (gs : List Gate) (g : Gate)
    (i : ℕ) (hi : i < inps.length + gs.length) :
    wireFun inps (gs ++ [g]) i = wireFun inps gs i := by
  funext a
  unfold wireFun
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp only [circuitStep]
  exact getD_snoc_lt _ _ false i (by rw [foldl_circuitStep_len, List.length_map]; exact hi)

private lemma wireFun_snoc_gt {α : Type} (inps : List (α → Bool)) (gs : List Gate) (g : Gate)
    (i : ℕ) (hi : inps.length + gs.length < i) :
    wireFun inps (gs ++ [g]) i = fun _ => Bool.false := by
  funext a
  unfold wireFun
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp only [circuitStep]
  exact getD_snoc_gt _ _ false i (by rw [foldl_circuitStep_len, List.length_map]; exact hi)

private lemma wireFun_snoc_eq {α : Type} (inps : List (α → Bool)) (gs : List Gate) (g : Gate) :
    wireFun inps (gs ++ [g]) (inps.length + gs.length) =
      fun a => g.op.eval (g.inputs.map fun w => wireFun inps gs w a) := by
  funext a
  unfold wireFun
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp only [circuitStep]
  have hlen : (gs.foldl circuitStep (inps.map fun f => f a)).length = inps.length + gs.length := by
    rw [foldl_circuitStep_len, List.length_map]
  rw [← hlen, getD_snoc_eq]

private lemma compile_gates {α : Type} (inps : List (α → Bool)) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ (x5 x6 : List (α → Bool)),
      x5.length ≤ notCnt gs ∧
      x6.length + notCnt gs ≤ gs.length ∧
      x6.Nodup ∧
      (∀ f ∈ x6, ∃ (L1 L2 : List (α → Bool)), x6 = L1 ++ f :: L2 ∧
        ∃ (u v : α → Bool), allow inps x5 L1 u ∧ allow inps x5 L1 v ∧
          ((f = fun a => u a && v a) ∨ (f = fun a => u a || v a))) ∧
      (∀ i : ℕ, allow inps x5 x6 (wireFun inps gs i)) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], [], by simp [notCnt], by simp [notCnt], List.nodup_nil, by simp, ?_⟩
    intro i
    apply Or.inl
    by_cases hi : i < inps.length
    · refine Or.inr (Or.inr (Or.inl ?_))
      have heq : wireFun inps [] i = inps[i] := by
        funext a
        unfold wireFun
        rw [List.foldl_nil, List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map]
      rw [heq]
      exact List.getElem_mem hi
    · refine Or.inl ?_
      funext a
      unfold wireFun
      rw [List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp; omega)
  | append_singleton gs g ih =>
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left [g] hg')
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hfan g (List.mem_append_right gs List.mem_cons_self)
    obtain ⟨x5, x6, hx5_len, hx6_len, hnodup, hstep, hwires⟩ := ih hgs
    have hreuse : ∀ (f_new : α → Bool),
        f_new = wireFun inps (gs ++ [g]) (inps.length + gs.length) →
        allow inps x5 x6 f_new →
        ∃ (x5' x6' : List (α → Bool)),
          x5'.length ≤ notCnt (gs ++ [g]) ∧
          x6'.length + notCnt (gs ++ [g]) ≤ (gs ++ [g]).length ∧
          x6'.Nodup ∧
          (∀ f ∈ x6', ∃ (L1 L2 : List (α → Bool)), x6' = L1 ++ f :: L2 ∧
            ∃ (u v : α → Bool), allow inps x5' L1 u ∧ allow inps x5' L1 v ∧
              ((f = fun a => u a && v a) ∨ (f = fun a => u a || v a))) ∧
          (∀ i : ℕ, allow inps x5' x6' (wireFun inps (gs ++ [g]) i)) := by
      intro f_new hf_eq hall
      refine ⟨x5, x6, ?_, ?_, hnodup, hstep, ?_⟩
      · rw [notCnt_snoc]; split <;> omega
      · rw [notCnt_snoc, List.length_append, List.length_singleton]; split <;> omega
      · intro i
        rcases lt_trichotomy i (inps.length + gs.length) with hlt | rfl | hgt
        · rw [wireFun_snoc_lt inps gs g i hlt]; exact hwires i
        · rw [← hf_eq]; exact hall
        · rw [wireFun_snoc_gt inps gs g i hgt]; exact Or.inl (Or.inl rfl)
    rcases g with ⟨op, ins⟩
    rcases hg with ⟨hop, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · -- AND
      rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · apply hreuse (fun _ => Bool.true)
        · rw [wireFun_snoc_eq]; funext a; rfl
        · exact Or.inl (Or.inr (Or.inl rfl))
      · apply hreuse (wireFun inps gs u)
        · rw [wireFun_snoc_eq]; funext a; simp [GateOp.eval]
        · exact hwires u
      · let f_new : α → Bool := fun a => wireFun inps gs u a && wireFun inps gs v a
        have hf_eq : f_new = wireFun inps (gs ++ [⟨GateOp.and, [u, v]⟩]) (inps.length + gs.length) := by
          rw [wireFun_snoc_eq]; funext a; simp [f_new, GateOp.eval]
        by_cases hmem : f_new ∈ x6
        · exact hreuse f_new hf_eq (Or.inl (Or.inr (Or.inr (Or.inr hmem))))
        · refine ⟨x5, x6 ++ [f_new], ?_, ?_, ?_, ?_, ?_⟩
          · rw [notCnt_snoc]; simp; exact hx5_len
          · rw [notCnt_snoc, List.length_append, List.length_singleton, List.length_append, List.length_singleton]
            simp; omega
          · rw [List.nodup_append]
            refine ⟨hnodup, List.nodup_singleton f_new, ?_⟩
            intro a ha b hb hab
            simp only [List.mem_singleton] at hb
            subst hb; subst hab
            exact hmem ha
          · intro f hf
            rw [List.mem_append, List.mem_singleton] at hf
            rcases hf with hfold | rfl
            · obtain ⟨L1, L2, hL, u', v', hu', hv', hop'⟩ := hstep f hfold
              refine ⟨L1, L2 ++ [f_new], ?_, u', v', hu', hv', hop'⟩
              rw [hL, List.append_assoc, List.cons_append]
            · exact ⟨x6, [], rfl, wireFun inps gs u, wireFun inps gs v,
                hwires u, hwires v, Or.inl rfl⟩
          · intro i
            rcases lt_trichotomy i (inps.length + gs.length) with hlt | rfl | hgt
            · rw [wireFun_snoc_lt inps gs _ i hlt]
              exact allow_mono_L (fun f hf => List.mem_append_left [f_new] hf) (hwires i)
            · rw [← hf_eq]
              exact Or.inl (Or.inr (Or.inr (Or.inr (List.mem_append_right x6 List.mem_cons_self))))
            · rw [wireFun_snoc_gt inps gs _ i hgt]
              exact Or.inl (Or.inl rfl)
      · simp at hlen
    · -- OR
      rcases ins with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · apply hreuse (fun _ => Bool.false)
        · rw [wireFun_snoc_eq]; funext a; rfl
        · exact Or.inl (Or.inl rfl)
      · apply hreuse (wireFun inps gs u)
        · rw [wireFun_snoc_eq]; funext a; simp [GateOp.eval]
        · exact hwires u
      · let f_new : α → Bool := fun a => wireFun inps gs u a || wireFun inps gs v a
        have hf_eq : f_new = wireFun inps (gs ++ [⟨GateOp.or, [u, v]⟩]) (inps.length + gs.length) := by
          rw [wireFun_snoc_eq]; funext a; simp [f_new, GateOp.eval]
        by_cases hmem : f_new ∈ x6
        · exact hreuse f_new hf_eq (Or.inl (Or.inr (Or.inr (Or.inr hmem))))
        · refine ⟨x5, x6 ++ [f_new], ?_, ?_, ?_, ?_, ?_⟩
          · rw [notCnt_snoc]; simp; exact hx5_len
          · rw [notCnt_snoc, List.length_append, List.length_singleton, List.length_append, List.length_singleton]
            simp; omega
          · rw [List.nodup_append]
            refine ⟨hnodup, List.nodup_singleton f_new, ?_⟩
            intro a ha b hb hab
            simp only [List.mem_singleton] at hb
            subst hb; subst hab
            exact hmem ha
          · intro f hf
            rw [List.mem_append, List.mem_singleton] at hf
            rcases hf with hfold | rfl
            · obtain ⟨L1, L2, hL, u', v', hu', hv', hop'⟩ := hstep f hfold
              refine ⟨L1, L2 ++ [f_new], ?_, u', v', hu', hv', hop'⟩
              rw [hL, List.append_assoc, List.cons_append]
            · exact ⟨x6, [], rfl, wireFun inps gs u, wireFun inps gs v,
                hwires u, hwires v, Or.inr rfl⟩
          · intro i
            rcases lt_trichotomy i (inps.length + gs.length) with hlt | rfl | hgt
            · rw [wireFun_snoc_lt inps gs _ i hlt]
              exact allow_mono_L (fun f hf => List.mem_append_left [f_new] hf) (hwires i)
            · rw [← hf_eq]
              exact Or.inl (Or.inr (Or.inr (Or.inr (List.mem_append_right x6 List.mem_cons_self))))
            · rw [wireFun_snoc_gt inps gs _ i hgt]
              exact Or.inl (Or.inl rfl)
      · simp at hlen
    · -- NOT
      rcases ins with _ | ⟨u, rest⟩
      · apply hreuse (fun _ => Bool.true)
        · rw [wireFun_snoc_eq]; funext a; rfl
        · exact Or.inl (Or.inr (Or.inl rfl))
      · let fu : α → Bool := wireFun inps gs u
        let f_new : α → Bool := fun a => !fu a
        have hf_eq : f_new = wireFun inps (gs ++ [⟨GateOp.not, u :: rest⟩]) (inps.length + gs.length) := by
          rw [wireFun_snoc_eq]; funext a; simp [f_new, fu, GateOp.eval]
        rcases hwires u with hbase | ⟨h, hhmem, hhb, hheq⟩
        · -- fu is in baseAllow inps x6; add fu to x5
          refine ⟨fu :: x5, x6, ?_, ?_, hnodup, ?_, ?_⟩
          · rw [notCnt_snoc]; simp; omega
          · rw [notCnt_snoc, List.length_append, List.length_singleton]; simp; omega
          · intro f hf
            obtain ⟨L1, L2, hL, u', v', hu', hv', hop'⟩ := hstep f hf
            exact ⟨L1, L2, hL, u', v',
              allow_mono_x5 (fun w hw => List.mem_cons_of_mem fu hw) hu',
              allow_mono_x5 (fun w hw => List.mem_cons_of_mem fu hw) hv', hop'⟩
          · intro i
            rcases lt_trichotomy i (inps.length + gs.length) with hlt | rfl | hgt
            · rw [wireFun_snoc_lt inps gs _ i hlt]
              exact allow_mono_x5 (fun w hw => List.mem_cons_of_mem fu hw) (hwires i)
            · rw [← hf_eq]
              exact Or.inr ⟨fu, List.mem_cons_self, hbase, rfl⟩
            · rw [wireFun_snoc_gt inps gs _ i hgt]
              exact Or.inl (Or.inl rfl)
        · -- fu = !h with baseAllow inps x6 h, so f_new = !!h = h!
          have hfn : f_new = h := by
            funext a
            dsimp only [f_new, fu]
            rw [hheq]
            simp
          apply hreuse f_new hf_eq
          rw [hfn]
          exact Or.inl hhb

end PEqualNP.Outside.L_meta_6060_aux

theorem PEqualNP.Outside.L_meta_6060 :
    ∀ (x1 : Type) (x2 : List (x1 → Bool)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
        ∃ (x5 : List (x1 → Bool)) (x6 : List (x1 → Bool)),
          x5.length ≤ PEqualNP.NotBracket.notCount x3 ∧
            x6.length + PEqualNP.NotBracket.notCount x3 ≤ x3.size ∧
              x6.Nodup ∧
                have x7 : List (x1 → Bool) → (x1 → Bool) → Prop := fun (x7 : List (x1 → Bool)) (x8 : x1 → Bool) => (x8 = fun (x9 : x1) => Bool.false) ∨ (x8 = fun (x9 : x1) => Bool.true) ∨ x8 ∈ x2 ∨ x8 ∈ x7;
                have x8 : List (x1 → Bool) → (x1 → Bool) → Prop := fun (x8 : List (x1 → Bool)) (x9 : x1 → Bool) => x7 x8 x9 ∨ ∃ x10 ∈ x5, x7 x8 x10 ∧ x9 = fun (x11 : x1) => !x10 x11;
                (∀ x9 ∈ x6, ∃ (x11 : List (x1 → Bool)) (x12 : List (x1 → Bool)), x6 = x11 ++ x9 :: x12 ∧ ∃ (x13 : x1 → Bool) (x14 : x1 → Bool), x8 x11 x13 ∧ x8 x11 x14 ∧ ((x9 = fun (x15 : x1) => x13 x15 && x14 x15) ∨ x9 = fun (x15 : x1) => x13 x15 || x14 x15)) ∧ x8 x6 fun (x9 : x1) => x3.eval (List.map (fun (x10 : x1 → Bool) => x10 x9) x2) := by
  intro x1 x2 x3 hfan
  obtain ⟨x5, x6, hx5, hx6, hnd, hstep, hwires⟩ :=
    PEqualNP.Outside.L_meta_6060_aux.compile_gates x2 x3.gates hfan
  refine ⟨x5, x6, hx5, hx6, hnd, ?_⟩
  exact ⟨hstep, hwires x3.output⟩
