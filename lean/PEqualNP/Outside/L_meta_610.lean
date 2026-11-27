import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta610

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk

private lemma prefix_inv {n : ℕ} (G : SimpleGraph (Fin n))
    (L : Finset (Fin n)) (S : Set ℕ) (x : Fin n → Bool)
    (y0 : Fin n → Bool) (yl : Fin n → Fin n → Bool)
    (hy0_spec : ∀ v : Fin n, v ∉ L → y0 v = true)
    (hyl_self : ∀ l ∈ L, yl l l = true)
    (hyl_other : ∀ l ∈ L, ∀ v : Fin n, v ∉ L → ¬ G.Adj v l → yl l v = true)
    (hNoEdge : ∀ u v : Fin n, G.Adj u v → ¬ (x u = true ∧ x v = true))
    (hSL : ∀ l ∈ L, l.val ∈ S)
    (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hSUp : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
      ∀ i ∈ g.inputs, i < n + j → i ∈ S → n + j ∈ S)
    (hSAnd : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and →
      ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j → ¬ (a ∈ S ∧ b ∈ S)) :
    ∀ k : ℕ,
      (gs.foldl wiresStep (List.ofFn x)).getD k false = true →
      (k ∉ S →
        (gs.foldl wiresStep (List.ofFn y0)).getD k false = true ∧
        ∀ l ∈ L, x l = true → (gs.foldl wiresStep (List.ofFn (yl l))).getD k false = true) ∧
      (((gs.foldl wiresStep (List.ofFn y0)).getD k false = true ∧
        ∀ l ∈ L, x l = true → (gs.foldl wiresStep (List.ofFn (yl l))).getD k false = true) ∨
       (∃ l ∈ L, x l = true ∧ (gs.foldl wiresStep (List.ofFn (yl l))).getD k false = true)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp only [List.foldl_nil] at hk ⊢
    by_cases hlt : k < n
    · rw [getD_ofFn x k hlt] at hk
      by_cases hmem : (⟨k, hlt⟩ : Fin n) ∈ L
      · have hkS : k ∈ S := hSL ⟨k, hlt⟩ hmem
        refine ⟨fun hnot => False.elim (hnot hkS), Or.inr ⟨⟨k, hlt⟩, hmem, hk, ?_⟩⟩
        rw [getD_ofFn (yl ⟨k, hlt⟩) k hlt]
        exact hyl_self ⟨k, hlt⟩ hmem
      · have hP : (List.ofFn y0).getD k false = true ∧
            ∀ l ∈ L, x l = true → (List.ofFn (yl l)).getD k false = true := by
          refine ⟨by rw [getD_ofFn y0 k hlt]; exact hy0_spec ⟨k, hlt⟩ hmem, ?_⟩
          intro l hl hxl
          rw [getD_ofFn (yl l) k hlt]
          have hna : ¬ G.Adj ⟨k, hlt⟩ l := fun hadj => hNoEdge ⟨k, hlt⟩ l hadj ⟨hk, hxl⟩
          exact hyl_other l hl ⟨k, hlt⟩ hmem hna
        exact ⟨fun _ => hP, Or.inl hP⟩
    · have hge : (List.ofFn x).length ≤ k := by rw [List.length_ofFn]; omega
      rw [getD_ge_length _ k hge] at hk
      cases hk
  | append_singleton gs g ih =>
    have hM_pre : ∀ g' ∈ gs,
        g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (List.mem_append_left [g] hg')
    have hSUp_pre : ∀ (j : ℕ) (g' : Gate), gs[j]? = some g' →
        ∀ i ∈ g'.inputs, i < n + j → i ∈ S → n + j ∈ S := by
      intro j g' hget i hi hilt hiS
      have hj : j < gs.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hget
        cases hget
      have hget' : (gs ++ [g])[j]? = some g' := by
        rw [List.getElem?_append_left hj]
        exact hget
      exact hSUp j g' hget' i hi hilt hiS
    have hSAnd_pre : ∀ (j : ℕ) (g' : Gate), gs[j]? = some g' → g'.op = GateOp.and →
        ∀ a b : ℕ, g'.inputs = [a, b] → a < n + j → b < n + j → ¬ (a ∈ S ∧ b ∈ S) := by
      intro j g' hget hop a b hab ha hb
      have hj : j < gs.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hget
        cases hget
      have hget' : (gs ++ [g])[j]? = some g' := by
        rw [List.getElem?_append_left hj]
        exact hget
      exact hSAnd j g' hget' hop a b hab ha hb
    have ih' := ih hM_pre hSUp_pre hSAnd_pre
    have hlen_w : ∀ z : Fin n → Bool,
        (gs.foldl wiresStep (List.ofFn z)).length = n + gs.length := by
      intro z
      rw [foldl_wiresStep_length, List.length_ofFn]
    have hget_last : (gs ++ [g])[gs.length]? = some g := by
      simp [List.getElem?_append_right (le_refl gs.length)]
    have hW_lt : ∀ (z : Fin n → Bool) (k : ℕ), k < n + gs.length →
        ((gs ++ [g]).foldl wiresStep (List.ofFn z)).getD k false =
        (gs.foldl wiresStep (List.ofFn z)).getD k false := by
      intro z k hk
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlt : k < (gs.foldl wiresStep (List.ofFn z)).length := by
        rw [hlen_w z]; exact hk
      simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    have hW_eq : ∀ z : Fin n → Bool,
        ((gs ++ [g]).foldl wiresStep (List.ofFn z)).getD (n + gs.length) false =
        g.op.eval (g.inputs.map fun i => (gs.foldl wiresStep (List.ofFn z)).getD i false) := by
      intro z
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, wiresStep]
      exact getD_append_last_eq _ _ (n + gs.length) (hlen_w z)
    have htrue_lt : ∀ i : ℕ,
        (gs.foldl wiresStep (List.ofFn x)).getD i false = true → i < n + gs.length := by
      intro i hi
      by_contra hge
      have hle : (gs.foldl wiresStep (List.ofFn x)).length ≤ i := by
        rw [hlen_w x]; omega
      rw [getD_ge_length _ i hle] at hi
      cases hi
    intro k hk
    by_cases hlt : k < n + gs.length
    · rw [hW_lt x k hlt] at hk
      rw [hW_lt y0 k hlt]
      simp only [hW_lt _ k hlt]
      exact ih' k hk
    · by_cases heq : k = n + gs.length
      · subst heq
        rw [hW_eq x] at hk
        rw [hW_eq y0]
        simp only [hW_eq]
        have hgM := hM g (List.mem_append_right gs List.mem_cons_self)
        have hglen : g.inputs.length ≤ 2 := hgM.2
        have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgM.1
        rcases hgop with hand | hor
        · rw [hand] at hk ⊢
          rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
          · have hP : GateOp.and.eval (List.map (fun i => (gs.foldl wiresStep (List.ofFn y0)).getD i false) []) = true ∧
                ∀ l ∈ L, x l = true →
                  GateOp.and.eval (List.map (fun i => (gs.foldl wiresStep (List.ofFn (yl l))).getD i false) []) = true := by
              simp [GateOp.eval]
            exact ⟨fun _ => hP, Or.inl hP⟩
          · rw [hli] at hk
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true] at hk ⊢
            have ha_lt : a < n + gs.length := htrue_lt a hk
            have ha_mem : a ∈ g.inputs := by rw [hli]; exact List.mem_cons_self
            obtain ⟨ha1, ha2⟩ := ih' a hk
            refine ⟨fun hnot => ha1 (fun haS => hnot (hSUp gs.length g hget_last a ha_mem ha_lt haS)), ha2⟩
          · rw [hli] at hk
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hk ⊢
            obtain ⟨hxa, hxb⟩ := hk
            have ha_lt : a < n + gs.length := htrue_lt a hxa
            have hb_lt : b < n + gs.length := htrue_lt b hxb
            have ha_mem : a ∈ g.inputs := by rw [hli]; exact List.mem_cons_self
            have hb_mem : b ∈ g.inputs := by rw [hli]; exact List.mem_cons_of_mem a List.mem_cons_self
            obtain ⟨ha1, ha2⟩ := ih' a hxa
            obtain ⟨hb1, hb2⟩ := ih' b hxb
            constructor
            · intro hnot
              have ha_not : a ∉ S := fun haS => hnot (hSUp gs.length g hget_last a ha_mem ha_lt haS)
              have hb_not : b ∉ S := fun hbS => hnot (hSUp gs.length g hget_last b hb_mem hb_lt hbS)
              obtain ⟨ha_y0, ha_yl⟩ := ha1 ha_not
              obtain ⟨hb_y0, hb_yl⟩ := hb1 hb_not
              exact ⟨⟨ha_y0, hb_y0⟩, fun l hl hxl => ⟨ha_yl l hl hxl, hb_yl l hl hxl⟩⟩
            · have hnotboth : ¬ (a ∈ S ∧ b ∈ S) :=
                hSAnd gs.length g hget_last hand a b hli ha_lt hb_lt
              by_cases haS : a ∈ S
              · have hb_not : b ∉ S := fun hbS => hnotboth ⟨haS, hbS⟩
                obtain ⟨hb_y0, hb_yl⟩ := hb1 hb_not
                rcases ha2 with ⟨ha_y0, ha_yl⟩ | ⟨l, hl, hxl, ha_l⟩
                · exact Or.inl ⟨⟨ha_y0, hb_y0⟩, fun l hl hxl => ⟨ha_yl l hl hxl, hb_yl l hl hxl⟩⟩
                · exact Or.inr ⟨l, hl, hxl, ha_l, hb_yl l hl hxl⟩
              · obtain ⟨ha_y0, ha_yl⟩ := ha1 haS
                rcases hb2 with ⟨hb_y0, hb_yl⟩ | ⟨l, hl, hxl, hb_l⟩
                · exact Or.inl ⟨⟨ha_y0, hb_y0⟩, fun l hl hxl => ⟨ha_yl l hl hxl, hb_yl l hl hxl⟩⟩
                · exact Or.inr ⟨l, hl, hxl, ha_yl l hl hxl, hb_l⟩
          · rw [hli] at hglen; simp at hglen
        · rw [hor] at hk ⊢
          rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
          · rw [hli] at hk; simp [GateOp.eval] at hk
          · rw [hli] at hk
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false] at hk ⊢
            have ha_lt : a < n + gs.length := htrue_lt a hk
            have ha_mem : a ∈ g.inputs := by rw [hli]; exact List.mem_cons_self
            obtain ⟨ha1, ha2⟩ := ih' a hk
            refine ⟨fun hnot => ha1 (fun haS => hnot (hSUp gs.length g hget_last a ha_mem ha_lt haS)), ha2⟩
          · rw [hli] at hk
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true] at hk ⊢
            rcases hk with hxa | hxb
            · have ha_lt : a < n + gs.length := htrue_lt a hxa
              have ha_mem : a ∈ g.inputs := by rw [hli]; exact List.mem_cons_self
              obtain ⟨ha1, ha2⟩ := ih' a hxa
              constructor
              · intro hnot
                have ha_not : a ∉ S := fun haS => hnot (hSUp gs.length g hget_last a ha_mem ha_lt haS)
                obtain ⟨ha_y0, ha_yl⟩ := ha1 ha_not
                exact ⟨Or.inl ha_y0, fun l hl hxl => Or.inl (ha_yl l hl hxl)⟩
              · rcases ha2 with ⟨ha_y0, ha_yl⟩ | ⟨l, hl, hxl, ha_l⟩
                · exact Or.inl ⟨Or.inl ha_y0, fun l hl hxl => Or.inl (ha_yl l hl hxl)⟩
                · exact Or.inr ⟨l, hl, hxl, Or.inl ha_l⟩
            · have hb_lt : b < n + gs.length := htrue_lt b hxb
              have hb_mem : b ∈ g.inputs := by rw [hli]; exact List.mem_cons_of_mem a List.mem_cons_self
              obtain ⟨hb1, hb2⟩ := ih' b hxb
              constructor
              · intro hnot
                have hb_not : b ∉ S := fun hbS => hnot (hSUp gs.length g hget_last b hb_mem hb_lt hbS)
                obtain ⟨hb_y0, hb_yl⟩ := hb1 hb_not
                exact ⟨Or.inr hb_y0, fun l hl hxl => Or.inr (hb_yl l hl hxl)⟩
              · rcases hb2 with ⟨hb_y0, hb_yl⟩ | ⟨l, hl, hxl, hb_l⟩
                · exact Or.inl ⟨Or.inr hb_y0, fun l hl hxl => Or.inr (hb_yl l hl hxl)⟩
                · exact Or.inr ⟨l, hl, hxl, Or.inr hb_l⟩
          · rw [hli] at hglen; simp at hglen
      · have hge : ((gs ++ [g]).foldl wiresStep (List.ofFn x)).length ≤ k := by
          rw [foldl_wiresStep_length, List.length_ofFn, List.length_append, List.length_cons,
            List.length_nil]
          omega
        rw [getD_ge_length _ k hge] at hk
        cases hk

end PEqualNP.Outside.LMeta610

theorem PEqualNP.Outside.L_meta_610 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (L : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → (u ∈ L ↔ v ∉ L)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∃ S : Set ℕ, (∀ l ∈ L, l.val ∈ S) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j → i ∈ S → n + j ∈ S) ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ a b : ℕ, g.inputs = [a, b] → a < n + j → b < n + j → ¬ (a ∈ S ∧ b ∈ S))) → (∀ u v : Fin n, G.Adj u v → C.eval (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))) = true) → C.eval (List.ofFn (fun i : Fin n => decide (i ∉ L))) = false → (∀ l ∈ L, C.eval (List.ofFn (fun i : Fin n => decide (i = l ∨ (i ∉ L ∧ ¬ G.Adj i l)))) = false) → ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro n G _ L _ C hM hS hEdge hY0 hYl x
  constructor
  · intro hC
    by_contra hNo
    have hNoEdge : ∀ u v : Fin n, G.Adj u v → ¬ (x u = true ∧ x v = true) := by
      intro u v hadj ⟨hu, hv⟩
      exact hNo ⟨u, v, hadj, hu, hv⟩
    obtain ⟨S, hSL, hSUp, hSAnd⟩ := hS
    have hinv := PEqualNP.Outside.LMeta610.prefix_inv G L S x
      (fun i : Fin n => decide (i ∉ L))
      (fun l i : Fin n => decide (i = l ∨ (i ∉ L ∧ ¬ G.Adj i l)))
      (fun v hv => by simp [hv])
      (fun l _ => by simp)
      (fun l _ v hv hna => by simp [hv, hna])
      hNoEdge hSL C.gates hM hSUp hSAnd C.output hC
    rcases hinv.2 with ⟨hy0t, _⟩ | ⟨l, hl, _, hylt⟩
    · have hf : (C.gates.foldl PEqualNP.Outside.LMeta610.wiresStep
          (List.ofFn (fun i : Fin n => decide (i ∉ L)))).getD C.output false = false := hY0
      rw [hy0t] at hf
      cases hf
    · have hf : (C.gates.foldl PEqualNP.Outside.LMeta610.wiresStep
          (List.ofFn (fun i : Fin n => decide (i = l ∨ (i ∉ L ∧ ¬ G.Adj i l))))).getD C.output false = false := hYl l hl
      rw [hylt] at hf
      cases hf
  · rintro ⟨u, v, hadj, hxu, hxv⟩
    have hMon : ∀ g ∈ C.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) :=
      fun g hg => (hM g hg).1
    have he := hEdge u v hadj
    refine PEqualNP.Outside.LMeta610.monotone_foldl_wiresStep C.gates hMon
      (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))) (List.ofFn x)
      (by simp) ?_ C.output he
    intro k hk
    by_cases hlt : k < n
    · rw [PEqualNP.Outside.LMeta610.getD_ofFn _ k hlt] at hk ⊢
      simp only [decide_eq_true_eq] at hk
      rcases hk with hku | hkv
      · rw [hku]; exact hxu
      · rw [hkv]; exact hxv
    · have hge : (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))).length ≤ k := by
        rw [List.length_ofFn]; omega
      rw [PEqualNP.Outside.LMeta610.getD_ge_length _ k hge] at hk
      cases hk
