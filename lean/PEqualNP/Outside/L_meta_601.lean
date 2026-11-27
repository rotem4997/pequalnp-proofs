import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_601

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

private lemma runWires_nil (x : List Bool) : runWires [] x = x := rfl

private lemma runWires_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    runWires (gs ++ [g]) x = stepWire (runWires gs x) g := by
  simp [runWires]

private lemma runWires_length (gs : List Gate) (x : List Bool) :
    (runWires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runWires]
  | append_singleton gs g ih =>
    rw [runWires_append_singleton, stepWire, List.length_append, List.length_singleton, ih]
    simp [Nat.add_assoc]

private lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [if_pos rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [if_neg h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

private def zeroInput (n : ℕ) : List Bool :=
  List.ofFn (fun _ : Fin n => false)

private def unitInput (n : ℕ) (u : Fin n) : List Bool :=
  List.ofFn (fun w : Fin n => decide (w = u))

private lemma getD_zeroInput (n i : ℕ) : (zeroInput n).getD i false = false := by
  rw [zeroInput, List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_ofFn]
    simp [h]
  · rw [List.getElem?_eq_none]
    · rfl
    · simpa using (not_lt.mp h)

private lemma getD_unitInput_eq_true (n : ℕ) (u : Fin n) (i : ℕ)
    (h : (unitInput n u).getD i false = true) : i = u.val := by
  rw [unitInput, List.getD_eq_getElem?_getD] at h
  by_cases hi : i < n
  · rw [List.getElem?_ofFn] at h
    simp only [hi, dite_true, Option.getD_some, decide_eq_true_eq] at h
    exact congrArg Fin.val h
  · rw [List.getElem?_eq_none (by simpa using not_lt.mp hi)] at h
    simp at h

private lemma card_image_merge {α : Type*} [DecidableEq α]
    (D : Finset α) (color : α → ℕ) (c1 c2 : ℕ) :
    (D.image color).card ≤
      (D.image (fun x => if color x = c2 then c1 else color x)).card + 1 := by
  classical
  let color' := fun x => if color x = c2 then c1 else color x
  have hsub : D.image color ⊆ insert c2 (D.image color') := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_cases h : color x = c2
    · rw [h]
      exact Finset.mem_insert_self c2 _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨x, hx, by simp [color', h]⟩
  calc
    (D.image color).card ≤ (insert c2 (D.image color')).card := Finset.card_le_card hsub
    _ ≤ (D.image color').card + 1 := Finset.card_insert_le _ _

private lemma exists_coloring (n : ℕ) (D : Finset (Fin n)) (A : Finset ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.or → j ∈ A) :
    ∃ color : Fin n → ℕ,
      D.card ≤ (D.image color).card + (A ∩ Finset.range gs.length).card ∧
      ∀ (i : ℕ), (runWires gs (zeroInput n)).getD i false = false →
        ∀ u ∈ D, ∀ v ∈ D,
          (runWires gs (unitInput n u)).getD i false = true →
          (runWires gs (unitInput n v)).getD i false = true →
          color u = color v := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun u => u.val, ?_, ?_⟩
    · have hinj : Function.Injective (fun u : Fin n => u.val) := Fin.val_injective
      rw [Finset.card_image_of_injective D hinj]
      simp
    · intro i _ u _ v _ hu hv
      rw [runWires_nil] at hu hv
      have hu' := getD_unitInput_eq_true n u i hu
      have hv' := getD_unitInput_eq_true n v i hv
      exact hu'.symm.trans hv'
  | append_singleton gs g ih =>
    have hmono_gs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have hA_gs : ∀ (j : ℕ) (g' : Gate), gs[j]? = some g' → g'.op = GateOp.or → j ∈ A := by
      intro j g' hj hop
      have hlt : j < gs.length := by
        by_contra h
        rw [List.getElem?_eq_none (not_lt.mp h)] at hj
        simp at hj
      apply hA j g' _ hop
      rwa [List.getElem?_append_left hlt]
    obtain ⟨color, hcard, hinv⟩ := ih hmono_gs hA_gs
    have hg_mono := hmono g (List.mem_append_right _ (List.mem_singleton_self g))
    have hlen0 : (runWires gs (zeroInput n)).length = n + gs.length := by
      rw [runWires_length, zeroInput, List.length_ofFn]
    have hlenu (u : Fin n) : (runWires gs (unitInput n u)).length = n + gs.length := by
      rw [runWires_length, unitInput, List.length_ofFn]
    have hrange_mono : (A ∩ Finset.range gs.length).card ≤
        (A ∩ Finset.range (gs ++ [g]).length).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_inter.mp hx with ⟨hxA, hxr⟩
      rw [Finset.mem_range] at hxr
      exact Finset.mem_inter.mpr ⟨hxA, Finset.mem_range.mpr (by simp; omega)⟩
    have hold : ∀ (i : ℕ), i < n + gs.length →
        (runWires (gs ++ [g]) (zeroInput n)).getD i false =
          (runWires gs (zeroInput n)).getD i false := by
      intro i hi
      rw [runWires_append_singleton, stepWire, getD_append_singleton, hlen0, ite_eq_left_iff]
      intro h; exact False.elim (h hi)
    have holdu (u : Fin n) (i : ℕ) (hi : i < n + gs.length) :
        (runWires (gs ++ [g]) (unitInput n u)).getD i false =
          (runWires gs (unitInput n u)).getD i false := by
      rw [runWires_append_singleton, stepWire, getD_append_singleton, hlenu u, ite_eq_left_iff]
      intro h; exact False.elim (h hi)
    have hnew0 : (runWires (gs ++ [g]) (zeroInput n)).getD (n + gs.length) false =
        g.op.eval (g.inputs.map fun k => (runWires gs (zeroInput n)).getD k false) := by
      rw [runWires_append_singleton, stepWire, getD_append_singleton, hlen0]
      simp
    have hnewu (u : Fin n) : (runWires (gs ++ [g]) (unitInput n u)).getD (n + gs.length) false =
        g.op.eval (g.inputs.map fun k => (runWires gs (unitInput n u)).getD k false) := by
      rw [runWires_append_singleton, stepWire, getD_append_singleton, hlenu u]
      simp
    have hgtu (u : Fin n) (i : ℕ) (hi : n + gs.length < i) :
        (runWires (gs ++ [g]) (unitInput n u)).getD i false = false := by
      apply getD_of_ge
      rw [runWires_length, unitInput, List.length_ofFn, List.length_append, List.length_singleton]
      omega
    rcases hg_mono with ⟨hg_op, hg_len⟩
    rcases hg_op with hop | hop
    · refine ⟨color, le_trans hcard (Nat.add_le_add_left hrange_mono _), ?_⟩
      intro i hi0 u hu v hv hu1 hv1
      by_cases hlt : i < n + gs.length
      · rw [hold i hlt] at hi0
        rw [holdu u i hlt] at hu1
        rw [holdu v i hlt] at hv1
        exact hinv i hi0 u hu v hv hu1 hv1
      · by_cases heq : i = n + gs.length
        · subst heq
          rw [hnew0, hop, GateOp.eval] at hi0
          rw [hnewu u, hop, GateOp.eval] at hu1
          rw [hnewu v, hop, GateOp.eval] at hv1
          have hex : ∃ k ∈ g.inputs, (runWires gs (zeroInput n)).getD k false = false := by
            by_contra hall
            push Not at hall
            have hall' : (g.inputs.map fun k => (runWires gs (zeroInput n)).getD k false).all id = true := by
              rw [List.all_eq_true]
              intro b hb
              rcases List.mem_map.mp hb with ⟨k, hk, rfl⟩
              have hne := hall k hk
              cases hval : (runWires gs (zeroInput n)).getD k false
              · exact False.elim (hne hval)
              · rfl
            rw [hall'] at hi0
            cases hi0
          rcases hex with ⟨k, hk, hk0⟩
          rw [List.all_eq_true] at hu1 hv1
          have hku : (runWires gs (unitInput n u)).getD k false = true :=
            hu1 _ (List.mem_map_of_mem hk)
          have hkv : (runWires gs (unitInput n v)).getD k false = true :=
            hv1 _ (List.mem_map_of_mem hk)
          exact hinv k hk0 u hu v hv hku hkv
        · have hgt : n + gs.length < i := by omega
          rw [hgtu u i hgt] at hu1
          cases hu1
    · have hjA : gs.length ∈ A := by
        apply hA gs.length g _ hop
        rw [List.getElem?_append_right (le_refl _)]
        simp
      have hrange_succ : (A ∩ Finset.range (gs ++ [g]).length).card =
          (A ∩ Finset.range gs.length).card + 1 := by
        have hlen_app : (gs ++ [g]).length = gs.length + 1 := by simp
        rw [hlen_app, Finset.range_add_one, Finset.inter_insert_of_mem hjA,
          Finset.card_insert_of_notMem]
        simp
      by_cases hzero_new : (runWires (gs ++ [g]) (zeroInput n)).getD (n + gs.length) false = false
      · have hzero_inputs : ∀ k ∈ g.inputs, (runWires gs (zeroInput n)).getD k false = false := by
          rw [hnew0, hop, GateOp.eval] at hzero_new
          intro k hk
          by_contra hne
          have htrue : (runWires gs (zeroInput n)).getD k false = true := by
            cases hval : (runWires gs (zeroInput n)).getD k false
            · exact False.elim (hne hval)
            · rfl
          have hany : (g.inputs.map fun k => (runWires gs (zeroInput n)).getD k false).any id = true := by
            rw [List.any_eq_true]
            exact ⟨true, List.mem_map.mpr ⟨k, hk, htrue⟩, rfl⟩
          rw [hany] at hzero_new
          cases hzero_new
        match hgin : g.inputs with
        | [] =>
          refine ⟨color, le_trans hcard (Nat.add_le_add_left hrange_mono _), ?_⟩
          intro i hi0 u hu v hv hu1 hv1
          by_cases hlt : i < n + gs.length
          · rw [hold i hlt] at hi0
            rw [holdu u i hlt] at hu1
            rw [holdu v i hlt] at hv1
            exact hinv i hi0 u hu v hv hu1 hv1
          · by_cases heq : i = n + gs.length
            · subst heq
              rw [hnewu u, hop, hgin, GateOp.eval] at hu1
              simp at hu1
            · rw [hgtu u i (by omega)] at hu1
              cases hu1
        | [a] =>
          refine ⟨color, le_trans hcard (Nat.add_le_add_left hrange_mono _), ?_⟩
          intro i hi0 u hu v hv hu1 hv1
          by_cases hlt : i < n + gs.length
          · rw [hold i hlt] at hi0
            rw [holdu u i hlt] at hu1
            rw [holdu v i hlt] at hv1
            exact hinv i hi0 u hu v hv hu1 hv1
          · by_cases heq : i = n + gs.length
            · subst heq
              rw [hnewu u, hop, hgin, GateOp.eval] at hu1
              rw [hnewu v, hop, hgin, GateOp.eval] at hv1
              simp at hu1 hv1
              exact hinv a (hzero_inputs a (by simp [hgin])) u hu v hv hu1 hv1
            · rw [hgtu u i (by omega)] at hu1
              cases hu1
        | [a, b] =>
          have ha0 : (runWires gs (zeroInput n)).getD a false = false :=
            hzero_inputs a (by simp [hgin])
          have hb0 : (runWires gs (zeroInput n)).getD b false = false :=
            hzero_inputs b (by simp [hgin])
          by_cases hboth :
              (∃ u0 ∈ D, (runWires gs (unitInput n u0)).getD a false = true) ∧
              (∃ v0 ∈ D, (runWires gs (unitInput n v0)).getD b false = true)
          · rcases hboth with ⟨⟨u0, hu0, hu0a⟩, ⟨v0, hv0, hv0b⟩⟩
            let color' : Fin n → ℕ := fun x => if color x = color v0 then color u0 else color x
            refine ⟨color', ?_, ?_⟩
            · have hm : (D.image color).card ≤ (D.image color').card + 1 :=
                card_image_merge D color (color u0) (color v0)
              rw [hrange_succ]
              omega
            · intro i hi0 u hu v hv hu1 hv1
              by_cases hlt : i < n + gs.length
              · rw [hold i hlt] at hi0
                rw [holdu u i hlt] at hu1
                rw [holdu v i hlt] at hv1
                have heq_c := hinv i hi0 u hu v hv hu1 hv1
                simp [color', heq_c]
              · by_cases heq : i = n + gs.length
                · subst heq
                  rw [hnewu u, hop, hgin, GateOp.eval] at hu1
                  rw [hnewu v, hop, hgin, GateOp.eval] at hv1
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                    Bool.or_false, Bool.or_eq_true] at hu1 hv1
                  have hcu : color' u = color' u0 := by
                    rcases hu1 with hua | hub
                    · have h1 := hinv a ha0 u hu u0 hu0 hua hu0a
                      simp [color', h1]
                    · have h1 := hinv b hb0 u hu v0 hv0 hub hv0b
                      simp only [color', h1, ite_true]
                      by_cases he : color u0 = color v0
                      · simp [he]
                      · simp [he]
                  have hcv : color' v = color' u0 := by
                    rcases hv1 with hva | hvb
                    · have h1 := hinv a ha0 v hv u0 hu0 hva hu0a
                      simp [color', h1]
                    · have h1 := hinv b hb0 v hv v0 hv0 hvb hv0b
                      simp only [color', h1, ite_true]
                      by_cases he : color u0 = color v0
                      · simp [he]
                      · simp [he]
                  exact hcu.trans hcv.symm
                · rw [hgtu u i (by omega)] at hu1
                  cases hu1
          · refine ⟨color, le_trans hcard (Nat.add_le_add_left hrange_mono _), ?_⟩
            intro i hi0 u hu v hv hu1 hv1
            by_cases hlt : i < n + gs.length
            · rw [hold i hlt] at hi0
              rw [holdu u i hlt] at hu1
              rw [holdu v i hlt] at hv1
              exact hinv i hi0 u hu v hv hu1 hv1
            · by_cases heq : i = n + gs.length
              · subst heq
                rw [hnewu u, hop, hgin, GateOp.eval] at hu1
                rw [hnewu v, hop, hgin, GateOp.eval] at hv1
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                  Bool.or_false, Bool.or_eq_true] at hu1 hv1
                rcases hu1 with hua | hub <;> rcases hv1 with hva | hvb
                · exact hinv a ha0 u hu v hv hua hva
                · exfalso
                  exact hboth ⟨⟨u, hu, hua⟩, ⟨v, hv, hvb⟩⟩
                · exfalso
                  exact hboth ⟨⟨v, hv, hva⟩, ⟨u, hu, hub⟩⟩
                · exact hinv b hb0 u hu v hv hub hvb
              · rw [hgtu u i (by omega)] at hu1
                cases hu1
        | _ :: _ :: _ :: _ =>
          rw [hgin] at hg_len
          simp at hg_len
      · refine ⟨color, le_trans hcard (Nat.add_le_add_left hrange_mono _), ?_⟩
        intro i hi0 u hu v hv hu1 hv1
        by_cases hlt : i < n + gs.length
        · rw [hold i hlt] at hi0
          rw [holdu u i hlt] at hu1
          rw [holdu v i hlt] at hv1
          exact hinv i hi0 u hu v hv hu1 hv1
        · by_cases heq : i = n + gs.length
          · subst heq
            exact False.elim (hzero_new hi0)
          · rw [hgtu u i (by omega)] at hu1
            cases hu1

end PEqualNP.Outside.L_meta_601

theorem PEqualNP.Outside.L_meta_601 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset (Fin n)) (A : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → C.eval (List.ofFn (fun _ : Fin n => false)) = false → (∀ u ∈ D, C.eval (List.ofFn (fun w : Fin n => decide (w = u))) = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → D.card ≤ A.card + 1 := by
  intro n C D A hmono h0 hD hA
  obtain ⟨color, hcard, hinv⟩ :=
    PEqualNP.Outside.L_meta_601.exists_coloring n D A C.gates hmono hA
  have hsub : (A ∩ Finset.range C.gates.length).card ≤ A.card :=
    Finset.card_le_card Finset.inter_subset_left
  rcases D.eq_empty_or_nonempty with rfl | ⟨u0, hu0⟩
  · simp
  · have hconst : D.image color ⊆ {color u0} := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨u, hu, rfl⟩
      rw [Finset.mem_singleton]
      exact hinv C.output h0 u hu u0 hu0 (hD u hu) (hD u0 hu0)
    have himg : (D.image color).card ≤ 1 := by
      calc
        (D.image color).card ≤ ({color u0} : Finset ℕ).card := Finset.card_le_card hconst
        _ = 1 := Finset.card_singleton _
    omega
