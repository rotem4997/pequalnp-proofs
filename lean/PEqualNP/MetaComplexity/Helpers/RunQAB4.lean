import PEqualNP.MetaComplexity.Helpers.RunQAB3

/-!
# Theorem QA, cases B1 and B2 together: `qaGapB`

The route (one argument for B1 and B2, by values; leastness of `C` is not used beyond the row):
`t` is the image of `M` in `qaL`, a wire of the free-input chain `T`. `Rm` is the read relation
of `C` restricted to reads of earlier wires and to paths that do not pass through `M`.

* LIFT: every wire `w != M` reached from `x_q3` by an `Rm` path is not `o2` and its image is a
  wire of `T` at most `t`. (Through `o2` would put `W2` above `x_q3`: `W2` is false at `1_q3`
  with `x_q2` on (tool W) but its image is true there (OR chain). Past `t` would need two
  readers of `t` in `qaL`: the path gate and the kept reader of `M`; the sole-reader clauses
  make them one gate, which then lists `t` twice, against the side clause.)
* At `p = 1_e + 1_q4` and `p + 1_q3`, `M` is false (`o2` is false at `p`), so every wire
  outside the `Rm`-cone of `x_q3` agrees, and the output is in the cone. LIFT puts the image
  of the output (the last chain wire) at most `t`, so `t` is the last chain wire, and the kept
  reader of `M` (it has one: else `F` does not see `x_q2` at `1_e`) reads it: impossible.
* A reader `g_l` of `M` is excluded on the way: then `A_l`, an AND, reads `t` in `qaL`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Loc.Removal

theorem qa_gapB : qaGapB := by
  intro n F H C e q2 q4 g1 g2 a1 a2 o2 jM u1 u2 w1 w2 W2 z hFP hdist hH hF p1 p2 p3 p4 p5 p6 p7
    hmin hCF hga hg1 hg2 hre ha1 ha2 hr1 hr2 hu1 hu2 hoM hog ho hrq hM hro hLmin k c hchain hT
  obtain ⟨hcm, hclast, hcout, hcop, hc0, hcs, hr0, hrs, _, hside0, hsides⟩ := hchain

  set S := qaS (g1 : ℕ) g2 o2 jM with hSdef
  set tg := qaTgt (g1 : ℕ) g2 jM u1 u2 z with htgdef
  set d := n + 1 + cnt S C.gates.length with hddef
  set ρ := qaRho (n + 1) S tg d with hρdef
  obtain ⟨t, htT, htM⟩ := hT
  have hρlt0 : ∀ j, j < n + 1 → ρ j = j := fun j h => qaRho_lt (n + 1) S tg d h
  have hρkeep : ∀ p, p ∉ S → ρ (n + 1 + p) = n + 1 + cnt S p :=
    fun p h => qaRho_keep (n + 1) S tg d h
  have hρalias : ∀ p i, p ∈ S → tg p = some i → i < n + 1 + p → ρ (n + 1 + p) = ρ i :=
    fun p i h1 h2 h3 => qaRho_alias (n + 1) S tg d h1 h2 h3
  have hρbound : ∀ p a, a < n + 1 + p → ρ a < n + 1 + cnt S p ∨ ρ a = d :=
    fun p a h => qaRho_bound (n + 1) S tg d p a h
  -- basic facts
  have hmemS : ∀ p, p ∈ S ↔ p = g1.val ∨ p = g2.val ∨ p = o2.val ∨ p = jM.val := by
    intro p; simp [hSdef, qaS]
  have hFin : ∀ a b : Fin C.gates.length, n + 1 + a.val = n + 1 + b.val → a = b :=
    fun a b h => Fin.ext (by omega)
  have hMg1 : jM ≠ g1 := by intro h; have := hM.1; rw [h, hg1.1] at this; cases this
  have hMg2 : jM ≠ g2 := by intro h; have := hM.1; rw [h, hg2.1] at this; cases this
  have helast : e.val ≠ n := fun h => hdist.2.2.2.1 (Fin.ext (by rw [Fin.val_last]; exact h))
  have hq2last : q2.val ≠ n := fun h => hdist.2.2.2.2.1 (Fin.ext (by rw [Fin.val_last]; exact h))
  have hLlen : (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length = cnt S C.gates.length := qa_L_len _ _ _ _ _ _ _ _ _
  have hLout : (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).output = ρ C.output := rfl
  have ht_le : t ≤ n + 1 + (c (Fin.last k)).val := by
    rcases htT with rfl | ⟨i, rfl⟩
    · omega
    · have := Fin.le_iff_val_le_val.mp (hcm.monotone (Fin.le_last i)); omega
  have ht_d : t < d := by
    show t < n + 1 + cnt S C.gates.length
    have h1 := hclast; have h2 := hLlen; omega
  have hlastR : ∀ jj : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length,
      n + 1 + (c (Fin.last k)).val < n + 1 + jj.val → False := by
    intro jj h; have := jj.isLt; omega
  have hTread : ∀ (jj : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length) (τ : ℕ), qaReads ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get jj) τ →
      τ < n + 1 + jj.val → (τ = n ∨ ∃ i : Fin (k + 1), τ = n + 1 + (c i).val) →
      (τ = n ∧ jj = c 0) ∨ ∃ i : Fin k, τ = n + 1 + (c i.castSucc).val ∧ jj = c i.succ :=
    fun jj τ h1 h2 h3 => qa_next n (qaL (n + 1) C g1 g2 o2 jM u1 u2 z) k c hclast (fun j h => hr0 j h) (fun i j h => hrs i j h)
      jj τ h1 h2 h3
  have hTop : ∀ (jj : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length) (τ : ℕ),
      ((τ = n ∧ jj = c 0) ∨ ∃ i : Fin k, τ = n + 1 + (c i.castSucc).val ∧ jj = c i.succ) →
      ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get jj).op = GateOp.or ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get jj).inputs.length = 2 := by
    rintro jj τ (⟨_, rfl⟩ | ⟨i, _, rfl⟩)
    · exact hcop 0
    · exact hcop _
  have htb : ∀ (q : ℕ) (b : ℕ), b < n + 1 + q → ρ b = t → t < n + 1 + cnt S q := by
    intro q b hb hbt
    rcases hρbound q b hb with h | h
    · rw [← hbt]; exact h
    · exfalso; rw [hbt] at h; omega
  -- the output is neither q2 nor o2 (else x_last OR H would be constant)
  have hout_q2 : C.output ≠ q2.val := by
    intro hq
    apply qa_H_const n H hH
    intro x
    rw [← hF x, ← hCF]
    show (wiresFrom C.gates (List.ofFn _)).getD C.output false = true
    rw [hq, getD_wiresFrom _ _ _ (by simp; have := q2.isLt; omega), qa_ofFn_getD _ _ q2.isLt]
    simp [Function.update_apply, Ne.symm hdist.1]
  have hout_o2 : C.output ≠ n + 1 + o2.val := by
    intro hq
    apply qa_H_const n H hH
    intro x
    rw [← hF x, ← hCF]
    show (wiresFrom C.gates (List.ofFn _)).getD C.output false = true
    rw [hq, qa_val_fin (n + 1) C _ o2]
    refine qa_or_true _ _ ho.1 q2.val ho.2.2.1 ?_
    try beta_reduce
    rw [if_pos (by omega), getD_wiresFrom _ _ _ (by simp; omega), qa_ofFn_getD _ _ q2.isLt]
    simp [Function.update_apply, Ne.symm hdist.1]
  -- tool W at p = 1_e + 1_q4: W2 is false there
  have hW2p : W2 < n + 1 + o2.val →
      (wiresFrom C.gates (List.ofFn (fun i : Fin (n + 1) => decide (i = e ∨ i = q4)))).getD
        W2 false = false := by
    intro hlt
    apply qa_toolW_or (n + 1) C q2 o2 W2 ho.1 ho.2.2.2.1 (Ne.symm ho.2.2.2.2) hlt
      (fun j h => hrq j trivial h) hout_q2
    have hupd : Function.update (fun i : Fin (n + 1) => decide (i = e ∨ i = q4)) q2
        (!(fun i : Fin (n + 1) => decide (i = e ∨ i = q4)) q2) =
        fun i : Fin (n + 1) => decide (i = e ∨ i = q4 ∨ i = q2) := by
      funext i
      by_cases hi : i = q2
      · rw [hi]; simp [Ne.symm hdist.1, hdist.2.2.1]
      · simp [Function.update_of_ne hi, hi]
    rw [hupd, hCF, hCF, p5, p6]
    simp
  -- M has a reader, or is the output
  have hMr : C.output = n + 1 + jM.val ∨
      ∃ r : Fin C.gates.length, jM < r ∧ qaReads (C.gates.get r) (n + 1 + jM.val) := by
    by_contra hno
    push_neg at hno
    obtain ⟨hno1, hno2⟩ := hno
    have key := qa_agreeF (n + 1) C (fun i => decide (i = e)) (fun i => decide (i = e ∨ i = q2))
      (fun w => w = q2.val ∨ w = n + 1 + o2.val ∨ w = n + 1 + jM.val)
      (by
        intro i hi
        have : i ≠ q2 := fun h => hi (Or.inl (by rw [h]))
        simp [this])
      (by
        intro j hB ih
        apply qa_gate_agree _ _ _ _ _ j _ ih
        intro a ha halt hBa
        apply hB
        rcases hBa with h | h | h
        · rw [h] at ha
          have := hrq j trivial ha
          right; left; rw [this]
        · rw [h] at ha halt
          have hlt : o2 < j := Fin.lt_def.mpr (by omega)
          have := hro j hlt ha
          right; right; rw [this]
        · rw [h] at ha halt
          exact absurd ha (hno2 j (Fin.lt_def.mpr (by omega))))
      C.output (by
        rintro (h | h | h)
        · exact hout_q2 h
        · exact hout_o2 h
        · exact hno1 h)
    have h1 : circuitFun (n + 1) C (fun i => decide (i = e)) =
        circuitFun (n + 1) C (fun i => decide (i = e ∨ i = q2)) := key
    rw [hCF, hCF, p3, p4] at h1
    cases h1
  -- a reader g_l of M is impossible: A_l would be an AND reading t in qaL
  have hgcase : ∀ (g a : Fin C.gates.length) (u : ℕ), g.val ∈ S → tg g.val = some u →
      ((C.gates.get g).op = GateOp.or ∧ (C.gates.get g).inputs.length = 2 ∧
        e.val ∈ (C.gates.get g).inputs ∧ u ∈ (C.gates.get g).inputs ∧ e.val ≠ u) →
      (C.gates.get a).op = GateOp.and → n + 1 + g.val ∈ (C.gates.get a).inputs → g < a →
      jM < g → qaReads (C.gates.get g) (n + 1 + jM.val) → False := by
    intro g a u hgS htg hg hAop hAmem hga' hMg hrd
    have hmem : n + 1 + jM.val ∈ (C.gates.get g).inputs := by
      rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
      · rw [hg.1] at hn; cases hn
      · exact hm
    have hu : u = n + 1 + jM.val := by
      rcases qa_two _ hg.2.1 _ _ hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2 with hl | hl <;>
        rw [hl] at hmem <;> simp at hmem <;> omega
    have hρg : ρ (n + 1 + g.val) = t := by
      rw [← htM, hρalias _ _ hgS htg (by rw [hu]; have := Fin.lt_def.mp hMg; omega), hu]
    have haS : a.val ∉ S := by
      intro haS
      rcases (hmemS _).mp haS with h | h | h | h
      · have : a = g1 := Fin.ext h
        rw [this, hg1.1] at hAop; cases hAop
      · have : a = g2 := Fin.ext h
        rw [this, hg2.1] at hAop; cases hAop
      · have : a = o2 := Fin.ext h
        rw [this, ho.1] at hAop; cases hAop
      · have h1 := Fin.lt_def.mp hga'; have h2 := Fin.lt_def.mp hMg; omega
    obtain ⟨ha', hop', _, hrd'⟩ := qa_kept_read (n + 1) C g1 g2 o2 jM u1 u2 z a haS
    have hR : qaReads ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get ⟨cnt S a.val, ha'⟩)
        (ρ (n + 1 + g.val)) := hrd' (n + 1 + g.val)
      (Or.inr ⟨by rw [hAop]; exact fun h => GateOp.noConfusion h, hAmem⟩)
      (by have := Fin.lt_def.mp hga'; omega)
    rw [hρg] at hR
    have hb := htb a.val (n + 1 + g.val) (by have := Fin.lt_def.mp hga'; omega) hρg
    have := (hTop _ t (hTread _ t hR hb htT)).1
    rw [hop', hAop] at this
    cases this
  have hMR : ∀ r : Fin C.gates.length, jM < r → qaReads (C.gates.get r) (n + 1 + jM.val) →
      r.val ∉ S ∧ ∃ hr' : cnt S r.val < (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length,
        qaReads ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get ⟨cnt S r.val, hr'⟩) t ∧ t < n + 1 + cnt S r.val := by
    intro r hr1 hr2
    have hrS : r.val ∉ S := by
      intro hS
      rcases (hmemS _).mp hS with h | h | h | h
      · have hr : r = g1 := Fin.ext h
        rw [hr] at hr1 hr2
        exact hgcase g1 a1 u1 ((hmemS _).mpr (Or.inl rfl)) (by simp [htgdef, qaTgt]) hg1
          ha1.1 ha1.2.2.1 hga.2.2.1 hr1 hr2
      · have hr : r = g2 := Fin.ext h
        rw [hr] at hr1 hr2
        have hne : (g2 : ℕ) ≠ g1 := fun h' => hga.1 (Fin.ext h').symm
        exact hgcase g2 a2 u2 ((hmemS _).mpr (Or.inr (Or.inl rfl)))
          (by simp [htgdef, qaTgt, hne]) hg2 ha2.1 ha2.2.2.1 hga.2.2.2 hr1 hr2
      · have h1 := Fin.lt_def.mp hr1; have h2 := Fin.lt_def.mp hoM; omega
      · have h1 := Fin.lt_def.mp hr1; omega
    refine ⟨hrS, ?_⟩
    obtain ⟨hr', _, _, hrd'⟩ := qa_kept_read (n + 1) C g1 g2 o2 jM u1 u2 z r hrS
    have hR : qaReads ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get ⟨cnt S r.val, hr'⟩)
        (ρ (n + 1 + jM.val)) := hrd' _ hr2 (by have := Fin.lt_def.mp hr1; omega)
    rw [htM] at hR
    exact ⟨hr', hR, htb r.val (n + 1 + jM.val) (by have := Fin.lt_def.mp hr1; omega) htM⟩
  -- a chain gate listing t twice is impossible
  have hdup : ∀ jj : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length, (∀ w ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get jj).inputs, w = t) →
      ((t = n ∧ jj = c 0) ∨ ∃ i : Fin k, t = n + 1 + (c i.castSucc).val ∧ jj = c i.succ) →
      False := by
    rintro jj hall (⟨ht, rfl⟩ | ⟨i, ht, rfl⟩)
    · obtain ⟨w, hw, hwne, _⟩ := hside0
      exact hwne ((hall w hw).trans ht)
    · obtain ⟨w, hw, hwne, _⟩ := hsides i
      exact hwne ((hall w hw).trans ht)
  -- the relation and the invariant
  let Rm : ℕ → ℕ → Prop := fun a b => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧
    qaReads (C.gates.get j) a ∧ a < n + 1 + j.val ∧ a ≠ n + 1 + jM.val
  let J : ℕ → Prop := fun w => w ≠ n + 1 + o2.val ∧
    (ρ w = n ∨ ∃ i : Fin (k + 1), ρ w = n + 1 + (c i).val) ∧ ρ w ≤ t
  have hJn : J n := by
    refine ⟨by omega, Or.inl (hρlt0 n (by omega)), ?_⟩
    rw [hρlt0 n (by omega)]
    rcases htT with rfl | ⟨i, rfl⟩ <;> omega
  have hstep : ∀ a b, J a → Rm a b → b ≠ n + 1 + jM.val → J b := by
    rintro a b ⟨haO, haT, hat⟩ ⟨j, rfl, hrd, hlt, haM⟩ hbM
    have hjM : j ≠ jM := fun h => hbM (by rw [h])
    by_cases hjS : j.val ∈ S
    · rcases (hmemS _).mp hjS with h | h | h | h
      · -- j = g1
        have hj : j = g1 := Fin.ext h
        rw [hj] at hrd hlt
        have hmem : a ∈ (C.gates.get g1).inputs := by
          rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
          · rw [hg1.1] at hn; cases hn
          · exact hm
        have hae : a = e.val ∨ a = u1 := by
          rcases qa_two _ hg1.2.1 _ _ hg1.2.2.1 hg1.2.2.2.1 hg1.2.2.2.2 with hl | hl <;>
            rw [hl] at hmem <;> simp at hmem <;> first | exact hmem | exact hmem.symm
        rcases hae with ha | ha
        · exfalso
          rw [ha, hρlt0 _ e.isLt] at haT
          rcases haT with h' | ⟨i, h'⟩
          · exact helast h'
          · have := e.isLt; omega
        · have hρb : ρ (n + 1 + j.val) = ρ a := by
            rw [hj, ha]
            exact hρalias _ _ ((hmemS _).mpr (Or.inl rfl))
              (by simp [htgdef, qaTgt]) (by rw [← ha]; exact hlt)
          refine ⟨fun h' => hog.1 ((hFin _ _ h').symm.trans hj), ?_, ?_⟩
          · rw [hρb]; exact haT
          · rw [hρb]; exact hat
      · -- j = g2
        have hj : j = g2 := Fin.ext h
        rw [hj] at hrd hlt
        have hmem : a ∈ (C.gates.get g2).inputs := by
          rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
          · rw [hg2.1] at hn; cases hn
          · exact hm
        have hae : a = e.val ∨ a = u2 := by
          rcases qa_two _ hg2.2.1 _ _ hg2.2.2.1 hg2.2.2.2.1 hg2.2.2.2.2 with hl | hl <;>
            rw [hl] at hmem <;> simp at hmem <;> first | exact hmem | exact hmem.symm
        rcases hae with ha | ha
        · exfalso
          rw [ha, hρlt0 _ e.isLt] at haT
          rcases haT with h' | ⟨i, h'⟩
          · exact helast h'
          · have := e.isLt; omega
        · have hne : (g2 : ℕ) ≠ g1 := fun h' => hga.1 (Fin.ext h').symm
          have hρb : ρ (n + 1 + j.val) = ρ a := by
            rw [hj, ha]
            exact hρalias _ _ ((hmemS _).mpr (Or.inr (Or.inl rfl)))
              (by simp [htgdef, qaTgt, hne]) (by rw [← ha]; exact hlt)
          refine ⟨fun h' => hog.2 ((hFin _ _ h').symm.trans hj), ?_, ?_⟩
          · rw [hρb]; exact haT
          · rw [hρb]; exact hat
      · -- j = o2: then a = W2 is above x_q3, against tool W
        exfalso
        have hj : j = o2 := Fin.ext h
        rw [hj] at hrd hlt
        have hmem : a ∈ (C.gates.get o2).inputs := by
          rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
          · rw [ho.1] at hn; cases hn
          · exact hm
        have haq : a = q2.val ∨ a = W2 := by
          rcases qa_two _ ho.2.1 _ _ ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2 with hl | hl <;>
            rw [hl] at hmem <;> simp at hmem <;> first | exact hmem | exact hmem.symm
        rcases haq with ha | ha
        · rw [ha, hρlt0 _ q2.isLt] at haT
          rcases haT with h' | ⟨i, h'⟩
          · exact hq2last h'
          · have := q2.isLt; omega
        · rw [ha] at hlt haT
          have hW2e : W2 ≠ e.val := by
            intro h'
            rcases hre o2 trivial (Or.inr ⟨by rw [ho.1]; exact fun hh => GateOp.noConfusion hh,
              h' ▸ ho.2.2.2.1⟩) with h'' | h''
            · exact hog.1 h''
            · exact hog.2 h''
          have hval := qa_remove_val n C e q2 g1 g2 o2 jM u1 u2 z hdist.1 hga.1 hog.1 hog.2 hoM
            hg1 hg2 (fun j h => hre j trivial h) ⟨ho.1, ho.2.2.1⟩ (fun j h => hrq j trivial h)
            hM hro (fun i : Fin (n + 1) => decide (i = Fin.last n)) W2
            (by
              rintro (h' | h' | h')
              · exact hW2e h'
              · exact ho.2.2.2.2 h'.symm
              · omega)
          have hC : (wiresFrom C.gates (List.ofFn (Function.update (Function.update
              (fun i : Fin (n + 1) => decide (i = Fin.last n)) q2 true) e false))).getD
              W2 false = false := by
            apply qa_toolW_or (n + 1) C q2 o2 W2 ho.1 ho.2.2.2.1 (Ne.symm ho.2.2.2.2) hlt
              (fun j h => hrq j trivial h) hout_q2
            have hup : Function.update (Function.update (Function.update
                (fun i : Fin (n + 1) => decide (i = Fin.last n)) q2 true) e false) q2
                (!(Function.update (Function.update
                  (fun i : Fin (n + 1) => decide (i = Fin.last n)) q2 true) e false) q2) =
                fun i : Fin (n + 1) => decide (i = Fin.last n) := by
              funext i
              simp only [Function.update_apply]
              by_cases hi : i = q2
              · simp [hi, hdist.1, Ne.symm hdist.1, hdist.2.2.2.2.1]
              · by_cases hie : i = e
                · simp [hi, hie, hdist.1, Ne.symm hdist.1, hdist.2.2.2.1]
                · simp [hi, hie]
            rw [hup, hCF, hCF, p1, hF]
            simp
          have hn0 : (wiresFrom (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates (List.ofFn
              (fun i : Fin (n + 1) => decide (i = Fin.last n)))).getD n false = true := by
            rw [getD_wiresFrom _ _ _ (by simp), qa_ofFn_getD _ _ (by omega)]
            simp [Fin.ext_iff]
          have hL : (wiresFrom (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates (List.ofFn
              (fun i : Fin (n + 1) => decide (i = Fin.last n)))).getD (ρ W2) false = true := by
            rcases haT with h' | ⟨i, h'⟩
            · rw [h']; exact hn0
            · rw [h']
              exact qa_or_chain_ge (n + 1) (qaL (n + 1) C g1 g2 o2 jM u1 u2 z) k c n _ (fun i => (hcop i).1) hc0 (by omega)
                (fun i => ⟨hcs i, hcm (Fin.lt_def.mpr (by simp))⟩) hn0 i
          have := hval.symm.trans hL
          rw [hC] at this
          cases this
      · exact absurd (Fin.ext h) hjM
    · -- j kept
      obtain ⟨hj', hop', hin', hrd'⟩ := qa_kept_read (n + 1) C g1 g2 o2 jM u1 u2 z j hjS
      have hRa : qaReads ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get ⟨cnt S j.val, hj'⟩)
        (ρ a) := hrd' a hrd hlt
      have hin2 : ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get ⟨cnt S j.val, hj'⟩).inputs =
          (C.gates.get j).inputs.map (fun i =>
            ρ (if i < n + 1 + j.val then i else n + 1 + C.gates.length)) := hin'
      have hρlt : ρ a < n + 1 + cnt S j.val := by
        rcases hρbound j.val a hlt with h | h
        · exact h
        · exfalso; omega
      have hρb : ρ (n + 1 + j.val) = n + 1 + cnt S j.val := hρkeep _ hjS
      have hjo : j ≠ o2 := fun h => hjS ((hmemS _).mpr (Or.inr (Or.inr (Or.inl (by rw [h])))))
      have E := hTread ⟨cnt S j.val, hj'⟩ (ρ a) hRa hρlt haT
      by_cases hat' : ρ a = t
      · exfalso
        rcases hMr with hout | ⟨r, hr1, hr2⟩
        · have htl : t = n + 1 + (c (Fin.last k)).val := by
            rw [← htM, ← hout, ← hLout]; exact hcout
          exact hlastR ⟨cnt S j.val, hj'⟩ (by rw [← htl, ← hat']; exact hρlt)
        · obtain ⟨hrS, hr', hrRead, hrlt⟩ := hMR r hr1 hr2
          rw [hat'] at E
          have E2 := hTread ⟨cnt S r.val, hr'⟩ t hrRead hrlt htT
          have hjr : (⟨cnt S j.val, hj'⟩ : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length) = ⟨cnt S r.val, hr'⟩ := by
            rcases E with ⟨_, e1⟩ | ⟨i1, ti1, e1⟩ <;> rcases E2 with ⟨_, e2⟩ | ⟨i2, ti2, e2⟩
            · rw [e1, e2]
            · exfalso; omega
            · exfalso; omega
            · have h1 : c i1.castSucc = c i2.castSucc := Fin.ext (by omega)
              have h2 := Fin.castSucc_injective _ (hcm.injective h1)
              rw [e1, e2, h2]
          have hjr' : j = r := Fin.ext (qa_cnt_inj hjS hrS (congrArg Fin.val hjr))
          rw [← hjr'] at hr2 hr1
          have hT2 := hTop _ t E
          rw [hop'] at hT2
          have hlen2 : (C.gates.get j).inputs.length = 2 := by
            have := hT2.2; rw [hin2, List.length_map] at this; exact this
          have hamem : a ∈ (C.gates.get j).inputs := by
            rcases hrd with ⟨hn, _⟩ | ⟨_, hm⟩
            · rw [hT2.1] at hn; cases hn
            · exact hm
          have hMmem : n + 1 + jM.val ∈ (C.gates.get j).inputs := by
            rcases hr2 with ⟨hn, _⟩ | ⟨_, hm⟩
            · rw [hT2.1] at hn; cases hn
            · exact hm
          apply hdup ⟨cnt S j.val, hj'⟩ _ E
          intro w hw
          rw [hin2] at hw
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
          have hy' : y = a ∨ y = n + 1 + jM.val := by
            rcases qa_two _ hlen2 _ _ hamem hMmem haM with hl | hl <;>
              rw [hl] at hy <;> simp at hy <;> first | exact hy | exact hy.symm
          rcases hy' with rfl | rfl
          · rw [if_pos hlt]; exact hat'
          · rw [if_pos (by have := Fin.lt_def.mp hr1; omega)]; exact htM
      · refine ⟨fun h => hjo (hFin _ _ h), ?_, ?_⟩
        · rw [hρb]
          rcases E with ⟨_, e1⟩ | ⟨i, _, e1⟩
          · right; exact ⟨0, by rw [← e1]⟩
          · right; exact ⟨i.succ, by rw [← e1]⟩
        · rw [hρb]
          have hlt' : ρ a < t := lt_of_le_of_ne hat hat'
          rcases E with ⟨h1, e1⟩ | ⟨i, h1, e1⟩
          · have h1' : n + 1 + cnt S j.val = n + 1 + (c 0).val := by rw [← e1]
            rw [h1']
            rcases htT with rfl | ⟨i'', rfl⟩
            · omega
            · have := Fin.le_iff_val_le_val.mp (hcm.monotone (Fin.zero_le i'')); omega
          · have h1' : n + 1 + cnt S j.val = n + 1 + (c i.succ).val := by rw [← e1]
            rw [h1']
            rcases htT with rfl | ⟨i'', rfl⟩
            · omega
            · have hc : c i.castSucc < c i'' := Fin.lt_def.mpr (by omega)
              have hi := hcm.lt_iff_lt.mp hc
              have hi' : i.succ ≤ i'' := by
                rw [Fin.le_def]; rw [Fin.lt_def] at hi; simp at hi ⊢; omega
              have := Fin.le_iff_val_le_val.mp (hcm.monotone hi'); omega
  have hlift : ∀ w, Relation.TransGen Rm n w → w ≠ n + 1 + jM.val → J w := by
    intro w hw
    induction hw with
    | single hab => exact fun hb => hstep _ _ hJn hab hb
    | tail _ hbc ih =>
      intro hc
      obtain ⟨_, _, _, _, hne⟩ := id hbc
      exact hstep _ _ (ih hne) hbc hc
  -- agreement at p = 1_e + 1_q4 and p + 1_q3
  have hBo2 : ¬ (n + 1 + o2.val = n ∨ (Relation.TransGen Rm n (n + 1 + o2.val) ∧
      n + 1 + o2.val ≠ n + 1 + jM.val)) := by
    rintro (h | ⟨h1, h2⟩)
    · omega
    · exact (hlift _ h1 h2).1 rfl
  have ho2v : (wiresFrom C.gates (List.ofFn (fun i : Fin (n + 1) => decide (i = e ∨ i = q4)))).getD
      (n + 1 + o2.val) false = false := by
    rw [qa_val_fin (n + 1) C _ o2, ho.1, qa_or2 _ ho.2.1 _ _ ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2]
    try beta_reduce
    rw [if_pos (by omega), getD_wiresFrom _ _ _ (by simp; omega), qa_ofFn_getD _ _ q2.isLt]
    by_cases hWl : W2 < n + 1 + o2.val
    · rw [if_pos hWl, hW2p hWl]; simp [Ne.symm hdist.1, hdist.2.2.1]
    · rw [if_neg hWl]; simp [Ne.symm hdist.1, hdist.2.2.1]
  have key := qa_agreeF (n + 1) C (fun i => decide (i = e ∨ i = q4))
    (fun i => decide (i = e ∨ i = q4 ∨ i = Fin.last n))
    (fun w => w = n ∨ (Relation.TransGen Rm n w ∧ w ≠ n + 1 + jM.val))
    (by
      intro i hB
      have : i ≠ Fin.last n := fun h => hB (Or.inl (by rw [h]; simp))
      simp [this])
    (by
      intro j hB ih
      by_cases hjM : j = jM
      · have ho2v' := (ih _ (by have := Fin.lt_def.mp hoM; omega) hBo2).symm.trans ho2v
        rw [hjM, qa_val_fin (n + 1) C _ jM, qa_val_fin (n + 1) C _ jM,
          qa_and_false _ _ hM.1 (n + 1 + o2.val) hM.2.2.1
            (by rw [if_pos (by omega)]; exact ho2v),
          qa_and_false _ _ hM.1 (n + 1 + o2.val) hM.2.2.1
            (by rw [if_pos (by omega)]; exact ho2v')]
      · apply qa_gate_agree _ _ _ _ _ j _ ih
        intro a ha halt hBa
        apply hB
        right
        have hjne : n + 1 + j.val ≠ n + 1 + jM.val := fun h => hjM (hFin _ _ h)
        rcases hBa with h | ⟨h1, h2⟩
        · refine ⟨Relation.TransGen.single ⟨j, rfl, h ▸ ha, h ▸ halt, by omega⟩, hjne⟩
        · exact ⟨Relation.TransGen.tail h1 ⟨j, rfl, ha, halt, h2⟩, hjne⟩)
  have hBout : C.output = n ∨ (Relation.TransGen Rm n C.output ∧ C.output ≠ n + 1 + jM.val) := by
    by_contra hBo
    have h1 : circuitFun (n + 1) C (fun i => decide (i = e ∨ i = q4)) =
        circuitFun (n + 1) C (fun i => decide (i = e ∨ i = q4 ∨ i = Fin.last n)) :=
      key C.output hBo
    rw [hCF, hCF, p5, p7] at h1
    cases h1
  rcases hBout with h | ⟨h1, h2⟩
  · have := p1
    rw [← hCF] at this
    change (wiresFrom C.gates (List.ofFn _)).getD C.output false = false at this
    rw [h, getD_wiresFrom _ _ _ (by simp), qa_ofFn_getD _ _ (by omega)] at this
    simp [Fin.ext_iff] at this
  · have hJo := (hlift _ h1 h2).2.2
    rw [← hLout, hcout] at hJo
    have htl : t = n + 1 + (c (Fin.last k)).val := le_antisymm ht_le hJo
    rcases hMr with hout | ⟨r, hr1, hr2⟩
    · exact h2 hout
    · obtain ⟨_, hr', _, hrlt⟩ := hMR r hr1 hr2
      exact hlastR ⟨cnt S r.val, hr'⟩ (by rw [← htl]; exact hrlt)

end PEqualNP.MetaComplexity.Helpers.RunFour2
