import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2089_2
    (single :
      let U : Type := Fin 13
      let S : Finset U := {0,1,3,9}
      let I : U → U → Prop := fun p w => ∃ d ∈ S, p = w+d
      let A : Finset U → U → Prop := fun P w => ∀ p ∈ P, ¬ I p w
      let X : Type := Fin 26 → Bool
      let T : U → U → X := fun p w i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)
      let F : Finset U → X := fun P i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w, i = Fin.natAdd 13 w ∧ A P w)
      let N : Finset U → Prop := fun P => (∀ p ∉ P, ∃ w, A P w ∧ I p w) ∧ ((∃ w, ∀ p ∈ P, I p w) ∨ ∃ p, ∀ w, A P w → I p w)
      ∀ C : Circuit, Monotone2 C → C.size ≤ 60 →
      let V : ℕ → X → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
      let H : (X → Bool) → Prop := fun f => ∀ p w, I p w → f (T p w) = true
      ∀ a b : ℕ, H (fun x => V a x || V b x) → ¬ H (V a) → ¬ H (V b) →
        (∀ P, N P → ¬ (V a (F P) || V b (F P)) = true) → False)
    (multiple :
      let U : Type := Fin 13
      let S : Finset U := {0,1,3,9}
      let I : U → U → Prop := fun p w => ∃ d ∈ S, p = w+d
      let A : Finset U → U → Prop := fun P w => ∀ p ∈ P, ¬ I p w
      let X : Type := Fin 26 → Bool
      let T : U → U → X := fun p w i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)
      let F : Finset U → X := fun P i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w, i = Fin.natAdd 13 w ∧ A P w)
      let N : Finset U → Prop := fun P => (∀ p ∉ P, ∃ w, A P w ∧ I p w) ∧ ((∃ w, ∀ p ∈ P, I p w) ∨ ∃ p, ∀ w, A P w → I p w)
      ∀ C : Circuit, Monotone2 C →
      let V : ℕ → X → Bool := fun i x => (C.wires (List.ofFn x ++ [true,false])).getD i false
      let H : (X → Bool) → Prop := fun f => ∀ p w, I p w → f (T p w) = true
      let test : (ℕ × ℕ) → X → Bool := fun e x => V e.1 x || V e.2 x
      let covers : Finset (ℕ × ℕ) → Prop := fun K => ∀ P, N P → ∃ e ∈ K, ¬ test e (F P) = true
      ∀ K : Finset (ℕ × ℕ), 2 ≤ K.card → C.size + 2 * K.card ≤ 64 →
        (∀ e ∈ K, H (test e) ∧ ¬ H (V e.1) ∧ ¬ H (V e.2)) →
        covers K → (∀ e ∈ K, ¬ covers (K.erase e)) → False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  intro S I A T F W C hm hs a b hab hp hn
  classical
  let X := Fin 26 → Bool
  let P (x : X) := ∃ p w, I p w ∧ x = T p w
  let hot (f : X → Bool) := ∀ x, P x → f x = true
  let legal (gs : List Gate) := ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  let step (z : List Bool) (g : Gate) := z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
  let run (gs : List Gate) (z : List Bool) := gs.foldl step z
  let raw (x : X) := List.ofFn x
  let init (x : X) := raw x ++ [true,false]
  let V (gs : List Gate) (i : ℕ) (x : X) := (run gs (raw x)).getD i false
  let B (ds : List Gate) (i : ℕ) (x : X) := (run ds (init x)).getD i false
  let fire (ds : List Gate) (e : ℕ × ℕ) (x : X) := B ds e.1 x || B ds e.2 x
  let pass (ds : List Gate) (L : List (ℕ × ℕ)) (x : X) := ∀ e ∈ L, fire ds e x = true
  let specs (ds : List Gate) (L : List (ℕ × ℕ)) := ∀ e ∈ L, e.1 < 28+ds.length ∧ e.2 < 28+ds.length ∧ hot (fire ds e) ∧ ¬hot (B ds e.1) ∧ ¬hot (B ds e.2)
  have len (gs : List Gate) (z : List Bool) : (run gs z).length = z.length + gs.length := by
    induction gs generalizing z with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (step z g)).length = _
      rw [ih]; simp [step]; omega
  have snoc (gs : List Gate) (g : Gate) (z : List Bool) (i : ℕ) :
      (run (gs++[g]) z).getD i false = if i = z.length+gs.length then
        g.op.eval (g.inputs.map fun j => (run gs z).getD j false) else (run gs z).getD i false := by
    change ((gs++[g]).foldl step z).getD i false = _
    rw [List.foldl_append]; change (run gs z ++ [_]).getD i false = _
    rw [← len]; split_ifs with h
    · subst i; simp [List.getD_eq_getElem?_getD,run]
    · by_cases hlt : i < (run gs z).length
      · exact List.getD_append _ _ _ _ hlt
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have vstep (gs : List Gate) (g : Gate) (i : ℕ) (x : X) :
      V (gs++[g]) i x = if i = 26+gs.length then g.op.eval (g.inputs.map fun j => V gs j x) else V gs i x := by
    simpa only [V, raw, List.length_ofFn] using snoc gs g (raw x) i
  have bstep (ds : List Gate) (g : Gate) (i : ℕ) (x : X) :
      B (ds++[g]) i x = if i = 28+ds.length then g.op.eval (g.inputs.map fun j => B ds j x) else B ds i x := by
    have hi : (init x).length = 28 := by simp [init,raw]
    simpa only [B, hi] using snoc ds g (init x) i
  have topBit (ds : List Gate) (x : X) : B ds 26 x = true := by
    induction ds using List.reverseRecOn with
    | nil => simp [B,run,init,raw,List.getD_eq_getElem?_getD]
    | append_singleton ds g ih => rw [bstep, ite_eq_right (by omega), ih]
  have av (ds : List Gate) (L : List (ℕ × ℕ)) (h : specs ds L) (x : X) (hx : P x) : pass ds L x :=
    fun e he => (h e he).2.2.1 x hx
  have andEq (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEq (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have baseCold (i : ℕ) : ¬ hot (V [] i) := by
    intro h
    have p₀ := h (T 0 0) ⟨0,0,⟨0,by decide,by decide⟩,rfl⟩
    have p₁ := h (T 1 1) ⟨1,1,⟨0,by decide,by decide⟩,rfl⟩
    change (List.ofFn (T 0 0)).getD i false = true at p₀
    change (List.ofFn (T 1 1)).getD i false = true at p₁
    by_cases hi : i < 26
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,dite_true,Option.getD_some] at p₀ p₁
      have dis : ∀ j : Fin 26, ¬(T 0 0 j = true ∧ T 1 1 j = true) := by decide
      exact dis ⟨i,hi⟩ ⟨p₀,p₁⟩
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)] at p₀; contradiction
  -- H is a set, not a stack: a shared demand is peeled only once.
  have extract (gs : List Gate) (hg : legal gs) (H : Finset ℕ) (ht : ∀ i ∈ H, hot (V gs i)) :
      ∃ (ds : List Gate) (L : List (ℕ × ℕ)) (r : ℕ → ℕ), legal ds ∧
        ds.length + H.card ≤ gs.length ∧ ds.length + 2*L.length ≤ gs.length + H.card ∧
        specs ds L ∧ (∀ i, r i < 28+ds.length) ∧
        (∀ x, pass ds L x → ∀ i, V gs i x = B ds (r i) x) ∧
        (∀ x, pass ds L x → ∀ i ∈ H, V gs i x = true) := by
    induction gs using List.reverseRecOn generalizing H with
    | nil =>
      have hz : H = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => baseCold i (ht i hi))
      subst H
      refine ⟨[],[],fun i => if i < 26 then i else 27,by simp [legal],by simp,by simp,by simp [specs],?_,?_,by simp⟩
      · intro i; change (if i < 26 then i else 27) < 28; split_ifs <;> omega
      · intro x _ i; change (raw x).getD i false = (init x).getD (if i < 26 then i else 27) false
        by_cases hi : i < 26
        · rw [ite_eq_left hi]; exact (List.getD_append _ _ _ _ (by simpa [raw] using hi)).symm
        · rw [ite_eq_right hi,List.getD_eq_default _ _ (by simp [raw]; omega)]
          simp [init,raw,List.getD_eq_getElem?_getD]
    | append_singleton gs g ih =>
      let n := 26+gs.length
      have hg' : legal gs := fun u hu => hg u (by simp [hu])
      have hop := hg g (by simp)
      have hold (i : ℕ) (hi : i ≠ n) (x : X) : V (gs++[g]) i x = V gs i x := by rw [vstep,ite_eq_right hi]
      have hnew (x : X) : V (gs++[g]) n x = g.op.eval (g.inputs.map fun j => V gs j x) := by rw [vstep,ite_eq_left rfl]
      by_cases hmem : n ∈ H
      · let R := H.erase n
        have cardR : R.card+1 = H.card := Finset.card_erase_add_one hmem
        have oldR (i : ℕ) (hi : i ∈ R) : hot (V gs i) := by
          obtain ⟨hne,hH⟩ := Finset.mem_erase.mp hi
          exact fun x hx => (hold i hne x).symm.trans (ht i hH x hx)
        -- How to discharge this demand: demand at most two older hot wires,
        -- or emit one OR test whose two operands each miss an incidence.
        have peel : (∃ J : Finset ℕ, J.card ≤ 2 ∧ (∀ j ∈ J, hot (V gs j)) ∧
            ∀ x, (∀ j ∈ J, V gs j x = true) → V (gs++[g]) n x = true) ∨
            ∃ u v, ¬hot (V gs u) ∧ ¬hot (V gs v) ∧
              ∀ x, V (gs++[g]) n x = (V gs u x || V gs v x) := by
          rcases (show g.op = .and ∨ g.op = .or from hop.1) with h | h
          · left; refine ⟨g.inputs.toFinset,(List.toFinset_card_le _).trans hop.2,?_,?_⟩
            · intro j hj x hx
              have hval := ht n hmem x hx
              rw [hnew,h,andEq,List.all_eq_true] at hval
              exact hval _ (List.mem_map.mpr ⟨j,List.mem_toFinset.mp hj,rfl⟩)
            · intro x hJ; rw [hnew,h,andEq,List.all_eq_true]
              rintro _ hv; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
              exact hJ j (List.mem_toFinset.mpr hj)
          · by_cases he : ∃ j ∈ g.inputs, hot (V gs j)
            · obtain ⟨j,hj,hhot⟩ := he
              left; refine ⟨{j},by simp,by simpa using hhot,?_⟩
              intro x hJ; rw [hnew,h,orEq,List.any_eq_true]
              exact ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,hJ j (by simp)⟩
            · have hlen : g.inputs.length = 2 := by
                by_contra hlen
                have hl := hop.2
                cases hh : g.inputs with
                | nil => have hh₀ := ht n hmem (T 0 0) ⟨0,0,⟨0,by decide,by decide⟩,rfl⟩; rw [hnew,h,hh] at hh₀; contradiction
                | cons j js =>
                  cases js with
                  | nil =>
                    apply he; refine ⟨j,by simp [hh],fun x hx => ?_⟩
                    have hh₀ := ht n hmem x hx
                    simpa [hnew,h,hh,orEq] using hh₀
                  | cons k ks =>
                    rw [hh] at hl hlen
                    simp only [List.length_cons] at hl hlen
                    omega
              obtain ⟨u,v,huv⟩ := List.length_eq_two.mp hlen
              right; refine ⟨u,v,fun hh => he ⟨u,by simp [huv],hh⟩,fun hh => he ⟨v,by simp [huv],hh⟩,?_⟩
              intro x; rw [hnew,h,huv,orEq]; simp
        -- The skipped output is a true constant on all assignments that pass.
        have finish (ds : List Gate) (L : List (ℕ × ℕ)) (r : ℕ → ℕ)
            (hd : legal ds) (hd1 : ds.length + H.card ≤ (gs++[g]).length)
            (hd2 : ds.length + 2*L.length ≤ (gs++[g]).length + H.card)
            (hsp : specs ds L) (hb : ∀ i, r i < 28+ds.length)
            (heq : ∀ x, pass ds L x → ∀ i, V gs i x = B ds (r i) x)
            (hr : ∀ x, pass ds L x → ∀ i ∈ R, V gs i x = true)
            (hnw : ∀ x, pass ds L x → V (gs++[g]) n x = true) :
            ∃ (ds : List Gate) (L : List (ℕ × ℕ)) (r : ℕ → ℕ), legal ds ∧
              ds.length + H.card ≤ (gs++[g]).length ∧ ds.length + 2*L.length ≤ (gs++[g]).length + H.card ∧
              specs ds L ∧ (∀ i, r i < 28+ds.length) ∧
              (∀ x, pass ds L x → ∀ i, V (gs++[g]) i x = B ds (r i) x) ∧
              (∀ x, pass ds L x → ∀ i ∈ H, V (gs++[g]) i x = true) := by
          refine ⟨ds,L,fun i => if i = n then 26 else r i,hd,hd1,hd2,hsp,?_,?_,?_⟩
          · intro i; change (if i = n then 26 else r i) < _; split_ifs <;> first | omega | exact hb i
          · intro x hx i; change _ = B ds (if i = n then 26 else r i) x; split_ifs with h
            · subst i; rw [hnw x hx,topBit]
            · rw [hold i h,heq x hx]
          · intro x hx i hi; by_cases h : i = n
            · exact h ▸ hnw x hx
            · exact (hold i h x).trans (hr x hx i (Finset.mem_erase.mpr ⟨h,hi⟩))
        rcases peel with ⟨J,hcard,hhot,hpass⟩ | ⟨u,v,hu,hv,heval⟩
        · obtain ⟨ds,L,r,hd,h1,h2,hsp,hbd,heq,hdem⟩ := ih hg' (R ∪ J) (fun i hi => (Finset.mem_union.mp hi).elim (oldR i) (hhot i))
          have c1 := Finset.card_le_card (Finset.subset_union_left (s₂ := J) (s₁ := R))
          have c2 := Finset.card_union_le R J
          apply finish ds L r hd (by simp; omega) (by simp; omega) hsp hbd heq
          · exact fun x hx i hi => hdem x hx i (Finset.mem_union_left _ hi)
          · exact fun x hx => hpass x (fun j hj => hdem x hx j (Finset.mem_union_right _ hj))
        · obtain ⟨ds,L,r,hd,h1,h2,hsp,hbd,heq,hdem⟩ := ih hg' R oldR
          let e := (r u,r v)
          have oldPass (x : X) (hx : pass ds (e::L) x) : pass ds L x := fun q hq => hx q (List.mem_cons_of_mem _ hq)
          have eqp (i : ℕ) (x : X) (hx : P x) := heq x (av ds L hsp x hx) i
          have hsnew : specs ds (e::L) := by
            intro q hq; rcases List.mem_cons.mp hq with rfl | hm'
            · refine ⟨hbd u,hbd v,?_,?_,?_⟩
              · intro x hx; change (B ds (r u) x || B ds (r v) x) = true
                rw [← eqp u x hx,← eqp v x hx,← heval]; exact ht n hmem x hx
              · exact fun h => hu (fun x hx => (eqp u x hx).trans (h x hx))
              · exact fun h => hv (fun x hx => (eqp v x hx).trans (h x hx))
            · exact hsp q hm'
          apply finish ds (e::L) r hd (by simp; omega) (by simp; omega) hsnew hbd
            (fun x hx => heq x (oldPass x hx)) (fun x hx => hdem x (oldPass x hx))
          intro x hx; rw [heval,heq x (oldPass x hx) u,heq x (oldPass x hx) v]; exact hx e List.mem_cons_self
      · obtain ⟨ds,L,r,hd,h1,h2,hsp,hbd,heq,hdem⟩ := ih hg' H (fun i hi x hx => (hold i (fun h => hmem (h ▸ hi)) x).symm.trans (ht i hi x hx))
        let g' : Gate := ⟨g.op,g.inputs.map r⟩
        let D := ds++[g']
        have stay (i : ℕ) (hi : i < 28+ds.length) (x : X) : B D i x = B ds i x := by rw [show D = _ from rfl,bstep,ite_eq_right (by omega)]
        have fe (q : ℕ × ℕ) (hq : q ∈ L) (x : X) : fire D q x = fire ds q x := by
          change (_ || _) = (_ || _); rw [stay _ (hsp q hq).1,stay _ (hsp q hq).2.1]
        have back (x : X) (hx : pass D L x) : pass ds L x := fun q hq => (fe q hq x).symm.trans (hx q hq)
        refine ⟨D,L,fun i => if i = n then 28+ds.length else r i,?_,by simp [D]; omega,by simp [D]; omega,?_,?_,?_,?_⟩
        · intro u hu; rcases List.mem_append.mp hu with hu | hu
          · exact hd u hu
          · have : u = g' := List.mem_singleton.mp hu; subst u; exact ⟨hop.1,by simpa [g'] using hop.2⟩
        · intro q hq; obtain ⟨ha,hb,hc,he,hf⟩ := hsp q hq
          exact ⟨by simp [D]; omega,by simp [D]; omega,fun x hx => (fe q hq x).trans (hc x hx),
            fun h => he (fun x hx => (stay _ ha x).symm.trans (h x hx)),fun h => hf (fun x hx => (stay _ hb x).symm.trans (h x hx))⟩
        · intro i; have := hbd i; change (if i = n then 28+ds.length else r i) < _
          split_ifs <;> simp [D]
          omega
        · intro x hx i; change _ = B D (if i = n then 28+ds.length else r i) x; split_ifs with hi
          · subst i; rw [hnew,show D = ds++[g'] from rfl,bstep,ite_eq_left rfl]
            change g.op.eval _ = g.op.eval ((g.inputs.map r).map _)
            rw [List.map_map]; congr 1; exact List.map_congr_left (fun j _ => heq x (back x hx) j)
          · rw [hold i hi,stay _ (hbd i),heq x (back x hx)]
        · intro x hx i hi; rw [hold i (fun h => hmem (h ▸ hi))]; exact hdem x (back x hx) i hi
  let H : Finset ℕ := {a.val,b.val}
  have ne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hcard : H.card = 2 := by simp [H,ne]
  have hp' (x : X) (hx : P x) : V C.gates a.val x = true ∧ V C.gates b.val x = true := by
    obtain ⟨p,w,hi,rfl⟩ := hx
    have h := hp p w hi
    change GateOp.and.eval [V C.gates a.val (T p w),V C.gates b.val (T p w)] = true at h
    simpa [andEq] using h
  obtain ⟨ds,L,r,hd,h1,h2,hsp,_,_,hdem⟩ := extract C.gates hm H (by
    intro i hi x hx; rcases (show i = a.val ∨ i = b.val by simpa [H] using hi) with rfl | rfl
    · exact (hp' x hx).1
    · exact (hp' x hx).2)
  let D : Circuit := ⟨ds,0⟩
  have dsize : D.size = ds.length := rfl
  change C.gates.length ≤ 62 at hs
  have cost : D.size + 2*L.length ≤ 64 := by omega
  have d60 : D.size ≤ 60 := by omega
  let N := fun (s : Finset (Fin 13)) => (∀ p ∉ s, ∃ w, A s w ∧ I p w) ∧ ((∃ w, ∀ p ∈ s, I p w) ∨ ∃ p, ∀ w, A s w → I p w)
  have reject (s : Finset (Fin 13)) (h : N s) : ∃ e ∈ L, ¬ fire ds e (F s) = true := by
    by_contra! hall
    have ha := hdem (F s) hall a.val (by simp [H])
    have hb := hdem (F s) hall b.val (by simp [H])
    have hneg := hn s h.1 h.2
    change GateOp.and.eval [V C.gates a.val (F s),V C.gates b.val (F s)] = false at hneg
    simp [andEq,ha,hb] at hneg
  have N0 : N ∅ := ⟨fun p _ => ⟨p,by simp [A],0,by decide,by simp⟩,Or.inl ⟨0,by simp⟩⟩
  have missed (i : ℕ) (h : ¬ hot (B ds i)) : ¬ ∀ p w, I p w → B ds i (T p w) = true := by
    intro allPairs
    apply h
    rintro x ⟨p,w,hi,rfl⟩
    exact allPairs p w hi
  let covers (K : Finset (ℕ × ℕ)) := ∀ s, N s → ∃ e ∈ K, ¬ fire ds e (F s) = true
  have anyCover : ∃ n, ∃ K ⊆ L.toFinset, covers K ∧ K.card = n := by
    refine ⟨_,L.toFinset,Finset.Subset.rfl,?_,rfl⟩
    intro s hs'; obtain ⟨e,he,hf⟩ := reject s hs'; exact ⟨e,List.mem_toFinset.mpr he,hf⟩
  obtain ⟨K,hsub,hcov,hcardK⟩ := Nat.find_spec anyCover
  have cardLe : K.card ≤ L.length := (Finset.card_le_card hsub).trans L.toFinset_card_le
  have orig (e) (he : e ∈ K) : e ∈ L := List.mem_toFinset.mp (hsub he)
  have minimal (e) (he : e ∈ K) : ¬ covers (K.erase e) := by
    intro smaller
    have bound := Nat.find_min' anyCover ⟨K.erase e,(Finset.erase_subset _ _).trans hsub,smaller,rfl⟩
    have lt := Finset.card_erase_lt_of_mem he
    omega
  by_cases hmulti : 2 ≤ K.card
  · apply multiple D hd K hmulti (by omega) _ hcov minimal
    intro e he; have h := (hsp e (orig e he)).2.2
    exact ⟨fun p w hi => h.1 _ ⟨p,w,hi,rfl⟩,missed _ h.2.1,missed _ h.2.2⟩
  · obtain ⟨e,he,hf⟩ := hcov ∅ N0
    have hall (q) (hq : q ∈ K) : q = e := by
      by_contra hne
      have sub : ({q,e} : Finset _) ⊆ K := by
        intro t ht; rcases (show t = q ∨ t = e by simpa using ht) with rfl | rfl
        · exact hq
        · exact he
      have bound := Finset.card_le_card sub
      simp [hne] at bound
      omega
    have h := (hsp e (orig e he)).2.2
    apply single D hd d60 e.1 e.2 (fun p w hi => h.1 _ ⟨p,w,hi,rfl⟩) (missed _ h.2.1) (missed _ h.2.2)
    intro s hs'; obtain ⟨q,hq,hf⟩ := hcov s hs'; exact hall q hq ▸ hf
