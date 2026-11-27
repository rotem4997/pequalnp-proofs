import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2602_2
    (face : let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      ∀ B : Circuit, Monotone2 B →
        (∀ x : Fin 26 → Bool, x 0 = false → x 13 = false →
          (B.eval (List.ofFn x) = true ↔ ∃ a b, I a b ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true)) → 56 ≤ B.size)
    (path : let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      ∀ C : Circuit, PEqualNP.TopForm.IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) → C.size ≤ 64 →
      let V := fun (x : Fin 26 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
      (∀ x, V x C.output = true ↔ ∃ a b, I a b ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true) →
      (∀ p l, I p l → ∃ S : Finset ℕ, S ⊆ Finset.range C.size ∧ 56 ≤ S.card ∧
        ∀ j ∈ S, ∀ i < 26+j, ∃ x, x (Fin.castAdd 13 p) = false ∧ x (Fin.natAdd 13 l) = false ∧ V x i ≠ V x (26+j)) →
      let walk := fun t : ℕ => Relation.ReflTransGen (fun a w : ℕ => ∃ (j b : ℕ) (g : Gate),
        w = 26+j ∧ C.gates[j]? = some g ∧ (g.inputs = [a,b] ∨ g.inputs = [b,a]) ∧
        (g.op = .or ∨ V (fun k => decide (k.val=t)) b = true)) (13-t) C.output
      walk 0 ∨ walk 13) :
¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  classical
  rintro ⟨C, _, sizeC, gates, spec, ⟨v, vi, vg, vf⟩, ⟨u, ui, ug, uf⟩⟩
  let I := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let V := fun (x : Fin 26 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
  have per (g : Gate) (h : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b := by
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem h
    obtain ⟨o,a,b,e,n,_⟩ := gates j _ (List.getElem?_eq_getElem hj)
    exact ⟨o,a,b,e,n⟩
  have ao : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨fun g hg => (per g hg).1, ?_, ?_⟩
    · intro j hj i hi
      have h := List.getElem?_eq_getElem hj
      obtain ⟨_,a,b,e,_,ha,hb⟩ := gates j _ h
      change i ∈ (C.gates.getD j _).inputs at hi
      rw [List.getD_eq_getElem _ _ hj,e] at hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact (List.mem_singleton.mp hi) ▸ hb
    · intro g hg
      obtain ⟨a,b,e,_⟩ := (per g hg).2
      rw [e]; rfl
  have nodup (g : Gate) (hg : g ∈ C.gates) : g.inputs.Nodup := by
    obtain ⟨a,b,e,h⟩ := (per g hg).2
    simp [e,h]
  have faces (p l : Fin 13) (edge : I p l) : ∃ S : Finset ℕ,
      S ⊆ Finset.range C.size ∧ 56 ≤ S.card ∧ ∀ j ∈ S, ∀ i < 26+j, ∃ x,
        x (Fin.castAdd 13 p) = false ∧ x (Fin.natAdd 13 l) = false ∧ V x i ≠ V x (26+j) := by
    let X := Fin 26 → Bool
    let F (x : X) := x (Fin.castAdd 13 p) = false ∧ x (Fin.natAdd 13 l) = false
    let st (s : List Bool) (g : Gate) := s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]
    let val (gs : List Gate) (x : X) (i : ℕ) := (gs.foldl st (List.ofFn x)).getD i false
    have lens (s : List Bool) (gs : List Gate) : (gs.foldl st s).length = s.length+gs.length := by
      induction gs generalizing s with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons,ih,st,List.length_append,List.length_cons,List.length_nil]
        clear * -; lia -abstractProof
    have append (gs : List Gate) (g : Gate) (x : X) :
        (gs++[g]).foldl st (List.ofFn x) = gs.foldl st (List.ofFn x) ++
          [g.op.eval (g.inputs.map (val gs x))] := by rw [List.foldl_append]; rfl
    have before (gs : List Gate) (g : Gate) (x : X) {i : ℕ} (h : i < 26+gs.length) :
        val (gs++[g]) x i = val gs x i := by
      change ((gs++[g]).foldl st _).getD _ _ = _
      rw [append]; exact List.getD_append _ _ _ _ (by rwa [lens,List.length_ofFn])
    have last (gs : List Gate) (g : Gate) (x : X) : val (gs++[g]) x (26+gs.length) =
        g.op.eval (g.inputs.map (val gs x)) := by
      change ((gs++[g]).foldl st _).getD _ _ = _
      rw [append,List.getD_append_right _ _ _ _ (by rw [lens,List.length_ofFn])]
      simp [lens]
    let legal (gs : List Gate) := ∀ j (g : Gate), gs[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j
    let fresh (gs : List Gate) (j : ℕ) := ∀ i < 26+j, ∃ x, F x ∧ val gs x i ≠ val gs x (26+j)
    -- Keep just the first representative of each column on this face, preserving shared uses.
    have pack (gs : List Gate) (hg : legal gs) :
        ∃ (ds : List Gate) (r : ℕ → ℕ) (S : Finset ℕ),
          Monotone2 ⟨ds,0⟩ ∧ ds.length = S.card ∧ S ⊆ Finset.range gs.length ∧
          (∀ j ∈ S, fresh gs j) ∧ (∀ i < 26+gs.length, r i < 26+ds.length) ∧
          ∀ x, F x → ∀ i < 26+gs.length, val ds x (r i) = val gs x i := by
      induction gs using List.reverseRecOn with
      | nil =>
        refine ⟨[], id, ∅, ?_⟩
        have m : Monotone2 ⟨[],0⟩ := fun g h => (List.not_mem_nil (a := g) h).elim
        exact ⟨m,rfl,by simp,by simp,fun _ h => h,fun _ _ _ _ => rfl⟩
      | append_singleton gs g ih =>
        have h0 : legal gs := by
          intro j z hz
          apply hg j z
          have lt : j < gs.length := by
            by_contra! h
            rw [List.getElem?_eq_none h] at hz
            contradiction
          rw [List.getElem?_append_left lt]
          exact hz
        obtain ⟨ds,r,S,md,ct,sub,fr,valid,agree⟩ := ih h0
        have eqLen : (gs++[g]).length = gs.length+1 := by simp
        have newG := hg gs.length g (by simp)
        obtain ⟨op,a,b,inp,_,ha,hb⟩ := newG
        have sub' {k} (hk : k ∈ S) : k < gs.length := Finset.mem_range.mp (sub hk)
        have fr' {k} (hk : k ∈ S) : fresh (gs++[g]) k := by
          intro i hi
          obtain ⟨x,hx,hne⟩ := fr k hk i hi
          have hk' := sub' hk
          exact ⟨x,hx,by rwa [before _ _ _ (by clear * - hi hk'; lia -abstractProof),
            before _ _ _ (by clear * - hk'; lia -abstractProof)]⟩
        by_cases dup : ∃ i < 26+gs.length, ∀ x, F x → val gs x i = val (gs++[g]) x (26+gs.length)
        · obtain ⟨i,hi,rep⟩ := dup
          let r' (k : ℕ) := if k=26+gs.length then r i else r k
          refine ⟨ds,r',S,md,ct,fun k hk => Finset.mem_range.mpr (eqLen ▸ Nat.lt_succ_of_lt (sub' hk)),
            fun _ hk => fr' hk,?_,?_⟩
          · intro k hk
            by_cases e : k=26+gs.length
            · simpa [r',e] using valid i hi
            · simpa [r',e] using valid k (by clear * - hk eqLen e; lia -abstractProof)
          · intro x hx k hk
            by_cases e : k=26+gs.length
            · simpa [r',e] using (agree x hx i hi).trans (rep x hx)
            · have hk' : k < 26+gs.length := by clear * - hk eqLen e; lia -abstractProof
              simpa [r',e,before gs g x hk'] using agree x hx k hk'
        · let d : Gate := ⟨g.op,[r a,r b]⟩
          let r' (i : ℕ) := if i=26+gs.length then 26+ds.length else r i
          have nS : gs.length ∉ S := fun h => (Nat.lt_irrefl _) (sub' h)
          have dl : (ds++[d]).length = ds.length+1 := by simp
          refine ⟨ds++[d],r',insert gs.length S,?_,?_,?_,?_,?_,?_⟩
          · intro z hz
            rcases List.mem_append.mp hz with h | h
            · exact md z h
            · obtain rfl := List.mem_singleton.mp h
              exact ⟨op,le_rfl⟩
          · rw [Finset.card_insert_of_notMem nS, dl, ct]
          · intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hk <;> apply Finset.mem_range.mpr
            · rw [eqLen]; exact Nat.lt_succ_self _
            · rw [eqLen]; exact Nat.lt_succ_of_lt (sub' hk)
          · intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hk
            · intro i hi
              by_contra! no
              apply dup
              refine ⟨i,hi,fun x hx => ?_⟩
              exact (before _ _ x hi).symm.trans (no x hx)
            · exact fr' hk
          · intro i hi
            by_cases e : i = 26+gs.length
            · simp [r',e,dl]
            · have h := valid i (by clear * - hi eqLen e; lia -abstractProof)
              simp only [r',e,ite_false]; rw [dl]; exact Nat.lt_succ_of_lt h
          · intro x hx i hi
            by_cases e : i = 26+gs.length
            · rw [e,show r' (26+gs.length) = 26+ds.length by simp [r'],last,last,inp]
              change g.op.eval ([r a,r b].map _) = g.op.eval ([a,b].map _)
              simp only [List.map_cons,List.map_nil,agree x hx a ha,agree x hx b hb]
            · have h : i < 26+gs.length := by clear * - hi eqLen e; lia -abstractProof
              simp only [r',e,ite_false,before _ _ _ (valid i h),before gs g x h,agree x hx i h]
    obtain ⟨ds,r,S,md,ct,sub,fr,_,agree⟩ := pack C.gates gates
    have live : C.output < 26+C.gates.length := by
      by_contra! outside
      let x : X := fun _ => true
      have yes := (spec x).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩
      change (C.gates.foldl st (List.ofFn x)).getD C.output false = true at yes
      rw [List.getD_eq_default _ _ (by rwa [lens,List.length_ofFn])] at yes
      contradiction
    -- Translate the line to zero and rotate its four incident points.
    let P : Fin 13 → Fin 13 := ![1,3,2,9,5,6,12,8,4,0,11,7,10]
    let L : Fin 13 → Fin 13 := ![0,2,6,9,5,3,12,8,4,10,11,7,1]
    let A (f : Fin 13 → Fin 13) (d z : Fin 13) :=
      if d = 0 then z else if d = 1 then f (f (f z)) else if d = 3 then f (f z) else f z
    have rot : ∀ d : Fin 13, I d 0 → A P d d = 0 ∧ A L d 0 = 0 ∧
        (∀ a b, I a b ↔ I (A P d a) (A L d b)) ∧
        (∀ z, ∃ a, A P d a = z) ∧ (∀ z, ∃ b, A L d b = z) := by decide
    have shift : ∀ a b s : Fin 13, I (a-s) (b-s) ↔ I a b := by decide
    let d := p-l
    obtain ⟨hp,hl,inc,ontoP,ontoL⟩ := rot d (by simpa [d] using (shift p l l).2 edge)
    let α := fun z => A P d (z-l)
    let β := fun z => A L d (z-l)
    have rel (a b) : I a b ↔ I (α a) (β b) := (shift a b l).symm.trans (inc _ _)
    let q : Fin 26 → Fin 26 := Fin.addCases (m := 13) (n := 13) (motive := fun _ => Fin 26)
      (fun a => Fin.castAdd 13 (α a)) (fun b => Fin.natAdd 13 (β b))
    have qp (a) : q (Fin.castAdd 13 a) = Fin.castAdd 13 (α a) := Fin.addCases_left a
    have ql (b) : q (Fin.natAdd 13 b) = Fin.natAdd 13 (β b) := Fin.addCases_right b
    let idx (i : ℕ) := if h : i < 26 then (q ⟨i,h⟩).val else i
    let ren (g : Gate) : Gate := ⟨g.op,g.inputs.map idx⟩
    have idxHi {i} (h : 26 ≤ i) : idx i = i := dite_eq_right (Nat.not_lt.mpr h)
    have idxLt {i n} (h : i < 26+n) : idx i < 26+n := by
      by_cases hi : i < 26
      · simp only [idx,dite_eq_left hi]
        exact lt_of_lt_of_le (q ⟨i,hi⟩).isLt (Nat.le_add_right _ _)
      · rwa [idxHi (Nat.not_lt.mp hi)]
    have corr (gs : List Gate) (y : X) (i : ℕ) :
        val (gs.map ren) y (idx i) = val gs (y ∘ q) i := by
      induction gs using List.reverseRecOn generalizing i with
      | nil =>
        change (List.ofFn y).getD (idx i) false = (List.ofFn (y ∘ q)).getD i false
        by_cases h : i < 26
        · simp only [idx,dite_eq_left h]
          rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (q ⟨i,h⟩).isLt),
            List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]),List.getElem_ofFn,List.getElem_ofFn]
          rfl
        · rw [idxHi (Nat.not_lt.mp h),List.getD_eq_default _ _ (by simpa using Nat.not_lt.mp h),
            List.getD_eq_default _ _ (by simpa using Nat.not_lt.mp h)]
      | append_singleton gs g ih =>
        simp only [List.map_append,List.map_cons,List.map_nil]
        by_cases low : i < 26+gs.length
        · rw [before _ _ _ (by rw [List.length_map]; exact idxLt low),before _ _ _ low]
          exact ih i
        by_cases eq : i = 26+gs.length
        · subst i
          rw [idxHi (Nat.le_add_right _ _),←List.length_map (f := ren) (as := gs),last,
            List.length_map,last]
          change g.op.eval ((g.inputs.map idx).map _) = g.op.eval (g.inputs.map _)
          rw [List.map_map]
          exact congrArg g.op.eval (List.map_congr_left (fun u _ => ih u))
        · have big : 26+gs.length+1 ≤ i := by clear * - low eq; lia -abstractProof
          rw [idxHi (by clear * - big; lia -abstractProof)]
          change ((gs.map ren ++ [ren g]).foldl st _).getD i false = ((gs++[g]).foldl st _).getD i false
          rw [List.getD_eq_default _ _ (by rw [lens,List.length_ofFn,List.length_append,List.length_map]; exact big),
            List.getD_eq_default _ _ (by rw [lens,List.length_ofFn,List.length_append]; exact big)]
    let B : Circuit := ⟨ds.map ren,idx (r C.output)⟩
    have mm : Monotone2 B := by
      intro g hg
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
      exact ⟨(md z hz).1,by change (z.inputs.map idx).length ≤ 2; rw [List.length_map]; exact (md z hz).2⟩
    have bound := face B mm (by
      intro y y0 y13
      change val (ds.map ren) y (idx (r C.output)) = true ↔ _
      have fp : α p = 0 := hp
      have fl : β l = 0 := by simpa only [β,sub_self] using hl
      have hF : F (y ∘ q) := by
        change y (q (Fin.castAdd 13 p)) = false ∧ y (q (Fin.natAdd 13 l)) = false
        rw [qp,ql,fp,fl]; exact ⟨y0,y13⟩
      rw [corr,agree _ hF C.output live]
      change C.eval (List.ofFn (y ∘ q)) = true ↔ _
      rw [spec]
      simp only [Function.comp_apply,qp,ql]
      constructor
      · rintro ⟨a,b,h,ha,hb⟩
        exact ⟨α a,β b,(rel _ _).mp h,ha,hb⟩
      · rintro ⟨a,b,h,ha,hb⟩
        obtain ⟨u,hu⟩ := ontoP a
        obtain ⟨v,hv⟩ := ontoL b
        have ea : α (u+l) = a := by simpa only [α,add_sub_cancel_right] using hu
        have eb : β (v+l) = b := by simpa only [β,add_sub_cancel_right] using hv
        refine ⟨u+l,v+l,(rel _ _).mpr ?_,?_,?_⟩
        · simpa only [ea,eb] using h
        · simpa only [ea] using ha
        · simpa only [eb] using hb)
    refine ⟨S,sub,by change 56 ≤ (ds.map ren).length at bound; rwa [List.length_map,ct] at bound,?_⟩
    intro j hj i hi
    obtain ⟨x,⟨h1,h2⟩,h3⟩ := fr j hj i hi
    exact ⟨x,h1,h2,h3⟩
  let R (t a w : ℕ) := ∃ (j b : ℕ) (g : Gate), w = 26+j ∧ C.gates[j]? = some g ∧
    (g.inputs = [a,b] ∨ g.inputs = [b,a]) ∧ (g.op = .or ∨ V (fun k => decide (k.val=t)) b = true)
  have carry (t : ℕ) (d : ℕ → Bool) (init : d (13-t) = true)
      (rec : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (26+j) = ((V (fun k => decide (k.val=t)) a && d b) ||
          (d a && V (fun k => decide (k.val=t)) b))) ∧
        (g.op = .or → d (26+j) = (d a || d b))) :
      ∀ w, Relation.ReflTransGen (R t) (13-t) w → d w = true := by
    intro w h
    induction h with
    | refl => exact init
    | tail _ step ih =>
      obtain ⟨j,b,g,rfl,hg,inputs,pass⟩ := step
      have ops := (gates j g hg).1
      rcases inputs with e | e
      · obtain ⟨a',o'⟩ := rec _ _ _ _ hg e
        rcases ops with h | h
        · rcases pass with bad | side
          · rw [h] at bad; contradiction
          · simp [a' h,ih,side]
        · simp [o' h,ih]
      · obtain ⟨a',o'⟩ := rec _ _ _ _ hg e
        rcases ops with h | h
        · rcases pass with bad | side
          · rw [h] at bad; contradiction
          · simp [a' h,ih,side]
        · simp [o' h,ih]
  rcases path C ao nodup sizeC spec faces with h | h
  · have start : v (13-0) = true := (vi 13 (by decide)).trans (by decide)
    exact Bool.noConfusion ((carry 0 v start vg C.output h).symm.trans vf)
  · have start : u (13-13) = true := (ui 0 (by decide)).trans (by decide)
    exact Bool.noConfusion ((carry 13 u start ug C.output h).symm.trans uf)
