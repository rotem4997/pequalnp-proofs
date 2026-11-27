import PEqualNP.Defs

-- The circuit evaluation lemmas follow L_meta_2868 and willakone's L_meta_2051.
-- The four-cycle and biclique arguments adapt L_meta_1878 and L_meta_1491.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership


theorem PEqualNP.Outside.R_meta_5326_813
    (packing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    NoFourCycle G → IsAO2 n C →
    ∀ (z : Fin C.size → Fin n) (o : Fin C.size → ℕ) (U : Finset (Fin C.size)),
    (∀ i ∈ U, (C.gates.get i).op = GateOp.and ∧
      ∀ x : Fin n → Bool, x (z i)=true → wireVal n C (o i) x=true → graphFun G ∅ x=true) →
    (∀ i ∈ U, wireVal n C (o i) (fun v => decide (¬G.Adj (z i) v))=false) →
    (G.edgeFinset.filter (fun e : Sym2 (Fin n) => ∃ i ∈ U, ∃ p, e=s(z i,p) ∧
      wireVal n C (o i) (pairInput p p)=true)).card ≤ C.size)
    (obstruction : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    Nat.card {e : Sym2 (Fin n) // e ∈ Ustar G C ∧ ∃ u v, e=s(u,v) ∧ ∃ i ∈ tops G C, ∃ b : Fin 2,
      let W := wireVal n C (opnd C i b)
      let V := wireVal n C (opnd C i (1-b))
      (∀ w, W (pairInput w w)=true ↔ w=u) ∧ V (pairInput v v)=true ∧
      ∃ S : Finset (Fin n), (∀ w ∈ S, ¬G.Adj u w) ∧ (∃ j ∈ S, ∃ t ∈ S, G.Adj j t) ∧
      let test := fun B : Finset (Fin n) => V (fun w => decide (w∈B))
      test S=true ∧ ∀ w ∈ S, test (S.erase w)=false} ≤ k*(C.size+1)) :
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [_x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.true ∧ PEqualNP.CleanedNonEdge.wireVal x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  let wf (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
      wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
    simp [wf, List.foldl_append]
  have wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
    induction gs with
    | nil => intro w; simp [wf]
    | cons g gs ih =>
      intro w
      have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      simp only [wf, List.foldl_cons] at this ⊢
      rw [this]; simp; omega
  have wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wf gs w).getD i false = w.getD i false := by
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
      simp only [wf, List.foldl_cons] at this ⊢
      rw [this]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length + pre.length) :
      (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
    have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
    rw [this]
    exact wf_keep post _ i (by rw [wf_len]; exact hi)
  have getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
    simp [List.getD_eq_getElem?_getD]
  have wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
      (hk : k ≤ gates.length) :
      (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
    conv_lhs => rw [← List.take_append_drop k gates]
    exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)
  have gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
      (wf gates X).getD (X.length + k) false
        = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
    rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
    have := getD_snoc_eq (wf (gates.take k) X)
      (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
    rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
    exact this
  let val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
    (wf gates (List.ofFn x)).getD w false
  have iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
      (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
        i < n + k ∧ val gates i x = true := by
    by_cases hi : i < n + k
    · dsimp only [val]; rw [wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
      simp [hi]
    · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
      simp [hi]
  have val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
      (hop : gates[k].op = GateOp.and) :
      val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
    have := gate_val gates (List.ofFn x) k hk
    rw [List.length_ofFn] at this
    dsimp only [val]; rw [this, hop]
    delta GateOp.eval; simp only [List.all_map, List.all_eq_true, Function.comp, id]
    constructor
    · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
    · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)
  have val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
      (hop : gates[k].op = GateOp.or) :
      val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
    have := gate_val gates (List.ofFn x) k hk
    rw [List.length_ofFn] at this
    dsimp only [val]; rw [this, hop]
    delta GateOp.eval; simp only [List.any_map, List.any_eq_true, Function.comp, id]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩
  have val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
      val gates w x = x ⟨w, hw⟩ := by
    dsimp only [val]; rw [wf_keep gates _ w (by simpa using hw)]
    simp [List.getD_eq_getElem?_getD, hw]
  have val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
      (hw : n + gates.length ≤ w) : val gates w x = false := by
    dsimp only [val]; rw [List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]
  have val_mono (gates : List Gate) {n : ℕ}
      (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
      ∀ w, val gates w x = true → val gates w x' = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro h
      by_cases hwn : w < n
      · rw [val_input gates _ w hwn] at h ⊢
        exact hx _ h
      · by_cases hbig : n + gates.length ≤ w
        · rw [val_big gates x w hbig] at h
          exact Bool.noConfusion h
        · have hi : w - n < gates.length := by omega
          have he : n + (w - n) = w := by omega
          rw [← he] at h ⊢
          rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
          · apply (val_and gates x' (w - n) hi ha).2
            intro j hj
            obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
            exact ⟨hjlt, ih j (by omega) hjv⟩
          · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
            exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩
  have biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
      (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
      (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
      A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
    obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
    exact h4 a b c d hac hbd
      ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩
  have pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
    delta pairInput; simp
  have graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
      graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    delta graphFun; simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pairInput_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (G.irrefl hab).elim
      · exact hab
      · exact hab.symm
      · exact (G.irrefl hab).elim
    · intro h
      exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
  have no4 {n : ℕ} (G : SimpleGraph (Fin n))
      (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
      (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
      (hac : a ≠ c) (hbd : b ≠ d) : False := by
    have e1 := G.ne_of_adj hab
    have e2 := G.ne_of_adj hbc
    have e3 := G.ne_of_adj hcd
    have e4 := G.ne_of_adj hda
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e2, e3, e4, hbd, Ne.symm e1, Ne.symm hac]
      · simp [e1, e2, hac, hbd, Ne.symm e1, Ne.symm e4]
    have h5 := hg a _ hcyc
    simp at h5
  have noFourCycle {n : ℕ} (G : SimpleGraph (Fin n))
      (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) [DecidableRel G.Adj] :
      NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨ax,bx⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨ay,by'⟩ := (Finset.mem_filter.mp hy).2
    by_contra hxy
    exact no4 G girth a x b y ax bx.symm by' ay.symm hab hxy
  let support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
    Finset.univ.filter fun v => wireVal n C w (pairInput v v) = true
  have top_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (i : ℕ) (hit : i ∈ tops G C) : i<C.size := by
    let : DecidableEq GateOp := gateOpDecEq
    unfold tops gatesWhere at hit
    exact Finset.mem_range.mp (Finset.mem_filter.mp hit).1
  have support_iff {n : ℕ} {C : Circuit} {w : ℕ} {v : Fin n} :
      v ∈ support (n:=n) C w ↔ wireVal n C w (pairInput v v)=true := by simp [support]
  have extend {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (v : Fin n) (w : ℕ)
      (on : wireVal n C w (pairInput v v)=true) (x : Fin n → Bool) (xv : x v=true) :
      wireVal n C w x=true := by
    apply val_mono C.gates (fun g hg => ⟨by simpa using ao.1 g hg, (ao.2.2 g hg).le⟩)
      (pairInput v v) x _ w on
    intro i hi
    have e : i=v := by exact Or.elim ((pairInput_true _ _ _).mp hi) id id
    simpa [e] using xv
  have top_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (ao : IsAO2 n C) (t : Fin C.size) (ht : t.val ∈ tops G C) :
      opnd C t.val 0 < n+C.size ∧ opnd C t.val 1 < n+C.size ∧
      ∀ x, wireVal n C (opnd C t.val 0) x = true → wireVal n C (opnd C t.val 1) x = true → graphFun G ∅ x = true := by
    let : DecidableEq GateOp := gateOpDecEq
    have len : t.val < C.gates.length := t.isLt
    have geq : gateAt C t.val = C.gates[t.val] := by delta gateAt; simp [List.getD_eq_getElem?_getD,len]
    obtain ⟨_,kind,below⟩ := Finset.mem_filter.mp ht
    have member : gateAt C t.val ∈ C.gates := geq ▸ List.getElem_mem len
    obtain ⟨p,q,pins⟩ := List.length_eq_two.mp (ao.2.2 _ member)
    have p0 : opnd C t.val 0=p := by delta opnd; simp [pins]
    have p1 : opnd C t.val 1=q := by delta opnd; simp [pins]
    have hp : p<n+t.val := ao.2.1 t len p (by simp [pins])
    have hq : q<n+t.val := ao.2.1 t len q (by simp [pins])
    rw [p0,p1]
    refine ⟨by omega,by omega,?_⟩
    intro x ap aq
    apply below x
    apply (val_and C.gates x t.val len (by rwa [←geq])).2
    intro w hw
    rw [←geq,pins] at hw
    rcases (by simpa using hw : w=p ∨ w=q) with rfl | rfl
    · exact ⟨hp,ap⟩
    · exact ⟨hq,aq⟩
  have normalizeWithOrigin {n : ℕ} (hn : 0<n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (girth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
      (ao : IsAO2 n C) :
      ∃ (z : Fin C.size → Fin n) (o : Fin C.size → ℕ) (U : Finset (Fin C.size)),
        (∀ i ∈ U, o i < n+C.size) ∧
        (∀ i ∈ U, (C.gates.get i).op = GateOp.and) ∧
        (∀ i ∈ U, ∀ x, x (z i) = true → wireVal n C (o i) x = true → graphFun G ∅ x = true) ∧
        (∀ i ∈ U, i.val ∈ tops G C ∧ ∃ b : Fin 2,
          wireVal n C (opnd C i.val b) (pairInput (z i) (z i))=true ∧
          o i = opnd C i.val (1-b) ∧
          ∀ w, wireVal n C (opnd C i.val b) (pairInput w w)=true → w=z i) ∧
        ∀ (u v : Fin n) t, t ∈ tops G C → wireVal n C (opnd C t 0) (pairInput u u)=true →
          wireVal n C (opnd C t 1) (pairInput v v)=true →
          ∃ i ∈ U, ∃ p, s(u,v) = s(z i,p) ∧ wireVal n C (o i) (pairInput p p)=true := by
    classical
    let left (i : Fin C.size) := support (n:=n) C (opnd C i 0)
    let right (i : Fin C.size) := support (n:=n) C (opnd C i 1)
    let U := (Finset.univ : Finset (Fin C.size)).filter fun i => i.val ∈ tops G C ∧ (left i).Nonempty ∧ (right i).Nonempty
    have chooseStar (i : Fin C.size) : ∃ c : Fin n, ∃ w : ℕ, i ∈ U → w < n+C.size ∧
        (∀ x, x c=true → wireVal n C w x=true → graphFun G ∅ x=true) ∧
        (∃ b : Fin 2, wireVal n C (opnd C i.val b) (pairInput c c)=true ∧
          w = opnd C i.val (1-b) ∧
          ∀ v, wireVal n C (opnd C i.val b) (pairInput v v)=true → v=c) ∧
        ∀ u ∈ left i, ∀ v ∈ right i, ∃ p, s(u,v)=s(c,p) ∧ wireVal n C w (pairInput p p)=true := by
      by_cases hi : i ∈ U
      · obtain ⟨it,lex,rex⟩ := (Finset.mem_filter.mp hi).2
        obtain ⟨h0,h1,out⟩ := top_data G C ao i it
        have cross (u : Fin n) (hu : u∈left i) (v : Fin n) (hv : v∈right i) : G.Adj u v :=
          (graphFun_pair G u v).mp (out (pairInput u v)
            (extend C ao u _ (support_iff.mp hu) _ (by delta pairInput; simp))
            (extend C ao v _ (support_iff.mp hv) _ (by delta pairInput; simp)))
        have h4 := fun (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d) =>
          fun (h : G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) => no4 G girth a b c d h.1 h.2.1 h.2.2.1 h.2.2.2 hac hbd
        rcases biclique_star G h4 (left i) (right i) cross with l | r
        · obtain ⟨c,mc⟩ := lex
          refine ⟨c,opnd C i 1,fun _ => ⟨h1,fun x hx hw => out x (extend C ao c _ (support_iff.mp mc) x hx) hw,
            ⟨0,support_iff.mp mc,rfl,fun v hv => Finset.card_le_one.mp l v (support_iff.mpr hv) c mc⟩,?_⟩⟩
          intro u hu v hv
          exact ⟨v,by rw [Finset.card_le_one.mp l u hu c mc],support_iff.mp hv⟩
        · obtain ⟨c,mc⟩ := rex
          refine ⟨c,opnd C i 0,fun _ => ⟨h0,fun x hx hw => out x hw (extend C ao c _ (support_iff.mp mc) x hx),
            ⟨1,support_iff.mp mc,rfl,fun v hv => Finset.card_le_one.mp r v (support_iff.mpr hv) c mc⟩,?_⟩⟩
          intro u hu v hv
          exact ⟨u,by rw [Finset.card_le_one.mp r v hv c mc,Sym2.eq_swap],support_iff.mp hu⟩
      · exact ⟨⟨0,hn⟩,0,fun h => False.elim (hi h)⟩
    choose z o spec using chooseStar
    have kind (i : Fin C.size) (hi : i∈U) : (C.gates.get i).op = GateOp.and := by
      let : DecidableEq GateOp := gateOpDecEq
      have it : i.val ∈ tops G C := (Finset.mem_filter.mp hi).2.1
      have op : (gateAt C i.val).op = GateOp.and := (Finset.mem_filter.mp it).2.1
      have lt : i.val < C.gates.length := i.isLt
      change (C.gates[i.val]).op = GateOp.and
      delta gateAt at op; simpa [List.getD_eq_getElem?_getD,lt] using op
    refine ⟨z,o,U,fun i hi => (spec i hi).1,kind,fun i hi => (spec i hi).2.1,
      fun i hi => ⟨(Finset.mem_filter.mp hi).2.1,(spec i hi).2.2.1⟩,?_⟩
    intro u v t ht hu hv
    have len : t<C.size := top_lt G C t ht
    let i : Fin C.size := ⟨t,len⟩
    have ll : u∈left i := support_iff.mpr hu
    have rr : v∈right i := support_iff.mpr hv
    have hi : i∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht,⟨u,ll⟩,⟨v,rr⟩⟩
    exact ⟨i,hi,(spec i hi).2.2.2 u ll v rr⟩
  obtain ⟨k,hk⟩ := obstruction
  refine ⟨k+1,?_⟩
  intro n G _ C girth least top
  have toFilter (s : Finset (Sym2 (Fin n))) (p : Sym2 (Fin n) → Prop) (d : DecidablePred p) :
      Nat.card {e // e∈s ∧ p e} = (@Finset.filter _ p d s).card := by
    let f : {e // e∈s ∧ p e} ≃ ↥(@Finset.filter _ p d s) :=
      Equiv.subtypeEquivRight (fun _ => (@Finset.mem_filter _ p d s _).symm)
    exact (Nat.card_congr f).trans (Nat.card_eq_fintype_card.trans (Fintype.card_coe _))
  have obstruct := hk n G C girth least top
  rw [toFilter _ _ (fun _ => Classical.propDecidable _)] at obstruct
  by_cases hn : 0<n
  · obtain ⟨z,o,U,_,andGate,safe,origin,cover⟩ :=
      normalizeWithOrigin hn G C girth least.1
    let cold (i : Fin C.size) := wireVal n C (o i) (fun v => decide (¬G.Adj (z i) v)) = false
    let D := U.filter cold
    have packed := packing n G C (noFourCycle G girth) least.1 z o D
      (fun i hi => ⟨andGate i (Finset.mem_filter.mp hi).1, safe i (Finset.mem_filter.mp hi).1⟩)
      (fun _ hi => (Finset.mem_filter.mp hi).2)
    have minimum (i : Fin C.size) (hi : i ∈ U) (hhot : ¬cold i) :
        ∃ S : Finset (Fin n), (∀ w ∈ S, ¬G.Adj (z i) w) ∧ (∃ j ∈ S, ∃ t ∈ S, G.Adj j t) ∧
          let test := fun B : Finset (Fin n) => wireVal n C (o i) (fun w => decide (w∈B))
          test S=true ∧ ∀ w∈S, test (S.erase w)=false := by
      let N := Finset.univ.filter (fun w => ¬ G.Adj (z i) w)
      let P (B : Finset (Fin n)) := wireVal n C (o i) (fun w => decide (w∈B))=true
      have hN : P N := by
        have h : wireVal n C (o i) (fun v => decide (¬G.Adj (z i) v)) = true :=
          Bool.eq_true_of_not_eq_false hhot
        simpa [P,N] using h
      obtain ⟨S,hSN,hmin⟩ := exists_minimal_le_of_wellFoundedLT P N hN
      have hnbr (w : Fin n) (hw : w∈S) : ¬ G.Adj (z i) w := (Finset.mem_filter.mp (hSN hw)).2
      have erase (w : Fin n) (hw : w∈S) : ¬P (S.erase w) := by
        intro hp
        have incl := hmin.2 hp (Finset.erase_subset w S)
        exact (Finset.notMem_erase w S) (incl hw)
      refine ⟨S,hnbr,?_,hmin.1,fun w hw => Bool.eq_false_iff.mpr (erase w hw)⟩
      let x (w : Fin n) := decide (w=z i ∨ w∈S)
      have hx : wireVal n C (o i) x = true :=
        val_mono C.gates
          (fun g hg => ⟨least.1.1 g hg,(least.1.2.2 g hg).le⟩)
          (fun w : Fin n => decide (w∈S)) x
          (fun w hw => decide_eq_true (Or.inr (of_decide_eq_true hw))) _ hmin.1
      have hf := safe i hi x (by simp [x]) hx
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true at hf; simp only [Finset.notMem_empty,false_and,exists_false,decide_false,
        Bool.false_or,decide_eq_true_eq,x] at hf
      obtain ⟨a,b,hab,ha,hb⟩ := hf
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (G.irrefl hab).elim
      · exact (hnbr b hb hab).elim
      · exact (hnbr a ha hab.symm).elim
      · exact ⟨a,ha,b,hb,hab⟩
    apply le_trans (b := C.size+k*(C.size+1))
    · refine le_trans (Finset.card_le_card ?_)
        ((Finset.card_union_le _ _).trans (Nat.add_le_add packed obstruct))
      intro e he
      obtain ⟨heU,u,v,he,t,ht,hu,hv⟩ := Finset.mem_filter.mp he
      obtain ⟨i,hi,p,hp,hptrue⟩ := cover u v t ht hu hv
      have eq := he.trans hp
      rw [Finset.mem_union]
      by_cases hc : cold i
      · exact Or.inl (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp heU).1,i,Finset.mem_filter.mpr ⟨hi,hc⟩,p,eq,hptrue⟩)
      · obtain ⟨htop,b,hs,hw,unique⟩ := origin i hi
        right
        apply (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) (Ustar G C) e).2
        refine ⟨heU,z i,p,eq,i.val,htop,b,?_,?_,?_⟩
        · intro w
          exact ⟨unique w, fun he => he ▸ hs⟩
        · rw [← hw]; exact hptrue
        · rw [← hw]; exact minimum i hi hc
    · rw [Nat.add_mul,one_mul]
      omega
  · have h0 : n=0 := by omega
    subst n
    apply le_trans (b := 0)
    · refine Nat.le_of_eq (Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr ?_))
      intro e he
      obtain ⟨u,_⟩ := (Finset.mem_filter.mp he).2
      exact Fin.elim0 u
    · omega
